// aig.hpp -- And-Inverter Graph with structural hashing and 64-bit parallel
// simulation. Literal encoding: lit = 2*var + phase. var 0 is constant FALSE
// (lit 0 = false, lit 1 = true).
#pragma once
#include <cassert>
#include <cstdint>
#include <random>
#include <unordered_map>
#include <vector>

struct Aig
{
  struct Node
  {
    int f0 = -1, f1 = -1; // fanin literals; PI/const: -1
  };
  std::vector<Node> nodes; // index = var
  std::vector<int> pis;    // var ids
  std::unordered_map<uint64_t, int> strash;

  // simulation state: one vector<uint64_t> per var
  std::vector<std::vector<uint64_t>> sim;
  int simWords = 0;

  Aig () { nodes.push_back (Node ()); } // var 0 = const0

  static int
  mkLit (int var, bool ph)
  {
    return 2 * var + (ph ? 1 : 0);
  }
  static int
  litVar (int lit)
  {
    return lit >> 1;
  }
  static bool
  litPh (int lit)
  {
    return lit & 1;
  }
  static int
  litNot (int lit)
  {
    return lit ^ 1;
  }

  bool
  isPi (int var) const
  {
    return nodes[var].f0 < 0 && var != 0;
  }
  bool
  isAnd (int var) const
  {
    return nodes[var].f0 >= 0;
  }
  int
  numVars () const
  {
    return (int)nodes.size ();
  }

  int
  newPi ()
  {
    int v = (int)nodes.size ();
    nodes.push_back (Node ());
    pis.push_back (v);
    return 2 * v;
  }

  int
  mkAnd (int a, int b)
  {
    if (a > b)
      std::swap (a, b);
    if (a == 0)
      return 0; // 0 & x = 0
    if (a == 1)
      return b; // 1 & x = x
    if (a == b)
      return a; // x & x = x
    if ((a ^ b) == 1)
      return 0; // x & !x = 0
    uint64_t key = ((uint64_t)a << 32) | (uint32_t)b;
    auto it = strash.find (key);
    if (it != strash.end ())
      return 2 * it->second;
    int v = (int)nodes.size ();
    Node n;
    n.f0 = a;
    n.f1 = b;
    nodes.push_back (n);
    strash.emplace (key, v);
    return 2 * v;
  }
  int
  mkOr (int a, int b)
  {
    return litNot (mkAnd (litNot (a), litNot (b)));
  }
  int
  mkXor (int a, int b)
  {
    return mkOr (mkAnd (a, litNot (b)), mkAnd (litNot (a), b));
  }
  int
  mkMux (int s, int t, int e)
  { // s ? t : e
    return mkOr (mkAnd (s, t), mkAnd (litNot (s), e));
  }

  // ---------- simulation ----------
  void
  simInit (int words, uint64_t seed = 0x5eed5eedULL)
  {
    simWords = words;
    sim.assign (nodes.size (), {});
    std::mt19937_64 rng (seed);
    for (auto &s : sim)
      s.assign (words, 0);
    for (int v : pis)
      for (int w = 0; w < words; w++)
        sim[v][w] = rng ();
    simRecompute ();
  }
  void
  simEnsure ()
  { // extend sim arrays after nodes added
    while ((int)sim.size () < (int)nodes.size ())
      sim.push_back (std::vector<uint64_t> (simWords, 0));
  }
  void
  simRecompute ()
  {
    simRecomputeWords (0, simWords);
  }
  // recompute only word range [wLo, wHi) -- cheap refresh after pattern
  // injection
  void
  simRecomputeWords (int wLo, int wHi)
  {
    simEnsure ();
    for (int v = 1; v < (int)nodes.size (); v++)
      {
        if (!isAnd (v))
          continue;
        const Node &n = nodes[v];
        const auto &s0 = sim[litVar (n.f0)];
        const auto &s1 = sim[litVar (n.f1)];
        uint64_t m0 = litPh (n.f0) ? ~0ULL : 0ULL;
        uint64_t m1 = litPh (n.f1) ? ~0ULL : 0ULL;
        auto &d = sim[v];
        for (int w = wLo; w < wHi; w++)
          d[w] = (s0[w] ^ m0) & (s1[w] ^ m1);
      }
  }
  // drop all nodes/PIs created at or above nVars (per-round scratch cleanup)
  void
  rollback (int nVars)
  {
    if ((int)nodes.size () <= nVars)
      return;
    for (auto it = strash.begin (); it != strash.end ();)
      {
        if (it->second >= nVars)
          it = strash.erase (it);
        else
          ++it;
      }
    nodes.resize (nVars);
    pis.erase (std::remove_if (pis.begin (), pis.end (),
                               [&] (int v) { return v >= nVars; }),
               pis.end ());
    if ((int)sim.size () > nVars)
      sim.resize (nVars);
  }
  // add one extra pattern (bit position) from a PI assignment; caller
  // resimulates in batch patterns are appended into word slot `slot`, bit
  // `bit`.
  void
  simSetPiBit (int var, int slot, int bit, bool val)
  {
    if (val)
      sim[var][slot] |= (1ULL << bit);
    else
      sim[var][slot] &= ~(1ULL << bit);
  }
  uint64_t
  simWord (int lit, int w) const
  {
    uint64_t s = sim[litVar (lit)][w];
    return litPh (lit) ? ~s : s;
  }
  bool
  simBit (int lit, int w, int b) const
  {
    return (simWord (lit, w) >> b) & 1;
  }

  // signature for equivalence bucketing: phase-normalized hash of all sim
  // words
  uint64_t
  signature (int var) const
  {
    const auto &s = sim[var];
    bool ph = s[0] & 1; // normalize so bit0 == 0
    uint64_t h = 1469598103934665603ULL;
    for (int w = 0; w < simWords; w++)
      {
        uint64_t x = ph ? ~s[w] : s[w];
        h = (h ^ x) * 1099511628211ULL;
      }
    return h;
  }
};
