// rectify.hpp -- SAT-based internal-point rectification.
// Iteratively picks a net t in G1 and a replacement function f(existing nets)
// such that substituting t := f fixes failing POs while preserving passing
// ones. Validity: UNSAT( bad0(m) & bad1(m) ) where bad_v = OR_po( G1po[t->v]
// != R2po ). Function synthesis: divisor support selection by
// counterexample-guided greedy covering + truth-table enumeration over the
// chosen support (<= 8 divisors).
#pragma once
#include <algorithm>
#include <array>
#include <chrono>
#include <functional>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "aig.hpp"
#include "netlist.hpp"
#include "sat.hpp"

struct RectifyFix
{
  std::string target; // net name in G1
  int paigLit;        // function in patch AIG over patch PIs
};

struct Rectifier
{
  Aig &aig;
  SatAig &sat;
  Netlist &G;                                      // g1 netlist
  std::vector<int> &gNetLit;                       // original g1 net -> lit
  const std::unordered_map<std::string, int> &rPo; // po name -> r2 lit
  const std::unordered_map<std::string, int> &piLitByName;
  Aig &paig;
  std::function<int (const std::string &)>
      supportOf;                                    // port name -> paig PI lit
  std::unordered_map<int, std::string> &paigPiName; // paig PI var -> name

  std::vector<RectifyFix> fixes;
  std::set<std::string> targetSet;
  std::set<std::string>
      knownSup; // support names already paid for by accepted fixes
  bool verbose = false;
  int maxFixCostPerPo = 16; // reject fixes costlier than this per fixed PO
  long workBudget = 9000; // rectification budget in SAT calls (deterministic)
  long pairWorkBudget = 2500; // extra SAT-call budget for the pair phase
  uint64_t simSeed = 0x5eed5eedULL;
  long workStart = 0;
  std::vector<std::pair<std::string, int>>
      rPoOrdered; // name-sorted (deterministic)

  // current circuit state
  std::unordered_map<int, int>
      patchedDrv;          // netId -> paig lit (overrides gate)
  std::vector<int> curLit; // netId -> main aig lit

  Rectifier (Aig &a, SatAig &s, Netlist &g, std::vector<int> &gl,
             const std::unordered_map<std::string, int> &rpo,
             const std::unordered_map<std::string, int> &piln, Aig &pa,
             std::function<int (const std::string &)> sof,
             std::unordered_map<int, std::string> &ppn)
      : aig (a), sat (s), G (g), gNetLit (gl), rPo (rpo), piLitByName (piln),
        paig (pa), supportOf (sof), paigPiName (ppn)
  {
    for (auto &kv : rPo)
      rPoOrdered.push_back (kv);
    std::sort (rPoOrdered.begin (), rPoOrdered.end ());
  }

  // deterministic budget: counted in SAT calls, not wall clock
  bool
  timeUp () const
  {
    return sat.numCalls - workStart > workBudget;
  }

  // evaluate paig literal into main aig, with paig-PI substitution values
  int
  evalPaig (int pl, std::unordered_map<int, int> &sub,
            std::unordered_map<int, int> &memo)
  {
    int v = Aig::litVar (pl);
    auto it = memo.find (v);
    int base;
    if (it != memo.end ())
      base = it->second;
    else if (v == 0)
      base = 0;
    else if (!paig.isAnd (v))
      base = sub.at (v);
    else
      {
        int a = evalPaig (paig.nodes[v].f0, sub, memo);
        int b = evalPaig (paig.nodes[v].f1, sub, memo);
        base = aig.mkAnd (a, b);
      }
    memo[v] = base;
    return base ^ Aig::litPh (pl);
  }

  // recompute curLit for the whole patched circuit
  void
  recompute ()
  {
    std::unordered_map<int, int> noForce;
    evalInto (curLit, noForce);
  }
  // evaluate the patched circuit; `forced` nets take the given literals
  void
  evalInto (std::vector<int> &curLit,
            const std::unordered_map<int, int> &forced)
  {
    curLit.assign (G.netName.size (), -1);
    curLit[0] = 0;
    curLit[1] = 1;
    for (int pi : G.pis)
      if (!patchedDrv.count (pi))
        curLit[pi] = gNetLit[pi]; // patched PI: eval below
    for (auto &[nid, l] : forced)
      curLit[nid] = l;
    // readiness: gate ins, or patch fn support names
    std::vector<std::vector<int>> needs (G.netName.size ());
    std::vector<int> drvGate (G.netName.size (), -1);
    for (size_t gi = 0; gi < G.gates.size (); gi++)
      drvGate[G.gates[gi].out] = (int)gi;
    auto insOf = [&] (int nid)
      {
        std::vector<int> ins;
        auto pit = patchedDrv.find (nid);
        if (pit != patchedDrv.end ())
          {
            // supports of the paig cone
            std::unordered_set<int> seen;
            std::vector<int> st{ Aig::litVar (pit->second) };
            while (!st.empty ())
              {
                int v = st.back ();
                st.pop_back ();
                if (v == 0 || seen.count (v))
                  continue;
                seen.insert (v);
                if (!paig.isAnd (v))
                  {
                    const std::string &nm = paigPiName.at (v);
                    std::string base = nm;
                    if (base.size () > 3
                        && base.substr (base.size () - 3) == "_in")
                      base = base.substr (0, base.size () - 3);
                    // _in refers to the ORIGINAL driver cone; treat as
                    // dependency on the original gate's inputs
                    if (nm != base)
                      {
                        auto dit = G.netId.find (base);
                        if (dit != G.netId.end () && drvGate[dit->second] >= 0)
                          for (int i2 : G.gates[drvGate[dit->second]].ins)
                            ins.push_back (i2);
                      }
                    else
                      {
                        auto nit = G.netId.find (nm);
                        if (nit != G.netId.end ())
                          ins.push_back (nit->second);
                      }
                  }
                else
                  {
                    st.push_back (Aig::litVar (paig.nodes[v].f0));
                    st.push_back (Aig::litVar (paig.nodes[v].f1));
                  }
              }
          }
        else if (drvGate[nid] >= 0)
          {
            ins = G.gates[drvGate[nid]].ins;
          }
        return ins;
      };
    // worklist evaluation
    bool progress = true;
    std::vector<int> pend;
    for (int nid = 2; nid < (int)G.netName.size (); nid++)
      if (curLit[nid] == -1 && (patchedDrv.count (nid) || drvGate[nid] >= 0))
        pend.push_back (nid);
    while (progress)
      {
        progress = false;
        for (int nid : pend)
          {
            if (curLit[nid] != -1)
              continue;
            auto deps = insOf (nid);
            bool ready = true;
            for (int d : deps)
              if (curLit[d] == -1)
                {
                  ready = false;
                  break;
                }
            if (!ready)
              continue;
            auto pit = patchedDrv.find (nid);
            if (pit != patchedDrv.end ())
              {
                std::unordered_map<int, int> sub, memo;
                collectSub (pit->second, sub);
                curLit[nid] = evalPaig (pit->second, sub, memo);
              }
            else
              {
                const Gate &g = G.gates[drvGate[nid]];
                std::vector<int> lits;
                for (int in : g.ins)
                  lits.push_back (curLit[in]);
                curLit[nid] = gateFn (g.type, lits);
              }
            progress = true;
          }
      }
  }
  // gather substitution map paigPI var -> main lit (current values / _in
  // originals)
  void
  collectSub (int pl, std::unordered_map<int, int> &sub)
  {
    std::unordered_set<int> seen;
    std::vector<int> st{ Aig::litVar (pl) };
    while (!st.empty ())
      {
        int v = st.back ();
        st.pop_back ();
        if (v == 0 || seen.count (v))
          continue;
        seen.insert (v);
        if (!paig.isAnd (v))
          {
            const std::string &nm = paigPiName.at (v);
            sub[v] = litForPortName (nm);
          }
        else
          {
            st.push_back (Aig::litVar (paig.nodes[v].f0));
            st.push_back (Aig::litVar (paig.nodes[v].f1));
          }
      }
  }
  // value for a patch input port name in the CURRENT circuit
  int
  litForPortName (const std::string &nm)
  {
    std::string base = nm;
    bool isIn = false;
    if (base.size () > 3 && base.substr (base.size () - 3) == "_in")
      {
        std::string b2 = base.substr (0, base.size () - 3);
        if (targetSet.count (b2))
          {
            base = b2;
            isIn = true;
          }
      }
    int nid = G.netId.at (base);
    if (isIn)
      {
        // original driver's function over current values
        if (piLitByName.count (base) && !gateDriven (nid))
          return piLitByName.at (base);
        const Gate &g = G.gates[gateIdx (nid)];
        std::vector<int> lits;
        for (int in : g.ins)
          lits.push_back (curLit[in]);
        return gateFn (g.type, lits);
      }
    return curLit[nid];
  }
  bool
  gateDriven (int nid) const
  {
    for (auto &g : G.gates)
      if (g.out == nid)
        return true;
    return false;
  }
  int
  gateIdx (int nid) const
  {
    for (size_t i = 0; i < G.gates.size (); i++)
      if (G.gates[i].out == nid)
        return (int)i;
    return -1;
  }
  int
  gateFn (const std::string &type, const std::vector<int> &lits)
  {
    auto foldAnd = [&] (bool inv)
      {
        int acc = 1;
        for (int l : lits)
          acc = aig.mkAnd (acc, l);
        return inv ? Aig::litNot (acc) : acc;
      };
    auto foldOr = [&] (bool inv)
      {
        int acc = 0;
        for (int l : lits)
          acc = aig.mkOr (acc, l);
        return inv ? Aig::litNot (acc) : acc;
      };
    if (type == "and")
      return foldAnd (false);
    if (type == "nand")
      return foldAnd (true);
    if (type == "or")
      return foldOr (false);
    if (type == "nor")
      return foldOr (true);
    if (type == "xor" || type == "xnor")
      {
        int acc = 0;
        for (int l : lits)
          acc = aig.mkXor (acc, l);
        return type == "xor" ? acc : Aig::litNot (acc);
      }
    if (type == "not")
      return Aig::litNot (lits[0]);
    if (type == "buf")
      return lits[0];
    throw std::runtime_error ("bad type");
  }

  // ---- graph helpers on the current netlist ----
  std::vector<std::vector<int>> fanoutAdj; // netId -> consumer net ids
  void
  buildAdj ()
  {
    fanoutAdj.assign (G.netName.size (), {});
    std::vector<int> drvGate (G.netName.size (), -1);
    for (size_t gi = 0; gi < G.gates.size (); gi++)
      drvGate[G.gates[gi].out] = (int)gi;
    for (int nid = 2; nid < (int)G.netName.size (); nid++)
      {
        auto pit = patchedDrv.find (nid);
        if (pit != patchedDrv.end ())
          {
            std::unordered_set<int> seen;
            std::vector<int> st{ Aig::litVar (pit->second) };
            std::set<int> deps;
            while (!st.empty ())
              {
                int v = st.back ();
                st.pop_back ();
                if (v == 0 || seen.count (v))
                  continue;
                seen.insert (v);
                if (!paig.isAnd (v))
                  {
                    const std::string &nm = paigPiName.at (v);
                    std::string base = nm;
                    if (base.size () > 3
                        && base.substr (base.size () - 3) == "_in")
                      base = base.substr (0, base.size () - 3);
                    auto nit = G.netId.find (base);
                    if (nit != G.netId.end ())
                      deps.insert (nit->second);
                  }
                else
                  {
                    st.push_back (Aig::litVar (paig.nodes[v].f0));
                    st.push_back (Aig::litVar (paig.nodes[v].f1));
                  }
              }
            for (int d : deps)
              fanoutAdj[d].push_back (nid);
          }
        else if (drvGate[nid] >= 0)
          {
            for (int in : G.gates[drvGate[nid]].ins)
              if (in > 1)
                fanoutAdj[in].push_back (nid);
          }
      }
  }
  std::unordered_set<int>
  tfo (int nid)
  {
    std::unordered_set<int> res;
    std::vector<int> st{ nid };
    res.insert (nid);
    while (!st.empty ())
      {
        int n = st.back ();
        st.pop_back ();
        for (int f : fanoutAdj[n])
          if (!res.count (f))
            {
              res.insert (f);
              st.push_back (f);
            }
      }
    return res;
  }

  // cofactor evaluation: value of net when target net t is forced to constant
  // cv
  int
  cofNet (int nid, int t, int cv, const std::unordered_set<int> &tfoSet,
          std::unordered_map<int, int> &memo)
  {
    std::unordered_map<int, int> forced{ { t, cv } };
    return cofNetF (nid, forced, tfoSet, memo);
  }
  // multi-net version: forced maps netId -> constant literal (0/1)
  int
  cofNetF (int nid, const std::unordered_map<int, int> &forced,
           const std::unordered_set<int> &tfoSet,
           std::unordered_map<int, int> &memo)
  {
    auto fit = forced.find (nid);
    if (fit != forced.end ())
      return fit->second;
    if (!tfoSet.count (nid))
      return curLit[nid];
    auto it = memo.find (nid);
    if (it != memo.end ())
      return it->second;
    auto pit = patchedDrv.find (nid);
    int res;
    if (pit != patchedDrv.end ())
      {
        std::unordered_map<int, int> sub, pm;
        // supports evaluated under cofactor
        std::unordered_set<int> seen;
        std::vector<int> st{ Aig::litVar (pit->second) };
        while (!st.empty ())
          {
            int v = st.back ();
            st.pop_back ();
            if (v == 0 || seen.count (v))
              continue;
            seen.insert (v);
            if (!paig.isAnd (v))
              {
                const std::string &nm = paigPiName.at (v);
                std::string base = nm;
                bool isIn = false;
                if (base.size () > 3 && base.substr (base.size () - 3) == "_in"
                    && targetSet.count (base.substr (0, base.size () - 3)))
                  {
                    base = base.substr (0, base.size () - 3);
                    isIn = true;
                  }
                int bnid = G.netId.at (base);
                if (isIn)
                  {
                    if (piLitByName.count (base) && gateIdx (bnid) < 0)
                      sub[v] = piLitByName.at (base);
                    else
                      {
                        const Gate &g = G.gates[gateIdx (bnid)];
                        std::vector<int> lits;
                        for (int in : g.ins)
                          lits.push_back (cofNetF (in, forced, tfoSet, memo));
                        sub[v] = gateFn (g.type, lits);
                      }
                  }
                else
                  {
                    sub[v] = cofNetF (bnid, forced, tfoSet, memo);
                  }
              }
            else
              {
                st.push_back (Aig::litVar (paig.nodes[v].f0));
                st.push_back (Aig::litVar (paig.nodes[v].f1));
              }
          }
        res = evalPaig (pit->second, sub, pm);
      }
    else
      {
        int gi = gateIdx (nid);
        if (gi < 0)
          return curLit[nid]; // PI (shouldn't be in TFO unless forced)
        const Gate &g = G.gates[gi];
        std::vector<int> lits;
        for (int in : g.ins)
          lits.push_back (cofNetF (in, forced, tfoSet, memo));
        res = gateFn (g.type, lits);
      }
    memo[nid] = res;
    return res;
  }

  // main entry: returns true if all failing POs were fixed by rectification
  bool run (int maxRounds);

  // helpers used by run()
  struct Cand
  {
    int nid;
    int bad0, bad1;               // main-aig lits
    std::vector<std::string> pos; // POs in TFO (A(t))
    int fixNow = 0;
    int tfoSize = 0;
  };

  std::vector<std::string> carryF; // failing POs carried between rounds
  std::vector<int>
      realPis;    // PIs of the actual circuits (excludes 2-copy dup PIs)
  int simmed = 0; // sim watermark (vars below are simulated)
  void
  simEvalFrom ()
  {
    aig.simEnsure ();
    for (int v = simmed; v < aig.numVars (); v++)
      {
        if (!aig.isAnd (v))
          continue;
        const auto &n = aig.nodes[v];
        auto &d = aig.sim[v];
        const auto &s0 = aig.sim[Aig::litVar (n.f0)];
        const auto &s1 = aig.sim[Aig::litVar (n.f1)];
        uint64_t q0 = Aig::litPh (n.f0) ? ~0ULL : 0ULL,
                 q1 = Aig::litPh (n.f1) ? ~0ULL : 0ULL;
        for (int w = 0; w < aig.simWords; w++)
          d[w] = (s0[w] ^ q0) & (s1[w] ^ q1);
      }
    simmed = aig.numVars ();
  }

  // copy an aig cone substituting PIs by fresh duplicate PIs (for 2-copy
  // queries)
  std::unordered_map<int, int> piDup;    // orig PI var -> dup PI lit
  std::unordered_map<int, int> copyMemo; // orig var -> copied lit
  int
  aigCopy (int lit)
  {
    int v = Aig::litVar (lit);
    auto it = copyMemo.find (v);
    int base;
    if (it != copyMemo.end ())
      base = it->second;
    else if (v == 0)
      base = 0;
    else if (!aig.isAnd (v))
      {
        auto d = piDup.find (v);
        base = (d != piDup.end ()) ? d->second : (piDup[v] = aig.newPi ());
      }
    else
      {
        int a = aigCopy (aig.nodes[v].f0);
        int b = aigCopy (aig.nodes[v].f1);
        base = aig.mkAnd (a, b);
      }
    copyMemo[v] = base;
    return base ^ Aig::litPh (lit);
  }

  // ---- care-pattern collection via SAT enumeration ----
  // Returns pattern slots (slot,bit) of injected patterns; enumerates up to
  // cap models of `cond`. Uses an activation literal so blocking clauses are
  // session-local.
  int injectCounter = 0;
  static constexpr int kCareSlots
      = 2; // last 2 sim words reserved for care patterns
  std::vector<std::pair<int, int>>
  enumPatterns (int cond, int cap)
  {
    std::vector<std::pair<int, int>> pats;
    int act = sat.alloc ();
    for (int k = 0; k < cap; k++)
      {
        sat.solver->assume (act);
        sat.solver->assume (sat.litOf (cond));
        sat.solver->limit ("conflicts", 20000);
        sat.numCalls++;
        if (sat.solver->solve () != 10)
          break;
        // record + inject pattern
        int slotBase = aig.simWords - kCareSlots;
        int slot = slotBase + (injectCounter / 64) % kCareSlots;
        int bit = injectCounter % 64;
        injectCounter++;
        std::vector<int> block{ -act };
        aig.simEnsure ();
        for (int pi : realPis)
          {
            if ((int)sat.satVar.size () > pi && sat.satVar[pi])
              {
                bool val = sat.value (2 * pi);
                aig.simSetPiBit (pi, slot, bit, val);
                block.push_back (val ? -sat.satVar[pi] : sat.satVar[pi]);
              }
            else
              {
                aig.simSetPiBit (pi, slot, bit, false);
              }
          }
        for (int l : block)
          sat.solver->add (l);
        sat.solver->add (0);
        pats.push_back ({ slot, bit });
      }
    return pats;
  }

  // synthesize replacement function for candidate c. Returns paig lit, or
  // INT32_MIN.
  int
  synthesize (const Cand &c, const std::unordered_set<int> *extraTfo = nullptr)
  {
    auto tfoSet = tfo (c.nid);
    if (extraTfo)
      tfoSet.insert (extraTfo->begin (), extraTfo->end ());
    // divisor pool: named non-target nets outside TFO(t), plus t_in (old
    // value)
    struct Div
    {
      std::string name;
      int lit;
    };
    std::vector<Div> divs;
    for (int nid = 2; nid < (int)G.netName.size (); nid++)
      {
        if (tfoSet.count (nid))
          continue;
        if (curLit[nid] < 0)
          continue;
        if (targetSet.count (G.netName[nid]))
          continue;
        divs.push_back ({ G.netName[nid], curLit[nid] });
      }
    divs.push_back ({ G.netName[c.nid] + "_in", curLit[c.nid] });
    if (divs.empty ())
      return INT32_MIN;

    // care patterns: SAT enumeration first (diverse), then scan existing sim
    // words
    injectCounter = 0;
    auto p1 = enumPatterns (c.bad0, 40); // must-1 patterns
    auto p0 = enumPatterns (c.bad1, 40); // must-0 patterns
    simEvalFrom ();                      // new nodes: all words
    aig.simRecomputeWords (aig.simWords - kCareSlots, aig.simWords);
    for (int w = 0; w < aig.simWords - kCareSlots; w++)
      {
        uint64_t b0 = aig.simWord (c.bad0, w), b1 = aig.simWord (c.bad1, w);
        for (int b = 0; b < 64; b++)
          {
            if ((b0 >> b) & 1 && p1.size () < 64)
              p1.push_back ({ w, b });
            if ((b1 >> b) & 1 && p0.size () < 64)
              p0.push_back ({ w, b });
          }
      }
    if (p1.empty () && p0.empty ())
      return INT32_MIN; // no care info: give up

    // ---- greedy support selection over sample pairs, CEGAR-refined ----
    // bit-packed: for divisor d, row i is a word-mask over p0 of pairs it
    // separates
    std::vector<int> S; // indices into divs
    auto cover = [&]() -> bool {  // greedy set cover on packed bitsets
            S.clear();
            size_t n1 = std::min(p1.size(), (size_t)128), n0 = std::min(p0.size(), (size_t)128);
            if (n1 == 0 || n0 == 0) return true;  // one-sided: constant handles it
            size_t n0w = (n0 + 63) / 64;
            uint64_t tail = (n0 % 64) ? ((1ULL << (n0 % 64)) - 1) : ~0ULL;
            size_t rowW = n1 * n0w;
            std::vector<uint64_t> sep(divs.size() * rowW);
            std::vector<uint64_t> b0m(n0w, 0);
            for (size_t d = 0; d < divs.size(); d++) {
                for (auto& w : b0m) w = 0;
                for (size_t j = 0; j < n0; j++)
                    if (aig.simBit(divs[d].lit, p0[j].first, p0[j].second))
                        b0m[j >> 6] |= 1ULL << (j & 63);
                uint64_t* row = &sep[d * rowW];
                for (size_t i = 0; i < n1; i++) {
                    bool b1 = aig.simBit(divs[d].lit, p1[i].first, p1[i].second);
                    for (size_t w = 0; w < n0w; w++) {
                        uint64_t x = b1 ? ~b0m[w] : b0m[w];
                        if (w == n0w - 1) x &= tail;
                        row[i * n0w + w] = x;
                    }
                }
            }
            std::vector<uint64_t> uncov(rowW, 0);
            for (size_t i = 0; i < n1; i++)
                for (size_t w = 0; w < n0w; w++)
                    uncov[i * n0w + w] = (w == n0w - 1) ? tail : ~0ULL;
            size_t remaining = n1 * n0;
            while (remaining > 0) {
                int bestD = -1;
                size_t bestCnt = 0;
                for (size_t d = 0; d < divs.size(); d++) {
                    const uint64_t* row = &sep[d * rowW];
                    size_t cnt = 0;
                    for (size_t w = 0; w < rowW; w++)
                        cnt += __builtin_popcountll(row[w] & uncov[w]);
                    if (cnt > bestCnt) { bestCnt = cnt; bestD = (int)d; }
                }
                if (bestD < 0 || bestCnt == 0) return false;  // some pair not separable
                S.push_back(bestD);
                const uint64_t* row = &sep[bestD * rowW];
                for (size_t w = 0; w < rowW; w++) uncov[w] &= ~row[w];
                remaining -= bestCnt;
                if (S.size() > 10) return false;
            }
            return true;
        };
    if (!cover ())
      return INT32_MIN;

    // CEGAR sufficiency: exists m (bad0), m' (bad1) agreeing on S?
    copyMemo.clear ();
    piDup.clear ();
    int bad1Copy = aigCopy (c.bad1);
    std::unordered_map<int, int> divCopy; // div index -> copied lit
    auto divCopyLit = [&] (int d)
      {
        auto it = divCopy.find (d);
        if (it != divCopy.end ())
          return it->second;
        return divCopy[d] = aigCopy (divs[d].lit);
      };
    for (int iter = 0; iter < 24; iter++)
      {
        if (timeUp ())
          return INT32_MIN;
        std::vector<int> assumps{ c.bad0, bad1Copy };
        for (int d : S)
          {
            int eq = aig.mkXor (divs[d].lit, divCopyLit (d));
            assumps.push_back (Aig::litNot (eq));
          }
        sat.solver->limit ("conflicts", 50000);
        int r = sat.solveAssume (assumps);
        if (r == 20)
          break; // sufficient
        if (r != 10)
          return INT32_MIN;
        // new distinguishing pair: values from both copies -> inject as
        // patterns
        int slotBase = aig.simWords - kCareSlots;
        int slot = slotBase + (injectCounter / 64) % kCareSlots;
        int bit = injectCounter % 64;
        injectCounter++;
        aig.simEnsure ();
        for (int pi : realPis)
          aig.simSetPiBit (pi, slot, bit,
                           (int)sat.satVar.size () > pi && sat.satVar[pi]
                               && sat.value (2 * pi));
        p1.push_back ({ slot, bit });
        int slot2 = slotBase + (injectCounter / 64) % kCareSlots;
        int bit2 = injectCounter % 64;
        injectCounter++;
        for (int pi : realPis)
          {
            bool val = false;
            auto d = piDup.find (pi);
            if (d != piDup.end ())
              {
                int dv = Aig::litVar (d->second);
                val = (int)sat.satVar.size () > dv && sat.satVar[dv]
                      && sat.value (d->second);
              }
            aig.simSetPiBit (pi, slot2, bit2, val);
          }
        p0.push_back ({ slot2, bit2 });
        simEvalFrom (); // new nodes: all words
        aig.simRecomputeWords (aig.simWords - kCareSlots, aig.simWords);
        if (!cover ())
          return INT32_MIN;
        if (iter == 23)
          return INT32_MIN;
      }
    if (S.size () > 8)
      return INT32_MIN;

    // ---- truth table over S via model enumeration ----
    // enumerate care cells directly (few) instead of querying all 2^|S| cells
    int n = (int)S.size ();
    int cells = 1 << n;
    std::vector<int> tt (cells, -1); // 1 / 0 / -1 = DC
    for (int side = 0; side < 2; side++)
      {
        int cond = side == 0 ? c.bad0 : c.bad1;
        int val = side == 0 ? 1 : 0;
        int act = sat.alloc ();
        for (int k = 0; k <= cells; k++)
          {
            sat.solver->assume (act);
            sat.solver->assume (sat.litOf (cond));
            sat.numCalls++;
            int r = sat.solver->solve ();
            if (r == 20)
              break;
            if (r != 10)
              return INT32_MIN;
            int cell = 0;
            std::vector<int> block{ -act };
            for (int k2 = 0; k2 < n; k2++)
              {
                bool b = sat.value (divs[S[k2]].lit);
                if (b)
                  cell |= 1 << k2;
                int sl = sat.litOf (divs[S[k2]].lit);
                block.push_back (b ? -sl : sl);
              }
            if (tt[cell] == 1 - val)
              return INT32_MIN; // sufficiency violated
            tt[cell] = val;
            for (int l : block)
              sat.solver->add (l);
            sat.solver->add (0);
          }
      }
    // ---- TT -> paig (Shannon), try DC fill 0 and 1, keep smaller ----
    std::function<int (std::vector<int> &, int, int, int)> shannon
        = [&] (std::vector<int> &t, int lo, int len, int k) -> int
      {
        bool all0 = true, all1 = true;
        for (int i2 = lo; i2 < lo + len; i2++)
          {
            if (t[i2] != 0)
              all0 = false;
            if (t[i2] != 1)
              all1 = false;
          }
        if (all0)
          return 0;
        if (all1)
          return 1;
        int half = len / 2;
        int f0 = shannon (t, lo, half, k + 1);
        int f1 = shannon (t, lo + half, half, k + 1);
        int sv = supportOf (divs[S[n - 1 - k]].name);
        // variable order: S[n-1] is the MSB half split
        return paig.mkMux (sv, f1, f0);
      };
    int bestLit = INT32_MIN, bestSz = 1 << 30;
    for (int fill = 0; fill <= 1; fill++)
      {
        std::vector<int> t2 (tt);
        for (auto &x : t2)
          if (x < 0)
            x = fill;
        // reorder: shannon splits on MSB = S[n-1]; tt index bit k = S[k]
        int lit = shannon (t2, 0, cells, 0);
        int sz = coneSize (lit);
        if (sz < bestSz)
          {
            bestSz = sz;
            bestLit = lit;
          }
      }
    // espresso-lite: greedy cube expansion over ON+DC (and dually OFF+DC) --
    // exploits scattered don't-cares that constant fills miss
    auto sopBuild = [&] (int onVal) -> int
      {
        int full = (1 << n) - 1;
        std::vector<bool> covered (cells, false);
        int fLit = 0;
        for (int m = 0; m < cells; m++)
          {
            if (tt[m] != onVal || covered[m])
              continue;
            int freeMask = 0;
            for (int k = 0; k < n; k++)
              {
                int cand = freeMask | (1 << k);
                int fixedMask = full & ~cand;
                bool okc = true;
                for (int sub = cand;; sub = (sub - 1) & cand)
                  {
                    int cell = (m & fixedMask) | sub;
                    if (tt[cell] == 1 - onVal)
                      {
                        okc = false;
                        break;
                      }
                    if (sub == 0)
                      break;
                  }
                if (okc)
                  freeMask = cand;
              }
            int fixedMask = full & ~freeMask;
            for (int sub = freeMask;; sub = (sub - 1) & freeMask)
              {
                int cell = (m & fixedMask) | sub;
                if (tt[cell] == onVal)
                  covered[cell] = true;
                if (sub == 0)
                  break;
              }
            int cube = 1;
            for (int k = 0; k < n; k++)
              {
                if (freeMask & (1 << k))
                  continue;
                int sv = supportOf (divs[S[k]].name);
                cube = paig.mkAnd (cube,
                                   ((m >> k) & 1) ? sv : Aig::litNot (sv));
              }
            fLit = paig.mkOr (fLit, cube);
          }
        return onVal == 1 ? fLit : Aig::litNot (fLit);
      };
    for (int side = 0; side <= 1; side++)
      {
        int lit = sopBuild (side == 0 ? 1 : 0);
        int sz = coneSize (lit);
        if (sz < bestSz)
          {
            bestSz = sz;
            bestLit = lit;
          }
      }
    return bestLit;
  }

  int
  coneSize (int pl)
  {
    std::unordered_set<int> seen;
    std::vector<int> st{ Aig::litVar (pl) };
    int cnt = 0;
    while (!st.empty ())
      {
        int v = st.back ();
        st.pop_back ();
        if (v == 0 || seen.count (v))
          continue;
        seen.insert (v);
        cnt++;
        if (paig.isAnd (v))
          {
            st.push_back (Aig::litVar (paig.nodes[v].f0));
            st.push_back (Aig::litVar (paig.nodes[v].f1));
          }
      }
    return cnt;
  }
  // ands + not-yet-used supports + the target wire itself
  int
  fixCostEstimate (int pl)
  {
    if (pl == INT32_MIN)
      return 1 << 30;
    std::unordered_set<int> seen;
    std::vector<int> st{ Aig::litVar (pl) };
    int cnt = 1;
    while (!st.empty ())
      {
        int v = st.back ();
        st.pop_back ();
        if (v == 0 || seen.count (v))
          continue;
        seen.insert (v);
        if (paig.isAnd (v))
          {
            cnt++;
            st.push_back (Aig::litVar (paig.nodes[v].f0));
            st.push_back (Aig::litVar (paig.nodes[v].f1));
          }
        else if (!knownSup.count (paigPiName.at (v)))
          {
            cnt++;
          }
      }
    return cnt;
  }
  void
  noteSupports (int pl)
  {
    std::unordered_set<int> seen;
    std::vector<int> st{ Aig::litVar (pl) };
    while (!st.empty ())
      {
        int v = st.back ();
        st.pop_back ();
        if (v == 0 || seen.count (v))
          continue;
        seen.insert (v);
        if (paig.isAnd (v))
          {
            st.push_back (Aig::litVar (paig.nodes[v].f0));
            st.push_back (Aig::litVar (paig.nodes[v].f1));
          }
        else
          {
            knownSup.insert (paigPiName.at (v));
          }
      }
  }

  // ---- two-point joint rectification (tried when single-point rounds stall)
  // ---- Valid pair (t1,t2): no input makes all four cofactor combinations
  // bad. f1 is synthesized against must-sets "both v1 options bad"; then f2
  // against the f1-conditioned bads. Divisors of both exclude the union TFO.
  std::vector<std::string> pairFixedPos; // POs covered by the applied pair
  bool
  tryPairs (const std::vector<Cand> &cands, const std::vector<std::string> &F,
            int minGain = 1)
  {
    long pairWorkStart = sat.numCalls;
    std::set<std::string> Fset (F.begin (), F.end ());
    // rank single candidates (including SAT-invalid ones: they are the pair
    // fodder)
    std::vector<const Cand *> top;
    for (auto &c : cands)
      if (!targetSet.count (G.netName[c.nid]))
        top.push_back (&c);
    std::sort (top.begin (), top.end (),
               [] (const Cand *a, const Cand *b)
                 {
                   if (a->fixNow != b->fixNow)
                     return a->fixNow > b->fixNow;
                   if (a->tfoSize != b->tfoSize)
                     return a->tfoSize < b->tfoSize;
                   return a->nid < b->nid; // total order: deterministic
                 });
    size_t topCap
        = getenv ("ECO_PAIR_TOP") ? atoi (getenv ("ECO_PAIR_TOP")) : 64;
    if (top.size () > topCap)
      top.resize (topCap);
    struct P
    {
      int i, j, gain, sz;
    };
    std::vector<P> ps;
    for (size_t i = 0; i < top.size (); i++)
      for (size_t j = i + 1; j < top.size (); j++)
        {
          std::set<std::string> u (top[i]->pos.begin (), top[i]->pos.end ());
          u.insert (top[j]->pos.begin (), top[j]->pos.end ());
          int gain = 0;
          for (auto &nm : u)
            if (Fset.count (nm))
              gain++;
          if (gain < minGain)
            continue;
          ps.push_back (
              { (int)i, (int)j, gain, top[i]->tfoSize + top[j]->tfoSize });
        }
    std::sort (ps.begin (), ps.end (),
               [] (const P &a, const P &b)
                 {
                   if (a.gain != b.gain)
                     return a.gain > b.gain;
                   if (a.sz != b.sz)
                     return a.sz < b.sz;
                   if (a.i != b.i)
                     return a.i < b.i;
                   return a.j < b.j; // total order: deterministic
                 });
    size_t psCap
        = getenv ("ECO_PAIR_MAX") ? atoi (getenv ("ECO_PAIR_MAX")) : 2000;
    if (ps.size () > psCap)
      ps.resize (psCap);
    int satChecks = 0, simKilled = 0, satInvalid = 0, synthFail = 0,
        costRej = 0;
    for (auto &pr : ps)
      {
        int satCap
            = getenv ("ECO_PAIR_SAT") ? atoi (getenv ("ECO_PAIR_SAT")) : 100;
        if (sat.numCalls - pairWorkStart > pairWorkBudget
            || satChecks >= satCap)
          break;
        int n1 = top[pr.i]->nid, n2 = top[pr.j]->nid;
        auto tfoU = tfo (n1);
        {
          auto t2s = tfo (n2);
          tfoU.insert (t2s.begin (), t2s.end ());
        }
        std::vector<std::pair<std::string, int>> apos;
        for (int po : G.pos)
          if (tfoU.count (po))
            apos.push_back ({ G.netName[po], po });
        // 4 cofactor miters; combo bit1 = v1, bit0 = v2
        int bad[4];
        for (int combo = 0; combo < 4; combo++)
          {
            std::unordered_map<int, int> forced{ { n1, (combo >> 1) & 1 },
                                                 { n2, combo & 1 } };
            std::unordered_map<int, int> memo;
            int bd = 0;
            for (auto &[nm, pn] : apos)
              bd = aig.mkOr (bd, aig.mkXor (cofNetF (pn, forced, tfoU, memo),
                                            rPo.at (nm)));
            bad[combo] = bd;
          }
        simEvalFrom ();
        bool kill = false;
        for (int w = 0; w < aig.simWords && !kill; w++)
          {
            uint64_t x = aig.simWord (bad[0], w) & aig.simWord (bad[1], w)
                         & aig.simWord (bad[2], w) & aig.simWord (bad[3], w);
            if (x)
              kill = true;
          }
        if (kill)
          {
            simKilled++;
            continue;
          }
        satChecks++;
        sat.solver->limit ("conflicts", 100000);
        int r = sat.solveAssume ({ bad[0], bad[1], bad[2], bad[3] });
        if (r == 10)
          { // invalidity witness -> improve screening
            int slotBase = aig.simWords - kCareSlots;
            int slot = slotBase + (injectCounter / 64) % kCareSlots;
            int bit = injectCounter % 64;
            injectCounter++;
            aig.simEnsure ();
            for (int pi : realPis)
              aig.simSetPiBit (pi, slot, bit,
                               (int)sat.satVar.size () > pi && sat.satVar[pi]
                                   && sat.value (2 * pi));
            simEvalFrom ();
            aig.simRecomputeWords (aig.simWords - kCareSlots, aig.simWords);
            satInvalid++;
            continue;
          }
        if (r != 20)
          {
            satInvalid++;
            continue;
          }
        // valid pair: register targets before synthesis (blocks them as
        // divisors and gives t_in the old-value semantics), roll back on
        // failure
        const std::string tn1 = G.netName[n1], tn2 = G.netName[n2];
        targetSet.insert (tn1);
        targetSet.insert (tn2);
        auto bail = [&] ()
          {
            targetSet.erase (tn1);
            targetSet.erase (tn2);
          };
        Cand cA;
        cA.nid = n1;
        cA.bad0 = aig.mkAnd (bad[0], bad[1]); // v1=0 bad for both v2
        cA.bad1 = aig.mkAnd (bad[2], bad[3]); // v1=1 bad for both v2
        simEvalFrom ();
        int f1 = synthesize (cA, &tfoU);
        if (f1 == INT32_MIN)
          {
            bail ();
            synthFail++;
            continue;
          }
        std::unordered_map<int, int> sub, m2;
        collectSub (f1, sub);
        int F1 = evalPaig (f1, sub, m2);
        Cand cB;
        cB.nid = n2;
        cB.bad0 = aig.mkMux (F1, bad[2], bad[0]); // v2=0 bad, given v1=f1(m)
        cB.bad1 = aig.mkMux (F1, bad[3], bad[1]);
        simEvalFrom ();
        int f2 = synthesize (cB, &tfoU);
        if (f2 == INT32_MIN)
          {
            bail ();
            synthFail++;
            continue;
          }
        int gain = pr.gain;
        int cost = fixCostEstimate (f1) + fixCostEstimate (f2);
        if (cost > maxFixCostPerPo * gain)
          {
            bail ();
            costRej++;
            continue;
          }
        patchedDrv[n1] = f1;
        patchedDrv[n2] = f2;
        fixes.push_back ({ tn1, f1 });
        fixes.push_back ({ tn2, f2 });
        noteSupports (f1);
        noteSupports (f2);
        pairFixedPos.clear ();
        for (auto &[nm, pn] : apos)
          pairFixedPos.push_back (nm);
        if (verbose)
          fprintf (stderr,
                   "[rectify] pair fix (%s, %s): fixes %d POs, est cost %d\n",
                   tn1.c_str (), tn2.c_str (), gain, cost);
        return true;
      }
    if (verbose)
      fprintf (
          stderr,
          "[rectify] pairs: top=%zu pairs=%zu simKill=%d satChk=%d satInv=%d "
          "synthFail=%d costRej=%d\n",
          top.size (), ps.size (), simKilled, satChecks, satInvalid, synthFail,
          costRej);
    return false;
  }

  // ---- post-run helpers for hybrid assembly ----
  void
  finalize ()
  {
    recompute ();
    buildAdj ();
  }
  std::vector<std::string>
  failingNow ()
  {
    std::vector<std::string> F;
    std::unordered_map<std::string, int> poNet;
    for (int po : G.pos)
      poNet[G.netName[po]] = po;
    for (auto &[nm, rlit] : rPoOrdered)
      if (sat.proveEq (curLit[poNet.at (nm)], rlit, nullptr, -1) != 1)
        F.push_back (nm);
    return F;
  }
  // names of nets whose value differs from the original circuit (TFO of fixes)
  std::set<std::string>
  bannedNames ()
  {
    std::set<std::string> res;
    for (auto &fx : fixes)
      {
        int nid = G.netId.at (fx.target);
        for (int n : tfo (nid))
          res.insert (G.netName[n]);
      }
    return res;
  }
  // TFO names of a set of nets on the current graph
  std::set<std::string>
  tfoNames (const std::vector<std::string> &nets)
  {
    std::set<std::string> res;
    for (auto &nm : nets)
      for (int n : tfo (G.netId.at (nm)))
        res.insert (G.netName[n]);
    return res;
  }
  // Would replacing the given failing POs by their R2 functions (no consumer
  // preservation) keep every PO correct on the current circuit?
  bool
  noPresCheck (const std::vector<std::string> &remFail)
  {
    std::unordered_map<int, int> forced;
    for (auto &nm : remFail)
      forced[G.netId.at (nm)] = rPo.at (nm);
    std::vector<int> lits;
    evalInto (lits, forced);
    for (auto &[nm, rlit] : rPoOrdered)
      {
        int nid = G.netId.at (nm);
        if (lits[nid] < 0)
          return false;
        if (sat.proveEq (lits[nid], rlit, nullptr, -1) != 1)
          return false;
      }
    return true;
  }
};

// out-of-line: keep header readable
inline bool
Rectifier::run (int maxRounds)
{
  workStart = sat.numCalls;
  aig.simInit (16 + kCareSlots,
               simSeed); // fresh sim incl. reserved care slots
  simmed = aig.numVars ();
  realPis = aig.pis;
  const int rollbackMark
      = aig.numVars (); // per-round scratch above this is discarded
  // PO name -> netId
  std::unordered_map<std::string, int> poNet;
  for (int po : G.pos)
    poNet[G.netName[po]] = po;

  for (int round = 0; round < maxRounds; round++)
    {
      if (round > 0)
        {
          aig.rollback (
              rollbackMark); // discard cofactor scratch from prior round
          simmed = std::min (simmed, aig.numVars ());
          sat.forgetAigVarsFrom (
              rollbackMark); // those var indices will be reused
          sat.reset ();      // drop dead-miter clauses from the prior round
        }
      recompute ();
      buildAdj ();
      // failing POs: full SAT check in round 0, incrementally maintained
      // afterwards
      std::vector<std::string> F;
      if (round == 0)
        {
          for (auto &[nm, rlit] : rPoOrdered)
            if (sat.proveEq (curLit[poNet.at (nm)], rlit, nullptr, -1) != 1)
              F.push_back (nm);
        }
      else
        {
          F = carryF;
        }
      if (F.empty ())
        return true;
      if (timeUp ())
        return false;
      std::set<std::string> Fset (F.begin (), F.end ());

      // candidate targets: named nets in TFI of failing POs (sorted:
      // deterministic)
      std::unordered_set<int> tfi;
      {
        std::vector<int> st;
        std::vector<int> drvGate (G.netName.size (), -1);
        for (size_t gi = 0; gi < G.gates.size (); gi++)
          drvGate[G.gates[gi].out] = (int)gi;
        for (auto &nm : F)
          st.push_back (poNet.at (nm));
        while (!st.empty ())
          {
            int n = st.back ();
            st.pop_back ();
            if (tfi.count (n))
              continue;
            tfi.insert (n);
            auto pit = patchedDrv.find (n);
            if (pit != patchedDrv.end ())
              continue; // don't dig past prior fixes
            if (drvGate[n] >= 0)
              for (int in : G.gates[drvGate[n]].ins)
                if (in > 1)
                  st.push_back (in);
          }
      }
      simEvalFrom (); // cover nodes created by recompute()
      // build candidates with cofactor miters (sorted net order:
      // deterministic)
      std::vector<int> tfiOrdered (tfi.begin (), tfi.end ());
      std::sort (tfiOrdered.begin (), tfiOrdered.end ());
      std::vector<Cand> cands;
      for (int nid : tfiOrdered)
        {
          if (targetSet.count (G.netName[nid]))
            continue;
          Cand c;
          c.nid = nid;
          auto tfoSet = tfo (nid);
          c.tfoSize = (int)tfoSet.size ();
          // A(t): POs in tfo
          std::vector<std::pair<std::string, int>> apos; // name, poNet
          for (int po : G.pos)
            if (tfoSet.count (po))
              apos.push_back ({ G.netName[po], po });
          int fixNow = 0;
          for (auto &[nm, pn] : apos)
            if (Fset.count (nm))
              fixNow++;
          if (fixNow == 0)
            continue;
          c.fixNow = fixNow;
          std::unordered_map<int, int> m0, m1;
          int bad0 = 0, bad1 = 0;
          for (auto &[nm, pn] : apos)
            {
              c.pos.push_back (nm);
              int p0 = cofNet (pn, nid, 0, tfoSet, m0);
              int p1 = cofNet (pn, nid, 1, tfoSet, m1);
              bad0 = aig.mkOr (bad0, aig.mkXor (p0, rPo.at (nm)));
              bad1 = aig.mkOr (bad1, aig.mkXor (p1, rPo.at (nm)));
            }
          c.bad0 = bad0;
          c.bad1 = bad1;
          cands.push_back (c);
        }
      // simulate new nodes incrementally, filter obviously-invalid candidates
      simEvalFrom ();
      std::vector<Cand> valid;
      for (auto &c : cands)
        {
          bool bad = false;
          for (int w = 0; w < aig.simWords && !bad; w++)
            if (aig.simWord (c.bad0, w) & aig.simWord (c.bad1, w))
              bad = true;
          if (!bad)
            valid.push_back (c);
        }
      std::sort (valid.begin (), valid.end (),
                 [] (const Cand &a, const Cand &b)
                   {
                     if (a.fixNow != b.fixNow)
                       return a.fixNow > b.fixNow;
                     if (a.tfoSize != b.tfoSize)
                       return a.tfoSize < b.tfoSize;
                     return a.nid < b.nid; // total order: deterministic
                   });
      if (verbose)
        fprintf (stderr, "[rectify] round %d: F=%zu cands=%zu simValid=%zu\n",
                 round, F.size (), cands.size (), valid.size ());
      // high-value pair rectification first: one pair can fix a whole bus
      if (getenv ("ECO_PAIR_R0") && round == 0 && F.size () >= 6
          && tryPairs (cands, F, 4))
        {
          std::set<std::string> fixedPos (pairFixedPos.begin (),
                                          pairFixedPos.end ());
          carryF.clear ();
          for (auto &nm : F)
            if (!fixedPos.count (nm))
              carryF.push_back (nm);
          continue;
        }
      // exact validity + synthesis; SAT counterexamples are fed back into the
      // simulation so later candidates get screened cheaply.
      int attempts = 0, synthed = 0;
      bool applied = false;
      struct Best
      {
        int nid = -1;
        int lit = 0;
        int cost = 1 << 30;
        int fixNow = 0;
        std::vector<std::string> pos;
      };
      Best best;
      for (auto &c : valid)
        {
          if (timeUp () || attempts >= 60)
            break;
          if (best.nid != -1 && c.fixNow < best.fixNow)
            break; // sorted; tier finished
          // re-screen against current sim (includes injected counterexamples)
          bool screened = false;
          for (int w = 0; w < aig.simWords && !screened; w++)
            if (aig.simWord (c.bad0, w) & aig.simWord (c.bad1, w))
              screened = true;
          if (screened)
            continue;
          attempts++;
          sat.solver->limit ("conflicts", 50000);
          int r = sat.solveAssume ({ c.bad0, c.bad1 });
          if (r != 20)
            {
              if (r == 10)
                { // inject invalidity witness into sim
                  int slotBase = aig.simWords - kCareSlots;
                  int slot = slotBase + (injectCounter / 64) % kCareSlots;
                  int bit = injectCounter % 64;
                  injectCounter++;
                  aig.simEnsure ();
                  for (int pi : realPis)
                    aig.simSetPiBit (pi, slot, bit,
                                     (int)sat.satVar.size () > pi
                                         && sat.satVar[pi]
                                         && sat.value (2 * pi));
                  simEvalFrom ();
                  aig.simRecomputeWords (aig.simWords - kCareSlots,
                                         aig.simWords);
                }
              continue;
            }
          synthed++;
          int flit = synthesize (c);
          if (verbose)
            fprintf (stderr,
                     "[rectify]   cand %s: fixes %d, synth %s (est %d)\n",
                     G.netName[c.nid].c_str (), c.fixNow,
                     flit == INT32_MIN ? "FAIL" : "ok",
                     flit == INT32_MIN ? -1 : fixCostEstimate (flit));
          if (flit == INT32_MIN)
            continue;
          int fcost = fixCostEstimate (flit);
          if (best.nid == -1 || c.fixNow > best.fixNow
              || (c.fixNow == best.fixNow && fcost < best.cost))
            {
              best = { c.nid, flit, fcost, c.fixNow, c.pos };
            }
          if (best.nid != -1 && best.cost <= 3)
            break; // near-optimal; stop searching
          if (synthed >= 8 && best.nid != -1)
            break;
        }
      if (best.nid != -1 && best.cost <= maxFixCostPerPo * best.fixNow)
        {
          const std::string &tn = G.netName[best.nid];
          if (verbose)
            fprintf (
                stderr,
                "[rectify] round %d: fix %s (fixes %d POs, est cost %d)\n",
                round, tn.c_str (), best.fixNow, best.cost);
          patchedDrv[best.nid] = best.lit;
          targetSet.insert (tn);
          fixes.push_back ({ tn, best.lit });
          noteSupports (best.lit);
          applied = true;
          // validity proof covers every PO in A(t): drop them from the failing
          // set
          carryF.clear ();
          std::set<std::string> fixedPos (best.pos.begin (), best.pos.end ());
          for (auto &nm : F)
            if (!fixedPos.count (nm))
              carryF.push_back (nm);
        }
      else if (best.nid != -1)
        {
          if (verbose)
            fprintf (stderr,
                     "[rectify] round %d: best fix too costly (%d for %d "
                     "POs); stopping\n",
                     round, best.cost, best.fixNow);
        }
      if (!applied && tryPairs (cands, F))
        {
          applied = true;
          std::set<std::string> fixedPos (pairFixedPos.begin (),
                                          pairFixedPos.end ());
          carryF.clear ();
          for (auto &nm : F)
            if (!fixedPos.count (nm))
              carryF.push_back (nm);
        }
      if (!applied)
        return false;
    }
  // final check
  recompute ();
  std::unordered_map<std::string, int> poNet2;
  for (int po : G.pos)
    poNet2[G.netName[po]] = po;
  for (auto &[nm, rlit] : rPo)
    if (sat.proveEq (curLit[poNet2.at (nm)], rlit, nullptr, -1) != 1)
      return false;
  return true;
}
