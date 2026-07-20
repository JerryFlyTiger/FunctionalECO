// patch.hpp -- patch AIG -> BLIF -> ABC (optimize + map to contest-cost
// genlib)
//              -> gate netlist -> patch.v emission + exact contest cost model.
#pragma once
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "aig.hpp"

// A gate-level patch netlist (module top_eco).
struct PatchGate
{
  std::string type; // and,or,nand,nor,xor,xnor,not,buf
  std::string out;
  std::vector<std::string> ins; // net names or "1'b0"/"1'b1"
};
struct PatchNetlist
{
  std::vector<std::string> inputs;  // support port names (may end with _in)
  std::vector<std::string> outputs; // target port names
  std::vector<PatchGate> gates;
  bool valid = false;
};

// ---- exact contest cost ----
// cost = #wires (ports + internal, distinct, constants excluded)
//      + sum(numInputs(gate) - 2)  + #distinct constants used (<=2)
inline int
patchCost (const PatchNetlist &p)
{
  std::set<std::string> wires;
  std::set<std::string> consts;
  for (auto &s : p.inputs)
    wires.insert (s);
  for (auto &s : p.outputs)
    wires.insert (s);
  int prim = 0;
  for (auto &g : p.gates)
    {
      wires.insert (g.out);
      prim += (int)g.ins.size () - 2;
      for (auto &i : g.ins)
        {
          if (i == "1'b0" || i == "1'b1")
            consts.insert (i);
          else
            wires.insert (i);
        }
    }
  return (int)wires.size () + prim + (int)consts.size ();
}

// ---- Verilog identifier emission (escape if needed) ----
inline std::string
vEsc (const std::string &n)
{
  bool simple
      = !n.empty () && (std::isalpha ((unsigned char)n[0]) || n[0] == '_');
  for (char c : n)
    if (!(std::isalnum ((unsigned char)c) || c == '_' || c == '$'))
      simple = false;
  if (n == "1'b0" || n == "1'b1")
    return n;
  return simple ? n : ("\\" + n + " ");
}

inline void
writePatchV (const PatchNetlist &p, const std::string &path)
{
  std::ostringstream os;
  os << "module top_eco (";
  bool first = true;
  for (auto &s : p.outputs)
    {
      os << (first ? "" : ", ") << vEsc (s);
      first = false;
    }
  for (auto &s : p.inputs)
    {
      os << (first ? "" : ", ") << vEsc (s);
      first = false;
    }
  os << ");\n";
  if (!p.outputs.empty ())
    {
      os << "  output ";
      for (size_t i = 0; i < p.outputs.size (); i++)
        os << (i ? ", " : "") << vEsc (p.outputs[i]);
      os << ";\n";
    }
  if (!p.inputs.empty ())
    {
      os << "  input ";
      for (size_t i = 0; i < p.inputs.size (); i++)
        os << (i ? ", " : "") << vEsc (p.inputs[i]);
      os << ";\n";
    }
  // internal wires
  std::set<std::string> ports (p.inputs.begin (), p.inputs.end ());
  for (auto &s : p.outputs)
    ports.insert (s);
  std::set<std::string> internals;
  for (auto &g : p.gates)
    {
      if (!ports.count (g.out))
        internals.insert (g.out);
      for (auto &i : g.ins)
        if (i != "1'b0" && i != "1'b1" && !ports.count (i))
          internals.insert (i);
    }
  if (!internals.empty ())
    {
      os << "  wire ";
      bool f2 = true;
      for (auto &s : internals)
        {
          os << (f2 ? "" : ", ") << vEsc (s);
          f2 = false;
        }
      os << ";\n";
    }
  int id = 0;
  for (auto &g : p.gates)
    {
      os << "  " << g.type << " eco_g" << id++ << " (" << vEsc (g.out);
      for (auto &i : g.ins)
        os << ", " << vEsc (i);
      os << ");\n";
    }
  os << "endmodule\n";
  std::ofstream f (path);
  f << os.str ();
}

// ---------------- BLIF I/O ----------------
// Write a multi-output patch AIG region as BLIF.
// poLits[i] corresponds to poNames[i]; piName maps aig PI var -> port name.
inline void
aigToBlif (const Aig &a, const std::unordered_map<int, std::string> &piName,
           const std::vector<std::string> &poNames,
           const std::vector<int> &poLits, const std::string &path)
{
  // collect used nodes
  std::vector<int> order;
  std::unordered_set<int> seen;
  std::vector<int> stack;
  for (int L : poLits)
    stack.push_back (Aig::litVar (L));
  while (!stack.empty ())
    {
      int v = stack.back ();
      if (seen.count (v) || v == 0)
        {
          stack.pop_back ();
          continue;
        }
      if (!a.isAnd (v))
        {
          seen.insert (v);
          order.push_back (v);
          stack.pop_back ();
          continue;
        }
      int v0 = Aig::litVar (a.nodes[v].f0), v1 = Aig::litVar (a.nodes[v].f1);
      bool ready = true;
      if (!seen.count (v0) && v0 != 0)
        {
          stack.push_back (v0);
          ready = false;
        }
      if (!seen.count (v1) && v1 != 0)
        {
          stack.push_back (v1);
          ready = false;
        }
      if (!ready)
        continue;
      seen.insert (v);
      order.push_back (v);
      stack.pop_back ();
    }
  // internal BLIF names use a prefix that cannot collide with G1 net names
  auto nName = [&] (int v) -> std::string
    {
      auto it = piName.find (v);
      if (it != piName.end ())
        return it->second;
      return "ecoN" + std::to_string (v) + "_";
    };
  std::ofstream f (path);
  f << ".model patch\n.inputs";
  std::vector<int> pisUsed;
  for (int v : order)
    if (!a.isAnd (v))
      pisUsed.push_back (v);
  for (int v : pisUsed)
    f << " " << nName (v);
  f << "\n.outputs";
  for (auto &s : poNames)
    f << " " << s;
  f << "\n";
  bool needConst0 = false;
  for (int L : poLits)
    if (Aig::litVar (L) == 0)
      needConst0 = true;
  if (needConst0)
    f << ".names ecoC0__\n"; // const 0 node (no cubes)
  for (int v : order)
    {
      if (!a.isAnd (v))
        continue;
      int f0 = a.nodes[v].f0, f1 = a.nodes[v].f1;
      f << ".names " << nName (Aig::litVar (f0)) << " "
        << nName (Aig::litVar (f1)) << " " << nName (v) << "\n";
      f << (Aig::litPh (f0) ? "0" : "1") << (Aig::litPh (f1) ? "0" : "1")
        << " 1\n";
    }
  for (size_t i = 0; i < poNames.size (); i++)
    {
      int L = poLits[i];
      int v = Aig::litVar (L);
      if (v == 0)
        {
          f << ".names ecoC0__ " << poNames[i] << "\n"
            << (Aig::litPh (L) ? "0" : "1") << " 1\n";
        }
      else
        {
          f << ".names " << nName (v) << " " << poNames[i] << "\n"
            << (Aig::litPh (L) ? "0" : "1") << " 1\n";
        }
    }
  f << ".end\n";
}

// Parse (possibly mapped) BLIF back into a PatchNetlist. Handles .names with
// <=2 inputs (SOP) and .gate lines from our genlib. Returns valid=false on
// anything unexpected.
inline PatchNetlist
blifToPatch (const std::string &path)
{
  PatchNetlist p;
  std::ifstream f (path);
  if (!f)
    return p;
  // read logical lines with '\' continuation
  std::vector<std::string> lines;
  std::string cur, ln;
  while (std::getline (f, ln))
    {
      if (!ln.empty () && ln[0] == '#')
        continue;
      while (!ln.empty () && (ln.back () == '\r' || ln.back () == ' '))
        ln.pop_back ();
      if (!ln.empty () && ln.back () == '\\')
        {
          cur += ln.substr (0, ln.size () - 1) + " ";
          continue;
        }
      cur += ln;
      lines.push_back (cur);
      cur.clear ();
    }
  auto split = [] (const std::string &s)
    {
      std::vector<std::string> t;
      std::istringstream is (s);
      std::string w;
      while (is >> w)
        t.push_back (w);
      return t;
    };
  std::vector<std::string> outputsOrder;
  // gather .names blocks
  for (size_t i = 0; i < lines.size (); i++)
    {
      auto tok = split (lines[i]);
      if (tok.empty ())
        continue;
      if (tok[0] == ".inputs")
        p.inputs.assign (tok.begin () + 1, tok.end ());
      else if (tok[0] == ".outputs")
        outputsOrder.assign (tok.begin () + 1, tok.end ());
      else if (tok[0] == ".names")
        {
          std::vector<std::string> sig (tok.begin () + 1, tok.end ());
          if (sig.empty ())
            return p;
          std::string out = sig.back ();
          sig.pop_back ();
          std::vector<std::string> cubes;
          while (i + 1 < lines.size () && !lines[i + 1].empty ()
                 && lines[i + 1][0] != '.')
            {
              cubes.push_back (lines[++i]);
            }
          PatchGate g;
          g.out = out;
          if (sig.size () == 0)
            {
              // constant: cube "1" => const1, none => const0
              bool one = false;
              for (auto &c : cubes)
                {
                  auto ct = split (c);
                  if (!ct.empty () && ct.back () == "1" && ct.size () == 1)
                    one = true;
                }
              g.type = "buf";
              g.ins = { one ? std::string ("1'b1") : std::string ("1'b0") };
            }
          else if (sig.size () == 1)
            {
              if (cubes.size () != 1)
                return p;
              auto ct = split (cubes[0]);
              if (ct.size () != 2 || ct[1] != "1")
                return p;
              g.type = (ct[0] == "1") ? "buf" : "not";
              g.ins = { sig[0] };
            }
          else if (sig.size () == 2)
            {
              // build 4-bit truth table t[a<<1|b]
              int tt = 0;
              for (auto &c : cubes)
                {
                  auto ct = split (c);
                  if (ct.size () != 2 || ct[1] != "1" || ct[0].size () != 2)
                    return p;
                  for (int m = 0; m < 4; m++)
                    {
                      int av = (m >> 1) & 1, bv = m & 1;
                      char ca = ct[0][0], cb = ct[0][1];
                      bool okA = (ca == '-') || (ca - '0' == av);
                      bool okB = (cb == '-') || (cb - '0' == bv);
                      if (okA && okB)
                        tt |= 1 << m;
                    }
                }
              g.ins = { sig[0], sig[1] };
              switch (tt)
                { // bit m set means f(a= m>>1, b= m&1)=1
                case 0b1000:
                  g.type = "and";
                  break; // a&b (bit3=11)
                case 0b1110:
                  g.type = "or";
                  break;
                case 0b0111:
                  g.type = "nand";
                  break;
                case 0b0001:
                  g.type = "nor";
                  break;
                case 0b0110:
                  g.type = "xor";
                  break;
                case 0b1001:
                  g.type = "xnor";
                  break;
                case 0b0000:
                  g.type = "buf";
                  g.ins = { std::string ("1'b0") };
                  break;
                case 0b1111:
                  g.type = "buf";
                  g.ins = { std::string ("1'b1") };
                  break;
                case 0b1100:
                  g.type = "buf";
                  g.ins = { sig[0] };
                  break; // f=a
                case 0b1010:
                  g.type = "buf";
                  g.ins = { sig[1] };
                  break; // f=b
                case 0b0011:
                  g.type = "not";
                  g.ins = { sig[0] };
                  break;
                case 0b0101:
                  g.type = "not";
                  g.ins = { sig[1] };
                  break;
                default:
                  return p; // nonstandard 2-input fn: shouldn't happen w/
                            // genlib
                }
            }
          else
            {
              return p; // >2 inputs unexpected
            }
          p.gates.push_back (g);
        }
      else if (tok[0] == ".gate")
        {
          // .gate <name> a=<x> [b=<y>] O=<z>
          if (tok.size () < 3)
            return p;
          std::string gname = tok[1];
          std::map<std::string, std::string> pin;
          for (size_t k = 2; k < tok.size (); k++)
            {
              auto eq = tok[k].find ('=');
              if (eq == std::string::npos)
                return p;
              pin[tok[k].substr (0, eq)] = tok[k].substr (eq + 1);
            }
          PatchGate g;
          g.out = pin["O"];
          if (gname == "zero")
            {
              g.type = "buf";
              g.ins = { std::string ("1'b0") };
            }
          else if (gname == "one")
            {
              g.type = "buf";
              g.ins = { std::string ("1'b1") };
            }
          else if (gname == "inv1")
            {
              g.type = "not";
              g.ins = { pin["a"] };
            }
          else if (gname == "buf1")
            {
              g.type = "buf";
              g.ins = { pin["a"] };
            }
          else
            {
              std::string t
                  = gname.substr (0, gname.size () - 1); // and2 -> and
              if (t != "and" && t != "or" && t != "nand" && t != "nor"
                  && t != "xor" && t != "xnor")
                return p;
              g.type = t;
              g.ins = { pin["a"], pin["b"] };
            }
          p.gates.push_back (g);
        }
    }
  p.outputs = outputsOrder;
  p.valid = true;
  // drop unused inputs
  std::set<std::string> used;
  for (auto &g : p.gates)
    for (auto &i : g.ins)
      used.insert (i);
  std::vector<std::string> ins2;
  for (auto &s : p.inputs)
    if (used.count (s))
      ins2.push_back (s);
  p.inputs = ins2;
  return p;
}

// Fallback: patch AIG -> gates directly (ands + nots), no ABC.
inline PatchNetlist
aigToPatchDirect (const Aig &a,
                  const std::unordered_map<int, std::string> &piName,
                  const std::vector<std::string> &poNames,
                  const std::vector<int> &poLits)
{
  PatchNetlist p;
  p.outputs = poNames;
  std::unordered_map<int, std::string> litName; // aig lit -> net name
  std::set<std::string> usedIns;
  int wid = 0;
  litName[1] = "1'b1";
  litName[0] = "1'b0";
  std::function<std::string (int)> nameOf = [&] (int L) -> std::string
    {
      auto it = litName.find (L);
      if (it != litName.end ())
        return it->second;
      int v = Aig::litVar (L);
      if (!a.isAnd (v))
        { // PI
          std::string base = piName.at (v);
          litName[2 * v] = base;
          usedIns.insert (base);
          if (Aig::litPh (L))
            {
              std::string w = "eco_w" + std::to_string (wid++);
              p.gates.push_back ({ "not", w, { base } });
              litName[L] = w;
              return w;
            }
          return base;
        }
      std::string s0 = nameOf (a.nodes[v].f0);
      std::string s1 = nameOf (a.nodes[v].f1);
      std::string w = "eco_w" + std::to_string (wid++);
      p.gates.push_back ({ "and", w, { s0, s1 } });
      litName[2 * v] = w;
      if (Aig::litPh (L))
        {
          std::string wn = "eco_w" + std::to_string (wid++);
          p.gates.push_back ({ "not", wn, { w } });
          litName[L] = wn;
          return wn;
        }
      return w;
    };
  for (size_t i = 0; i < poNames.size (); i++)
    {
      std::string src = nameOf (poLits[i]);
      p.gates.push_back ({ "buf", poNames[i], { src } });
    }
  for (auto &s : usedIns)
    p.inputs.push_back (s);
  p.valid = true;
  return p;
}

// Run ABC on the patch BLIF with several scripts; return best (min cost)
// result.
inline PatchNetlist
optimizeWithAbc (const std::string &abcBin, const std::string &genlib,
                 const std::string &blifIn, const std::string &tmpDir,
                 int supportCnt, bool verbose)
{
  PatchNetlist best;
  std::vector<std::string> scripts = {
    "dc2; dc2; dch -f; map -a",
    "dc2; dc2; dc2; dc2; dch; map -a",
  };
  if (supportCnt <= 16)
    scripts.push_back ("collapse; sop; fx; strash; dc2; dch -f; map -a");
  if (const char *es = getenv ("ECO_EXTRA_SCRIPT"))
    scripts.push_back (es);
  // single abc invocation runs every script (process spawn dominates
  // otherwise)
  std::string cmd = abcBin + " -c \"read_genlib " + genlib + "; ";
  for (size_t i = 0; i < scripts.size (); i++)
    {
      std::string out = tmpDir + "/mapped" + std::to_string (i) + ".blif";
      cmd += "read_blif " + blifIn + "; strash; " + scripts[i]
             + "; write_blif " + out + "; ";
    }
  cmd += "\" > " + tmpDir + "/abc.log 2>&1";
  std::system (cmd.c_str ()); // parse whatever outputs were produced
  for (size_t i = 0; i < scripts.size (); i++)
    {
      PatchNetlist p
          = blifToPatch (tmpDir + "/mapped" + std::to_string (i) + ".blif");
      if (!p.valid)
        continue;
      if (!best.valid || patchCost (p) < patchCost (best))
        best = p;
      if (verbose)
        fprintf (stderr, "  [abc] script %zu -> cost %d\n", i, patchCost (p));
    }
  // large patches: one more (slower) don't-care pass is worth the extra ~0.1s
  if (!best.valid || patchCost (best) >= 100)
    {
      std::string out = tmpDir + "/mappedX.blif";
      std::string c2 = abcBin + " -c \"read_genlib " + genlib + "; read_blif "
                       + blifIn
                       + "; strash; dc2; dc2; dch -f; map -a; mfs; strash; "
                         "dch -f; map -a; "
                         "write_blif "
                       + out + "\" >> " + tmpDir + "/abc.log 2>&1";
      std::system (c2.c_str ());
      PatchNetlist p = blifToPatch (out);
      if (p.valid && (!best.valid || patchCost (p) < patchCost (best)))
        best = p;
      if (verbose && p.valid)
        fprintf (stderr, "  [abc] mfs script -> cost %d\n", patchCost (p));
    }
  return best;
}
