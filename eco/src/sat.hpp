// sat.hpp -- CaDiCaL wrapper: incremental SAT over an Aig (Tseitin encoding on
// demand).
#pragma once
#include <memory>
#include <vector>

#include "aig.hpp"
#include "cadical.hpp"

struct SatAig
{
  std::unique_ptr<CaDiCaL::Solver> solver
      = std::make_unique<CaDiCaL::Solver> ();
  const Aig *aig = nullptr;
  std::vector<int> satVar; // aig var -> sat var (0 = not yet encoded)
  int nextVar = 1;
  long numCalls = 0;

  void
  attach (const Aig &a)
  {
    solver->configure (
        "plain"); // tiny incremental instances: inprocessing is overhead
    aig = &a;
    satVar.assign (a.numVars (), 0);
    satVar[0] = alloc ();
    solver->add (-satVar[0]); // const0 is false
    solver->add (0);
  }
  // forget encodings for aig vars >= v (after Aig::rollback reuses those
  // indices); dead clauses stay in the solver but reference only retired SAT
  // vars
  void
  forgetAigVarsFrom (int v)
  {
    if ((int)satVar.size () > v)
      satVar.resize (v);
  }
  // drop all clauses (incl. dead miters / blocking garbage); cones re-encode
  // lazily
  void
  reset ()
  {
    solver = std::make_unique<CaDiCaL::Solver> ();
    nextVar = 1;
    satVar.clear ();
    attach (*aig);
  }
  int
  alloc ()
  {
    nextVar++;
    return solver->declare_one_more_variable (); // CaDiCaL requires explicit
                                                 // declaration
  }

  int
  litOf (int aigLit)
  {
    int v = encodeVar (Aig::litVar (aigLit));
    return Aig::litPh (aigLit) ? -v : v;
  }
  int
  encodeVar (int var)
  {
    if ((int)satVar.size () < aig->numVars ())
      satVar.resize (aig->numVars (), 0);
    if (satVar[var])
      return satVar[var];
    // encode cone iteratively (avoid deep recursion)
    std::vector<int> stack{ var };
    while (!stack.empty ())
      {
        int v = stack.back ();
        if (satVar[v])
          {
            stack.pop_back ();
            continue;
          }
        if (!aig->isAnd (v))
          { // PI
            satVar[v] = alloc ();
            stack.pop_back ();
            continue;
          }
        int v0 = Aig::litVar (aig->nodes[v].f0),
            v1 = Aig::litVar (aig->nodes[v].f1);
        bool ready = true;
        if (!satVar[v0])
          {
            stack.push_back (v0);
            ready = false;
          }
        if (!satVar[v1])
          {
            stack.push_back (v1);
            ready = false;
          }
        if (!ready)
          continue;
        int c = alloc ();
        satVar[v] = c;
        int a = Aig::litPh (aig->nodes[v].f0) ? -satVar[v0] : satVar[v0];
        int b = Aig::litPh (aig->nodes[v].f1) ? -satVar[v1] : satVar[v1];
        solver->add (-c);
        solver->add (a);
        solver->add (0);
        solver->add (-c);
        solver->add (b);
        solver->add (0);
        solver->add (c);
        solver->add (-a);
        solver->add (-b);
        solver->add (0);
        stack.pop_back ();
      }
    return satVar[var];
  }

  // solve under assumptions (aig literals must be asserted true). 10 = SAT, 20
  // = UNSAT.
  int
  solveAssume (const std::vector<int> &aigLits)
  {
    for (int l : aigLits)
      solver->assume (litOf (l));
    numCalls++;
    return solver->solve ();
  }
  bool
  value (int aigLit)
  { // model value after SAT
    int sl = litOf (aigLit);
    int v = solver->val (std::abs (sl));
    bool b = v > 0;
    return sl < 0 ? !b : b;
  }
  // Checks a == b (as boolean functions over PIs).
  // Returns 1 = equal (proved), 0 = not equal (cexOut filled), -1 = unknown
  // (limit hit). confLimit < 0 means no limit.
  int
  proveEq (int a, int b, std::vector<std::pair<int, bool>> *cexOut = nullptr,
           long confLimit = -1)
  {
    if (a == b)
      return 1;
    if (a == Aig::litNot (b))
      { // opposite for every input: any assignment is a cex
        if (cexOut)
          {
            cexOut->clear ();
            for (int pi : aig->pis)
              cexOut->push_back ({ pi, false });
          }
        return 0;
      }
    for (int round = 0; round < 2; round++)
      {
        int x = round == 0 ? a : Aig::litNot (a);
        int y = round == 0 ? Aig::litNot (b) : b;
        if (confLimit >= 0)
          solver->limit ("conflicts", confLimit);
        int r = solveAssume ({ x, y });
        if (r == 10)
          {
            if (cexOut)
              {
                cexOut->clear ();
                for (int pi : aig->pis)
                  if (satVar[pi])
                    cexOut->push_back ({ pi, value (2 * pi) });
              }
            return 0;
          }
        if (r != 20)
          return -1; // interrupted / limit
      }
    return 1;
  }
};
