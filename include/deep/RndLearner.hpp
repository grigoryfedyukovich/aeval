#ifndef RNDLEARNER__HPP__
#define RNDLEARNER__HPP__

#include "Horn.hpp"
#include "CodeSampler.hpp"
#include "Distribution.hpp"
#include "LinCom.hpp"
#include "ae/SMTUtils.hpp"

using namespace std;
using namespace boost;
namespace ufo
{

  struct SynthResult {
    const bool foundInvariants;
    const bool cancelled;
    SynthResult(const bool fi, const bool c) :
      foundInvariants(fi), cancelled(c) {}
  };

  class RndLearner
  {
  private:

    ExprFactory &m_efac;
    EZ3 &m_z3;
    SMTUtils u;
    ufo::ZSolver<ufo::EZ3> m_smt_solver;
    ufo::ZSolver<ufo::EZ3> m_smt_safety_solver;

    CHCs& ruleManager;
    vector<Expr> decls;          //  container only mutated by `initializeDecl`
    vector<LAfactory> lfs;       // zips with `decls`; container only mutated by `initializeDecl`
    vector<Expr> curCandidates;
    map<int, int> incomNum;
    int numOfSMTChecks;

    const bool densecode;           // catch various statistics about the code (mostly, frequences) and setup the prob.distribution based on them
    const bool shrink;              // consider only a small subset of int constants and samples from the code
    const bool aggressivepruning;   // aggressive pruning of the search space based on SAT/UNSAT (WARNING: may miss some invariants)

    inline int invNumber() { return decls.size(); }

  public:

    RndLearner (ExprFactory &efac, EZ3 &z3, CHCs& r, bool b1, bool b2, bool b3) :
      m_efac(efac), m_z3(z3), ruleManager(r), m_smt_solver (z3),
      m_smt_safety_solver(z3), u(efac), numOfSMTChecks(0), densecode(b1),
      shrink(b2), aggressivepruning(b3) {}

    bool isTautology (Expr a)     // adjusted for big disjunctions
    {
      if (isOpX<TRUE>(a)) return true;

      ExprSet disjs;
      getDisj(a, disjs);
      if (disjs.size() == 1) return false;

      map<ExprSet, ExprSet> varComb;
      for (auto &a : disjs)
      {
        ExprSet avars;
        expr::filter (a, bind::IsConst(), std::inserter (avars, avars.begin ()));
        varComb[avars].insert(mkNeg(a));
      }

      m_smt_solver.reset();

      bool res = false;
      for (auto &v : varComb )
      {
        m_smt_solver.assertExpr(conjoin(v.second, m_efac));
        if (!m_smt_solver.solve ())
        {
          res = true; break;
        }
      }
      return res;
    }

    bool checkCandidates(function<void(unsigned, LAdisj&)> learnedLemma)
    {
      map<int, int> localNum = incomNum; // for local status

      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery) continue;

        m_smt_solver.reset();

        // pushing body
        m_smt_solver.assertExpr (hr.body);

        Expr cand1;
        Expr cand2;
        Expr invApp1;
        Expr invApp2;
        Expr lmApp;

        // pushing src relation
        if (!isOpX<TRUE>(hr.srcRelation))
        {
          int ind1 = getVarIndex(hr.srcRelation, decls);
          LAfactory& lf1 = lfs[ind1];

          if (localNum[ind1] > 0)
          {
            cand1 = curCandidates[ind1];
            invApp1 = cand1;
            for (int i = 0; i < hr.srcVars.size(); i++)
            {
              invApp1 = replaceAll(invApp1, lf1.getVarE(i), hr.srcVars[i]);
            }
            m_smt_solver.assertExpr(invApp1);
          }

          lmApp = conjoin(lf1.learntExprs, m_efac);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            lmApp = replaceAll(lmApp, lf1.getVarE(i), hr.srcVars[i]);
          }
          m_smt_solver.assertExpr(lmApp);
        }

        // pushing dst relation
        int ind2 = getVarIndex(hr.dstRelation, decls);
        cand2 = curCandidates[ind2];
        invApp2 = cand2;
        LAfactory& lf2 = lfs[ind2];

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          invApp2 = replaceAll(invApp2, lf2.getVarE(i), hr.dstVars[i]);
        }

        auto neggedInvApp2 = mk<NEG>(invApp2);
        m_smt_solver.assertExpr(neggedInvApp2);

        numOfSMTChecks++;
        boost::tribool res = m_smt_solver.solve ();
        if (res)    // SAT   == candidate failed
        {
          outs () << "   => bad candidate for " << *hr.dstRelation << "\n";
          lf2.assignPrioritiesForFailed(lf2.samples.back());
          return false;
        }
        else        // UNSAT == candadate is OK for now; keep checking
        {
          localNum[ind2]--;
          if (!res && localNum[ind2] == 0) // something inductive found
          {
            outs () << "   => learnt lemma for " << *hr.dstRelation << "\n";
            LAdisj& learntDisj = lf2.samples.back();
            lf2.assignPrioritiesForLearnt(learntDisj);
            lf2.learntExprs.insert(curCandidates[ind2]);
            lf2.learntLemmas.push_back(lf2.samples.size() - 1);
            learnedLemma(ind2, learntDisj);
          }
        }
      }
      return true;
    }

    bool checkSafety()
    {
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;

        int ind = getVarIndex(hr.srcRelation, decls);
        Expr invApp = curCandidates[ind];
        LAfactory& lf = lfs[ind];

        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          invApp = replaceAll(invApp, lf.getVarE(i), hr.srcVars[i]);
        }

        m_smt_safety_solver.assertExpr(invApp);

        numOfSMTChecks++;
        boost::tribool res = m_smt_safety_solver.solve ();
        if (!res) return true;
      }
      return false;
    }

    void setupSafetySolver()
    {
      // setup the safety solver
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          m_smt_safety_solver.assertExpr (hr.body);
          break;
        }
      }
    }

    void initializeDecl(Expr invDecl)
    {
      assert (invDecl->arity() > 2);

      decls.push_back(invDecl->arg(0));
      lfs.push_back(LAfactory(m_efac, densecode, aggressivepruning));  // indeces at decls, lfs, and curCandidates should be the same
      curCandidates.push_back(NULL);

      LAfactory& lf = lfs.back();

      // collect how many rules has invDecl on the right side
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation == decls.back())
          incomNum[invNumber()-1]++;
      }

      for (int i = 1; i < invDecl->arity()-1; i++)
      {
        Expr new_name = mkTerm<string> ("__v__" + to_string(i - 1), m_efac);
        Expr var = bind::mkConst(new_name, invDecl->arg(i));
        lf.addVar(var);
      }

      set<int> progConsts;
      set<int> intCoefs;
      vector<CodeSampler> css;

      // analize each rule separately:
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != decls.back() && hr.srcRelation != decls.back()) continue;

        css.push_back(CodeSampler(hr, invDecl, lf.getVars()));
        css.back().analyzeCode(densecode, shrink);

        for (auto &cand : css.back().candidates)
        {
          getLinCombCoefs(cand, intCoefs);
          getLinCombConsts(cand, css.back().intConsts);
        }

        // convert cs.intConsts to progConsts and add additive inverses (if applicable):
        for (auto &a : css.back().intConsts)
        {
          progConsts.insert( a);
          progConsts.insert(-a);
        }
      }

      // sort progConsts and push to vector:
      while (progConsts.size() > 0)
      {
        int min = INT_MAX;
        for (auto c : progConsts)
        {
          if (c < min)
          {
            min = c;
          }
        }
        progConsts.erase(min);
        lf.addConst(min);
      }

      intCoefs.insert(1);                           // add 1
      for (auto &a : lf.getConsts()) if (a != 0) intCoefs.insert(a);
      for (auto &a : intCoefs) intCoefs.insert(-a); // add the inverse
      for (auto &a : intCoefs) lf.addIntCoef(a);

      lf.initialize();
      lf.initDensities();

      // normalize samples obtained from CHCs and calculate various statistics:
      vector<LAdisj> lcss;
      for (auto &cs : css)
      {
        for (auto &cand : cs.candidates)
        {
          lcss.push_back(LAdisj());
          LAdisj& lcs = lcss.back();
          if (lf.exprToLAdisj(cand, lcs))
          {
            lcs.normalizePlus();
          }
          lcs.printLAdisj();
        }
      }

      if (densecode)
      {
        int multip = PRIORSTEP;                 // will add +PRIORSTEP to every occurrence

        // or, alternatively multip can depend on the type of CHC:
        //        if (cs.hr.isFact) multip = 1;
        //        else if (cs.hr.isQuery) multip = 2 * PRIORSTEP;
        //        else multip = PRIORSTEP;
        for (auto &lcs : lcss)
        {
          // specify weights for OR arity
          lf.orAritiesDensity[lcs.arity] += multip;

          for (int i = 0; i < lcs.arity; i++)
          {
            LAterm& lc = lcs.dstate[i];

            // specify weights for PLUS arity
            lf.plusAritiesDensity[lc.arity] += multip;

            // specify weights for const
            lf.intConstDensity[lc.intconst] += multip;

            // specify weights for comparison operation
            lf.cmpOpDensity[lc.cmpop] += multip;

            // specify weights for var combinations
            set<int> vars;
            int vars_id = -1;
            for (int j = 0; j < lc.vcs.size(); j = j+2) vars.insert(lc.vcs[j]);
            for (int j = 0; j < lf.varCombinations[lc.arity].size(); j++)
            {
              if (lf.varCombinations[lc.arity][j] == vars)
              {
                vars_id = j;
                break;
              }
            }
            assert(vars_id >= 0);
            lf.varDensity[lc.arity][vars_id] += multip;

            for (int j = 1; j < lc.vcs.size(); j = j+2)
            {
              lf.coefDensity[ lc.vcs [j-1] ] [lc.vcs [j] ] += multip;
            }
          }
        }

        outs() << "Statistics for " << *decls.back() << "\n";
        lf.printCodeStatistics();
      }
    }

    SynthResult synthesize(int maxAttempts, function<bool()> shouldStop,
      function<vector<pair<unsigned, LAdisj>>()> accumulateNewLemmas,
      function<void(unsigned, LAdisj&)> learnedLemma)
    {
      bool success = false;
      int iter = 1;

      std::srand(std::time(0));

      for (int i = 0; i < maxAttempts; i++)
      {
        // bail if we've been cancelled
        if (shouldStop()) {
          return SynthResult(false, true);
        }

        // Opportunity to grab external lemma
        for (pair<unsigned, LAdisj>& d : accumulateNewLemmas()) {
          // cout << "received lemma for decl " << d.first << ": "
          //      << lfs[d.first].toExpr(d.second) << endl;
          LAfactory &laf = lfs[d.first];
          laf.samples.push_back(d.second);
          LAdisj& disj = laf.samples.back();
          // disj.normalizePlus();
          // lf.assignPrioritiesForLearnt(disj);
          laf.learntExprs.insert(laf.toExpr(disj));
          laf.learntLemmas.push_back(laf.samples.size() - 1);
        }

        // first, guess candidates for each inv.declaration

        bool skip = false;
        for (int j = 0; j < invNumber(); j++)
        {
          if (curCandidates[j] != NULL) continue;   // if the current candidate is good enough
          LAfactory& lf = lfs[j];
          Expr cand = lf.getFreshCandidate();
          if (cand == NULL)
          {
            skip = true;
            break;
          }

          if (isTautology(cand) || !u.isSat(cand))  // keep searching
          {
            lf.assignPrioritiesForGarbage(lf.samples.back());
            skip = true;
            break;
          }
          curCandidates[j] = cand;
        }

        if (skip) continue;

        outs() << "\n  ---- new iteration " << iter++ <<  " ----\n";
        for (int j = 0; j < invNumber(); j++) outs () << "candidate for " << *decls[j] << ": " << *curCandidates[j] << "\n";

        // check all the candidates at once for all CHCs :

        if (checkCandidates(learnedLemma))
        {
          if (checkSafety())       // query is checked here
          {
            success = true;
            break;
          }
        }

        for (int j = 0; j < invNumber(); j++)  curCandidates[j] = NULL; // preparing for the next iteration
      }

      if (success) {
        outs () << "\n -----> Success after " << --iter << " iterations\n";
        outs () << "        total number of SMT checks: " << numOfSMTChecks << "\n";
        return SynthResult(true, false);
      } else {
        outs () << "\nNo success after " << maxAttempts << " iterations\n";
        outs () << "        total number of SMT checks: " << numOfSMTChecks << "\n";
        return SynthResult(false, false);
      }
    }
  };


  inline SynthResult learnInvariants(string smt, int maxAttempts, bool b1=true,
    bool b2=true, bool b3=true, function<bool()> shouldStop=nullptr,
    function<vector<pair<unsigned, LAdisj>>()> accumulateNewLemmas=nullptr,
    function<void(unsigned, LAdisj&)> learnedLemma=nullptr)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    ruleManager.print();

    RndLearner ds(m_efac, z3, ruleManager, b1, b2, b3);

    ds.setupSafetySolver();

    if (ruleManager.decls.size() > 1)
    {
      outs() << "WARNING: learning multiple invariants is currently unstable\n"
             << "         it is suggested to disable \'aggressivepruning\'\n";
    }

    for (auto& dcl: ruleManager.decls)
    {
      ds.initializeDecl(dcl);
    }

    return ds.synthesize(maxAttempts, shouldStop, accumulateNewLemmas,
      learnedLemma);
  }
}

#endif
