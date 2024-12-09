#ifndef RNDLEARNER__HPP__
#define RNDLEARNER__HPP__

#include "Horn.hpp"
#include "BndExpl.hpp"
#include "ae/SMTUtils.hpp"
#include "sampl/SeedMiner.hpp"
#include "sampl/Sampl.hpp"

#include <iostream>
#include <fstream>

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearner
  {
    protected:

    ExprFactory &m_efac;
    EZ3 &m_z3;
    SMTUtils u;
    ufo::ZSolver<ufo::EZ3> m_smt_solver;
    vector<ufo::ZSolver<ufo::EZ3>> m_smt_safety_solvers;
    map<int, bool> safety_progress;

    CHCs& ruleManager;
    ExprVector decls;
    vector<vector<SamplFactory>> sfs;
    ExprVector curCandidates;

    vector<map<int, Expr>> invarVars;
    vector<ExprVector> invarVarsShort;

    // for arrays
    vector<ExprSet> arrCands;
    vector<ExprVector> arrAccessVars;
    vector<ExprSet> arrIterRanges;

    int invNumber;
    int numOfSMTChecks;

    bool kind_succeeded;      // interaction with k-induction
    bool oneInductiveProof;

    bool densecode;           // catch various statistics about the code (mostly, frequences) and setup the prob.distribution based on them
    bool addepsilon;          // add some small probability to features that never happen in the code
    bool aggressivepruning;   // aggressive pruning of the search space based on SAT/UNSAT (WARNING: may miss some invariants)

    bool statsInitialized;
    int printLog;

    public:

    RndLearner (ExprFactory &efac, EZ3 &z3, CHCs& r, unsigned to, bool k, bool b1, bool b2, bool b3, int debug) :
      m_efac(efac), m_z3(z3), ruleManager(r), m_smt_solver (z3), u(efac, to),
      invNumber(0), numOfSMTChecks(0), oneInductiveProof(true), kind_succeeded (!k),
      densecode(b1), addepsilon(b2), aggressivepruning(b3),
      statsInitialized(false), printLog(debug)
      {
        if (printLog >= 2) ruleManager.print(printLog >= 4);
      }

    // these things are needed for TermCheck.hpp
    // could be moved there at some point
    Expr getFreshCand(int num = 0)
    {
      SamplFactory& sf = sfs[num].back();
      Expr f;
      while(f == NULL) f = sf.getFreshLinCom();
      if(printLog >= 4) outs() << "FreshCandidate: " << f << "\n";
      return f;
    }

    vector<cpp_int>& getAllConsts (int num = 0)
    {
      return sfs[num].back().lf.getConsts();
    }

    void blockCand(int num = 0)
    {
      SamplFactory& sf = sfs[num].back();
      sf.assignPrioritiesForBlocked();
    }

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
        if (avars.size() == 0) continue;
        varComb[avars].insert(mkNeg(a));
      }

      if (varComb.size() == 0) return false;

      m_smt_solver.reset();

      bool res = false;
      for (auto &v : varComb)
      {
        m_smt_solver.assertExpr(conjoin(v.second, m_efac));
        if (!m_smt_solver.solve ())
        {
          res = true; break;
        }
      }
      return res;
    }

    bool checkCandidates()
    {
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery) continue;

        m_smt_solver.reset();

        int ind1;  // to be identified later
        int ind2 = getVarIndex(hr.dstRelation, decls);

        // pushing body
        m_smt_solver.assertExpr (hr.body);
        Expr cand1;
        Expr cand2;
        Expr lmApp;

        // pushing src relation
        if (!isOpX<TRUE>(hr.srcRelation))
        {
          ind1 = getVarIndex(hr.srcRelation, decls);
          SamplFactory& sf1 = sfs[ind1].back();

          cand1 = curCandidates[ind1];

          for (auto & v : invarVars[ind1])
          {
            cand1 = replaceAll(cand1, v.second, hr.srcVars[v.first]);
          }
          m_smt_solver.assertExpr(cand1);

          lmApp = sf1.getAllLemmas();
          for (auto & v : invarVars[ind1])
          {
            lmApp = replaceAll(lmApp, v.second, hr.srcVars[v.first]);
          }
          m_smt_solver.assertExpr(lmApp);
        }

        // pushing dst relation
        cand2 = curCandidates[ind2];

        for (auto & v : invarVars[ind2])
        {
          cand2 = replaceAll(cand2, v.second, hr.dstVars[v.first]);
        }

        m_smt_solver.assertExpr(mk<NEG>(cand2));

        numOfSMTChecks++;
        boost::tribool res = m_smt_solver.solve ();
        if (res)    // SAT   == candidate failed
        {
          curCandidates[ind2] = mk<TRUE>(m_efac);
          return checkCandidates();
        }
      }

      bool res = false;
      for (auto &cand : curCandidates) res = !isOpX<TRUE>(cand);
      return res;
    }

    void assignPriorities()
    {
      for (int i = 0; i < invNumber; i++)
      {
        SamplFactory& sf = sfs[i].back();
        if (isOpX<TRUE>(curCandidates[i])) sf.assignPrioritiesForFailed();
        else sf.assignPrioritiesForLearned();
      }
    }

    void reportCheckingResults(bool doRedundancyOptim = true)
    {
      for (int i = 0; i < invNumber; i++)
      {
        Expr cand = curCandidates[i];
        SamplFactory& sf = sfs[i].back();
        if (isOpX<TRUE>(cand))
        {
          if (printLog) outs () << "    => bad candidate for " << *decls[i] << "\n";
        }
        else
        {
          if (printLog) outs () << "    => learned lemma for " << *decls[i] << "\n";

          if (doRedundancyOptim)
          {
            Expr allLemmas = sf.getAllLemmas();
            if (u.implies(allLemmas, cand))
            {
              curCandidates[i] = mk<TRUE>(m_efac);
            }
            else
            {
              sf.learnedExprs.insert(cand);
            }
          }
        }
      }
    }

    void resetlearnedLemmas()
    {
      for (auto & sf : sfs) sf.back().learnedExprs.clear();
    }

    bool checkWithKInduction()
    {
      if (ruleManager.chcs.size() != 3) return false; // current limitation
      if (sfs.size() != 1) return false;              // current limitation
      if (kind_succeeded) return false;

      Expr cand = curCandidates[0];
      if (isOpX<TRUE>(cand)) return false;

      SamplFactory& sf = sfs[0].back();
      Expr allLemmas = sf.getAllLemmas();

      // get lemmas to be included to inductive rule
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & hr = ruleManager.chcs[i];
        if (!hr.isInductive) continue;

        for (auto & v : invarVars[0])
        {
          allLemmas = replaceAll(allLemmas, v.second, hr.srcVars[v.first]);
        }
      }

      BndExpl bnd(ruleManager, allLemmas, printLog);

      int i;
      for (i = 2; i < 5; i++) // 2 - a reasanoble lowerbound, 5 - a hardcoded upperbound
      {
        kind_succeeded = bnd.kIndIter(i, i);
        numOfSMTChecks += i;
        if (kind_succeeded) break;
      }

      if (kind_succeeded)
      {
        outs () << "\n" << "K-induction succeeded after " << (i-1) << " iterations\n";
        oneInductiveProof = (i == 2);
        if (oneInductiveProof) // can complete the invariant only when the proof is 1-inductive
        {
          curCandidates[0] = bnd.getInv();
          bool addedRemainingLemma = checkCandidates() && checkSafety();
          if (addedRemainingLemma) sf.learnedExprs.insert(curCandidates[0]); // for serialization only

          if (printLog) outs () << "remaining lemma(s): " << *curCandidates[0] <<
                 "\nsanity check: " << addedRemainingLemma << "\n";
        }
      }

      return kind_succeeded;
    }

    void bootstrapBoundedProofs (int bnd, ExprSet& cands)
    {
      for (auto &hr: ruleManager.chcs)
        if (findNonlin(hr.body))
      {
        outs () << "Nonlinear arithmetic detected.\nInterpolation is skipped\n";
        return;
      }

      BndExpl be(ruleManager, printLog);
      Expr cand;
      int k = 0;
      while (k < bnd)
      {
        cand = be.getBoundedItp(k);
        k++;
        if (cand == NULL)
        {
          outs () << "Counterexample is found.\nThe system does not have a solution.\n";
          exit(0);
        }

        ExprSet cnjs;
        getConj(cand, cnjs);

        for (auto & a : cnjs) cands.insert(a);
      }
    }

    bool checkBoundedProofs (ExprSet& itpCandidates)
    {
      if (invNumber == 1) return false; // not supported yet

      for (auto it = itpCandidates.begin(), end = itpCandidates.end(); it != end; )
      {
        curCandidates[0] = *it; // current limitation

        if (printLog) outs () << "itp candidate for " << *decls[0] << ": " << **it << "\n";

        if (checkCandidates())
        {
          reportCheckingResults();
          itpCandidates.erase(it++);

          if (checkSafety())
          {
            return true;
          }
        }
        else
        {
          ++it;
        }
      }
      return false;
    }

    void resetSafetySolver()
    {
      int num = 0;
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;

        m_smt_safety_solvers[num].reset();
        m_smt_safety_solvers[num].assertExpr (hr.body);
        safety_progress[num] = false;
        num++;
      }
    }

    bool checkSafety()
    {
      int num = 0;
      for (auto &hr: ruleManager.chcs)
      {
        if (!hr.isQuery) continue;
        num++;

        int ind = getVarIndex(hr.srcRelation, decls);
        Expr invApp = curCandidates[ind];
        if (safety_progress[num-1] == true) continue;

        for (auto & v : invarVars[ind])
        {
          invApp = replaceAll(invApp, v.second, hr.srcVars[v.first]);
        }

        m_smt_safety_solvers[num-1].assertExpr(invApp);
        safety_progress[num-1] = bool(!m_smt_safety_solvers[num-1].solve ());

        numOfSMTChecks++;
      }

      for (auto a : safety_progress) if (a.second == false) return false;
      return true;
    }

    void setupSafetySolver()
    {
      // setup the safety solver
      for (auto &hr: ruleManager.chcs)
      {
        if (hr.isQuery)
        {
          m_smt_safety_solvers.push_back(ufo::ZSolver<ufo::EZ3>(m_z3));
          m_smt_safety_solvers.back().assertExpr (hr.body);
          safety_progress[safety_progress.size()] = false;
        }
      }
    }

    void updateRels()
    {
      // this should not affect the learning process for a CHC system with one (declare-rel ...)

      set<int> rels2update;

      for (int ind = 0; ind < invNumber; ind++)
      {
        Expr cand = curCandidates[ind];
        SamplFactory& sf = sfs[ind].back();
        if (!isOpX<TRUE>(cand))
        {
          for (auto &hr : ruleManager.chcs)
          {
            if (hr.srcRelation == decls[ind] &&
                hr.dstRelation != decls[ind] &&
                !hr.isQuery)
            {
              Expr lemma2add = curCandidates[ind];

              for (auto & v : invarVars[ind])
              {
                lemma2add = replaceAll(lemma2add, v.second, hr.srcVars[v.first]);
              }

              numOfSMTChecks++;
              if (u.implies(hr.body, lemma2add)) continue;

              hr.body = mk<AND>(hr.body, lemma2add);

              rels2update.insert(getVarIndex(hr.dstRelation, decls));
            }
          }
        }
      }

      for(auto ind : rels2update)
      {
        vector<SamplFactory>& sf = sfs[ind];
        sf.push_back(SamplFactory (m_efac, aggressivepruning));

        SamplFactory& sf_before = sf[sf.size()-2];
        SamplFactory& sf_after = sf.back();

        for (auto & var : invarVars[ind]) sf_after.addVar(var.second);
        sf_after.lf.nonlinVars = sf_before.lf.nonlinVars;

        set<cpp_int> progConsts, intCoefs;
        ExprSet cands;
        doSeedMining(decls[ind], cands, progConsts, intCoefs);
        initializeSamlp(decls[ind], cands, progConsts, intCoefs);

        sf_after.calculateStatistics(densecode, addepsilon);
        for (auto a : sf_before.learnedExprs)
        {
          sf_after.learnedExprs.insert(a);
          sf_after.exprToSampl(a);
          sf_after.assignPrioritiesForLearned();
        }
      }
    }

    void initializeDecl(Expr invDecl)
    {
      if (printLog) outs () << "\nINITIALIZE PREDICATE " << invDecl << "\n====================\n";
//      assert (invDecl->arity() > 2);
      assert(decls.size() == invNumber);
      assert(sfs.size() == invNumber);
      assert(curCandidates.size() == invNumber);

      decls.push_back(invDecl);
      invarVars.push_back(map<int, Expr>());
      invarVarsShort.push_back(ExprVector());

      curCandidates.push_back(NULL);

      sfs.push_back(vector<SamplFactory> ());
      sfs.back().push_back(SamplFactory (m_efac, aggressivepruning));
      SamplFactory& sf = sfs.back().back();

      for (int i = 0; i < ruleManager.invVars[invDecl].size(); i++)
      {
        Expr var = ruleManager.invVars[invDecl][i];
        if (sf.addVar(var))
        {
          invarVars[invNumber][i] = var;
          invarVarsShort[invNumber].push_back(var);
        }
      }

      arrCands.push_back(ExprSet());
      arrAccessVars.push_back(ExprVector());
      arrIterRanges.push_back(ExprSet());

      invNumber++;
    }

    bool initializedDecl(Expr invDecl)
    {
      return find (decls.begin(), decls.end(), invDecl) != decls.end();
    }

    virtual void doSeedMining(Expr invRel, ExprSet& cands, set<cpp_int>& progConsts, set<cpp_int>& intCoefs)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      // analyze each rule separately:
      for (auto &hr : ruleManager.chcs)
      {
        if (hr.dstRelation != invRel && hr.srcRelation != invRel) continue;

        SeedMiner sm(hr, invRel, invarVars[ind], sf.lf.nonlinVars);
        sm.analyzeCode();

        // convert intConsts to progConsts and add additive inverses (if applicable):
        for (auto &a : sm.intConsts) progConsts.insert(a);
        for (auto &a : sm.intCoefs) intCoefs.insert(a); // same for intCoefs
        for (auto &a : sm.candidates) cands.insert(a);
      }
    }

    void initializeSamlp(Expr invRel, ExprSet& cands, set<cpp_int>& progConsts, set<cpp_int>& intCoefs)
    {
      int ind = getVarIndex(invRel, decls);
      SamplFactory& sf = sfs[ind].back();
      if (sf.lf.nonlinVars.size() > 0)
      {
        if (printLog >= 3) outs() << "Multed vars: ";
        for (auto &a : sf.lf.nonlinVars)
        {
          if (printLog >= 3) outs() << *a.first << " = " << *a.second << "\n";
          sf.lf.addVar(a.second);
          Expr b = a.first->right();
          if (isNumericConst(b)) intCoefs.insert(lexical_cast<cpp_int>(b));
        }
      }

      for (auto &c : progConsts) progConsts.insert(-c);
      for (auto &a : intCoefs) intCoefs.insert(-a);
      for (auto &a : intCoefs) if (a != 0) sf.lf.addIntCoef(a);

      auto progConstsTmp = progConsts;
      for (auto &a : progConstsTmp)
        for (auto &b : intCoefs)
          progConsts.insert(a*b);

      // sort progConsts and push to vector:
      while (progConsts.size() > 0)
      {
        cpp_int min = *progConsts.begin();
        for (auto c : progConsts)
        {
          if (c < min)
          {
            min = c;
          }
        }
        progConsts.erase(min);
        sf.lf.addConst(min);
      }

      sf.initialize(arrCands[ind], arrAccessVars[ind], arrIterRanges[ind]);

      // normalize samples obtained from CHCs
      for (auto & cand : cands) Sampl& s = sf.exprToSampl(cand);
    }

    void prepareSeeds (Expr invRel, ExprSet& cands)
    {
      if (printLog) outs () << "\nSEED MINING for " << invRel << "\n===========\n";
      set<cpp_int> progConsts, intCoefs;
      doSeedMining(invRel, cands, progConsts, intCoefs);
      initializeSamlp(invRel, cands, progConsts, intCoefs);
    }

    void calculateStatistics()
    {
      statsInitialized = true;
      for (int i = 0; i < invNumber; i++)
      {
        sfs[i].back().calculateStatistics(densecode, addepsilon);

        if (printLog >= 3)
        {
          outs() << "\nSTATISTICS for " << *decls[i] << "\n===============\n";
          sfs[i].back().printStatistics();
        }
      }
    }

    void synthesize(int maxAttempts, ExprSet& itpCands)
    {
      if (printLog) outs () << "\nSAMPLING\n===============\n";
      bool success = false;
      int iter = 1;

      for (int i = 0; i < maxAttempts; i++)
      {
        // first, guess candidates for each inv.declaration

        bool skip = false;
        for (int j = 0; j < invNumber; j++)
        {
          if (curCandidates[j] != NULL) continue;   // if the current candidate is good enough
          SamplFactory& sf = sfs[j].back();
          Expr cand = sf.getFreshCandidate();
          if (cand == NULL)
          {
            skip = true;
            break;
          }

          if (isTautology(cand))  // keep searching
          {
            sf.assignPrioritiesForLearned();
            skip = true;
            break;
          }

          if (sf.lf.nonlinVars.size() > 0 && u.isFalse(cand))  // keep searching
          {
            sf.assignPrioritiesForFailed();
            skip = true;
            break;
          }

          curCandidates[j] = cand;
        }

        if (skip) continue;

        if (printLog)
        {
          outs() << "\n  ---- iteration " << iter <<  " ----\n";
          for (int j = 0; j < invNumber; j++)
            outs () << "candidate for " << *decls[j] << ": " << *curCandidates[j] << "\n";
        }

        iter++;

        // check all the candidates at once for all CHCs :

        int isInductive = checkCandidates();
        if (isInductive) success = checkSafety();       // query is checked here

        reportCheckingResults();
        if (success) break;

        if (isInductive)
        {
          success = checkWithKInduction();
          success = checkBoundedProofs(itpCands);
        }

        if (success) break;

        assignPriorities();
        updateRels();

        for (auto &cand : curCandidates) cand = NULL; // preparing for the next iteration
      }

      if (success) outs () << "Success after " << --iter      << " iterations\n";
      else         outs () <<      "Unknown after " << maxAttempts << " iterations\n";

      if (printLog)
        for (int j = 0; j < invNumber; j++)
          outs () << "        number of sampled lemmas for " << *decls[j] << ": "
            << sfs[j].back().learnedExprs.size() << "\n";

      if (printLog) outs () << "        number of SMT checks: " << numOfSMTChecks << "\n";
      if (success) printSolution();
    }

    void checkAllLemmas(vector<ExprSet>& lms, vector<ExprSet>& curMinLms, int& numTries, int invInd)
    {
      numTries++;
      resetSafetySolver();
      resetlearnedLemmas();
      for (int i = 0; i < invNumber; i++) curCandidates[i] = conjoin(lms[i], m_efac);

      if (checkCandidates() && checkSafety())
      {
        if (lms[invInd].size() < curMinLms[invInd].size()) curMinLms[invInd] = lms[invInd];

        for (auto & a : lms[invInd])
        {
          vector<ExprSet> lmsTry = lms;
          lmsTry[invInd].erase(a);

          checkAllLemmas(lmsTry, curMinLms, numTries, invInd);
        }
      }
    }

    void simplifyLemmas()
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        u.removeRedundantConjuncts(sf.learnedExprs);
      }
    }

    void printSolution(bool simplify = true)
    {
      for (int i = 0; i < decls.size(); i++)
      {
        Expr rel = decls[i];
        SamplFactory& sf = sfs[i].back();
        ExprSet lms = sf.learnedExprs;
        outs () << "(define-fun " << *rel << " (";
        for (auto & b : ruleManager.invVars[rel])
        outs () << "(" << *b << " " << u.varType(b) << ")";
        outs () << ") Bool\n  ";
        Expr tmp = conjoin(lms, m_efac);
        if (simplify && !containsOp<FORALL>(tmp)) u.removeRedundantConjuncts(lms);
        Expr res = simplifyArithm(conjoin(lms, m_efac));
        u.print(res);
        outs () << ")\n";
        assert(hasOnlyVars(res, ruleManager.invVars[rel]));
      }
    }
  };

  inline void learnInvariants(string smt, unsigned to, int maxAttempts,
                              bool kind, int itp, bool b1, bool b2, bool b3, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    RndLearner ds(m_efac, z3, ruleManager, to, kind, b1, b2, b3, debug);

    ds.setupSafetySolver();
    std::srand(std::time(0));
    ExprSet itpCands;

    if (ruleManager.decls.size() > 1)
    {
      outs () << "WARNING: learning multiple invariants is currently unstable\n"
             << "         it is suggested to disable \'aggressivepruning\'\n";
    }
    else if (itp > 0)
    {
      outs () << "WARNING: For more efficient itp-based bootstrapping,\n"
              << "         it is recommended to run --v2\n";
      // current limitation: ruleManager.decls.size() == 0
      ds.bootstrapBoundedProofs(itp, itpCands);
    }

    for (auto& dcl: ruleManager.decls)
    {
      ds.initializeDecl(dcl->left());
      ds.prepareSeeds(dcl->left(), itpCands); // itpCands isn't used
    }

    ds.calculateStatistics();
    ds.synthesize(maxAttempts, itpCands);
  };
}

#endif
