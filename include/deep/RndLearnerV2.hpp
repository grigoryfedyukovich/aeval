#ifndef RNDLEARNERV2__HPP__
#define RNDLEARNERV2__HPP__

#include "RndLearner.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class RndLearnerV2 : public RndLearner
  {
    private:

    map<Expr, ExprSet> modelsOfFailures;

    vector<HornRuleExt*> tr;
    vector<HornRuleExt*> fc;
    vector<HornRuleExt*> qr;

    ExprSet deferredLearned;
    ExprSet deferredFailed;
    ExprSet deferredBlocked;

    public:

    RndLearnerV2 (ExprFactory &efac, EZ3 &z3, CHCs& r, unsigned to, bool freqs, bool aggp, int debug) :
      RndLearner (efac, z3, r, to, /*k-induction*/ false, freqs, /*epsilon*/ true, aggp, debug){}

    Expr getModel(ExprVector& vars)
    {
      ExprVector eqs;
      ZSolver<EZ3>::Model m = m_smt_solver.getModel();
      for (auto & v : vars)
      {
        Expr e = m.eval(v);
        if (e == NULL)
        {
          return NULL;
        }
        else if (e != v)
        {
          eqs.push_back(mk<EQ>(v, e));
        }
        else
        {
          if (bind::isBoolConst(v))
            eqs.push_back(mk<EQ>(v, mk<TRUE>(m_efac)));
          else if (bind::isIntConst(v))
            eqs.push_back(mk<EQ>(v, mkTerm (mpz_class (guessUniformly (1000)-500), m_efac)));
        }
      }
      return conjoin (eqs, m_efac);
    }

    ExprSet& getlearnedLemmas(int num)
    {
      return sfs[num].back().learnedExprs;
    }

    void categorizeCHCs()
    {
      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr.push_back(&a);
        else if (a.isFact) fc.push_back(&a);
        else if (a.isQuery) qr.push_back(&a);
    }

    int redundancyCheck (ExprVector& lemmas, bool deferPriorities)
    {
      int num = 0;
      SamplFactory& sf = sfs[0].back();
      for (auto & l : lemmas)
      {
        if (deferPriorities)
        {
          deferredLearned.insert(l);
        }
        else
        {
          Sampl& s = sf.exprToSampl(l);
          if (!s.empty()) sf.assignPrioritiesForLearned();
        }
        numOfSMTChecks++;
        if (!u.implies(sf.getAllLemmas(), l))
        {
          sf.learnedExprs.insert(l);
          num++;
        }
      }
      return num;
    }

    bool checkSafetyAndReset(HornRuleExt* qu)
    {
      m_smt_solver.reset();
      m_smt_solver.assertExpr (qu->body);

      int ind = getVarIndex(qu->srcRelation, decls);
      SamplFactory& sf = sfs[ind].back();

      Expr lmApp = sf.getAllLemmas();
      for (int i = 0; i < qu->srcVars.size(); i++)
      {
        lmApp = replaceAll(lmApp, invarVars[ind][i], qu->srcVars[i]);
      }
      m_smt_solver.assertExpr(lmApp);

      numOfSMTChecks++;
      return bool(!m_smt_solver.solve ());
    }

    void getIS(HornRuleExt* hr, ExprVector& candSet, bool deferPriorities)
    {
      if (candSet.size() == 0) return;
      SamplFactory& sf = sfs[0].back();

      Expr cands = conjoin (candSet, m_efac);

      for (int i = candSet.size() - 1; i >= 0; i--)
      {
        Expr candPrime = candSet[i];

        for (int j = 0; j < hr->srcVars.size(); j++)
        {
          candPrime = replaceAll(candPrime, hr->srcVars[j], hr->dstVars[j]);
        }

        m_smt_solver.reset();
        m_smt_solver.assertExpr (hr->body);
        m_smt_solver.assertExpr (cands);
        m_smt_solver.assertExpr (sf.getAllLemmas());
        m_smt_solver.assertExpr (mk<NEG>(candPrime));

        numOfSMTChecks++;
        if (m_smt_solver.solve ())
        {
          modelsOfFailures[getModel(hr->srcVars)].insert(candSet[i]);

          if (deferPriorities)
          {
            deferredBlocked.insert(candSet[i]);
          }
          else
          {
            // GF: to debug (esp. nonlin opers)
            Sampl& s = sf.exprToSampl(candSet[i]);
            sf.assignPrioritiesForBlocked();
          }

          candSet.erase(candSet.begin() + i);

          getIS(hr, candSet, deferPriorities);
          return;
        }
      }
      return;
    }

    bool initCheckCand(HornRuleExt* fc, Expr cand)
    {
      Expr candPrime = cand;

      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        candPrime = replaceAll(candPrime, invarVars[0][j], fc->dstVars[j]);
      }

      m_smt_solver.reset();
      m_smt_solver.assertExpr (fc->body);
      m_smt_solver.assertExpr (mk<NEG>(candPrime));

      numOfSMTChecks++;
      return bool(!m_smt_solver.solve ());
    }

    bool houdini (ExprSet& cands, bool deferPriorities, bool skipInit)
    {
      SamplFactory& sf = sfs[0].back();
      ExprVector exprs;
      for (auto & a : cands) exprs.push_back(a);

      // initiation: remove crap first
      if (!skipInit)
      {
        for (auto a : fc)
        {
          for (int i = exprs.size() - 1; i >= 0; i--)
          {
            if (!initCheckCand(a, exprs[i]))
            {
              if (deferPriorities)
              {
                deferredFailed.insert(exprs[i]);
              }
              else
              {
                Sampl& s = sf.exprToSampl(exprs[i]);
                if (!s.empty()) sf.assignPrioritiesForFailed();
              }
              exprs.erase(exprs.begin()+i);
            }
          }
        }
      }

      // consecution
      for (auto a : tr) getIS(a, exprs, deferPriorities);

      // safety:
      int num = exprs.size();
      int newLemmaAdded = redundancyCheck(exprs, deferPriorities);

      if (newLemmaAdded == 0) return false;

      for (auto a : qr) if (!checkSafetyAndReset(a)) return false;

      return true;
    }

    void prioritiesDeferred()
    {
      SamplFactory& sf = sfs[0].back();

      for (auto & a : deferredLearned)
      {
        Sampl& s = sf.exprToSampl(a);
        sf.assignPrioritiesForLearned();
      }
      for (auto & a : deferredFailed)
      {
        Sampl& s = sf.exprToSampl(a);
        sf.assignPrioritiesForFailed();
      }
      for (auto & a : deferredBlocked)
      {
        Sampl& s = sf.exprToSampl(a);
        sf.assignPrioritiesForBlocked();
      }
    }

    bool synthesize(int maxAttempts, int batchSz, int scndChSz)
    {
      assert(sfs.size() == 1); // current limitation

      SamplFactory& sf = sfs[0].back();

      ExprVector candsBatch;

      bool success = false;
      int iter = 1;
      int triggerSecondChance = 0;
      int numFailInit = 0;

      for (int i = 0; i < maxAttempts; i++)
      {
        candsBatch.clear();

        if (printLog) outs() << "\n  ---- new iteration " << iter <<  " ----\n";

        while (candsBatch.size() < batchSz)
        {
          Expr cand = sf.getFreshCandidate();
          if (cand == NULL) continue;

          if (isTautology(cand))  // keep searching
          {
            sf.assignPrioritiesForLearned();
            continue;
          }

          if (sf.lf.nonlinVars.size() > 0 && !u.isSat(cand))  // keep searching
          {
            sf.assignPrioritiesForFailed();
            continue;
          }

          iter++;

          bool toskip = false;
          for (auto a : fc)
          {
            if (!initCheckCand(a, cand))
            {
              numFailInit++;
              sf.assignPrioritiesForFailed();
              toskip = true;
              break;
            }
          }
          if (toskip) continue;

          if (printLog) outs () << "   candidate for " << *decls[0] << ": " << *cand << "\n";

          candsBatch.push_back(cand);
        }

        for (auto a : tr) getIS(a, candsBatch, false);      // houdini

        if (candsBatch.size() == 0) continue;

        success = true;
        for (auto a : qr) success = success && checkSafetyAndReset(a);
        if (success) break;

        // second chance candidates
        triggerSecondChance += redundancyCheck(candsBatch, false);
        if (triggerSecondChance < scndChSz) continue;

        triggerSecondChance = 0;

        ExprSet secondChanceCands;
        for (auto it = modelsOfFailures.begin(); it != modelsOfFailures.end(); )
        {
          m_smt_solver.reset();
          m_smt_solver.assertExpr (it->first);
          m_smt_solver.assertExpr (sf.getAllLemmas());

          numOfSMTChecks++;
          if (!m_smt_solver.solve ()) // CE violated
          {
            for (auto & e : it->second) secondChanceCands.insert(e);
            modelsOfFailures.erase(it++);
          }
          else ++it;
        }

        if (secondChanceCands.size() > 0) success = houdini(secondChanceCands, false, true);
        if (success) break;
      }

      return success;
    }
  };
  
  inline void learnInvariants2(string smt, unsigned to, int maxAttempts,
                               int itp, int batch, int retry, bool freqs, bool aggp, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);

    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    RndLearnerV2 ds(m_efac, z3, ruleManager, to, freqs, aggp, debug);
    ds.categorizeCHCs();

    std::srand(std::time(0));

    if (ruleManager.decls.size() > 1)
    {
      outs() << "WARNING: learning multiple invariants is unsupported in --v2.\n"
             << "         Run --v3\n";
      return;
    }

    for (auto& dcl: ruleManager.decls) ds.initializeDecl(dcl->left());

    ExprSet cands;

    if (itp > 0) ds.bootstrapBoundedProofs(itp, cands);

    for (auto& dcl: ruleManager.decls) ds.prepareSeeds(dcl->arg(0), cands); // cands isn't used

    bool success = ds.houdini(cands, true, false);

    if (debug)
      outs () << "Number of bootstrapped lemmas: " << ds.getlearnedLemmas(0).size() << "\n";

    if (success)
      outs () << "Success after the bootstrapping\n";
    else
    {
      ds.calculateStatistics();
      ds.prioritiesDeferred();

      success = ds.synthesize(maxAttempts, batch, retry);
      if (debug)
        if (success) outs () << "Total number of learned lemmas: " << ds.getlearnedLemmas(0).size() << "\n";

      if (success) outs () << "Success after sampling\n";
      else         outs () << "No success after " << maxAttempts << " iterations\n";
    }

    if (success) ds.printSolution();
  }
}

#endif
