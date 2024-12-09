#ifndef SAMPL__HPP__
#define SAMPL__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"
#include "BoolCom.hpp"
#include "ArrCom.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // wrapper for LinCom.hpp, BoolCom.hpp, etc (in the future)
  class Sampl
  {
    public:

    Bdisj b_part;
    LAdisj l_part;

    int arity()
    {
      return l_part.arity + ((b_part.arity > 0) ? 1 : 0);
    }

    bool empty() { return arity() == 0; }

    Sampl() {}

  };

  class SamplFactory
  {
    private:
    ExprFactory &m_efac;

    vector<Sampl> samples;

    density hasBooleanComb;
    density orAritiesDensity;
    bool hasArrays = false;

    public:

    LAfactory lf;
    Bfactory bf;
    ARRfactory af;

    ExprSet learnedExprs;

    int initialized = 0;

    SamplFactory(ExprFactory &_efac, bool aggp) :
      m_efac(_efac), lf(_efac, aggp), bf(_efac), af(_efac, aggp) {}

    Expr getAllLemmas()
    {
      return conjoin(learnedExprs, m_efac);
    }

    bool addVar(Expr var)
    {
      bool added = false;
      if (bind::isBoolConst(var))
      {
        bf.addVar(var);
        added = true;
      }
      else if (bind::isIntConst(var))
      {
        lf.addVar(var);
        added = true;
      }
      else if (bind::isConst<ARRAY_TY> (var))
      {
        af.addVar(var);
        added = true;
        hasArrays = true;
      }
      return added;
    }

    void initialize(ExprSet& arrCands, ExprVector& arrAccessVars, ExprSet& arrRange)
    {
      bf.initialize();
      lf.initialize();
      if (hasArrays)
      {
        if (!arrAccessVars.empty() && !arrRange.empty())
        {
          af.initialize(lf.getVars(), arrCands, arrAccessVars, arrRange);
          initialized++;
        }
      }
      initialized++;
    }

    Sampl& exprToSampl(Expr ex)
    {
      samples.push_back(Sampl());
      Bdisj& bcs = samples.back().b_part;
      LAdisj& lcs = samples.back().l_part;

      bf.exprToBdisj(ex, bcs);
      lf.exprToLAdisj(ex, lcs);

      if (!lcs.empty()) lcs.normalizePlus();
      if (!bcs.empty()) bcs.normalizeOr();

      return samples.back();
    }

    Expr sampleToExpr(Sampl& s)
    {
      if (s.l_part.arity == 0 && s.b_part.arity == 0)
        return NULL;
      if (s.l_part.arity == 0)
        return bf.toExpr(s.b_part);
      if (s.b_part.arity == 0)
        return lf.toExpr(s.l_part);

      return mk<OR>(bf.toExpr(s.b_part), lf.toExpr(s.l_part));
    }

    void calculateStatistics(bool freqs, bool addepsilon)
    {
      int maxArity = 0;
      set<int> orArities;

      if (lf.getVars().size() > 0 && samples.size() == 0)
      {
        // artificially add one default sample in case there is nothing here
        // TODO: find a better solution
        exprToSampl (mk<GEQ>(lf.getVars()[0], mkTerm<string>("0", m_efac)));
      }

      for (auto &s : samples)
      {
        maxArity = max (maxArity, s.arity());
        orArities.insert(s.arity());
        orAritiesDensity[s.arity()] ++;
      }

      for (int i = 0; i < maxArity; i++)
      {
        if (orAritiesDensity[i] == 0)
          orArities.insert(i);
      }

      lf.initDensities(orArities);
      bf.initDensities();

      for (auto &s : samples)
      {
        LAdisj& l = s.l_part;
        Bdisj& b = s.b_part;
        if (!l.empty())
        {
          lf.calculateStatistics(l, s.arity(), freqs, addepsilon);
        }
        if (!b.empty())
        {
          bf.calculateStatistics(b, freqs);
          hasBooleanComb[1]++;
        }
        else
        {
          // frequency of empty bool combinations
          hasBooleanComb[0]++;
        }
      }

      // now, stabilization:

      if (!freqs)
      {
        for (auto & ar : orAritiesDensity)
        {
          ar.second = 1;
        }
      }

      bf.stabilizeDensities(addepsilon, freqs);

      for (auto & ar : orAritiesDensity)
      {
        lf.stabilizeDensities(ar.first, addepsilon, freqs);
      }
    }

    Expr getFreshLinCom()
    {
      samples.push_back(Sampl());
      Sampl& curCand = samples.back();

      if (!lf.guessTerm(curCand.l_part, 1, 1)) return NULL;
      curCand.l_part.normalizePlus();
      return lf.toExpr(curCand.l_part);
    }

    Expr getFreshCandidate(bool arrSimpl = true)
    {
      // for now, if a CHC system has arrays, we try candidates only with array
      // in the future, we will need arithmetic candidates as well
      if (hasArrays && initialized == 2)
      {
        Expr cand = arrSimpl ? af.guessSimplTerm() : af.guessTerm();
        if (cand != NULL)
        {
          for (auto & v : lf.nonlinVars) cand = replaceAll(cand, v.second, v.first);
          return cand;
        }
      }

      if (orAritiesDensity.empty()) return NULL;

      int arity = chooseByWeight(orAritiesDensity);
      int hasBool = chooseByWeight(hasBooleanComb);
      int hasLin = arity - hasBool;
    //  outs() << "arity, hasBool, hasLin\n";
    //  outs() << arity << "    " << hasBool << "    " << hasLin << "\n";
      samples.push_back(Sampl());
      Sampl& curCand = samples.back();

      Expr lExpr;
      if (hasLin > 0)
      {
        if (!lf.guessTerm(curCand.l_part, arity, hasLin)) return NULL;
        curCand.l_part.normalizePlus();
        lExpr = lf.toExpr(curCand.l_part);
      }

      Expr bExpr;
      if (hasBool > 0)
      {
        if (!bf.guessTerm(curCand.b_part)) return NULL;
        bExpr = bf.toExpr(curCand.b_part);
      }

      if (hasBool > 0 && hasLin > 0)
      {
        return mk<OR>(bExpr, lExpr);
      }
      else if (hasBool > 0)
      {
        return bExpr;
      }
      else
      {
        return lExpr;
      }
    }

    void assignPrioritiesForLearned(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForLearned(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);
    }

    void assignPrioritiesForFailed(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForFailed(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);
    }

    void assignPrioritiesForBlocked(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForBlocked(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);
    }

    void assignPrioritiesForLearned()
    {
      assignPrioritiesForLearned(samples.back());
    }

    void assignPrioritiesForFailed()
    {
      assignPrioritiesForFailed(samples.back());
    }

    void assignPrioritiesForBlocked()
    {
      assignPrioritiesForBlocked(samples.back());
    }

    void printStatistics()
    {
      for (auto &a : orAritiesDensity)
      {
        outs() << "OR arity density: " << a.first << " |--> " << a.second << "\n";
      }

      bf.printCodeStatistics();

      if (lf.getConsts().size() > 0)
      {
        outs() << "\nInt consts:\n";
        for (auto &form: lf.getConsts()) outs() << lexical_cast<string>(form) << ", ";
        outs() << "\b\b \n";

        for (auto &ar : orAritiesDensity) lf.printCodeStatistics(ar.first);
      }
    }
  };
}

#endif
