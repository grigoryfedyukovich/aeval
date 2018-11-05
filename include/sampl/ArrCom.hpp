#ifndef ARRCOM__HPP__
#define ARRCOM__HPP__

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class ARRfactory
  {
    private:

    ExprFactory &m_efac;
    ExprVector vars;
    ExprVector forall_args;
    LAfactory preFac;
    LAfactory postFac;
    Expr pre;
    density postOrAritiesDensity;

    public:

    ARRfactory(ExprFactory &_efac, bool _false) :
        m_efac(_efac), preFac(_efac, false), postFac(_efac, false) {};

    void addVar(Expr var)
    {
      vars.push_back(var); // currently, not used. TODO: at least some sanity checks later
    }

    void initializeLAfactory (LAfactory& lf, ExprSet& cands, ExprVector& intVars, int eps)
    {
      set<int> arrConsts;
      set<int> arrCoefs;
      for (auto & a : cands)
      {
        if (getLinCombCoefs(a, arrCoefs))
        {
          getLinCombConsts(a, arrConsts);
        }
      }
      arrConsts.insert(1);
      arrConsts.insert(-1);
      for (auto & a : intVars) lf.addVar(a);
      for (auto & a : arrConsts) lf.addConst(a);
      for (auto & a : arrCoefs) lf.addIntCoef(a);

      lf.initialize();
      set<int> orArities;
      vector <LAdisj> laDisjs;
      for (auto & a : cands)
      {
        LAdisj b;
        lf.exprToLAdisj(a, b);
        laDisjs.push_back(b);
        int ar = b.arity;
        postOrAritiesDensity[ar] ++;
        orArities.insert(ar);
      }

      lf.initDensities(orArities);
      for (auto & b : laDisjs) lf.calculateStatistics(b, b.arity, 0, 0);
      for (auto & ar : orArities) lf.stabilizeDensities(ar, eps, 1);
    }

    void initialize(ExprVector& intVars, ExprSet& arrCands, ExprSet& arrSelects, ExprSet& arrRange)
    {
      ExprSet it_vars;
      for (auto & a : arrSelects) {
      postFac.addVar(a);
      filter (a->right(), bind::IsConst(), std::inserter (it_vars, it_vars.begin ()));
      }
      for (auto & it : it_vars)
      {
        if (bind::isIntConst(it))
        {
          postFac.addVar(it);
          preFac.addVar(it);
          if (find(intVars.begin(), intVars.end(), it) == intVars.end())
            forall_args.push_back(it->left());
        }
      }

      pre = mk<TRUE>(m_efac);
      for (auto & a : arrRange)
      {
        if (!emptyIntersect(a, preFac.getVars()))
          pre = mk<AND>(pre, a);
      }

      initializeLAfactory(preFac, arrRange, intVars, 1);
      initializeLAfactory(postFac, arrCands, intVars, 0);
    }

    Expr guessTerm ()
    {
      LAdisj expr1;
      LAdisj expr2;
      // GF: fixed guesses, currently
      // TODO: 1) pruning based on dependencies of pre and expr1,
      //       2) pruning based on dependencies of expr1 and expr2,
      //       3) conjunctive and disjunctive expr1 and expr2
      int arity = chooseByWeight(postOrAritiesDensity);
      if (preFac.guessTerm(expr1, 1) && postFac.guessTerm(expr2, arity == 0 ? 1 : arity))
      {
        ExprVector args = forall_args;
        args.push_back(mk<IMPL>(mk<AND>(pre, preFac.toExpr(expr1)), postFac.toExpr(expr2)));
        Expr forallExpr = mknary<FORALL> (args);
        return forallExpr;
      }
      else
      {
        return NULL;
      }
    }

    // used for bootstrapping where `post` is one of the `arrCands`
    Expr getSimplCand(Expr post)
    {
      ExprVector args = forall_args;
      args.push_back(mk<IMPL>(pre, post));
      return mknary<FORALL> (args);
    }

    Expr guessSimplTerm ()
    {
      LAdisj expr2;
      int arity = chooseByWeight(postOrAritiesDensity);
      if (postFac.guessTerm(expr2, arity))
      {
        ExprVector args = forall_args;
        args.push_back(mk<IMPL>(pre, postFac.toExpr(expr2)));
        Expr forallExpr = mknary<FORALL> (args);
        return forallExpr;
      }
      else
      {
        return NULL;
      }
    }
  };
}


#endif
