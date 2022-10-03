#ifndef EXPRBVSIMPL__HPP__
#define EXPRBVSIMPL__HPP__
#include "ufo/Smt/EZ3.hh"
#include "ufo/ExprBv.hh"

namespace ufo
{
  struct bvMultCoef
  {
    int coef;
    bool overflows;
  };

  unsigned getBvSize(Expr exp);
  Expr rewriteSignedCmp(Expr exp);
  void getSignedCmps(Expr a, ExprVector &scmps);
  Expr reBuildBvNegCmp(Expr fla, Expr lhs, Expr rhs);

  Expr bvAdditiveInverse(Expr e);
  void getBaddTerm(Expr a, ExprVector &terms);
  Expr bvReBuildCmp(Expr exp, Expr lhs, Expr rhs);
  Expr bvFlipCmp(Expr fla, Expr lhs, Expr rhs);
  bool isBmulVar(Expr e, Expr var);
  Expr getBmulVar(Expr e, Expr var);
  Expr mkBmul(Expr e, Expr c);
  bool isBdivVar(Expr e, Expr var);
  bool isBmulBdivVar(Expr e, Expr var);
  bool isBvArith(Expr e);
  void getBvMultVars(Expr e, Expr var, ExprVector &outs);
  bvMultCoef oveflowChecker(ExprVector &adds, Expr var);
  bool bvTrySquashCoefs(ExprVector &adds, Expr var);

  void buleToBult(Expr e, ZSolver<EZ3>::Model &m, ExprSet &out);
  void bultToBule(Expr e, ZSolver<EZ3>::Model &m, ExprSet &out);
  void bugeToBugt(Expr e, ZSolver<EZ3>::Model &m, ExprSet &out);
  void bugtToBuge(Expr e, ZSolver<EZ3>::Model &m, ExprSet &out);
  Expr rewriteBurem(Expr exp);

  template <typename Range>
  static Expr mkbadd(Range &terms)
  {
    assert(terms.size() > 0);
    return (terms.size() == 1) ? *terms.begin() : mknary<BADD>(terms);
  }

} // namespace ufo
#endif
