#ifndef CHCSOLVER__HPP__
#define CHCSOLVER__HPP__

#include "deep/HornNonlin.hpp"
#include "ADTSolver.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  void chcSolve(char * smt_file)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(smt_file);
    ruleManager.print();

    // TODO: convert rules to recursive function and then to CHCs and call adt-ind
    //       e.g, smth like this:
//    ExprVector constructors;
//    ExprVector assumptions;
//    ExprVector empt;
//    for (auto & a : z3.getAdtConstructors()) constructors.push_back(regularizeQF(a));
//
//    Expr goal = mkNeg(ruleManager.chcs[ruleManager.qCHCNum].body);
//    for (auto & a : ruleManager.chcs)
//    {
//      if (a.isQuery)
//      {
//        for (int i = 0; i < a.srcRelations.size(); i++)
//        {
//          Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
//          assumptions.push_back(tmp);
//        }
//        goal = mkNeg(a.body);
//      }
//      else
//      {
//        ExprVector cnj;
//        for (int i = 0; i < a.srcRelations.size(); i++)
//        {
//          Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
//          cnj.push_back(tmp);
//        }
//        cnj.push_back(a.body);
//        assumptions.push_back(createQuantifiedFormula(
//          mk<IMPL>(conjoin(cnj, efac), bind::fapp (a.dstRelation, a.dstVars)), empt));
//      }
//    }
//    ADTSolver sol (goal, assumptions, constructors);
//    sol.solveNoind();
  }
}

#endif
