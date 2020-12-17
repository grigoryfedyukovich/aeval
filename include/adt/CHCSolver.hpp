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
    ExprSet adts;
    ruleManager.parse(smt_file);
    ruleManager.print();

    std::map<Expr,size_t> aux;
    ExprVector constructors;
    ExprVector assumptions;
    ExprVector empt;
    for (auto & a : z3.getAdtConstructors()) {
      constructors.push_back(regularizeQF(a));
      adts.insert(a->last());
    }

    ExprVector spec;
    ExprVector goal_assumptions;
    ExprMap replace_vars;
    std::vector<int> spec_ids;
    std::vector<size_t> adt_inds;

    for (auto & a : ruleManager.chcs) {
      if (a.isInductive) {
        size_t vars_size = a.dstRelation->arity();
        bool found_adt = false;
        for (size_t i = vars_size - 2; i > 0; --i) {
          bool is_adt = false;
          for (auto & adt : adts) {
            if ((*a.dstRelation)[i] == adt) {
              is_adt = true;
              found_adt = true;
              adt_inds.push_back(i);
              break;
            }
          }
          if (!is_adt) {
            aux[a.dstRelation->left()] = i;
            break;
          }
        }
        if (aux[a.dstRelation->left()] == 0 && found_adt) {
          for (int j = 0; j < adt_inds.size(); ++j) {
            size_t ind = adt_inds[j];
            Expr eq = mk<EQ>(a.srcVars[0][ind-1], a.dstVars[ind-1]);
            // Contains doesn't work correctly
            if (!contains(a.body, eq)) {
              aux[a.dstRelation->left()] = ind;
              break;
            }
          }
        }
      }
    }

    for (auto & a : ruleManager.chcs) {
      if (a.isQuery) {
        for (int i = 0; i < a.srcRelations.size(); i++) {
          if (aux[a.srcRelations[i]->left()] != 0) {
            size_t ind = aux[a.srcRelations[i]->left()];
            ExprVector types;
            ExprVector newVars;
            for(int j = 1; j < a.srcRelations[i]->arity() - 1; ++j) {
              if (j != ind) {
                Expr e = a.srcRelations[i]->arg(j);
                types.push_back(bind::typeOf(a.srcVars[i][j-1]));
                newVars.push_back(a.srcVars[i][j-1]);
              }
            }
            types.push_back(bind::typeOf(a.srcVars[i][ind-1]));
            Expr rel = bind::fdecl (efac.mkTerm(a.srcRelations[i]->left()->op()), types);
            Expr baseApp = bind::fapp (rel, newVars);
            Expr baseDef = mk<EQ>(baseApp, a.srcVars[i][ind-1]);
            replace_vars[a.srcRelations[i]->left()] = baseDef;
            // spec_ids.push_back(spec.size());
            // goal_assumptions.push_back(baseDef);
          }
          else {
             Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
             goal_assumptions.push_back(tmp);
          }
        }
        spec.push_back(mkNeg(a.body));
        // for(int j = 0; j < a.body->arity(); ++j) {
        //   outs() << isOpX<NEG>(a.body->arg(j)) << " " << *a.body->arg(j) << "\n";
        //   outs() << *a.body << "\n";
        //   if (isOpX<NEG>(a.body->arg(j))) {
        //     outs() << "neg " << a.body->arg(j) << "\n";
        //     spec.push_back(mkNeg(a.body->arg(j)));
        //   }
        //   goal_assumptions.push_back((a.body->arg(j)));
        // }
      }
      else {
        ExprVector cnj;
        for (int i = 0; i < a.srcRelations.size(); i++) {
          if (aux[a.srcRelations[i]->left()] != 0) {
            size_t ind = aux[a.srcRelations[i]->left()];
            Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
            ExprVector types;
            ExprVector newVars;
            for(int j = 1; j < a.srcRelations[i]->arity() - 1; ++j) {
              if (j != ind) {
                Expr e = a.srcRelations[i]->arg(j);
                types.push_back(bind::typeOf(a.srcVars[i][j-1]));
                newVars.push_back(a.srcVars[i][j-1]);
              }
            }
            types.push_back(bind::typeOf(a.srcVars[i][ind-1]));
            Expr rel = bind::fdecl (efac.mkTerm(a.dstRelation->left()->op()), types);
            Expr app = bind::fapp (rel, newVars);
            Expr def = mk<EQ>(app, a.srcVars[i][ind-1]);
            cnj.push_back(def);
          }
          else {
            Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
            cnj.push_back(tmp);
          }
        }
        cnj.push_back(a.body);
        Expr destination =  bind::fapp (a.dstRelation, a.dstVars);
        ExprVector vars = a.dstVars;
        if (aux[a.dstRelation->left()] != 0) {
          size_t ind = aux[a.dstRelation->left()];
          ExprVector types;
          ExprVector newVars;
          for(int j = 1; j < a.dstRelation->arity() - 1; ++j) {
            if (j != ind) {
              types.push_back(bind::typeOf(a.dstVars[j-1]));
              newVars.push_back(a.dstVars[j-1]);
            }
          }
          types.push_back(bind::typeOf(a.dstVars[ind-1]));
          Expr rel = bind::fdecl (efac.mkTerm(a.dstRelation->left()->op()), types);
          Expr baseApp = bind::fapp (rel, newVars);
          destination = mk<EQ>(baseApp, a.dstVars[ind-1]);
        }
        assumptions.push_back(createQuantifiedFormula(
        mk<IMPL>(conjoin(cnj, efac), destination), empt));
      }
    }
    outs() << "print assumptions: " << "\n";
    for (auto & a : assumptions) {
      outs() << *a << "\n";
    }

    for (auto & a : ruleManager.chcs) {
      if (aux[a.dstRelation->left()] != 0) {
        // Expr goal = conjoin(spec, efac);
        // Expr goal;
        ExprMap matching;
        ExprVector newAssumptions = assumptions;
        size_t ind = aux[a.dstRelation->left()];
        Expr e = replace_vars[a.dstRelation->left()];
        matching[e->right()] = a.dstVars[ind-1];
        for(int j = 1; j < a.dstRelation->arity() - 1; ++j) {
          if (j != ind) {
            matching[e->left()->arg(j)] = a.dstVars[j-1];
          }
        }
        outs() << "HERE " << *e << "\n";
        outs() << *replaceAll(e, matching) << "\n";
        newAssumptions.push_back(replaceAll(e, matching));
        // for (int i = 0; i < spec_ids.size(); ++i) {
        //   Expr e = goal_assumptions[spec_ids[i]];
        //   matching[e->right()] = a.dstVars[ind-1];
        //   for(int j = 1; j < a.dstRelation->arity() - 1; ++j) {
        //     if (j != ind) {
        //       matching[e->left()->arg(j)] = a.dstVars[j-1];
        //     }
        //   }
        //   newAssumptions.push_back(replaceAll(e, matching));
        // }
        for (auto & a : goal_assumptions) {
          newAssumptions.push_back(replaceAll(a, matching));
        }
        Expr goal = conjoin(spec, efac);
        newAssumptions.push_back(a.body);
        if (a.isInductive) {
          matching.clear();
          size_t ind = aux[a.srcRelations[0]->left()];
          Expr e = replace_vars[a.dstRelation->left()];
          matching[e->right()] = a.srcVars[0][ind-1];
          for(int j = 1; j < a.dstRelation->arity() - 1; ++j) {
            if (j != ind) {
              matching[e->left()->arg(j)] = a.srcVars[0][j-1];
            }
          }
          newAssumptions.push_back(replaceAll(e, matching));
          // Expr tmp = conjoin(spec, efac);
          // outs() << "tmp: " << *tmp << "\n";
          // for (int i = 0; i < spec_ids.size(); ++i) {
          //   Expr e = spec[spec_ids[i]];
          //   matching[e->right()] = a.srcVars[0][ind-1];
          //   for(int j = 1; j < a.srcRelations[0]->arity() - 1; ++j) {
          //     if (j != ind) {
          //       matching[e->left()->arg(j)] = a.srcVars[0][j-1];
          //     }
          //   }
          //   tmp = replaceAll(tmp, matching);
          //   newAssumptions.push_back(tmp);
          // }
        }

        outs() << "print new assumptions: " << "\n";
        for (auto & a : newAssumptions) {
          outs() << *a << "\n";
        }
        outs() << "goal: " << *goal << "\n";

        ADTSolver sol (goal, newAssumptions, constructors);
        sol.solveNoind();
      }
    }
  }
}

#endif
