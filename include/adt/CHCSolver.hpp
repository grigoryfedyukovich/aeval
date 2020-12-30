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

    ExprVector spec;
    ExprVector goal_assumptions;
    ExprMap replace_vars;
    std::vector<int> spec_ids;
    std::vector<size_t> adt_inds;
    ExprSet decls = ruleManager.decls;
    Expr goal;

    for (auto & a : z3.getAdtConstructors()) {
      constructors.push_back(regularizeQF(a));
      adts.insert(a->last());
    }

    for (auto & a : ruleManager.chcs) {
      
    }

    for (auto & decl: ruleManager.decls) {
      outs () << "decl " << *decl <<"\n";
      for (auto & a : ruleManager.chcs) {
        if (a.dstRelation == decl) {
          size_t vars_size = a.dstRelation->arity();
          if (a.isInductive) {
            bool found_adt = false;
            for (size_t i = vars_size - 2; i > 0; --i) {
              bool is_adt = false;
              for (auto & adt : adts) {
                if ((*a.dstRelation)[i] == adt) {
                  is_adt = true;
                  found_adt = true;
                  adt_inds.push_back(i - 1);
                  break;
                }
              }
              if (!is_adt) {
                aux[a.dstRelation->left()] = i - 1;
                break;
              }
            }
            if (aux[a.dstRelation->left()] == 0 && found_adt) {
              for (int j = 0; j < adt_inds.size(); ++j) {
                size_t ind = adt_inds[j];
                Expr eq1 = mk<EQ>(a.srcVars[0][ind], a.dstVars[ind]);
                Expr eq2 = mk<EQ>(a.dstVars[ind], a.srcVars[0][ind]);
                if (!contains(a.body, eq1) && !contains(a.body, eq2)) {
                  aux[a.dstRelation->left()] = ind;
                  break;
                }
              }
            }
          }
          else {
            aux[a.dstRelation->left()] = vars_size - 3;
          }
        }
      }
    }

    for (auto & a : ruleManager.chcs) {
      if (a.isQuery) {
        Expr destination;
        ExprVector cnj;
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < a.srcRelations.size(); i++) {
          if (decls.find(a.srcRelations[i]) != decls.end()) {
            size_t ind = aux[a.srcRelations[i]->left()];
            ExprVector types;
            ExprVector newVars;
            types.push_back(bind::typeOf(a.srcVars[i][ind]));
            for(int j = 0; j < a.srcRelations[i]->arity() - 2; ++j) {
              if (j != ind) {
                Expr e = a.srcRelations[i]->arg(j);
                types.push_back(bind::typeOf(a.srcVars[i][j]));
                newVars.push_back(a.srcVars[i][j]);
              }
            }
            Expr rel = bind::fdecl (efac.mkTerm(a.srcRelations[i]->left()->op()), types);
            Expr app = bind::fapp (rel, newVars);
            matching[a.srcVars[i][ind]] = app;
            args.push_back(a.srcVars[i][ind]);
            // Expr def = mk<EQ>(a.srcVars[i][ind], app);
            // cnj.push_back(def);
            // replace_vars[a.srcRelations[i]->left()] = def;
            // spec_ids.push_back(spec.size());
            // goal_assumptions.push_back(baseDef);
          }
          else {
             Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
             cnj.push_back(tmp);
          }
        }
        if (a.body->arity() > 1) {
          for(int j = 0; j < a.body->arity(); ++j) {
            if (isOpX<NEG>(a.body->arg(j))) {
              cnj.push_back(mkNeg(a.body->arg(j)));
            }
            else {
              cnj.push_back(a.body->arg(j));
            }
          }
        }
        else {
          cnj.push_back(mkNeg(a.body));
        }
        goal = (createQuantifiedFormula(replaceAll(conjoin(cnj, efac), matching), constructors));
      }
      else {
        ExprVector cnj;
        for (int i = 0; i < a.srcRelations.size(); i++) {
          if (decls.find(a.srcRelations[i]) != decls.end()) {
            size_t ind = aux[a.srcRelations[i]->left()];
            Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
            ExprVector types;
            ExprVector newVars;
            types.push_back(bind::typeOf(a.srcVars[i][ind]));
            for(int j = 0; j < a.srcRelations[i]->arity() - 2; ++j) {
              if (j != ind) {
                Expr e = a.srcRelations[i]->arg(j);
                types.push_back(bind::typeOf(a.srcVars[i][j]));
                newVars.push_back(a.srcVars[i][j]);
              }
            }
            Expr rel = bind::fdecl (efac.mkTerm(a.srcRelations[i]->left()->op()), types);
            Expr app = bind::fapp (rel, newVars);
            Expr def = mk<EQ>(app, a.srcVars[i][ind]);
            cnj.push_back(def);
          }
          else {
            Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
            cnj.push_back(tmp);
          }
        }
        cnj.push_back(a.body);
        Expr destination = bind::fapp (a.dstRelation, a.dstVars);
        ExprVector vars = a.dstVars;
        if (decls.find(a.dstRelation) != decls.end()) {
          size_t ind = aux[a.dstRelation->left()];
          ExprVector types;
          ExprVector newVars;
          types.push_back(bind::typeOf(a.dstVars[ind]));
          for(int j = 0; j < a.dstRelation->arity() - 2; ++j) {
            if (j != ind) {
              types.push_back(bind::typeOf(a.dstVars[j]));
              newVars.push_back(a.dstVars[j]);
            }
          }
          Expr rel = bind::fdecl (efac.mkTerm(a.dstRelation->left()->op()), types);
          Expr baseApp = bind::fapp (rel, newVars);
          destination = mk<EQ>(baseApp, a.dstVars[ind]);
        }
        assumptions.push_back(createQuantifiedFormula(
        mk<IMPL>(conjoin(cnj, efac), destination), constructors));
      }
    }
    outs() << "print assumptions: " << "\n";
    for (auto & a : assumptions) {
      outs() << *a << "\n";
    }

    // for (auto & a : ruleManager.chcs) {
    //   if (aux[a.dstRelation->left()] != 0) {
    //     // Expr goal = conjoin(spec, efac);
    //     // Expr goal;
    //     ExprMap matching;
    //     ExprVector newAssumptions = assumptions;
    //     size_t ind = aux[a.dstRelation->left()];
    //     Expr e = replace_vars[a.dstRelation->left()];
    //     matching[e->left()] = a.dstVars[ind];
    //     for(int j = 0; j < a.dstRelation->arity(); ++j) {
    //       if (j != ind) {
    //         matching[e->right()->arg(j)] = a.dstVars[j];
    //       }
    //     }
    //     newAssumptions.push_back(replaceAll(e, matching));
    //     // for (int i = 0; i < spec_ids.size(); ++i) {
    //     //   Expr e = goal_assumptions[spec_ids[i]];
    //     //   matching[e->right()] = a.dstVars[ind-1];
    //     //   for(int j = 1; j < a.dstRelation->arity() - 1; ++j) {
    //     //     if (j != ind) {
    //     //       matching[e->left()->arg(j)] = a.dstVars[j-1];
    //     //     }
    //     //   }
    //     //   newAssumptions.push_back(replaceAll(e, matching));
    //     // }
    //     for (auto & a : goal_assumptions) {
    //       newAssumptions.push_back(replaceAll(a, matching));
    //     }
    //     ExprVector replaced_spec;
    //     for (auto &s : spec) {
    //       replaced_spec.push_back(replaceAll(s, matching));
    //     }
    //     Expr goal = conjoin(replaced_spec, efac);
    //     for(int j = 0; j < a.body->arity(); ++j) {
    //       newAssumptions.push_back((a.body->arg(j)));
    //     }
    //     if (a.isInductive) {
    //       matching.clear();
    //       replaced_spec.clear();
    //       size_t ind = aux[a.srcRelations[0]->left()];
    //       Expr e = replace_vars[a.dstRelation->left()];
    //       matching[e->left()] = a.srcVars[0][ind];
    //       for(int j = 0; j < a.dstRelation->arity(); ++j) {
    //         if (j != ind) {
    //           matching[e->right()->arg(j)] = a.srcVars[0][j];
    //         }
    //       }
    //       newAssumptions.push_back(replaceAll(e, matching));
    //       for (auto &s : spec) {
    //         replaced_spec.push_back(replaceAll(s, matching));
    //       }
    //       newAssumptions.push_back(conjoin(replaced_spec, efac));
    //       // Expr tmp = conjoin(spec, efac);
    //       // outs() << "tmp: " << *tmp << "\n";
    //       // for (int i = 0; i < spec_ids.size(); ++i) {
    //       //   Expr e = spec[spec_ids[i]];
    //       //   matching[e->right()] = a.srcVars[0][ind-1];
    //       //   for(int j = 1; j < a.srcRelations[0]->arity() - 1; ++j) {
    //       //     if (j != ind) {
    //       //       matching[e->left()->arg(j)] = a.srcVars[0][j-1];
    //       //     }
    //       //   }
    //       //   tmp = replaceAll(tmp, matching);
    //       //   newAssumptions.push_back(tmp);
    //       // }
    //     }

    //     outs() << "print new assumptions: " << "\n";
    //     for (auto & a : newAssumptions) {
    //       outs() << *a << "\n";
    //     }
    //     outs() << "goal: " << *goal << "\n";

    vector<int> basenums, indnums; // dummies
    // res = solve(basenums, indnums);
    ADTSolver sol (goal, assumptions, constructors);
    sol.solve(basenums, indnums);
    //   }
      // if (a.isQuery) {
      //     outs() << "In query rules \n";
      //     for (int i = 0; i < a.srcRelations.size(); ++i) {
      //       outs() << *a.srcRelations[i] << "\n";
      //       for (int j = 0; j < a.srcVars[i].size(); ++j) {
      //         outs() << *a.srcVars[i][j] << "\n";
      //       }
      //     }
      //   }
  }
}

#endif
