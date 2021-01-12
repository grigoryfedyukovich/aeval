#ifndef CHCSOLVER__HPP__
#define CHCSOLVER__HPP__

#include "deep/HornNonlin.hpp"
#include "ADTSolver.hpp"
#include <algorithm>

using namespace std;
using namespace boost;
namespace ufo
{
  bool isConst(Expr expr) {
    return bind::isAdtConst(expr) || bind::isBoolConst(expr) || bind::isIntConst(expr) || bind::isRealConst(expr);
  }

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

    for (auto & decl: ruleManager.decls) {
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
        ExprMap body_matching;
        if (a.body->arity() > 1) {
          for(int j = 0; j < a.body->arity(); ++j) {
            if (isOpX<NEG>(a.body->arg(j))) {
              destination = mkNeg(a.body->arg(j));
            }
            // else if (isOpX<EQ>(a.body->arg(j))) {
            //   Expr body_elem = a.body->arg(j);
            //   if (body_elem->left()->arity() == 1) {
            //     body_matching[body_elem->left()] = body_elem->right();
            //     outs() << "body matching left " << *body_elem->left() << *body_elem->right() << "\n";
            //   }
            //   else if (body_elem->right()->arity() == 1) {
            //     body_matching[body_elem->right()] = body_elem->left();
            //     outs() << "body matching right " << *body_elem->right() << *body_elem->left() << "\n";
            //   }
            //   cnj.push_back(a.body->arg(j));
            // }
            else {
              cnj.push_back(a.body->arg(j));
            }
          }
        }
        else {
          destination = mkNeg(a.body);
        }
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
        outs() << *mk<IMPL>(conjoin(cnj, efac), destination) << "\n";
        outs() << *(replaceAll(mk<IMPL>(conjoin(cnj, efac), destination), matching)) << "\n";

        goal = replaceAll(mk<IMPL>(conjoin(cnj, efac), destination), matching);
        matching.clear();
        Expr left = goal->left();
        outs() << "left: " << *left << "\n";
        if (isOpX<AND>(left)) {
          for (int i = 0; i < left->arity(); ++i) {
            if (isOpX<EQ>(left->arg(i))) {
              if (left->arg(i)->left()->arity() == 1) {
                matching[left->arg(i)->left()] = left->arg(i)->right();
              }
              else if (left->arg(i)->right()->arity() == 1) {
                matching[left->arg(i)->right()] = left->arg(i)->left();
              }
            }
          }
        }
        else if (isOpX<EQ>(left)) {
          if (left->left()->arity() == 1 && !isConst(left->left())) {
            matching[left->left()] = left->right();
            outs() << *left->left() << " " << bind::isAdtConst(left->left()) << bind::IsVar () (left->left()) << bind::IsVar () (left->right()) << "\n";
          }
          else if (left->right()->arity() == 1) {
            matching[left->right()] = left->left();
          }
        }
        goal = replaceAll(goal, matching);
        outs() << "new goal: " << *goal << "\n";
        goal = simplifyArithm(goal);
        goal = simplifyBool(goal);
        if (goal->arity() > 0) {
          goal = createQuantifiedFormula(goal, constructors);
        }
      }
      else {
        ExprVector cnj;
        ExprMap matching;
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
            // matching[a.srcVars[i][ind]] = app;
            Expr def = mk<EQ>(app, a.srcVars[i][ind]);
            cnj.push_back(def);
          }
          else {
            Expr tmp = bind::fapp (a.srcRelations[i], a.srcVars[i]);
            cnj.push_back(tmp);
          }
        }
        for(int j = 0; j < a.body->arity(); ++j) {
          if (isOpX<EQ>(a.body->arg(j))) {
            Expr body_elem = a.body->arg(j);

            if (body_elem->left()->arity() == 1 
              && std::find(a.dstVars.begin(), a.dstVars.end(), body_elem->left()) != a.dstVars.end()) {
              outs() << "HERE LEFT\n" << *body_elem << "\n";
              matching[body_elem->left()] = body_elem->right();
            }
            else if (body_elem->right()->arity() == 1 
              && std::find(a.dstVars.begin(), a.dstVars.end(), body_elem->right()) != a.dstVars.end()) {
              outs() << "HERE RIGHT\n" << *body_elem << "\n";
              matching[body_elem->right()] = body_elem->left();
            }
            // else {
            //   cnj.push_back(a.body->arg(j));
            // }
            else {
              for (auto & v : a.dstVars) {
                Expr ineq = ineqSimplifier(v, body_elem);
                outs() << "INEQ " << *v << " " << *ineq << "\n";
                if (ineq->left() == v) {
                  matching[ineq->left()] = ineq->right();
                }
              }
            }
          }
          else {
            cnj.push_back(a.body->arg(j));
          }
        }
        // cnj.push_back(a.body);
        Expr destination = bind::fapp (a.dstRelation, a.dstVars);
        ExprVector vars = a.dstVars;
        size_t ind;
        if (decls.find(a.dstRelation) != decls.end()) {
          ind = aux[a.dstRelation->left()];
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
        Expr asmpt = mk<IMPL>(conjoin(cnj, efac), destination);
        outs() << "First asmpt: " << *asmpt << "\n";
        asmpt = replaceAll(asmpt, matching);
        outs() << "Second asmpt " << *asmpt << "\n";
        matching.clear();
        Expr left = asmpt->left();
        if (isOpX<AND>(asmpt->left())) {
          for (int i = 0; i < left->arity(); ++i) {
            if (isOpX<EQ>(left->arg(i))) {
              if (left->arg(i)->left()->arity() == 1) {
                matching[left->arg(i)->left()] = left->arg(i)->right();
              }
              else if (left->arg(i)->right()->arity() == 1) {
                matching[left->arg(i)->right()] = left->arg(i)->left();
              }
            }
          }
        }
        if (isOpX<EQ>(asmpt->left())) {
          if (asmpt->left()->left()->arity() == 1) {
            // Expr h = ineqSimplifier(asmpt->left()->left(), asmpt->left());
            matching[asmpt->left()->left()] = asmpt->left()->right();
            // outs() << *h << "\n";
          }
          else if (asmpt->left()->right()->arity() == 1) {
            // Expr h = ineqSimplifier(asmpt->left()->right(), asmpt->left());
            matching[asmpt->left()->right()] = asmpt->left()->left();
            // outs() << *h << "\n";
          }
        }
        asmpt = replaceAll(asmpt, matching);
        outs() << "Third asmpt " << *asmpt << "\n";
        asmpt = simplifyArithm(asmpt);
        asmpt = simplifyBool(asmpt);
        outs() << "NEW assumptions " << *asmpt << " " << asmpt->arity() << "\n";
        if (asmpt->arity() > 0) {
          asmpt = createQuantifiedFormula(asmpt, constructors);
        }
        assumptions.push_back(asmpt);
      }
    }
    outs() << "print assumptions: " << "\n";
    for (auto & a : assumptions) {
      outs() << *a << "\n";
    }
    outs() << "goal:\n" << *goal << "\n";

    ADTSolver sol (goal, assumptions, constructors);
    sol.solve();
  }
}

#endif
