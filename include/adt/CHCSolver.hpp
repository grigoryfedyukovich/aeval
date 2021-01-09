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
              destination = mkNeg(a.body->arg(j));
            }
            else {
              cnj.push_back(a.body->arg(j));
            }
          }
        }
        else {
          destination = mkNeg(a.body);
        }
        goal = (createQuantifiedFormula
          (replaceAll(mk<IMPL>(conjoin(cnj, efac), destination), matching), constructors));
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
            if (body_elem->right()->arity() == 1) {
              matching[body_elem->right()] = body_elem->left();
            }
            else {
              cnj.push_back(a.body->arg(j));
            }
            outs() << "HERE:\n" << *a.body->arg(j) << "\n" << a.body->arg(j)->left()->arity() << " " << a.body->arg(j)->right()->arity() << "\n";
          }
          else {
            cnj.push_back(a.body->arg(j));
          }
        }
        // cnj.push_back(a.body);
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
        Expr asmpt = mk<IMPL>(conjoin(cnj, efac), destination);
        outs() << "First asmpt: " << *asmpt << "\n";
        asmpt = replaceAll(asmpt, matching);
        outs() << "Second asmpt " << *asmpt << "\n";
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
