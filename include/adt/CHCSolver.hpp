#ifndef CHCSOLVER__HPP__
#define CHCSOLVER__HPP__

#include "deep/HornNonlin.hpp"
#include "ADTSolver.hpp"
#include "SimSynt.hpp"
#include <algorithm>

using namespace std;
using namespace boost;
namespace ufo
{
  class CHCSolver {
  private:
    ExprFactory &efac;
    ExprSet &adts;

    std::map<Expr,size_t> values_inds;
    ExprVector &constructors;
    ExprVector &assumptions;

    ExprSet &decls;
    vector<HornRuleExt> &chcs;

  public:
    CHCSolver(ExprVector& _constructors, ExprSet& _adts, ExprFactory &_efac, ExprSet &_decls, ExprVector &_assms, vector<HornRuleExt> &_chcs) :
      constructors(_constructors), adts(_adts), efac(_efac), decls(_decls), assumptions(_assms), chcs(_chcs) {}

    Expr createNewApp(HornRuleExt chc, int i, int ind) {
      ExprVector types;
      ExprVector newVars;
      for(int j = 0; j < chc.srcRelations[i]->arity() - 2; ++j) {
        if (j != ind) {
          Expr e = chc.srcRelations[i]->arg(j);
          types.push_back(bind::typeOf(chc.srcVars[i][j]));
          newVars.push_back(chc.srcVars[i][j]);
        }
      }
      types.push_back(bind::typeOf(chc.srcVars[i][ind]));
      Expr rel = bind::fdecl (efac.mkTerm(chc.srcRelations[i]->left()->op()), types);
      Expr app = bind::fapp (rel, newVars);
      return app;
    }

    void createLeftConjs(HornRuleExt chc, ExprVector & cnj) {
      for (int i = 0; i < chc.srcRelations.size(); i++) {
        if (decls.find(chc.srcRelations[i]) != decls.end()) {
          size_t ind = values_inds[chc.srcRelations[i]->left()];
          Expr app = createNewApp(chc, i, ind);
          Expr def = mk<EQ>(app, chc.srcVars[i][ind]);
          cnj.push_back(def);
        }
        else {
          Expr tmp = bind::fapp (chc.srcRelations[i], chc.srcVars[i]);
          cnj.push_back(tmp);
        }
      }
    }

    bool findMatchingFromBodyElement(HornRuleExt chc, Expr body_elem, ExprMap &matching) {
      if (body_elem->left()->arity() == 1
          && std::find(chc.dstVars.begin(), chc.dstVars.end(), body_elem->left()) != chc.dstVars.end()) {
        matching[body_elem->left()] = body_elem->right();
        return true;
      }
      else if (body_elem->right()->arity() == 1
          && std::find(chc.dstVars.begin(), chc.dstVars.end(), body_elem->right()) != chc.dstVars.end()) {
        matching[body_elem->right()] = body_elem->left();
        return true;
      }
        for (auto & v : chc.dstVars) {
          Expr ineq = ineqSimplifier(v, body_elem);
          if (ineq->left() == v) {
            matching[ineq->left()] = ineq->right();
            return true;
          }
        }
        if ((body_elem->left()->arity() == 1) && !(isConsctructor(bind::fname(body_elem->left())))) {
            matching[body_elem->left()] = body_elem->right();
            return true;
        }
        else if ((body_elem->right()->arity() == 1) && !(isConsctructor(bind::fname(body_elem->right())))) {
            matching[body_elem->right()] = body_elem->left();
            return true;
        }
      return false;
    }

    // find possible substitutions from body (add to cnj otherwise)
    void findMatchingFromBody(HornRuleExt chc, ExprMap &matching, ExprVector &cnj) {
      if (chc.body->arity() > 1) {
        for(int j = 0; j < chc.body->arity(); ++j) {
          Expr body_elem = chc.body->arg(j);
          if (!isOpX<EQ>(body_elem) || !findMatchingFromBodyElement(chc, body_elem, matching)) {
            cnj.push_back(body_elem);
          }
        }
      }
      else {
        if (!isOpX<EQ>(chc.body) || findMatchingFromBodyElement(chc, chc.body, matching)) {
          cnj.push_back(chc.body);
        }
      }
    }

    bool isConsctructor(Expr elem) {
      return std::find(constructors.begin(), constructors.end(), elem) != constructors.end();
    }

    void findMatchingFromLeftSideElem(Expr elem, ExprMap &matching) {
      if (isOpX<EQ>(elem)) {
        if (elem->left()->arity() == 1 && !(isConsctructor(bind::fname (elem->left())))) {
          matching[elem->left()] = elem->right();
        }
        else if (elem->right()->arity() == 1 && !(isConsctructor(bind::fname (elem->right())))) {
          matching[elem->right()] = elem->left();
        }
      }
    }

    void findMatchingFromLeftSide(Expr left, ExprMap &matching) {
      if (isOpX<AND>(left)) {
        for (int i = 0; i < left->arity(); ++i) {
          findMatchingFromLeftSideElem(left->arg(i), matching);
        }
      }
      else {
        findMatchingFromLeftSideElem(left, matching);
      }
    }

    Expr createDestination(HornRuleExt chc) {
      size_t ind = values_inds[chc.dstRelation->left()];
      ExprVector types;
      ExprVector newVars;
      for(int j = 0; j < chc.dstRelation->arity() - 2; ++j) {
        if (j != ind) {
          types.push_back(bind::typeOf(chc.dstVars[j]));
          newVars.push_back(chc.dstVars[j]);
        }
      }
      types.push_back(bind::typeOf(chc.dstVars[ind]));
      Expr rel = bind::fdecl (efac.mkTerm(chc.dstRelation->left()->op()), types);
      Expr baseApp = bind::fapp (rel, newVars);
      Expr destination = mk<EQ>(baseApp, chc.dstVars[ind]);
      return destination;
    }

    bool solve() {
      // find the return value for uninterpreted symbols (keep it in values_inds map)
      for (auto & decl: decls) {
          if (decl->arity() <= 3) {
              decls.erase(decl);
              break;
          }
        for (auto & chc : chcs) {
          if (chc.dstRelation == decl && !chc.isFact) {
// TODO: think about return value when there are only adt vars
              // std::vector<size_t> adt_inds;
              size_t vars_size = chc.dstRelation->arity();
              // bool found = false;
              // for (size_t i = vars_size - 2; i > 0; --i) {
              //   bool is_adt = false;
              //   for (auto & adt : adts) {
              //     if ((*chc.dstRelation)[i] == adt) {
              //       is_adt = true;
              //       adt_inds.push_back(i - 1);
              //       break;
              //     }
              //   }
              //   if (!is_adt) {
              //     values_inds[chc.dstRelation->left()] = i - 1;
              //     found = true;
              //     break;
              //   }
              // }
              // if (!found) {
              //   for (int i = 0; i < chc.srcRelations.size(); i++) {
              //     if (chc.srcRelations[i] == decl) {
              //       for (int j = 0; j < adt_inds.size(); ++j) {
              //         size_t ind = adt_inds[j];
              //         Expr eq1 = mk<EQ>(chc.srcVars[0][ind], chc.dstVars[ind]);
              //         Expr eq2 = mk<EQ>(chc.dstVars[ind], chc.srcVars[0][ind]);
              //         if (!contains(chc.body, eq1) && !contains(chc.body, eq2)) {
              //           values_inds[chc.dstRelation->left()] = ind;
              //           found = true;
              //           break;
              //         }
              //       }
              //       break;
              //     }
              //   }
              // }
              // if (!found) {
              values_inds[chc.dstRelation->left()] = vars_size - 3;
              // }
              break;
          }
        }
      }

      // creating assumptions
      for (auto & chc : chcs) {
        if (!chc.isQuery) {
          ExprVector cnj;
          ExprMap matching;
          createLeftConjs(chc, cnj);
          findMatchingFromBody(chc, matching, cnj);
          Expr destination = bind::fapp (chc.dstRelation, chc.dstVars);
          size_t ind;
          if (decls.find(chc.dstRelation) != decls.end()) {
            destination = createDestination(chc);
          }
          Expr asmpt = mk<IMPL>(conjoin(cnj, efac), destination);
          asmpt = replaceAll(asmpt, matching);

          // trying substitute equalities from left side to the right one
          matching.clear();
          Expr left = asmpt->left();
          findMatchingFromLeftSide(left, matching);
          asmpt = replaceAll(asmpt, matching);
          asmpt = simplifyArithm(asmpt);
          asmpt = simplifyBool(asmpt);
          if (asmpt->arity() > 0) {
            asmpt = createQuantifiedFormula(asmpt, constructors);
          }
          assumptions.push_back(asmpt);
        }
      }

      // creating queries for ADT-ind
      for (auto & chc : chcs) {
        if (chc.isQuery) {
          Expr destination;
          ExprVector cnj;
          ExprMap matching;
          if (chc.body->arity() > 1) {
            for(int j = 0; j < chc.body->arity(); ++j) {
              if (isOpX<NEG>(chc.body->arg(j))) {
                destination = mkNeg(chc.body->arg(j));
              }
              else {
                cnj.push_back(chc.body->arg(j));
              }
            }
          }
          else {
            destination = mkNeg(chc.body);
          }
          for (int i = 0; i < chc.srcRelations.size(); i++) {
            if (decls.find(chc.srcRelations[i]) != decls.end()) {
              size_t ind = values_inds[chc.srcRelations[i]->left()];
              Expr app = createNewApp(chc, i, ind);
              matching[chc.srcVars[i][ind]] = app;
            }
            else {
               Expr tmp = bind::fapp (chc.srcRelations[i], chc.srcVars[i]);
               cnj.push_back(tmp);
            }
          }

          Expr goal = replaceAll(mk<IMPL>(conjoin(cnj, efac), destination), matching);
          matching.clear();
          Expr left = goal->left();

          findMatchingFromLeftSide(left, matching);
          goal = replaceAll(goal, matching);
//          goal = simplifyArithm(goal);
          goal = simplifyBool(goal);
          ExprVector current_assumptions = assumptions;
          // outs() << "assumptions:\n";
          // for (auto & a : current_assumptions) {
          //   outs() << *a << "\n";
          // } 
          // outs() << "goal: \n";
          // outs() << *goal << "\n";
          if (!prove (current_assumptions, goal))
            return false;
          else {
            assumptions.push_back(goal);
          }
        }
        else {
          ExprVector cnj;
          ExprMap matching;
          createLeftConjs(chc, cnj);
          findMatchingFromBody(chc, matching, cnj);
          Expr destination = bind::fapp (chc.dstRelation, chc.dstVars);
          ExprVector vars = chc.dstVars;
          if (decls.find(chc.dstRelation) != decls.end()) {
            destination = createDestination(chc);
          }
          Expr goal = mk<IMPL>(conjoin(cnj, efac), destination);
          goal = replaceAll(goal, matching);
          goal = simplifyArithm(goal);
          goal = simplifyBool(goal);
          ExprVector current_assumptions = assumptions;
          if (!prove (current_assumptions, goal))
            return false;
        }
      }
      return true;
    }

    bool solveArr(){
      Expr decl = NULL;
      for (auto & d : decls){
        if (containsOp<ARRAY_TY>(d)){
          if (decl == NULL) decl = d;
          else return false;
        }
      }
      Expr base;
      ExprVector opsAdt, opsArr;
      set<int> visited;
      ExprMap varVersions;

      ExprSet adts;
      for (auto & c : constructors) adts.insert(c->last());

      while (visited.size() != chcs.size()){
        for (int i = 0; i < chcs.size(); i++){
          if (find(visited.begin(), visited.end(), i) != visited.end()) continue;
          auto &hr = chcs[i];

          if (hr.isInductive && varVersions.empty())
            for (int j = 0; j < hr.srcVars[0].size(); j++)
              varVersions[hr.srcVars[0][j]] = hr.dstVars[j];

          if (hr.isFact && varVersions.empty()) continue;

          ExprSet tmp, tmpAdt, tmpArr;
          getConj(hr.body, tmp);
          for (auto & a : tmp){
            bool adt = false;
            for (auto & c : adts)
              if (contains(a, c)) {
                tmpAdt.insert(a);
                adt = true;
                break;
              }
            if (!adt) tmpArr.insert(a);
          }
          assert (!tmpAdt.empty());

          if (hr.isFact && !varVersions.empty()){
            base = replaceAllRev(conjoin(tmpArr, efac), varVersions);
          } else {
            opsAdt.push_back(conjoin(tmpAdt, efac));
            opsArr.push_back(conjoin(tmpArr, efac));
          }
          visited.insert(i);
        }
      }

      // getting a candidate
      SimSynt sim (efac, opsAdt, opsArr, varVersions, constructors, decl, assumptions, base);
      sim.proc();

      // proving
      for (int i = 0; i < chcs.size(); i++){
        if (!checkCHC(chcs[i])) return false;
      }
      sim.printSol();
      return true;
    }

    bool checkCHC(HornRuleExt& hr, bool print = false){
      ExprVector assms = assumptions;
      Expr goal = hr.isQuery ? mk<FALSE>(efac) : bind::fapp (hr.dstRelation, hr.dstVars);
      for (int i = 0; i < hr.srcRelations.size(); i++){
        assms.push_back(bind::fapp (hr.srcRelations[i], hr.srcVars[i]));
      }
      assms.push_back(hr.body);
      return prove (assms, goal, 2, print);
    }

    bool prove (ExprVector& lemmas, Expr fla, int rounds = 2, bool print = false)
    {
      ADTSolver sol (fla, lemmas, constructors, 5, 2, 3, 1, print); // last false is for verbosity
      return isOpX<FORALL>(fla) ? sol.solve() : sol.solveNoind(rounds);
    }
  };

  void chcSolve(char * smt_file)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ExprSet adts;
    ruleManager.parse(smt_file);
//    ruleManager.print();

    ExprVector constructors;
    ExprVector assumptions;

    ExprSet& decls = ruleManager.decls;

    for (auto & a : z3.getAdtConstructors()) {
      constructors.push_back(regularizeQF(a));
      adts.insert(a->last());
    }

    CHCSolver sol (constructors, adts, efac, decls, ruleManager.extras, ruleManager.chcs);
    bool res = containsOp<ARRAY_TY>(conjoin(decls, efac)) ? sol.solveArr() : sol.solve();
    outs () << (res ? "unsat\n" : "unknown\n");
  }
}

#endif
