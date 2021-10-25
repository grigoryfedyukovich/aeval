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

    // Keep the current return values
    std::map<Expr,int> values_inds;
    ExprVector &constructors;
    ExprVector &assumptions;

    ExprSet &decls;
    ExprVector ordered_decls;
    vector<HornRuleExt> &chcs;
    int number_decls;
    bool givePriority = false;
    bool ignoreBaseVar = false;

    map<Expr, Expr> baseConstructors;
    map<Expr, Expr> indConstructors;

    map<Expr, Expr> baseDefinitions;
    map<Expr, Expr> indDefinitions;
    map<Expr, Expr> interpretations;

  public:
    CHCSolver(ExprVector& _constructors, ExprSet& _adts, ExprFactory &_efac, ExprSet &_decls, ExprVector &_assms, vector<HornRuleExt> &_chcs, bool _nonadtPriority = false, bool _ignoreBase = false) :
      constructors(_constructors), adts(_adts), efac(_efac), decls(_decls), assumptions(_assms), chcs(_chcs), givePriority(_nonadtPriority), ignoreBaseVar(_ignoreBase) {}

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

    void replaceDeclsInLeftPart(HornRuleExt chc, ExprVector & cnj) {
      for (int i = 0; i < chc.srcRelations.size(); i++) {
        if (decls.find(chc.srcRelations[i]) != decls.end()) {
          // as we don't allow mutual recursion and decls are sorted, 
          // we suppose that srcRelations doesn't contain predicates with unknown definition
          // TODO: should check the assumption above 
          int ind = values_inds[chc.srcRelations[i]->left()];
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

    bool findMatchingFromElement(HornRuleExt chc, Expr elem, ExprMap &matching) {
      if (!chc.isQuery) {
        if (elem->left()->arity() == 1
            && std::find(chc.dstVars.begin(), chc.dstVars.end(), elem->left()) != chc.dstVars.end()) {
          matching[elem->left()] = elem->right();
          return true;
        }
        else if (elem->right()->arity() == 1
            && std::find(chc.dstVars.begin(), chc.dstVars.end(), elem->right()) != chc.dstVars.end()) {
          matching[elem->right()] = elem->left();
          return true;
        }
        for (auto & v : chc.dstVars) {
          Expr ineq = ineqSimplifier(v, elem);
          if (ineq->left() == v) {
            matching[ineq->left()] = ineq->right();
            return true;
          }
        }
      }
      if ((elem->left()->arity() == 1) && !(isConstructor(bind::fname(elem->left())))) {
          matching[elem->left()] = elem->right();
          return true;
      }
      else if ((elem->right()->arity() == 1) && !(isConstructor(bind::fname(elem->right())))) {
          matching[elem->right()] = elem->left();
          return true;
      }
      return false;
    }

    bool findMatchingFromRule(HornRuleExt chc, ExprMap &matching, Expr rule) {
      if (isOpX<IMPL>(rule)) {
        rule = rule->left();
      }
      if (isOpX<AND>(rule)) {
        for(int j = 0; j < rule->arity(); ++j) {
          Expr elem = rule->arg(j);
          if (isOpX<EQ>(elem) && findMatchingFromElement(chc, elem, matching)) {
            return true;
          }
        }
      }
      else {
        if (isOpX<EQ>(rule) && findMatchingFromElement(chc, rule, matching)) {
          return true;
        }
      }
      return false;
    }

    bool isConstructor(Expr elem) {
      return std::find(constructors.begin(), constructors.end(), elem) != constructors.end();
    }

    Expr createDestination(HornRuleExt chc) {
      int ind = values_inds[chc.dstRelation->left()];
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

    Expr convertToFunction(HornRuleExt chc) {
      ExprVector cnj;
      ExprMap matching;
      Expr destination = bind::fapp (chc.dstRelation, chc.dstVars);
      if (decls.find(chc.dstRelation) != decls.end()) {
        destination = createDestination(chc);
        interpretations[chc.dstRelation] = destination;
      }
      replaceDeclsInLeftPart(chc, cnj);
      cnj.push_back(chc.body);
      Expr asmpt = mk<IMPL>(conjoin(cnj, efac), destination);
      while (!isOpX<EQ>(asmpt) && findMatchingFromRule(chc, matching, asmpt)) {
        asmpt = replaceAll(asmpt, matching);
        asmpt = simplifyBool(asmpt);
        matching.clear();
      }
      asmpt = simplifyArithm(asmpt);
      if (asmpt->arity() > 0) {
        asmpt = createQuantifiedFormula(asmpt, constructors);
      }
      return asmpt;
    }

    bool createAndCheckDefinition(Expr &decl) {
      ExprVector current_assumptions = assumptions;
      for (auto & chc : chcs) {
        if (chc.dstRelation == decl && chc.isFact) {
          for (int i = 0; i < chc.dstVars.size(); ++i) {
            // inductive variable should be an adt
            if (adts.find(bind::typeOf(chc.dstVars[i])) != adts.end()) {
              Expr baseConstructor = baseConstructors[bind::typeOf(chc.dstVars[i])];
              int baseConstructorArity = baseConstructor->arity() - 1;
              for(int j = 0; j < chc.body->arity(); ++j) {
                Expr body_elem = chc.body->arg(j);
                if (isOpX<EQ>(body_elem)) {
                  if ((body_elem->left() == chc.dstVars[i] && body_elem->right()->arity() == baseConstructorArity) ||
                    (body_elem->right() == chc.dstVars[i] && body_elem->left()->arity() == baseConstructorArity)) {
                    
                    Expr base_asmpt = convertToFunction(chc);
                    baseDefinitions[decl] = base_asmpt;

                    Expr indConstructor = indConstructors[bind::typeOf(chc.dstVars[i])];
                    if (indConstructor == NULL) {
                      assumptions.push_back(base_asmpt);
                      return true;
                    }
                    int indConstructorArity = indConstructor->arity() - 1;
                    ExprVector lemmas;

                    // we should check that this variable is inductive in inductive rule
                    for (auto & ind_chc : chcs) {
                      if (ind_chc.dstRelation == decl && !ind_chc.isFact) {
                        for (int k = 0; k < ind_chc.srcRelations.size(); ++k) {
                          if (ind_chc.srcRelations[k] == decl) {
                            Expr elem = ind_chc.body;
                            bool shouldBeChecked = false;
                            if (isOpX<EQ>(elem)) {
                              if ((elem->left() == ind_chc.dstVars[i] && elem->right()->arity() == indConstructorArity) ||
                                  (elem->right() == ind_chc.dstVars[i] && elem->left()->arity() == indConstructorArity)) {
                                shouldBeChecked = true;
                              }
                            }
                            else {
                              for(int m = 0; m < ind_chc.body->arity(); ++m) {
                                Expr ind_body_elem = ind_chc.body->arg(m);
                                if (isOpX<EQ>(ind_body_elem)) {
                                  // TODO: add comparison of src vars with conctructor
                                  if ((ind_body_elem->left() == ind_chc.dstVars[i] && ind_body_elem->right()->arity() == indConstructorArity) ||
                                    (ind_body_elem->right() == ind_chc.dstVars[i] && ind_body_elem->left()->arity() == indConstructorArity)) {
                                    shouldBeChecked = true;
                                  }
                                }
                              }
                            }
                            if (shouldBeChecked) {
                              Expr ind_asmpt = convertToFunction(ind_chc);
                              indDefinitions[decl] =  ind_asmpt;
                              bool foundRecursiveDefinition = true;
                              // We should check that for all rules (including non-definitive) this definition is correct
                              for (auto & rule : chcs) {
                                if (rule.dstRelation == decl) {
                                  Expr goal = convertToFunction(rule);
                                  current_assumptions.clear();
                                  current_assumptions = assumptions;
                                  current_assumptions.push_back(baseDefinitions[decl]);
                                  current_assumptions.push_back(indDefinitions[decl]);
                                  if (!prove (current_assumptions, goal)) {
                                    foundRecursiveDefinition = false;
                                    break;
                                  }
                                  else {
                                    lemmas.push_back(goal);
                                  }
                                }
                              }
                              if (foundRecursiveDefinition == true) {
                                for (auto & lemma : lemmas) {
                                  assumptions.push_back(lemma);
                                }
                                return true;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
      return false;
    }

    bool createAndCheckInterpretations() {
      // creating assumptions
      for (auto & decl : ordered_decls) {
        createAndCheckDefinition(decl);
      }

      // creating goals for ADT-ind from CHC-queries
      for (auto & chc : chcs) {
        if (chc.isQuery) {
          Expr destination;
          ExprVector cnj;
          ExprMap matching;
          if (chc.body->arity() > 1) {
            for(int j = 0; j < chc.body->arity(); ++j) {
              Expr body_elem = chc.body->arg(j);
              if (isOpX<NEG>(body_elem)) {
                destination = mkNeg(body_elem);
              }
              else {
                cnj.push_back(body_elem);
              }
            }
          }
          else {
            destination = mkNeg(chc.body);
          }
          if (decls.find(destination->left()) != decls.end()) {
            int ind = values_inds[destination->left()->left()];
            ExprVector types;
            ExprVector newVars;
            for(int j = 1; j < destination->arity(); ++j) {
              if (j - 1 != ind) {
                types.push_back(bind::typeOf(destination->arg(j)));
                newVars.push_back(destination->arg(j));
              }
            }
            types.push_back(bind::typeOf(destination->arg(ind + 1)));
            Expr rel = bind::fdecl (efac.mkTerm(destination->left()->left()->op()), types);
            Expr baseApp = bind::fapp (rel, newVars);
            destination = mk<EQ>(baseApp, destination->arg(ind + 1));
          }

          replaceDeclsInLeftPart(chc, cnj);
          Expr goal = mk<IMPL>(conjoin(cnj, efac), destination);
          while (!isOpX<EQ>(goal) && findMatchingFromRule(chc, matching, goal)) {
            goal = replaceAll(goal, matching);
            goal = simplifyBool(goal);
            matching.clear();
          }
          ExprVector current_assumptions = assumptions;
          goal = createQuantifiedFormula(goal, constructors);
          // Check if the goal may be proved in current interpretations
          if (!prove (current_assumptions, goal)) {
            return false;
          }
          else {
            assumptions.push_back(goal);
          }
        }
      }
      for (auto & decl : ordered_decls) {
        outs() << interpretations[decl] << "\n";
        outs() << baseDefinitions[decl] << "\n";
        outs() << indDefinitions[decl] << "\n";
      }
      return true;
  }

    int baseVar(Expr &decl) {
      for (auto & chc : chcs) {
        if (chc.dstRelation == decl) {
          for (int i = 0; i < chc.dstVars.size(); ++i) {
            if (adts.find(bind::typeOf(chc.dstVars[i])) != adts.end()) {
              for(int j = 0; j < chc.body->arity(); ++j) {
                Expr body_elem = chc.body->arg(j);
                if (isOpX<EQ>(body_elem)) {
                  if ((body_elem->left() == chc.dstVars[i] && body_elem->right()->arity() == 1) ||
                    (body_elem->right() == chc.dstVars[i] && body_elem->left()->arity() == 1)) {
                    return i;
                  }
                }
              }
            }
          }
        }
      }
      return -1;
    }

    // result is written to ordered_decls
    // cur_decls is used to find the mutual recursion
    bool orderDecls(Expr decl, ExprSet &cur_decls) {
      // Already contains this decl
      if (std::find(ordered_decls.begin(), ordered_decls.end(), decl) != ordered_decls.end())
        return true;
      cur_decls.insert(decl);
      for (auto & chc : chcs) {
        if (chc.dstRelation == decl && !chc.isFact) {
          for (int i = 0; i < chc.srcRelations.size(); i++) {
            // if the src symbol is already in ordered_decls do nothing
            if (chc.srcRelations[i] != decl && std::find(ordered_decls.begin(), ordered_decls.end(), chc.srcRelations[i]) == ordered_decls.end()) {
              // there is a mutual recursion, for now we cannot handle this
              if (cur_decls.find(chc.srcRelations[i]) != cur_decls.end()) {
                outs () << "could not order predicates -- mutual recursion is not supported\n";
                return false;
              }
              else {
                // current predicate depends on another, so we need to push this another predicate earlier
                orderDecls(chc.srcRelations[i], cur_decls);
              }
            }
          }
        }
      }
      ordered_decls.push_back(decl);
      return true;
    }

    // Get indexes in right order and remove the base index
    void excludeBaseVar(Expr& decl, std::vector<int> &idxs) {
      int bv = baseVar(decl);
      idxs.erase(idxs.begin() + bv);
    }

    void givePriorityNonAdt(Expr& decl, std::vector<int> &idxs) {
      std::vector<int> new_idxs;
      bool nonadtExists = false;
      for (auto & chc : chcs) {
        if (chc.dstRelation == decl) {
          for (int i = 0; i < idxs.size(); ++i) {
            bool is_adt = false;
            for (auto & adt : adts) {
              if ((*chc.dstRelation)[idxs[i]] == adt) {
                is_adt = true;
                break;
              }
            }
            if (!is_adt) {
              nonadtExists = true;
              new_idxs.push_back(idxs[i]);
            }
          }
          if (nonadtExists) {
            for (int i = 0; i < idxs.size(); ++i) {
              for (auto & adt : adts) {
                if ((*chc.dstRelation)[idxs[i]] == adt) {
                  new_idxs.push_back(idxs[i]);
                  break;
                }
              }
            }
            idxs = new_idxs;
          }
          break;
        }
      }
    }

    void setConstructors() {
      for (auto & a : constructors) {
        Expr type = a->last();
        bool ind = false;
        for (int i = 0; i < a->arity() - 1; i++)
        {
          if (a->last() == a->arg(i))
          {
            ind = true;
            if (indConstructors[type] != NULL && indConstructors[type] != a)
            {
              outs () << "Several inductive constructors are not supported\n";
              exit(1);
            }
            indConstructors[type] = a;
          }
        }
        if (!ind)
        {
          if (baseConstructors[type] != NULL && baseConstructors[type] != a)
          {
            outs () << "Several base constructors are not supported\n";
            exit(1);
          }
          baseConstructors[type] = a;
        } 
      }
    }

    bool findInterpretations(int idx, std::map<Expr,int> &buf) {
      if (idx >= ordered_decls.size()) {
        values_inds = buf;
        assumptions.clear();
        return createAndCheckInterpretations();
      }
      // Get the possible version of return variables
      Expr cur = ordered_decls[idx];
      for (auto & chc : chcs) {
        if (chc.dstRelation == cur) {
          size_t vars_size = chc.dstRelation->arity();
          std::vector<int> idxs;
          for (int i = 0; i < vars_size - 2; ++i) {
            idxs.push_back(i);
          }
          // add functions for filter variables here
          if (ignoreBaseVar) excludeBaseVar(cur, idxs);
          if (givePriority) givePriorityNonAdt(cur, idxs);
           // outs() << *chc.dstRelation->left() << " " << idxs.size() << "\n";
          for (int i = idxs.size() - 1; i >= 0; --i) {
            buf[chc.dstRelation->left()] = idxs[i];
            // outs() << *chc.dstRelation->left() << " " << idxs[i] << "\n";
            if (findInterpretations(idx + 1, buf))
              return true;
          }
          break;
        }
      }
      return false;
    }

    bool solve() {
      // Order current uninterpreted predicate symbols
      for (auto & decl: decls) {
        // outs() << *decl << "\n";
        ExprSet cur_decls;
        if (!orderDecls(decl, cur_decls))
          return false;
      }
      setConstructors();
      std::map<Expr,int> buf;
      return findInterpretations(0, buf);
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

    bool checkCHC(HornRuleExt& hr, bool print = false) {
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
      ADTSolver sol (fla, lemmas, constructors); // last false is for verbosity
      return isOpX<FORALL>(fla) ? sol.solve() : sol.solveNoind(rounds);
    }
  };

  void chcSolve(char * smt_file, bool givePriorityNonAdt, bool ignoreBaseVar)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ExprSet adts;
    ruleManager.parse(smt_file);
    // ruleManager.print();

    ExprVector constructors;

    ExprSet& decls = ruleManager.decls;

    for (auto & a : z3.getAdtConstructors()) {
      constructors.push_back(regularizeQF(a));
      adts.insert(a->last());
    }

    CHCSolver sol (constructors, adts, efac, decls, ruleManager.extras, ruleManager.chcs,
      givePriorityNonAdt, ignoreBaseVar);
    bool res = containsOp<ARRAY_TY>(conjoin(decls, efac)) ? sol.solveArr() : sol.solve();
    outs () << (res ? "sat\n" : "unknown\n");
  }
}

#endif
