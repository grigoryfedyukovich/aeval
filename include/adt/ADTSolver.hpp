#ifndef ADTSOLVER__HPP__
#define ADTSOLVER__HPP__
#include <assert.h>
#include <string.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{
  class ADTSolver
  {
    private:

    Expr goal;
    ExprVector& assumptions;
    ExprVector& constructors;

    map<Expr, Expr> baseConstructors;
    map<Expr, Expr> indConstructors;

    ExprFactory &efac;
    SMTUtils u;

    ExprVector rewriteHistory;
    vector<int> rewriteSequence;
    int maxDepth;
    int maxGrow;
    int mergingIts;
    int earlySplit;
    bool verbose;
    int sp = 2;
    int glob_ind = 0;
    ExprVector blockedAssms;

    public:

    ADTSolver(Expr _goal, ExprVector& _assumptions, ExprVector& _constructors,
              int _maxDepth = 5, int _maxGrow = 3, int _mergingIts = 3, int _earlySplit = 1, bool _verbose = false) :
        goal(_goal), assumptions(_assumptions), constructors(_constructors),
        efac(_goal->getFactory()), u(_goal->getFactory()), maxDepth(_maxDepth), maxGrow(_maxGrow), mergingIts(_mergingIts),
        earlySplit(_earlySplit), verbose(_verbose) {}

    bool simplifyGoal()
    {
      Expr goalQF = goal->last();
      goalQF = liftITEs(goalQF);
      goalQF = u.simplifyITE(goalQF);   // TODO: more simplification passes
      if (u.isEquiv(goalQF, mk<TRUE>(efac))) return true;

      ExprVector args;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (contains(goal->last(), goal->arg(i))) args.push_back(goal->arg(i));
      }
      if (args.size() == 0) goal = goalQF;
      else
      {
        args.push_back(goalQF);
        goal = mknary<FORALL>(args);
      }
      rewriteHistory.push_back(goal);
      return false;
    }

    bool mergeAssumptions(int bnd = -1)
    {
      // simplify them first
      int sz = assumptions.size();
      for (int i = 0; i < sz; i++) // TODO: add mores simplifications
      {
        Expr &a = assumptions[i];
        a = simplifyBool(a);
        if (isOpX<FORALL>(a))
        {
          Expr newAssm = replaceAll(a, a->last(), normalizeImpl(a->last()));
          if (newAssm != a)
          {
            assumptions.push_back(newAssm);
          }
        }
      }

      if (bnd == -1) bnd = mergingIts; // default val
      for (int i = 0; i < bnd; i++)
      {
        ExprSet newAssms;
        for (auto a : assumptions)
        {
          // todo: figure out why there could be NULLs
          if (a == NULL) continue;

          if (isOpX<ITE>(a))
          {
            newAssms.insert(a);
            continue; // GF: could be useful in principle
          }

          if (!isOpX<FORALL>(a) && simplifyAssm(a, newAssms))
          {
            return true;
          }
          if (isOpX<NEG>(a))
          {
            getConj(mkNeg(a->left()), newAssms);
          }
          else
          {
            newAssms.insert(a);
          }
        }
        assumptions.clear();
        for (auto & a : newAssms)
          if (find (blockedAssms.begin(), blockedAssms.end(), a) == blockedAssms.end())
            unique_push_back(a, assumptions);
      }
      return false;
    }

    void splitAssumptions()
    {
      ExprSet newAssms;
      for (auto & a : assumptions)
      {
        if (a != NULL) getConj(a, newAssms);
      }
      assumptions.clear();
      for (auto & a : newAssms) assumptions.push_back(a);
    }

    bool simplifyAssm(Expr assm, ExprSet& newAssms)
    {
      for (auto a : assumptions)
      {
        if (a == assm || a == NULL) continue;
        if (isOpX<FORALL>(assm) && !isOpX<FORALL>(a)) continue;

        Expr tmp = useAssumption(assm, a, true);
        if (tmp != NULL && !u.isTrue(tmp))
        {
          if (u.isFalse(tmp))
          {
            if (verbose) outs () << string(sp, ' ')
              << "inconsistent assumptions: " << *assm << " and " << *a << "\n";
            return true;
          }

          ExprSet tmps;
          getConj(simplifyBool(tmp), tmps);
          getConj(simplifyBool(simplifyArr(tmp)), tmps); // duplicate for the case of arrays
          for (auto & t : tmps)
          {
            if (find(assumptions.begin(), assumptions.end(), t) == assumptions.end())
            {
              newAssms.insert(t);
            }
          }
        }
      }
      return false;
    }

    // main method to do rewriting
    // TODO: separate the logic for fwd, otherwise the code gets messy
    Expr useAssumption(Expr subgoal, Expr assm, bool fwd = false)
    {
      if (isOpX<FORALL>(assm))
      {
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(bind::fapp(assm->arg(i)));

        Expr assmQF = assm->last();
        Expr repl = assmQF;

        bool isImpl = false;
        if (isOpX<IMPL>(assmQF))
        {
          if (fwd) assmQF = assmQF->left();
          else assmQF = assmQF->right();
          isImpl = true;
        }

        if (isOpX<ITE>(assmQF))
        {
          int res = -1;
          if (fwd)
          {
            if (findMatching (assmQF->left(), subgoal, args, matching))
            {
              res = 1;
            }
            else
            {
              matching.clear();
              if (findMatching (mkNeg(assmQF->left()), subgoal, args, matching))
              {
                res = 2;
              }
            }
            if (res > 0)
            {
              repl = replaceAll(assmQF->arg(res), matching);

              // sanity removal
              for (auto it = args.begin(); it != args.end();)
              {
                if (contains (repl, *it)) ++it;
                else it = args.erase(it);
              }

              if (!args.empty())
              {
                repl = createQuantifiedFormulaRestr(repl, args);
              }

              return repl;
            }
          }
          else
          {
            // !fwd

            if (findMatching (assmQF->right(), subgoal, args, matching))
            {
              res = 1;
            }
            else
            {
              matching.clear();
              if (findMatching (assmQF->last(), subgoal, args, matching))
              {
                res = 2;
              }
            }
            if (res > 0)
            {
              if (res == 1) repl = assmQF->left();
              else repl = mkNeg(assmQF->left());
              repl = replaceAll(repl, matching);

              ExprSet vars;
              filter(assmQF->left(), bind::IsConst (), inserter(vars, vars.begin()));

              for (auto it = args.begin(); it != args.end();)
              {
                if (find(vars.begin(), vars.end(), *it) != vars.end())
                {
                  it = args.erase(it);
                }
                else
                {
                  ++it;
                }
              }
              if (!args.empty()) repl = createQuantifiedFormulaRestr(repl, args, false);
  
              return repl;
            }
          }
        }

        // we first search for a matching of the entire assumption (usually some inequality)
        if (findMatchingSubexpr (assmQF, subgoal, args, matching))
        {
          repl = replaceAll(repl, matching);
          Expr replaced;
          if (isImpl)
          {
            if (fwd) // used in simplifyAssm
            {
              if (!isOpX<FORALL>(subgoal) && u.implies(subgoal, repl->left()))
              {
                ExprSet vars;
                filter (assmQF, bind::IsConst (), inserter(vars, vars.begin()));
                for (auto it = args.begin(); it != args.end();)
                {
                  bool found = false;
                  if (find(vars.begin(), vars.end(), *it) != vars.end())
                  {
                    found = true;
                    it = args.erase(it);
                  }
                  if (!found)
                  {
                    ++it;
                  }
                }

                // sanity removal
                for (auto it = args.begin(); it != args.end();)
                {
                  if (contains (repl->right(), *it)) ++it;
                  else it = args.erase(it);
                }

                if (args.empty())
                {
                  replaced = repl->right();
                }
                else
                {
                  replaced = createQuantifiedFormulaRestr(repl->right(), args);
                }
              }
            }
            else
            {
              ExprSet vars;
              filter(assmQF, bind::IsConst (), inserter(vars, vars.begin()));
              replaced = replaceAll(subgoal, repl->right(), repl->left());

              for (auto it = args.begin(); it != args.end();)
              {
                if (find(vars.begin(), vars.end(), *it) != vars.end())
                {
                  it = args.erase(it);
                }
                else
                {
                  ++it;
                }
              }
              if (!args.empty())
                replaced = createQuantifiedFormulaRestr(replaced, args, false);
            }
          }
          else
          {
            replaced = replaceAll(subgoal, repl, mk<TRUE>(efac));
          }

          if (subgoal != replaced) return replaced;
        }

        if (isImpl) return NULL;

        if (isOpX<EQ>(assmQF))
        {
          matching.clear();

          // if the assumption is equality, the we search for a matching of its LHS
          // (we can try matching the RHS as well, but it will likely give us infinite loops)
          if (findMatchingSubexpr (assmQF->left(), subgoal, args, matching))
          {
            repl = replaceAll(repl, matching);
            return replaceAll(subgoal, repl->left(), repl->right());
          }

          // try vice versa (dangerous since it will introduce repeated rewriting)
          matching.clear();
          if (!fwd && findMatchingSubexpr (assmQF->right(), subgoal, args, matching))
          {
            repl = replaceAll(repl, matching);
            return replaceAll(subgoal, repl->right(), repl->left());
          }
        }

        if ((isOpX<LEQ>(assmQF) && isOpX<LEQ>(subgoal)) ||
            (isOpX<GEQ>(assmQF) && isOpX<GEQ>(subgoal)) ||
            (isOpX<LT>(assmQF) && isOpX<LT>(subgoal)) ||
            (isOpX<GT>(assmQF) && isOpX<GT>(subgoal)))
        {
          if (findMatchingSubexpr (assmQF->left(), subgoal->left(), args, matching))
          {
            for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
            if (u.implies(repl, subgoal)) return mk<TRUE>(efac);
          }
        }

        if (isOpX<ITE>(subgoal))
        {
          if (findMatchingSubexpr (assmQF, subgoal->left(), args, matching))
          {
            for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
            if (u.implies(repl, subgoal->left())) return subgoal->right();
            if (u.implies(repl, mkNeg(subgoal->left()))) return subgoal->last();
          }
        }

        // try finding inconsistencies
        if (fwd)
        {
          ExprMap matching1;
          ExprVector args1;
          filter(subgoal, bind::IsConst (), inserter(args1, args1.begin()));
          if (findMatchingSubexpr (subgoal, assmQF, args1, matching1))
          {
            repl = assmQF;
            for (auto & m : matching1){
              auto it = find(args.begin(), args.end(), m.second);
              if (it != args.end())
              {
                repl = replaceAll(repl, m.second, m.first);
                args.erase(it);
              }
              else
              {
                if (m.second != m.first) return NULL;
              }
            }
            if (args.empty())
            {
              if (!u.isSat(subgoal, repl)) return mk<FALSE>(efac);
              return repl;
            }
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once
        if (!fwd && u.implies(assm, subgoal)) return mk<TRUE>(efac);
        if (fwd && !u.isSat(assm, subgoal)) return mk<FALSE>(efac);

        if (isOpX<EQ>(assm))
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            return res;
          }
        }
        // TODO: proper matching
        if (isOpX<IMPL>(subgoal) && u.implies(subgoal->left(), assm))
        {
          return subgoal->right();
        }
        if (isOpX<ITE>(subgoal))
        {
          if (u.implies(assm, subgoal->left()))
          {
            return subgoal->right();
          }
          if (u.implies(assm, mk<NEG>(subgoal->left())))
          {
            return subgoal->last();
          }
        }

        if (isOpX<OR>(assm) && fwd)
        {
          ExprSet dsjs;
          getDisj(assm, dsjs);
          bool rem = false;
          for (auto it = dsjs.begin(); it != dsjs.end();)
          {
            if (!u.isSat(*it, subgoal))
            {
              rem = true;
              it = dsjs.erase(it);
            }
            else ++it;
          }
          if (rem)
          {
            Expr res = disjoin(dsjs, efac);
            return res;
          }
        }

        ExprSet stores;
        getStores(subgoal, stores);

        if (stores.size() > 0)
        {
          if (isOpX<NEQ>(assm) && contains(subgoal, assm->left()) && contains(subgoal, assm->right()))
          {
            ExprMap substs;
            substs[assm->right()] = assm->left();
            substs[assm->left()] = assm->right();
            for (auto & a : stores)
            {
              if (isOpX<STORE>(a->left()) &&
                  ((a->right() == assm->right() && a->left()->right() == assm->left()) ||
                   (a->right() == assm->left() && a->left()->right() == assm->right())))
              {
                return replaceAll(subgoal, a, replaceAll(a, substs));
              }
            }
          }

          if (isOpX<SELECT>(assm))
          {

            for (auto & a : stores)
            {
              if (assm->left() == a->left() &&
                  assm->right() == a->right() &&
                  isOpX<TRUE>(a->last()))
              {
                return replaceAll(subgoal, a, a->left());
              }
            }
          }

          if (isOpX<NEG>(assm) && isOpX<SELECT>(assm->left()))
          {
            for (auto & a : stores)
            {
              if (assm->left()->left() == a->left() &&
                  assm->left()->right() == a->right() &&
                  isOpX<FALSE>(a->last()))
              {
                return replaceAll(subgoal, a, a->left());
              }
            }
          }
        }
      }
      // if nothing helped, return NULL -- it will be used for backtracking
      return NULL;
    }

    // this method is used when a strategy is specified from the command line
    bool tryStrategy(Expr subgoal, vector<int>& strat)
    {
      Expr subgoal_copy = subgoal;
      for (int i : strat)
      {
        assert (i < assumptions.size());
        subgoal_copy = useAssumption(subgoal_copy, assumptions[i]);
        if (subgoal_copy == NULL || subgoal_copy == subgoal) break;

        if (u.isEquiv(subgoal_copy, mk<TRUE>(efac))) return true;
      }
      return false;
    }

    bool handleExists(Expr subgoal)
    {
      if (verbose) outs () << string(sp, ' ')  << "existential quantifies are currently not supported\n";
      return false;
      // to be done
    }

    // this recursive method performs a naive search for a strategy
    bool rewriteAssumptions(Expr subgoal)
    {
      if (u.isEquiv(subgoal, mk<TRUE>(efac)))
      {
        if (verbose) outs () << string(sp, ' ') << "rewriting done\n";
        return true;
      }

      // check recursion depth
      if (rewriteSequence.size() >= maxDepth)
      {
        if (verbose) outs() << string(sp, ' ') << "Maximum recursion depth reached\n";
        return false;
      }

      // check consecutive applications of the same assumption
      if (rewriteSequence.size() > maxGrow)
      {
        bool incr = true;
        for (int i = 1; i < maxGrow + 1; i++)
        {
          if (treeSize(rewriteHistory[rewriteHistory.size() - i]) < treeSize(rewriteHistory[rewriteHistory.size() - i - 1]))
          {
            incr = false;
            break;
          }
        }

        if (incr)
        {
          if (verbose) outs() << string(sp, ' ') << "sequence of rewrites only grows\n";
          return false;
        }
      }

      auto assumptionsTmp = assumptions;
      bool toRem = false;
      if (isOpX<IMPL>(subgoal))
      {
        uniquePushConj(subgoal->left(), assumptions);
        if (assumptions.size() != assumptionsTmp.size())
        {
          toRem = true;
          if (mergeAssumptions())
          {
            assumptions = assumptionsTmp;
            return true;
          }
          printAssumptions();
        }
        subgoal = subgoal->right();
        if (verbose) outs() << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";
      }

      if (isOpX<EXISTS>(subgoal))
      {
        return handleExists(subgoal);
      }

      subgoal = liftITEs(subgoal);
      subgoal = u.simplifyITE(subgoal);
      subgoal = simplifyExists(subgoal);
      subgoal = simplifyArr(subgoal);
      subgoal = simplifyArithm(subgoal);
      subgoal = simplifyBool(subgoal);

      ExprSet subSub;
      if (isOpX<ITE>(subgoal))
      {
        subSub.insert(mk<IMPL>(subgoal->left(), subgoal->right()));
        subSub.insert(mk<IMPL>(mkNeg(subgoal->left()), subgoal->last()));
      }
      else
      {
        getConj(subgoal, subSub);
      }

      if (subSub.size() > 1)
      {
        bool res = true;
        int part = 1;
        for (auto & s : subSub)
        {
          if (verbose)
          {
            if (verbose) outs () << string(sp, ' ') << "proceed with (part " << part << "/" << subSub.size()<< "): " << *s << "\n";
            part++;
          }

          auto rewriteHistoryTmp = rewriteHistory;
          auto rewriteSequenceTmp = rewriteSequence;
          auto assumptionsTmp = assumptions;

          if (verbose) outs() << string(sp, ' ') << "{\n";
          sp += 2;
          res &= rewriteAssumptions(s);
          sp -= 2;
          if (verbose) outs() << string(sp, ' ') << "}\n";

          rewriteHistory = rewriteHistoryTmp;
          rewriteSequence = rewriteSequenceTmp;
          assumptions = assumptionsTmp;
          if (!res)
          {
            if (verbose) outs() << string(sp, ' ') << "failed to proceed\n";
            break;
          }
        }
        if (verbose) if (res) outs () << string(sp, ' ')  << "rewriting done\n";
        return res;
      }

      // here, assume subSub.size() == 1
      // thus, subgoal == *subSub.begin()

      // quick syntactic check first:
      for (int i = 0; i < assumptions.size(); i++)
      {
        if (assumptions[i] == subgoal)
        {
          if (toRem) assumptions = assumptionsTmp;
          if (verbose) outs () << string(sp, ' ') << "rewriting [" << i << "] done\n";
          return true;
        }
      }

      map<int, Expr> allAttempts;

      for (int i = 0; i < assumptions.size(); i++)
      {
        Expr a = assumptions[i];
        Expr res = useAssumption(subgoal, a);
        if (res != NULL)
        {
          if (u.isTrue(res)) return true;
          allAttempts[i] = res;
        }
      }

      vector<int> orderedAttempts1;
      vector<int> orderedAttempts2;
      // identifying an order for rewrites
      for (auto & a : allAttempts)
      {
        bool placed = false;

        bool sw;
        if (earlySplit == 1) sw = treeSize(subgoal) >= treeSize(a.second);
        else sw = true;

        if (sw)
        {
          for (int i = 0; i < orderedAttempts1.size(); i++)
          {
            if (treeSize(allAttempts[orderedAttempts1[i]]) > treeSize(a.second))
            {
              orderedAttempts1.insert(orderedAttempts1.begin() + i, a.first);
              placed = true;
              break;
            }
          }
          if (!placed) orderedAttempts1.push_back(a.first);
        }
        else
        {
          for (int i = 0; i < orderedAttempts2.size(); i++)
          {
            if (treeSize(allAttempts[orderedAttempts2[i]]) > treeSize(a.second))
            {
              orderedAttempts2.insert(orderedAttempts2.begin() + i, a.first);
              placed = true;
              break;
            }
          }
          if (!placed) orderedAttempts2.push_back(a.first);
        }
      }

      // first, try easier rewrites
      if (tryRewriting(orderedAttempts1, allAttempts, subgoal))
      {
        if (toRem) assumptions = assumptionsTmp;
        return true;
      }

      if (splitDisjAssumptions(subgoal)) return true;

      // second, try harder rewrites
      if (tryRewriting(orderedAttempts2, allAttempts, subgoal))
      {
        if (toRem) assumptions = assumptionsTmp;
        return true;
      }

      bool res = false;

      if (isOpX<OR>(subgoal)) res = splitByGoal(subgoal);
//      if (!res) res = proveByContradiction(subgoal);
//      if (!res) res = similarityHeuristic(subgoal);
      if (toRem) assumptions = assumptionsTmp;

      return res;
    }

    // try rewriting in a particular order
    bool tryRewriting(vector<int>& orderedAttempts, map<int, Expr>& allAttempts, Expr subgoal)
    {
      for (int i : orderedAttempts)
      {
        Expr res = allAttempts[i];
        if (verbose) outs() << string(sp, ' ') << "rewritten [" << i << "]: " << *res << "\n";

        // save history
        rewriteHistory.push_back(res);
        rewriteSequence.push_back(i);

        if (rewriteAssumptions(res))
        {
          if (verbose) if (res) outs () << string(sp, ' ')  << "rewriting done\n";
          return true;
        }
        else
        {
          // failed attempt, remove history
          rewriteHistory.pop_back();
          rewriteSequence.pop_back();
        }
        
        // backtrack:
        if (verbose) outs () << string(sp, ' ') << "backtrack to: " << *subgoal << "\n";
      }
      return false;
    }

    bool proveByContradiction (Expr subgoal)
    {
      auto assumptionsTmp = assumptions;
      uniquePushConj(mkNeg(subgoal), assumptions);
      bool res = false;
      if (mergeAssumptions(1))
      {
        res = true;
        if (verbose) outs () << string(sp, ' ') << "proven by contradiction\n";
      }
      assumptions = assumptionsTmp;
      return res;
    }

    bool splitByGoal (Expr subgoal)
    {
      // heuristically pick a split (currently, one one predicate)
      ExprSet dsjs;
      getDisj(subgoal, dsjs);
      if (dsjs.size() < 2) return false;

      auto spl = dsjs.end();
      for (auto it = dsjs.begin(); it != dsjs.end(); ++it)
      {
        for (auto & a : assumptions)
        {
          if (contains (a, *it))
          {
            if (isOp<ComparissonOp>(*it)) spl = it;  // try to find a comparisson
            if (*spl == NULL) spl = it;              // if none, find any
          }
        }
      }
      if (spl == dsjs.end()) spl = dsjs.begin();
      if (verbose) outs() << string(sp, ' ') << "deciding: " << **spl << "\n";

      auto rewriteHistoryTmp = rewriteHistory;
      auto rewriteSequenceTmp = rewriteSequence;
      auto assumptionsTmp = assumptions;

      uniquePushConj(mkNeg(*spl), assumptions);
      if (mergeAssumptions())
      {
        assumptions = assumptionsTmp;
        return true;
      }
      printAssumptions();

      dsjs.erase(spl);
      subgoal = disjoin(dsjs, efac);
      if (verbose) outs() << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";

      if (verbose) outs () << string(sp, ' ') << "{\n";
      sp += 2;
      bool res = rewriteAssumptions(subgoal);
      sp -= 2;
      if (verbose) outs () << string(sp, ' ') << "}\n";

      rewriteHistory = rewriteHistoryTmp;
      rewriteSequence = rewriteSequenceTmp;
      assumptions = assumptionsTmp;
      if (res)
      {
        if (verbose) outs () << string(sp, ' ') << "succeeded\n";
        return true;
      }

      return false;
    }

    // potentially useful heuristic
    bool similarityHeuristic (Expr subgoal)
    {
      // heuristically pick a split: first, using disjunctions
      ExprSet cands;
      for (auto & a : assumptions)
      {
        if (isOpX<OR>(a))
        {
          ExprSet dsjs;
          getDisj(a, dsjs);
          if (dsjs.size() < 2) continue;
          auto it = dsjs.begin();
          for (; it != dsjs.end(); ++it)
          {
            if (*it == subgoal)
            {
              it = dsjs.erase(it);
              cands.insert(disjoin(dsjs, efac));
              break;
            }
          }
        }
      }
      if (cands.empty())      // then, based on matching
      {
        ExprVector args;
        filter(subgoal, bind::IsConst (), inserter(args, args.begin()));
        for (auto & a : assumptions)
        {
          if (isOpX<FORALL>(a)) continue;

          ExprMap matching;
          if (findMatching (subgoal, a, args, matching))
          {
            ExprSet eqs;
            for (auto & m : matching)
              if (m.first != m.second)
                eqs.insert(mk<EQ>(m.first, m.second));
            cands.insert(mkNeg(conjoin(eqs, efac)));
          }
        }
        if (cands.empty()) return false;
      }

      bool changed = false;
      for (auto & c : cands)
      {
        bool redund = false;
        for (auto & a : assumptions)
        {
          if (isOpX<FORALL>(a)) continue;
          if (u.implies(a, c))
          {
            redund = true;
            break;
          }
        }
        if (redund) continue;
        uniquePushConj(c, assumptions);
        changed = true;
      }
      if (!changed) return false;

      if (mergeAssumptions())
      {
        return true;
      }
      printAssumptions();

      if (verbose) outs () << string(sp, ' ') << "current subgoal: " << *subgoal << "\n";
      if (verbose) outs () << string(sp, ' ') << "{\n";
      sp += 2;
      bool res = rewriteAssumptions(subgoal);
      sp -= 2;
      if (verbose) outs () << string(sp, ' ') << "}\n";

      return res;
    }

    bool splitDisjAssumptions (Expr subgoal)
    {
      // more like a brute force splitting
      set<ExprSet> cands;
      map<ExprSet, Expr> origAssms;
      for (auto it = assumptions.begin(); it != assumptions.end(); )
      {
        Expr a = *it;
        if (find (blockedAssms.begin(), blockedAssms.end(), *it) != blockedAssms.end())
        {
          it = assumptions.erase(it);
          continue;
        }
        if (isOpX<ITE>(a))
        {
          a = mk<OR>(mk<AND>(a->left(), a->right()),
                     mk<AND>(mkNeg(a->left()), a->last()));
        }
        a = simplifyBool(simplifyArr(a));
        if (isOpX<OR>(a))
        {
          ExprSet dsjs;
          getDisj(a, dsjs);
          if (dsjs.size() < 2) continue;
          cands.insert(dsjs);
          origAssms[dsjs] = *it;
        }
        ++it;
      }

      if (cands.empty()) return false;
      ExprSet spl = *cands.begin();

      if (spl.empty()) return false;

      blockedAssms.push_back(origAssms[spl]);

      int part = 1;
      bool res = true;

      auto assumptionsTmp = assumptions;
      auto rewriteHistoryTmp = rewriteHistory;
      auto rewriteSequenceTmp = rewriteSequence;

      for (auto & s : spl)
      {
        if (verbose) outs () << string(sp, ' ') << "split for (part " << part << "/"
            << spl.size()<< "): " << *s << "\n" << string(sp, ' ') << "{\n";
        sp += 2;

        uniquePushConj(s, assumptions);
        if (mergeAssumptions())
        {
          assumptions = assumptionsTmp;
          sp -= 2;
          if (verbose) outs () << string(sp, ' ') << "}\n";
          continue;
        }
        for (auto it = assumptions.begin(); it != assumptions.end(); ++it)
        {
          if (origAssms[spl] == *it)
          {
            assumptions.erase(it);
            break;
          }
        }
        printAssumptions();

        part++;

        res = rewriteAssumptions(subgoal);
        sp -= 2;
        if (verbose) outs () << string(sp, ' ') << "}\n";

        rewriteHistory = rewriteHistoryTmp;
        rewriteSequence = rewriteSequenceTmp;
        assumptions = assumptionsTmp;
        if (!res) break;
      }

      blockedAssms.pop_back();
      if (res)
      {
        if (verbose) outs () << string(sp, ' ') << "splitting succeeded\n";
        return true;
      }
      else
      {
        if (verbose) outs () << string(sp, ' ') << "unable to succeed\n";
        return false;
      }
    }

    // preprocessing of the main goal:
    //   - classify constructors for all ADTs that appear in the goal
    //   - replace all non-inductive ADTs
    void unfoldGoal()
    {
      ExprVector goalArgs;
      Expr unfoldedGoalQF = goal->last();
      bool toRebuild = false;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        for (auto & a : constructors)
        {
          if (a->last() == type)
          {
            bool ind = false;
            for (int i = 0; i < a->arity() - 1; i++)
            {
              if (a->last() == a->arg(i))
              {
                ind = true;
                if (indConstructors[type] != NULL && indConstructors[type] != a)
                {
                  outs () << "Several inductive constructors are not supported\n";
                  exit(0);
                }
                indConstructors[type] = a;
              }
            }
            if (!ind)
            {
              if (baseConstructors[type] != NULL && baseConstructors[type] != a)
              {
                outs () << "Several base constructors are not supported\n";
                exit(0);
              }
              baseConstructors[type] = a;
            }
          }
        }
        if (baseConstructors[type] != NULL && indConstructors[type] == NULL)
        {
          toRebuild = true;
          ExprVector args;
          args.push_back(baseConstructors[type]);
          for (int i = 1; i < baseConstructors[type]->arity() - 1; i++)
          {
            // TODO: make sure the name is unique
            Expr s = bind::mkConst(mkTerm<string>
                         ("_b_" + to_string(goalArgs.size()), efac),
                         baseConstructors[type]->arg(i));
            goalArgs.push_back(s->last());
            args.push_back(s);
          }
          Expr newApp = mknary<FAPP>(args);
          unfoldedGoalQF = replaceAll(unfoldedGoalQF, bind::fapp(goal->arg(i)), newApp);
        }
        else
        {
          goalArgs.push_back(goal->arg(i));
        }
      }

      if (toRebuild)
      {
        goalArgs.push_back(unfoldedGoalQF);
        goal = mknary<FORALL>(goalArgs);

        // continue recursively, because newly introduced vars may again need unfolding
        unfoldGoal();
      }
    }

    // this method can be (but not used currently) to add symmetric assumptions
    // and to enable searching for RHS of assumptions
    void insertSymmetricAssumption(Expr assm)
    {
      if (isOpX<EQ>(assm))
      {
        assumptions.push_back(mk<EQ>(assm->right(), assm->left()));
      }
      else if (isOpX<FORALL>(assm) && isOpX<EQ>(assm->last()))
      {
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(assm->arg(i));
        args.push_back(mk<EQ>(assm->last()->right(), assm->last()->left()));
        assumptions.push_back(mknary<FORALL>(args));
      }
    }

    void printAssumptions()
    {
      if (!verbose) return;
      outs () << string(sp, ' ') << "{\n";
      outs () << string(sp+2, ' ') << string(20, '=') << "\n";
      for (int i = 0; i < assumptions.size(); i++)
      {
        outs () << string(sp+2, ' ') << "| Assumptions [" << i << "]: "
                << *assumptions[i] << "\n";
      }
      outs () << string(sp+2, ' ') << string(20, '=') << "\n";
      outs () << string(sp, ' ') << "}\n";
    }

    bool induction(int num, vector<int>& basenums, vector<int>& indnums)
    {
      assert(num < goal->arity() - 1);
      Expr typeDecl = goal->arg(num);
      Expr type = goal->arg(num)->last();

      Expr baseConstructor = baseConstructors[type];
      Expr indConstructor = indConstructors[type];

      // instantiate every quantified variable (except the inductive one) in the goal
      Expr goalQF = goal->last();
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (i == num) continue;
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_v_" + to_string(glob_ind), efac), goal->arg(i)->last());
        glob_ind++;
        goalQF = replaceAll(goalQF, bind::fapp(goal->arg(i)), s);
      }

      // prove the base case
      Expr baseSubgoal = replaceAll(goalQF, typeDecl, baseConstructor);
      ExprVector assumptionsTmp = assumptions;
      if (isOpX<IMPL>(baseSubgoal))
      {
        assumptions.push_back(baseSubgoal->left());
        baseSubgoal = baseSubgoal->right();
      }

      if (verbose) outs() << "\nBase case:       " << *baseSubgoal << "\n{\n";
      bool baseres = false;
      if (mergeAssumptions())
      {
        if (verbose) outs() << "  proven trivially\n";
        baseres = true;
        assumptions = assumptionsTmp;
      }
      else
      {
        splitAssumptions();
        printAssumptions();

        rewriteHistory.clear();
        rewriteSequence.clear();

        baseres = basenums.empty() ?
                rewriteAssumptions(baseSubgoal) :
                tryStrategy(baseSubgoal, basenums);
      }

      if (verbose) outs () << "}\n";
      if (!baseres)
      {
        ExprVector newArgs;
        for (int i = 0; i < goal->arity() - 1; i++)
        {
          if (i == num) continue;
          newArgs.push_back(goal->arg(i));
        }
        if (newArgs.size() > 0)
        {
          if (verbose) outs () << "\nProceeding to nested induction\n";
          newArgs.push_back(replaceAll(goal->last(), typeDecl, baseConstructor));
          Expr newGoal = mknary<FORALL>(newArgs);
          ADTSolver sol (newGoal, assumptions, constructors, maxDepth, maxGrow, earlySplit);
          if (!sol.solve (basenums, indnums)) return false;
          if (verbose) outs () << "\nReturning to the outer induction\n\n";
        }
        else
        {
          return false;
        }
      }

      if (!assumptionsTmp.empty()) assumptions = assumptionsTmp;

      // generate inductive hypotheses
      ExprVector args;
      ExprVector indHypotheses;
      bool allQF = true;
      for (int i = 1; i < indConstructor->arity() - 1; i++)
      {
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), indConstructor->arg(i));
        glob_ind++;
        args.push_back(s);

        if (type == indConstructor->arg(i)) // type check
        {
          ExprVector argsIH;
          for (int j = 0; j < goal->arity() - 1; j++)
          {
            if (j != num) argsIH.push_back(goal->arg(j));
          }
          argsIH.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), s));
          if (argsIH.size() == 1)
          {
            indHypotheses.push_back(argsIH.back());
          }
          else
          {
            allQF = false;
            indHypotheses.push_back(mknary<FORALL>(argsIH));
          }
        }
      }
      for (auto & a : indHypotheses)
      {
        assumptions.push_back(a);
        // always add symmetric IH?
        insertSymmetricAssumption(a);
      }
      // for simplicity, add conjunction of hypotheses as a single hypothesis
      // should be removed in the future (when all QF-assumptions are used at the same time)
      if (indHypotheses.size() > 1 && allQF) assumptions.push_back(conjoin(indHypotheses, efac));

      // prove the inductive step
      Expr indConsApp = bind::fapp(indConstructor, args);
      Expr indSubgoal = replaceAll(goalQF, bind::fapp(typeDecl), indConsApp);

      if (isOpX<IMPL>(indSubgoal))
      {
        assumptions.push_back(indSubgoal->left());
        indSubgoal = indSubgoal->right();
      }

      if (mergeAssumptions()) return true;

      splitAssumptions();
      if (verbose) outs() << "Inductive step:  " << * indSubgoal << "\n{\n";
      printAssumptions();

      rewriteHistory.clear();
      rewriteSequence.clear();

      bool indres = indnums.empty() ?
               rewriteAssumptions(indSubgoal) :
               tryStrategy(indSubgoal, indnums);
      if (verbose)  outs () << "}\n";
      if (indres) return true;

      ExprVector newArgs;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (i == num) continue;
        newArgs.push_back(goal->arg(i));
      }

      if (newArgs.size() > 0)
      {
        if (verbose) outs () << "\nProceeding to nested induction\n";
        newArgs.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), indConsApp));
        Expr newGoal = mknary<FORALL>(newArgs);
        ADTSolver sol (newGoal, assumptions, constructors, maxDepth, maxGrow, earlySplit);
        if (sol.solve (basenums, indnums)) return true;
        if (verbose) outs () << "Nested induction unsuccessful\n\n";
      }

//      // last resort so far
      return doCaseSplitting(indSubgoal);
      return false;
    }

    bool doCaseSplitting(Expr goal)
    {
      for (int i = 0; i < assumptions.size(); i++)
      {
        Expr pre;
        auto a = assumptions[i];
        if (isOpX<FORALL>(a) && isOpX<IMPL>(a->last()))
        {
          ExprSet pres;
          getConj(a->last()->left(), pres);

          ExprVector varz;
          for (int i = 0; i < a->arity() - 1; i++) varz.push_back(bind::fapp(a->arg(i)));

          for (auto & p : pres)
          {
            if (emptyIntersect(p, varz))
            {
              pre = p;
              break;
            }
          }
        }

        if (isOpX<IMPL>(a)) pre = a->left();

        if (pre != NULL)
        {
          // GF: to support if isOpX<EQ>(pre) = true.
          Expr d = destructDiseq(pre);
          if (d != NULL)
          {
            assert(isOpX<EQ>(d));
            printAssumptions();
            if (verbose) outs () << "case splitting for " << *d->left() << ":\n";
            if (verbose) outs () << "  case " << *d << "\n{\n";
            auto assumptionsTmp = assumptions;
            auto rewriteHistoryTmp = rewriteHistory;
            auto rewriteSequenceTmp = rewriteSequence;

            for (int j = 0; j < assumptions.size(); j++)
            {
              assumptions[j] = simplifyBool(replaceAll(assumptions[j], pre, mk<TRUE>(efac)));
              assumptions[j] = replaceAll(assumptions[j], d->left(), d->right());
            }

            mergeAssumptions(1);
            printAssumptions();
            bool partiallyDone = rewriteAssumptions(replaceAll(goal, d->left(), d->right()));

            assumptions = assumptionsTmp;
            rewriteHistory = rewriteHistoryTmp;
            rewriteSequence = rewriteSequenceTmp;

            if (!partiallyDone) continue;
            if (verbose) outs() << "successful\n}\n";

            pre = mkNeg(pre);
            assert(isOpX<EQ>(pre) && pre->left() == d->left());
            if (verbose) outs () << "  case " << *pre << "\n{\n";

            for (int j = 0; j < assumptions.size(); j++)
            {
              assumptions[j] = simplifyBool(replaceAll(assumptions[j], pre, mk<TRUE>(efac)));
              assumptions[j] = replaceAll(assumptions[j], pre->left(), pre->right());
            }
            mergeAssumptions(1);
            printAssumptions();
            bool done = rewriteAssumptions(replaceAll(goal, pre->left(), pre->right()));

            assumptions = assumptionsTmp;
            rewriteHistory = rewriteHistoryTmp;
            rewriteSequence = rewriteSequenceTmp;

            if (done)
            {
              if (verbose) outs() << "successful\n}\n";
              return true;
            }
          }
        }
      }
      return false;
    }

    Expr destructDiseq(Expr e)
    {
      if (isOpX<NEG>(e))
      {
        e = mkNeg(e->left());
      }
      if (isOp<NEQ>(e))
      {
        Expr ty;
        if (bind::isAdtConst(e->left()))
        {
          ty = e->left()->last()->last();
        }
        else if (bind::isAdtConst(e->right()))
        {
          ty = e->right()->last()->last();
        }

        if (ty == NULL) return NULL;

        Expr t;
        if (e->right()->last() == baseConstructors[ty])
        {
          t = e->left();
        }
        else if (e->left()->last() == baseConstructors[ty])
        {
          t = e->right();
        }

        Expr indConstructor = indConstructors[ty];
        ExprVector args;
        for (int i = 1; i < indConstructor->arity() - 1; i++)
        {
          // TODO: make sure the name is unique
          Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(glob_ind), efac), indConstructor->arg(i));
          glob_ind++;
          args.push_back(s);
        }
        Expr indConsApp = bind::fapp(indConstructor, args);
        return mk<EQ>(t, indConsApp);
      }

      return NULL;
    }

    bool solveNoind(int rounds = 2)
    {
      auto assumptionsTmp = assumptions;
      mergeAssumptions(rounds);
      printAssumptions();
      if (verbose) outs () << "=====\n" << *goal << "\n\n\n";
      bool res = rewriteAssumptions(goal);
      if (res)
      {
        if (verbose) outs () << "\nProved\n";
      }
      else
      {
        // revert and try induction:
        assumptions = assumptionsTmp;
        ExprSet qFreeAssms;
        for (auto it = assumptions.begin(); it != assumptions.end(); )
        {
          if (!isOpX<FORALL>(*it))
          {
            if (isOpX<NEQ>(*it) || isOpX<FAPP>(*it) || isOpX<NEG>(*it) || isOpX<SELECT>(*it)) // super big hack
              qFreeAssms.insert(*it);

            it = assumptions.erase(it);
          }
          else ++it;
        }

        if (verbose) outs () << "\nProving by induction\n";
        goal = createQuantifiedFormula(mk<IMPL>(conjoin(qFreeAssms, efac), goal), constructors);

        vector<int> basenums, indnums; // dummies
        res = solve(basenums, indnums);
      }
      return res;
    }

    bool solve(vector<int>& basenums, vector<int>& indnums)
    {
      unfoldGoal();
      rewriteHistory.push_back(goal);
      for (int i = 0; i < 5; i++)
      {
        if (simplifyGoal())
        {
          if (verbose) outs () << "Trivially Proved\n";
          return true;
        }
      }

      // simple heuristic: if the result of every rewriting made the goal larger, we rollback
      bool toRollback = true;
      for (int i = 1; i < rewriteHistory.size(); i++)
        toRollback = toRollback &&
            (treeSize(rewriteHistory[i-1]) < treeSize(rewriteHistory[i]));

      if (toRollback) goal = rewriteHistory[0];

      if (verbose) outs () << "Simplified goal: " << *goal << "\n\n";

      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        if (baseConstructors[type] != NULL && indConstructors[type] != NULL)
        {
          if (induction(i, basenums, indnums))
          {
            if (verbose) outs () << "\nProved\n";
            return true;
          }
          else
          {
            if (verbose) outs () << "\nFailed\n";
            return false;
          }
        }
      }
      return false;
    }
  };

  static inline void getNums(vector<int>& nums, char * str)
  {
    if (str == NULL) return;
    int len = strlen(str);
    char* pch = strchr(str, ',');
    int pos1 = 0;
    int pos2 = 0;
    while (pch != NULL)
    {
      pos2 = pch - str;
      char* substr = (char*)malloc(pos2 - pos1);
      strncpy(substr, str + pos1, pos2 - pos1);
      nums.push_back(atoi(substr));
      pch = strchr(pch + 1, ',');
      pos1 = pos2 + 1;
    }
    if (pos1 == len) return;
    char* substr = (char*)malloc(len - pos1);
    strncpy(substr, str + pos1, len - pos1);
    nums.push_back(atoi(substr));
  }

  void adtSolve(EZ3& z3, Expr s, char* basecheck, char *indcheck, int maxDepth,
                int maxGrow, int mergingIts, int earlySplit, bool verbose)
  {
    vector<int> basenums;
    vector<int> indnums;
    getNums(basenums, basecheck);
    getNums(indnums, indcheck);
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(regularizeQF(a));

    ExprVector assumptions;
    Expr goal;

    ExprSet cnjs;
    getConj(s, cnjs);
    for (auto & c : cnjs)
    {
      if (isOpX<NEG>(c))
      {
        if (goal != NULL) assert (0 && "cannot identify goal (two asserts with negged formulas)");
        goal = regularizeQF(c->left());
      }
      else
      {
        assumptions.push_back(regularizeQF(c));
      }
    }

    if (goal == NULL)
    {
      outs () << "Unable to parse the query\n";
      return;
    }

    ADTSolver sol (goal, assumptions, constructors, maxDepth, maxGrow, mergingIts, earlySplit, verbose);
    if (isOpX<FORALL>(goal)) sol.solve(basenums, indnums);
    else sol.solveNoind();
  }
}

#endif
