#ifndef AEVALSOLVER__HPP__
#define AEVALSOLVER__HPP__
#include <assert.h>

#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"
#include "ae/MBPUtils.hpp"
#include "ae/SetHash.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  /** engine to solve validity of \forall-\exists formulas and synthesize Skolem relation */
  class AeValSolver {
  private:

    Expr s;
    Expr t;
    ExprSet v; // existentially quantified vars
    ExprSet sVars; // all vars (stVars U v)
    ExprSet stVars; // universally quantified vars

    ExprMap modelInvalid; // key: variable | value: assignment in model
    ExprMap separateSkols;

    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;

    unsigned partitioning_size;
    ExprVector projections;
    ExprVector instantiations;
    vector<ExprMap> skolMaps;
    vector<ExprMap> someEvals;
    ExprSet sensitiveVars; // for compaction
    set<int> bestIndexes; // for compaction
    unordered_set<set<int>> doneIndexes; // for compaction
    map<Expr, ExprVector> skolemConstraints;
    bool skol; // whether or not to produce a skolem (function)
    int debug;
    unsigned fresh_var_ind;

  public:

    AeValSolver (Expr _s, Expr _t, ExprSet &_v, int _debug, bool _skol) :
      s(_s), t(_t), v(_v),
      efac(s->getFactory()),
      z3(efac),
      smt (z3),
      u(efac),
      fresh_var_ind(0),
      partitioning_size(0),
      skol(_skol),
      debug(_debug)
    {
      filter (boolop::land(s,t), bind::IsConst (), inserter (stVars, stVars.begin()));
      sVars = stVars;
      minusSets(stVars, v);
    }

    void splitDefs (ExprMap &m1, ExprMap &m2, int curCnt = 0)
    {
      ExprMap m3;
      ExprMap m4;
      for (auto & a : m1)
      {
        if (a.second == NULL) continue;
        if (emptyIntersect(a.second, v))
        {
          m3.insert(a);
        }
        else
        {
          m4.insert(a);
        }
      }
      if (m3.size() == curCnt)
      {
        m2 = m4;
        return;
      }

      for (auto & a : m3)
      {
        for (auto & b : m1)
        {
          if (b.second == NULL) continue;
          if (a.first != b.first)
          {
            b.second = replaceAll(b.second, a.first, a.second);
          }
        }
      }
      splitDefs(m1, m2, m3.size());
    }

    /**
     * Decide validity of \forall s => \exists v . t
     */
    boost::tribool solve()
    {
      smt.reset();
      smt.assertExpr(s);

      if(!smt.solve())
      {
        if(debug)
          outs() << "The S-part is unsatisfiable;\nFormula is trivially valid\n";
        return false;
      }
      else
      {
        ZSolver<EZ3>::Model m = smt.getModel();

        for(auto &e : sVars)
          // keep a model in case the formula is invalid
          modelInvalid[e] = m.eval(e);
      }

      if(v.size() == 0)
      {
        smt.assertExpr(boolop::lneg(t));
        boost::tribool res = smt.solve();
        return res;
      }

      smt.push();
      smt.assertExpr(t);

      boost::tribool res = true;

      while(smt.solve())
      {
        outs().flush();

        ZSolver<EZ3>::Model m = smt.getModel();

        getMBPandSkolem(m);
        smt.pop();
        smt.assertExpr(boolop::lneg(projections.back()));
        if(!smt.solve())
        {
          res = false;
          break;
        }
        else
        {
          // keep a model in case the formula is invalid
          m = smt.getModel();
          for(auto &e : sVars)
            modelInvalid[e] = m.eval(e);
        }

        smt.push();
        smt.assertExpr(t);
      }
      return res;
    }

    /**
     * Extract MBP and local Skolem
     */
    void getMBPandSkolem(ZSolver<EZ3>::Model &m)
    {
      Expr pr = t;
      ExprMap substsMap;
      ExprMap modelMap;
      for(auto &exp : v)
      {
        MBPUtils mbpu(exp, m, u);
        ExprSet lits;
        u.getTrueLiterals(pr, m, lits, true);
        pr = simplifyArithm(mbpu.mixQE(conjoin(lits, efac), debug));
        if(m.eval(exp) != exp)
          modelMap[exp] = mk<EQ>(exp, m.eval(exp));

        if(debug >= 2)
        {
          outs() << "\nmodel " << partitioning_size << ":\n";
          for(auto &exp : stVars)
          {
            if(exp != m.eval(exp))
            {
              outs() << "[" << *exp << "=" << *m.eval(exp) << "],";
            }
          }
          outs() << "\n";
          outs() << "model map: \n";
          for(auto &m : modelMap)
          {
            pprint(m.second, 2);
          }
          outs() << "projection:\n";
          pprint(pr, 2);
        }

        if(debug)
          MBPSanityCheck(m, pr);

        for(auto it = lits.begin(); it != lits.end();)
        {
          if(contains(*it, exp))
            ++it;
          else
            it = lits.erase(it);
        }
        substsMap[exp] = conjoin(lits, efac);
      }

      if(debug)
        assert(emptyIntersect(pr, v));

      someEvals.push_back(modelMap);
      skolMaps.push_back(substsMap);
      projections.push_back(pr);
      partitioning_size++;
    }

    void MBPSanityCheck(ZSolver<EZ3>::Model &m, Expr &pr)
    {
      assert(isOpX<TRUE>(m.eval(pr)));
      ExprVector args;
      for(auto temp : v)
        args.push_back(temp->last());
      args.push_back(t);
      boost::tribool impl = u.implies(pr, mknary<EXISTS>(args));
      tribool_assert(impl);
    };

    void lastSanityCheck()
    {
      ExprVector args;
      for(auto temp : v)
        args.push_back(temp->last());
      args.push_back(mk<IMPL>(s, t));
      Expr sImpT = mknary<EXISTS>(args);
      Expr disjProj = mk<IMPL>(s, disjoin(projections, efac));
      boost::tribool impl = u.implies(disjProj, sImpT);
      tribool_assert(impl);
      impl = u.implies(sImpT, disjProj);
      tribool_assert(impl);
    }

    /**
     * Valid Subset of S (if overall AE-formula is invalid)
     */
    Expr getValidSubset(bool compact)
    {
      if (partitioning_size == 0){
        if (debug) outs() << "WARNING: Trivial valid subset (equal to False) due to 0 iterations\n";
        return mk<FALSE>(efac);
      }

      Expr prs;
      if (compact)
      {
        ExprSet all;
        vector<ExprSet> pprs;

        for (auto & a : projections)
        {
          ExprSet tmp;
          getConj(a, tmp);
          pprs.push_back(tmp);
          all.insert(tmp.begin(), tmp.end());
        }

        ExprSet common;

        for (auto & a : all)
        {
          bool everywhere = true;
          vector<ExprSet> pprsTmp = pprs;
          for (auto & p : pprsTmp)
          {
            bool found = false;
            for (auto it = p.begin(); it != p.end(); ++it)
            {
              if (*it == a) {
                found = true;
                p.erase(it);
                break;
              }
            }
            if (!found)
            {
              everywhere = false;
              break;
            }
          }
          if (everywhere)
          {
            pprs = pprsTmp;
            common.insert(a);
          }
        }

        ExprSet cnjs;
        for (auto & p : pprs) cnjs.insert(conjoin(p, efac));

        if (!cnjs.empty()) common.insert(simplifyBool(disjoin(cnjs, efac)));
        prs = conjoin(common, efac);
      }
      else
      {
        prs = disjoin(projections, efac);
      }
      if (isOpX<TRUE>(s)) return prs;
      return mk<AND>(s, prs);
    }

    /**
     * Model of S /\ \neg T (if AE-formula is invalid)
     */
    void printModelNeg(ostream& out)
    {
      out << "(model\n";
      Expr witn = mk<IMPL>(s, t);
      for (auto &var : sVars){
        Expr assnmt = var == modelInvalid[var] ? getDefaultAssignment(var) : modelInvalid[var];
        if (debug)
          witn = replaceAll(witn, var, assnmt);

        out << "  (define-fun " << *var << " () " <<
          (bind::isBoolConst(var) ? "Bool" : (bind::isIntConst(var) ? "Int" : "Real"))
                << "\n    " << *assnmt << ")\n";
      }
      out << ")\n";

      if (debug){
        outs () << "Sanity check [model]: " << (bool)u.isFalse(witn) << "\n";
      }
    }

    /**
     * Self explanatory
     */
    void getSymbolicMax(ExprSet& vec, Expr& curMax, bool isInt)
    {
      if (vec.size() == 0) return;
      ExprVector replFrom;
      ExprVector replTo;
      curMax = *vec.begin();
      if (vec.size() == 1) return;
      for (auto it = vec.begin(); ++it != vec.end(); ){
        auto &a = *it;
        if (u.isEquiv(mk<LT>(curMax, a), mk<TRUE>(efac))){
          curMax = a;
        } else if (u.isEquiv(mk<LT>(curMax, a), mk<FALSE>(efac))){
          //  curMax is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);

          Expr varName = mkTerm ("_aeval_tmp_max_" + ind, efac);
          Expr var = isInt ? bind::intConst(varName) : bind::realConst(varName);

          replFrom.push_back(var);
          replTo.push_back(mk<ITE>(mk<LT>(curMax, a), a, curMax));

          curMax = var;
        }
      }
      for (int i = replFrom.size() - 1; i >= 0; i--)
        curMax = replaceAll(curMax, replFrom[i], replTo[i]);
    }

    /**
     * Self explanatory
     */
    void getSymbolicMin(ExprSet& vec, Expr& curMin, bool isInt)
    {
      if (vec.size() == 0) return;
      ExprVector replFrom;
      ExprVector replTo;
      curMin = *vec.begin();
      if (vec.size() == 1) return;
      for (auto it = vec.begin(); ++it != vec.end(); ){
        auto &a = *it;
        if (u.isEquiv(mk<GT>(curMin, a), mk<TRUE>(efac))){
          curMin = a;
        } else if (u.isEquiv(mk<GT>(curMin, a), mk<FALSE>(efac))){
          //  curMin is OK
        } else {
          string ind = lexical_cast<string> (fresh_var_ind++);

          Expr varName = mkTerm ("_aeval_tmp_min_" + ind, efac);
          Expr var = isInt ? bind::intConst(varName) : bind::realConst(varName);

          replFrom.push_back(var);
          replTo.push_back(mk<ITE>(mk<GT>(curMin, a), a, curMin));

          curMin = var;
        }
      }
      for (int i = replFrom.size() - 1; i >= 0; i--)
        curMin = replaceAll(curMin, replFrom[i], replTo[i]);
    }

    void getSymbolicNeq(ExprSet& vec, Expr& lower, Expr& curNeq, Expr eps, bool isInt)
    {
      ExprVector replFrom;
      ExprVector replTo;

      Expr var1 = lower;
      Expr eps1;

      string ind = lexical_cast<string> (fresh_var_ind++);
      Expr varName = mkTerm ("_aeval_tmp_neq_" + ind, efac);
      Expr var2 = isInt ? bind::intConst(varName) : bind::realConst(varName);

      curNeq = var2;
      for (int i = 0; i < vec.size(); i++)
      {
        ExprSet neqqedConstrs;
        for (auto &a : vec) neqqedConstrs.insert(mk<EQ>(a, var1));

        string ind = lexical_cast<string> (fresh_var_ind++);
        Expr varName = mkTerm ("_aeval_tmp_neq_" + ind, efac);
        Expr newVar = isInt ? bind::intConst(varName) : bind::realConst(varName);

        replFrom.push_back(var2);
        replTo.push_back(mk<ITE>(disjoin(neqqedConstrs, efac), newVar, var1));

        eps1 = multVar(eps, i+1);
        var1 = mk<PLUS>(lower, eps1);
        var2 = newVar;
      }

      replFrom.push_back(var2);
      replTo.push_back(var1);

      for (int i = 0; i < replFrom.size(); i++)
        curNeq = replaceAll(curNeq, replFrom[i], replTo[i]);
    }

    /**
     * Based on type
     */
    Expr getDefaultAssignment(Expr var)
    {
      if (bind::isBoolConst(var)) return mk<TRUE>(efac);
      if (bind::isIntConst(var)) return mkTerm (mpz_class (0), efac);
      else           // that is, isRealConst(var) == true
        return mkTerm (mpq_class (0), efac);
    }

    /**
     * Return "e + eps"
     */
    Expr plusEps(Expr e, bool isInt = true)
    {
      if (isOpX<MPZ>(e) && isInt)
        return mkTerm (mpz_class (boost::lexical_cast<int> (e) + 1), efac);

      if (isInt) return mk<PLUS>(e, mkTerm (mpz_class (1), efac));
      else return mk<PLUS>(e, mkTerm (mpq_class (1), efac));
    }

    /**
     * Return "e - eps"
     */
    Expr minusEps(Expr e, bool isInt = true)
    {
      if (isOpX<MPZ>(e) && isInt)
        return mkTerm (mpz_class (boost::lexical_cast<int> (e) - 1), efac);

      if (isInt) return mk<MINUS>(e, mkTerm (mpz_class (1), efac));
      else return mk<MINUS>(e, mkTerm (mpq_class (1), efac));
    }

    /**
     * Extract function from relation
     */
    Expr getAssignmentForVar(Expr var, Expr exp)
    {
      if (debug >= 3)
      {
        outs () << "getAssignmentForVar " << *var << " in:\n";
        pprint(exp);
      }

      if (isOpX<TRUE>(exp))
      {
        return getDefaultAssignment(var);
      }
      if (!isNumeric(var))
      {
        ExprSet cnjs;
        getConj(exp, cnjs);
        for (auto & c : cnjs)
        {
          if (isOpX<EQ>(c))
          {
            if (var == c->left()) return c->right();
            if (var == c->right()) return c->left();
          }
          if (isBoolean(var))
          {
            if (c == var)
              return mk<TRUE>(efac);
            if (isOpX<NEG>(c) && c->left() == var)
              return mk<FALSE>(efac);
            if (isOpX<EQ>(c))
            {
              if (mk<NEG>(var) == c->left()) return mkNeg(c->right());
              if (mk<NEG>(var) == c->right()) return mkNeg(c->left());
            }
          }
        }
        assert(0);
      }

      bool isInt = bind::isIntConst(var);

      if (isOp<ComparissonOp>(exp))
      {
        if (isOpX<NEG>(exp)) exp = mkNeg(exp->left());

        if (!bind::isBoolConst(var) && var != exp->left())
          exp = ineqReverter(ineqMover(exp, var));
        // TODO: write a similar simplifier fo booleans

        assert (var == exp->left());

        if (isOpX<EQ>(exp) || isOpX<GEQ>(exp) || isOpX<LEQ>(exp)){
          if (exp->left() == exp->right()) return getDefaultAssignment(var);
          return exp->right();
        }
        else if (isOpX<LT>(exp)){
          return minusEps (exp->right(), isInt);
        }
        else if (isOpX<GT>(exp)){
          return plusEps (exp->right(), isInt);
        }
        else if (isOpX<NEQ>(exp)){
          return plusEps (exp->right(), isInt);
        }
        else assert(0);
      }
      else if (isOpX<NEG>(exp)){
        if (isOpX<EQ>(exp->left())) {
          return plusEps (getAssignmentForVar(var, exp->left()), isInt);
        }
      }
      else if (isOpX<AND>(exp))
      {
        exp = u.numericUnderapprox(exp); // try to see if there are only numerals
        if (isOpX<EQ>(exp)) return exp->right();

        ExprSet cnjs;
        getConj (exp, cnjs);
        u.removeRedundantConjuncts(cnjs);

        map<Expr, ExprSet> pre;
        for (auto & cnj : cnjs)
        {
          if (isOpX<IMPL>(cnj)) pre[cnj->left()].insert(cnj->right());
          else pre[mk<TRUE>(efac)].insert(cnj);
        }

        // sort keys of pre
        ExprVector sortedPre;
        for (auto & a : pre)
        {
          if (isOpX<TRUE>(a.first)) continue;
          int i = 0;
          while (i < sortedPre.size())
          {
            if (a.first != sortedPre[i] && u.implies (sortedPre[i], a.first)) break;
            i++;
          }
          sortedPre.insert(sortedPre.begin()+i, a.first);
        }

        // enhace the pre keys to avoid conflicts
        ExprVector preNegged;
        for (int i = 0; i < sortedPre.size(); i++)
        {
          ExprSet negged;
          negged.insert(sortedPre[i]);
          for (int j = 0; j < i; j++)
          {
            if (u.isSat(conjoin(negged, efac), mkNeg(sortedPre[j])))
              negged.insert(mkNeg(sortedPre[j]));
          }
          preNegged.push_back(conjoin(negged, efac));
        }

        // create the final ITE
        Expr sk = compositeAssm(pre[mk<TRUE>(efac)], var, isInt);
        for (int i = 0; i < sortedPre.size(); i++)
        {
          for (auto & b : pre)
          {
            if (sortedPre[i] != b.first && u.implies (preNegged[i], b.first))
            {
              pre[sortedPre[i]].insert(b.second.begin(), b.second.end());
            }
          }
          sk = mk<ITE>(preNegged[i], compositeAssm(pre[sortedPre[i]], var, isInt), sk);
        }

        return sk;
      }
      return exp;
    }

    Expr compositeAssm(ExprSet& cnjs, Expr var, bool isInt)
    {
        bool incomplete = false;

        // split constraints

        ExprSet conjLT;
        ExprSet conjLE;
        ExprSet conjGT;
        ExprSet conjGE;
        ExprSet conjNEQ;
        ExprSet conjEQ;

        u.removeRedundantConjuncts(cnjs);

        for (auto cnj : cnjs)
        {
          // preprocessing starts
          if (isOpX<NEG>(cnj)) cnj = mkNeg(cnj->left());
          cnj = ineqReverter(ineqMover(cnj, var));
          int c = isMultVar(cnj->left(), var);
          if (c == 1 && !isInt)
            cnj = reBuildCmp(cnj, var, cnj->right());
          if (c == -1 && !isInt)
            cnj = reBuildCmp(cnj, cnj->right(), var);
          if (c > 1 && !isInt)
            cnj = reBuildCmp(cnj, var, mk<DIV>(cnj->right(),
                    mkTerm (mpq_class (c), efac)));
          if (c < 0 && !isInt)
            cnj = reBuildCmp(cnj, mk<DIV>(cnj->right(),
                    mkTerm (mpq_class (-c), efac)), var);
          c = isMultVar(cnj->right(), var);
          if (c == 1 && !isInt)
            cnj = reBuildCmp(cnj, cnj->left(), var);
          if (c == -1 && !isInt)
            cnj = reBuildCmp(cnj, var, cnj->left());
          if (c > 1 && !isInt)
            cnj = reBuildCmp(cnj, mk<DIV>(cnj->left(),
                    mkTerm (mpq_class (c), efac)), var);
          if (c < 0 && !isInt)
            cnj = reBuildCmp(cnj, var, mk<DIV>(cnj->left(),
                    mkTerm (mpq_class (-c), efac)));
          // preprocessing ends

          if (isOpX<EQ>(cnj)){
            if (var == cnj->left()) {
              conjEQ.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LT>(cnj)){
            if (var == cnj->left()) {
              conjLT.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjGT.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<LEQ>(cnj)){
            if (var == cnj->left()) {
              conjLE.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjGE.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GT>(cnj)){
            if (var == cnj->left()) {
              conjGT.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjLT.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<GEQ>(cnj)){
            if (var == cnj->left()) {
              conjGE.insert(cnj->right());
            } else if (var == cnj->right()) {
              conjLE.insert(cnj->left());
            } else {
              incomplete = true;
            }
          }
          else if (isOpX<NEQ>(cnj)){
            if (var == cnj->left()) {
              conjNEQ.insert(cnj->right());
            } else {
              incomplete = true;
            }
          }
          else {
            incomplete = true;
          }

          if (incomplete && debug)
            outs() << "WARNING: This constraint is unsupported: " << *cnj << "\n";
        }

        // simplify some:
        for (auto & b : conjLE)
        {
          bool toBrk = false;
          for (auto & a : conjNEQ)
          {
            if (a == b)
            {
              conjLT.insert(a);
              conjNEQ.erase(a);
              conjLE.erase(b);
              toBrk = true;
              break;
            }
          }
          if (toBrk) break;
        }

        // simplify some:
        for (auto & b : conjGE)
        {
          bool toBrk = false;
          for (auto & a : conjNEQ)
          {
            if (a == b)
            {
              conjGT.insert(a);
              conjNEQ.erase(a);
              conjGE.erase(b);
              toBrk = true;
              break;
            }
          }
          if (toBrk) break;
        }

        // get the assignment (if exists)

        if (conjEQ.size() > 0) return *(conjEQ.begin()); // GF: maybe try to find the best of them

        // get symbolic max and min

        Expr curMaxGT, curMaxGE, curMinLT, curMinLE, curMax, curMin;
        getSymbolicMax(conjGT, curMaxGT, isInt);
        getSymbolicMax(conjGE, curMaxGE, isInt);
        getSymbolicMin(conjLT, curMinLT, isInt);
        getSymbolicMin(conjLE, curMinLE, isInt);

        if (isInt)
        {
          if (curMaxGT != NULL || curMaxGE != NULL)
          {
            if (curMaxGE == NULL) curMax = plusEps(curMaxGT);
            else if (curMaxGT == NULL) curMax = curMaxGE;
            else curMax = mk<ITE>(mk<GEQ>(curMaxGT, curMaxGE), plusEps(curMaxGT), curMaxGE);
          }

          if (curMinLT != NULL || curMinLE != NULL)
          {
            if (curMinLE == NULL) curMin = minusEps(curMinLT);
            else if (curMinLT == NULL) curMin = curMinLE;
            else curMin = mk<ITE>(mk<LEQ>(curMinLT, curMinLE), minusEps(curMinLT), curMinLE);
          }
        }
        else
        {
          if (curMaxGT != NULL || curMaxGE != NULL)
          {
            if (curMaxGE == NULL) curMax = curMaxGT;
            else if (curMaxGT == NULL) curMax = curMaxGE;
            else curMax = mk<ITE>(mk<GEQ>(curMaxGT, curMaxGE), curMaxGT, curMaxGE);
          }

          if (curMinLT != NULL || curMinLE != NULL)
          {
            if (curMinLE == NULL) curMin = curMinLT;
            else if (curMinLT == NULL) curMin = curMinLE;
            else curMin = mk<ITE>(mk<LEQ>(curMinLT, curMinLE), curMinLT, curMinLE);
          }
        }

        if (conjNEQ.size() == 0)
        {
          if (isInt)
          {
            if (curMax != NULL) return curMax;
            if (curMin != NULL) return curMin;
            assert (0);
          }

          if (curMinLT == NULL && curMinLE != NULL)
          {
            return curMinLE;
          }

          if (curMaxGT == NULL && curMaxGE != NULL)
          {
            return curMaxGE;
          }

          if (curMin == NULL)
          {
            return plusEps(curMaxGT, isInt);
          }

          if (curMax == NULL)
          {
            return minusEps(curMin, isInt);
          }

          // get value in the middle of max and min
          assert (curMin != NULL && curMax != NULL);
          return mk<DIV>(mk<PLUS>(curMin, curMax), mkTerm (mpq_class (2), efac));
        }

        // here conjNEQ.size() > 0

        Expr tmpMin;
        getSymbolicMin(conjNEQ, tmpMin, isInt);
        Expr tmpMax;
        getSymbolicMax(conjNEQ, tmpMax, isInt);

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return plusEps(tmpMax, isInt);
        }

        if (curMinLE != NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMinLE, tmpMin), curMinLE, tmpMin), isInt);
        }

        if (curMinLE == NULL && curMinLT != NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMinLT, tmpMin), curMinLT, tmpMin), isInt);
        }

        if (curMinLE != NULL && curMinLT != NULL && curMaxGE == NULL && curMaxGT == NULL)
        {
          return minusEps(mk<ITE>(mk<LT>(curMin, tmpMin), curMin, tmpMin), isInt);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE != NULL && curMaxGT == NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMaxGE, tmpMax), curMaxGE, tmpMax), isInt);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE == NULL && curMaxGT != NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMaxGT, tmpMax), curMaxGT, tmpMax), isInt);
        }

        if (curMinLE == NULL && curMinLT == NULL && curMaxGE != NULL && curMaxGT != NULL)
        {
          return plusEps(mk<ITE>(mk<GT>(curMax, tmpMax), curMax, tmpMax), isInt);
        }

        assert (curMinLE != NULL || curMinLT != NULL);
        assert (curMaxGE != NULL || curMaxGT != NULL);

        Expr eps;
        if (isInt)
        {
          eps = mkTerm (mpz_class (1), efac);

          if (curMaxGE == NULL) curMax = mk<PLUS>(curMaxGT, eps);
          else if (curMaxGT == NULL) curMax = curMaxGE;
          else curMax = mk<ITE>(mk<GEQ>(curMaxGT, curMaxGE), mk<PLUS>(curMaxGT, eps), curMaxGE);
        }
        else
        {
          eps = mk<DIV>(mk<MINUS>(curMin, curMax), mkTerm (mpq_class (conjNEQ.size() + 2), efac));
          curMax = mk<PLUS>(curMax, eps);
        }

        Expr curMid;
        getSymbolicNeq(conjNEQ, curMax, curMid, eps, isInt); // linear scan
        return curMid;
      }

    void searchDownwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug >= 3)
      {
        outs () << "searchDownwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      if (indexes.empty()) return;

      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
      if(debug >= 3) {
        outs() << "Pre set:\n";
        pprint(pre);
        outs() << "Post set:\n";
        pprint(post);
      }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        return;
      }
      else
      {
        Expr subs = ae.getValidSubset(false);
        if(debug >= 3) outs() << "subset: " << subs << "\n";
        if (isOpX<FALSE>(subs))
        {
//          for (int j : indexes)
//          {
//            set<int> indexes2 = indexes;
//            indexes2.erase(j);
//            searchDownwards(indexes2, var, skol);
//          }
          return;
        }
        else
        {
          bool erased = false;

          for (auto i = indexes.begin(); i != indexes.end();)
          {
            if (!u.implies(subs, projections[*i]))
            {
              i = indexes.erase(i);
              erased = true;
            }
            else
            {
              ++i;
            }
          }
          if (erased)
          {
            searchDownwards(indexes, var, skol);
          }
          else
          {
            for (int j : indexes)
            {
              set<int> indexes2 = indexes;
              indexes2.erase(j);
              if (!doneIndexes.insert(indexes2).second)
                return;
              searchDownwards(indexes2, var, skol);
            }
          }
        }
      }
    }

    void searchUpwards(set<int> &indexes, Expr var, ExprVector& skol)
    {
      if (debug >= 3)
      {
        outs () << "searchUpwards for " << *var << ": [[ indexes: ";
        for (auto i : indexes) outs() << i << ", ";
        outs () << " ]]\n";
      }
      ExprSet quant;
      quant.insert(var);
      ExprSet pre;
      ExprSet post;
      for (auto i : indexes)
      {
        pre.insert(projections[i]);
        post.insert(skol[i]);
      }
        if(debug >= 3) {
          outs() << "Pre set:\n";
          pprint(pre);
          outs() << "Post set:\n";
          pprint(post);
        }
      AeValSolver ae(disjoin(pre, efac), conjoin(post, efac), quant, false, false);

      if (!ae.solve())
      {
        if (bestIndexes.size() < indexes.size()) bestIndexes = indexes;
        for (int i = 0; i < partitioning_size; i++)
        {
          if (find (indexes.begin(), indexes.end(), i) != indexes.end()) continue;
          set<int> indexes2 = indexes;
          indexes2.insert(i);
          searchUpwards(indexes2, var, skol);
        }
        return;
      }
    }

    void breakCyclicSubsts(ExprMap& cyclicSubsts, ExprMap& evals, ExprMap& substsMap)
    {
      if (cyclicSubsts.empty()) return;

      map<Expr, int> tmp;
      for (auto & a : cyclicSubsts)
      {
        ExprSet vars;
        filter (a.second, bind::IsConst (), inserter (vars, vars.begin()));
        for (auto & b : vars)
        {
          if (find(v.begin(), v.end(), b) != v.end())
            tmp[b]++;
        }
      }

      int min = 0;
      Expr a;
      for (auto & b : tmp)
      {
        if (b.second >= min)
        {
          min = b.second;
          a = b.first;
        }
      }

      for (auto b = cyclicSubsts.begin(); b != cyclicSubsts.end(); b++)
        if (b->first == a)
        {
          substsMap[a] = evals[a]->right();
          cyclicSubsts.erase(b); break;
        }

      substsMap.insert (cyclicSubsts.begin(), cyclicSubsts.end());
      splitDefs(substsMap, cyclicSubsts);
      breakCyclicSubsts(cyclicSubsts, evals, substsMap);
    }

    Expr combineAssignments(ExprMap& allAssms, ExprMap& evals)
    {
      ExprSet skolTmp;
      ExprMap cyclicSubsts;
      splitDefs(allAssms, cyclicSubsts);

      breakCyclicSubsts(cyclicSubsts, evals, allAssms);
      assert (cyclicSubsts.empty());
      for (auto & a : sensitiveVars)
      {
        assert (emptyIntersect(allAssms[a], v));
        skolTmp.insert(mk<EQ>(a, allAssms[a]));
      }
      return conjoin(skolTmp, efac);
    }

    Expr getSkolemFunction (bool compact = false)
    {
      if (partitioning_size == 0)
        return mk<TRUE>(efac);

      ExprSet skolUncond;
      ExprSet eligibleVars;
      skolemConstraints.clear(); // GF: just in case
      doneIndexes.clear();

      // GF: to clean further
      for (auto &var: v)
      {
        bool elig = compact;
        if (elig) eligibleVars.insert(var);
        else sensitiveVars.insert(var);
      }

      for (auto & a : v)
      {
        ExprVector t;
        for (int i = 0; i < partitioning_size; i++)
        {
          assert(skolMaps[i][a] != NULL);
          t.push_back(skolMaps[i][a]); // should be on i-th position
        }
        skolemConstraints[a] = t;
      }

      map<Expr, set<int>> inds;
      ExprMap sameAssms;
      for (auto & var : eligibleVars)
      {
        bool same = true;
        auto & a = skolemConstraints[var];
        for (int i = 1; i < partitioning_size; i++)
        {
          if (a[0] != a[i])
          {
            same = false;
            break;
          }
        }
        if (same)
        {
          sameAssms[var] = getAssignmentForVar(var, a[0]);
          Expr skol = mk<EQ>(var, sameAssms[var]);
          skolUncond.insert(skol);
          separateSkols [var] = sameAssms[var];
        }
        else
        {
          sensitiveVars.insert(var);
        }
      }

      for (auto & var : sensitiveVars)
      {
        bestIndexes.clear();
        if (find(eligibleVars.begin(), eligibleVars.end(), var) != eligibleVars.end()
            && compact)
        {
          set<int> indexes;
          for (int i = 0; i < partitioning_size; i++) indexes.insert(i);
          searchDownwards (indexes, var, skolemConstraints[var]);
          searchUpwards (bestIndexes, var, skolemConstraints[var]);
        }
        inds[var] = bestIndexes;
      }

      Expr skol;
      ExprSet skolTmp;
      if (sensitiveVars.size() > 0)
      {
        set<int> intersect;
        for (int i = 0; i < partitioning_size; i ++)
        {
          int found = true;
          for (auto & a : inds)
          {
            if (find (a.second.begin(), a.second.end(), i) == a.second.end())
            {
              found = false;
              break;
            }
          }
          if (found) intersect.insert(i);
        }

        if (intersect.size() <= 1)
        {
          int maxSz = 0;
          int largestPre = 0;
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
            if (curSz > maxSz)
            {
              maxSz = curSz;
              largestPre = i;
            }
          }
          intersect.clear();
          intersect.insert(largestPre);
        }

        ExprMap allAssms = sameAssms;
        for (auto & a : sensitiveVars)
        {
          ExprSet cnjs;
          for (int b : intersect) getConj(skolemConstraints[a][b], cnjs);
          Expr def = getAssignmentForVar(a, conjoin(cnjs, efac));
          allAssms[a] = def;
        }
        Expr bigSkol = combineAssignments(allAssms, someEvals[*intersect.begin()]);
        if (debug) {
          boost::tribool impl = u.implies(mk<AND>(conjoin(skolUncond, efac), mk<AND>(s, projections[*intersect.begin()], bigSkol)), t);
          if(!impl)
            errs() << "Failed Sanity check [" << *intersect.begin() << "]" << endl;
          tribool_assert(impl);
        } 
        for (auto & evar : v)
        {
          Expr newSkol;
          for (int i = 0; i < partitioning_size; i++)
          {
            int curSz = treeSize(projections[i]);
          }
        }

        for (int i = 0; i < partitioning_size; i++)
        {
          allAssms = sameAssms;
          if (find(intersect.begin(), intersect.end(), i) == intersect.end())
          {
            for (auto & a : sensitiveVars)
            {
              Expr def = getAssignmentForVar(a, skolemConstraints[a][i]);
              allAssms[a] = def;
            }
            
            Expr mbpSkol = combineAssignments(allAssms, someEvals[i]);
            bigSkol = mk<ITE>(projections[i], mbpSkol, bigSkol);
            if (debug) {
              boost::tribool impl = u.implies(
                mk<AND>(conjoin(skolUncond, efac), mk<AND>(s, projections[i], mbpSkol)), t);
              if(!impl)
                errs() << "Failed Sanity check [" << i << "]" << endl;
              tribool_assert(impl);
            } 

            if (compact) bigSkol = u.simplifyITE(bigSkol);
          }
        }

        for (auto & a : sensitiveVars) separateSkols [a] = projectITE (bigSkol, a);

        skolUncond.insert(bigSkol);
      }
      return conjoin(skolUncond, efac);
    }

    Expr getSeparateSkol (Expr v) { return separateSkols [v]; }

    int getPartitioningSize() { return partitioning_size; }

    // Runnable only after getSkolemFunction
    Expr getSkolemConstraints(int i)
    {
      ExprSet constrs;
      for (auto & a : skolemConstraints)
        constrs.insert(a.second[i]);
      return conjoin(constrs, efac);
    }
  };

  void aeSolveAndSkolemize(Expr s, Expr t, bool skol, int debug, bool opt, bool compact, bool split)
  {
    ExprSet fa_qvars, ex_qvars;
    ExprFactory &efac = s->getFactory();
    SMTUtils u(efac);

    if(t == NULL)
    {
      if(!(isOpX<FORALL>(s) && isOpX<EXISTS>(s->last())))
        exit(0);
      s = regularizeQF(s);
      t = s->last()->last();
      for(int i = 0; i < s->last()->arity() - 1; i++)
        ex_qvars.insert(bind::fapp(s->last()->arg(i)));
      for(int i = 0; i < s->arity() - 1; i++)
        fa_qvars.insert(bind::fapp(s->arg(i)));

      s = mk<TRUE>(efac);
    }
    else
    {
      filter(s, bind::IsConst(), inserter(fa_qvars, fa_qvars.begin()));
      filter(t, bind::IsConst(), inserter(ex_qvars, ex_qvars.begin()));
      minusSets(ex_qvars, fa_qvars);
    }

    s = convertIntsToReals<DIV>(s);
    t = convertIntsToReals<DIV>(t);

    if(debug >= 3)
    {
      outs() << "s part: " << s << "\n";
      outs() << "t part: " << t << "\n";
      outs() << "s vars: [ ";
      for(auto &v : fa_qvars)
        outs() << v << " ";
      outs() << "]\n";
      outs() << "t vars: [ ";
      for(auto &v : ex_qvars)
        outs() << v << " ";
      outs() << "]\n";
    }

    Expr t_orig = t;
    if(opt)
    {
      ExprSet cnjs;
      getConj(t, cnjs);
      constantPropagation(fa_qvars, cnjs, true);
      // t = simpEquivClasses(fa_qvars, cnjs, efac);
      t = conjoin(cnjs, efac);
      t = simpleQE(t, ex_qvars);
      t = simplifyBool(t);
      if(debug >= 5)
      {
        outs() << "t part simplified: " << t << "\n";
      }
    }

    AeValSolver ae(s, t, ex_qvars, debug, skol);

    if(ae.solve())
    {
      outs() << "Iter: " << ae.getPartitioningSize() << "; Result: invalid\n";
      ae.printModelNeg(outs());
      outs() << "\nvalid subset:\n";
      u.serialize_formula(
        simplifyBool(simplifyArithm(ae.getValidSubset(compact))));
    }
    else
    {
      outs() << "Iter: " << ae.getPartitioningSize() << "; Result: valid\n";
      if(skol)
      {
        Expr skol = ae.getSkolemFunction(compact);
        if(split)
        {
          ExprVector sepSkols;
          for(auto &evar : ex_qvars)
            sepSkols.push_back(mk<EQ>(
              evar, simplifyBool(simplifyArithm(ae.getSeparateSkol(evar)))));
          u.serialize_formula(sepSkols);
          if(debug)
          {
            boost::tribool impl =
              u.implies(mk<AND>(s, conjoin(sepSkols, s->getFactory())), t_orig);
            tribool_assert(impl);
          }
        }
        else
        {
          outs() << "\nextracted skolem:\n";
          u.serialize_formula(simplifyBool(simplifyArithm(skol)));
          if(debug)
          {
            boost::tribool impl = u.implies(mk<AND>(s, skol), t_orig);
            tribool_assert(impl);
          }
        }
      }
    }
  }
}

#endif
