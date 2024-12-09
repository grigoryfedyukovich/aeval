#ifndef LINCOM__HPP__
#define LINCOM__HPP__

#define PRIORNOVISIT 0
#define PRIORSTEP 30
#define FREQCOEF 15
#define EPSILONFRACTION 5

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  typedef vector<vector <int>> lincoms;

  class LAterm
  {
    public:

    std::vector<int> vcs;

    int arity;
    int cmpop;
    int intconst;

    LAterm(){}

    int getSize()
    {
      return 3 + 2 * arity;
    }

    void normalizePlus()
    {
      int j;
      map<int, int> varsM;

      for (j = 0; j < vcs.size(); j += 2)
      {
        varsM[vcs[j]] = vcs[j+1];
      }

      // fill again
      j = 0;

      for (map<int,int>::iterator it=varsM.begin(); it!=varsM.end(); ++it)
      {
        vcs[j++] = it->first;
        vcs[j++] = it->second;
      }
    }
  };

  inline bool operator== (LAterm& a, LAterm& b)
  {
    if (a.arity != b.arity) return false;
    if (a.cmpop != b.cmpop) return false;
    if (a.intconst != b.intconst) return false;

    for (int i = 0; i < a.vcs.size(); i++)
    {
      if (a.vcs[i] != b.vcs[i]) return false;
    }
    return true;
  }

  class LAdisj
  {
    private:
    lincoms id;

    public:

    int arity = 0;
    vector<LAterm> dstate;    // i.e., disjunctive-state

    LAdisj(){}

    bool empty()
    {
      return arity == 0;
    }

    LAterm& newDisj()
    {
      arity++;
      dstate.push_back(LAterm());
      return dstate.back();
    }

    void addDisj(LAterm& s)
    {
      arity++;
      dstate.push_back(s);
    }

    void printLAdisj()
    {
      outs () << "Cur LAdisj (OR arity = " << arity << "): \n";
      for (int i = 0; i < arity; i++)
      {
        outs() << "   disj #" << i << ":\n";
        LAterm& s = dstate[i];

        outs() << "      ** arity +: " << s.arity << "\n";
        outs() << "      ** comparison op: " << s.cmpop << "\n";
        outs() << "      ** const: " << s.intconst << "\n";

        for (int j = 0; j < s.vcs.size(); )
        {
          outs() << "      ** var: " << s.vcs[j++] << "\n";
          outs() << "      ** coef: " << s.vcs[j++] << "\n";
        }
      }
      outs() << "\n";
    }

    void normalizePlus()
    {
      for (int i = 0; i < dstate.size(); i++)
      {
        LAterm& s = dstate[i];
        s.normalizePlus();
      }
    }

    lincoms& getId()
    {
      if (id.size() == 0)
      {
        for (int i = 0; i < dstate.size(); i++)
        {
          id.push_back(dstate[i].vcs);
        }
      }

      return id;
    }

    void clear()
    {
      arity = 0;
      dstate.clear();
      id.clear();
    }
  };

  inline void clone(LAterm& s, LAterm& t)
  {
    t.intconst = s.intconst;
    t.arity = s.arity;
    t.cmpop = s.cmpop;
    for (int i = 0; i < s.vcs.size(); i++)
    {
      t.vcs.push_back(s.vcs[i]);
    }
  }

  inline void clone(LAdisj& s, LAdisj& t)
  {
    for (int i = 0; i < s.arity; i++)
    {
      t.addDisj(s.dstate[i]);
    }
  }

  inline void dropDisj(LAdisj& s, LAdisj& t, int ind)
  {
    assert (s.arity > 1);
    for (int i = 0; i < s.arity; i++)
    {
      if (i != ind) t.addDisj(s.dstate[i]);
    }
  }

  class LAfactory
  {
    private:

    ExprFactory &m_efac;
    ExprVector vars;

    vector<int> varInds;
    vector<cpp_int> intCoefs;
    vector<cpp_int> intConsts;

    ExprVector intCoefsE;    // symmetric vectors with Expressions
    ExprVector intConstsE;
    ExprVector cmpOps;

    Expr auxVar1;
    Expr auxVar2;

    int indexGT;
    int indexGE;

    ExprSet nonlinVarsSet;

    public:

    ExprMap nonlinVars;

    // set of fields related to guessing:

    int prVarsDistrRange;
    set<int> orArities;
    map<int, density> plusAritiesDensity;
    map<int, density> intConstDensity;
    map<int, density> cmpOpDensity;
    map<int, vector<density>> varDensity;
    map<int, map<int, density>> coefDensity;
    vector<vector<set<int>>> varCombinations;

    map<lincoms, vector<weights>> ineqPriors;
    map<lincoms, set<int>> visited;
    bool aggressivepruning;

    LAfactory(ExprFactory &_efac, bool _aggressivepruning) :
        m_efac(_efac), aggressivepruning(_aggressivepruning){};

    void addVar(Expr var)
    {
      vars.push_back(var);
    }

    void addConst(cpp_int c)
    {
      intConsts.push_back(c);
    }

    void addIntCoef(cpp_int coef)
    {
      intCoefs.push_back(coef);
    }

    void initialize()  // should be called after addVar, addConst, and addIntCoef
    {
//      assert (intCoefs.size() > 0);
//      assert (intConsts.size() > 0);
//      assert (vars.size() > 0);

      prVarsDistrRange = 2 * intConsts.size();

      // auxiliary variables for inequations:
      auxVar1 = bind::intVar(mkTerm<string>("aux_deephorn_1", m_efac));
      auxVar2 = bind::intVar(mkTerm<string>("aux_deephorn_2", m_efac));

      for (int i = 0; i < vars.size(); i++) varInds.push_back(i);

      // two comparison operators (> and >=), so indexGT < indexGE
      cmpOps.push_back(mk<GT>  (auxVar1, auxVar2));
      indexGT = cmpOps.size() - 1;

      cmpOps.push_back(mk<GEQ> (auxVar1, auxVar2));
      indexGE = cmpOps.size() - 1;

//      // finally, map values to expressions
      for (auto &a : intCoefs) intCoefsE.push_back(mkMPZ(a, m_efac));    // assemble expressions
      for (auto &a : intConsts) intConstsE.push_back(mkMPZ(a, m_efac));  //

      for (auto &a : nonlinVars) nonlinVarsSet.insert(a.second);
    }

    vector<cpp_int>& getConsts()
    {
      return intConsts;
    }

    ExprVector& getVars()
    {
      return vars;
    }

    int getVar(int ind)
    {
      return varInds[ind];
    }

    int getIndexGT()
    {
      return indexGT;
    }

    int getIndexGE()
    {
      return indexGE;
    }

    int switchCmpOp(int ind)
    {
      // recall that there are two ops: >=, >
      assert (cmpOps.size() == 2);

      return (ind == 0) ? 1 : 0;
    }

    cpp_int getIntCoef(int i)
    {
      return intCoefs[i];
    }

    int getIntCoefsSize()
    {
      return intCoefs.size();
    }

    int getCmpOpsSize()
    {
      return cmpOps.size();
    }

    Expr getAtom(Expr templ, Expr var1, Expr var2)
    {
      Expr res = templ;
      res = replaceAll(res, auxVar1, var1);
      res = replaceAll(res, auxVar2, var2);
      return res;
    }

    Expr assembleLinComb(LAterm& s)
    {
      ExprVector apps;

      for (int i = 0; i < s.vcs.size(); i = i + 2)
      {
        Expr var = vars [ s.vcs[i] ];
        Expr coef = intCoefsE [ s.vcs[i + 1] ];
        apps.push_back(mk<MULT>(coef, var));
      }

      return mkplus (apps, m_efac);
    }

    Expr toExpr (LAterm& s, bool replaceNonlin=true)
    {
      Expr templ = cmpOps [ s.cmpop ];
      Expr ic = intConstsE [ s.intconst ];
      Expr lc = assembleLinComb(s);
      Expr ineq = getAtom(templ, lc, ic);

      if (replaceNonlin && nonlinVarsSet.size() > 0)
      {
        while (!emptyIntersect(ineq, nonlinVarsSet)) // replace cascadically
        {
          for (auto &a : nonlinVars) ineq = replaceAll(ineq, a.second, a.first);
        }
      }

      return ineq;
    }

    Expr toExpr (LAdisj& curCandCode)
    {
      int ar = curCandCode.arity;

      ExprSet dsj;
      for (int i = 0; i < ar; i++)
      {
        dsj.insert(toExpr (curCandCode.dstate[i]));
      }
      return disjoin(dsj, m_efac);
    }

    void exprToLAdisj(Expr ex, LAdisj& sample)
    {
      if (isOpX<OR>(ex))
      {
        for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
          exprToLAdisj(*it, sample);
      }
      else if (isOpX<GEQ>(ex) || isOpX<GT>(ex))
      {
        LAterm s;
        if (!isNumericConst(ex->right())) return;

        ExprVector all;
        getAddTerm (ex->left(), all);
        Expr aux = reBuildCmp(ex, auxVar1, auxVar2);

        s.arity = all.size();
        s.cmpop = getVarIndex(aux, cmpOps);
        s.intconst = getVarIndex(lexical_cast<cpp_int>(ex->right()), intConsts);

        if (s.intconst == -1 || s.cmpop == -1) return;

        for (auto &e : all)
        {
          Expr curVar = NULL;
          cpp_int curCoef;

          ExprVector ops;
          getMultOps (e, ops);
          for (auto & o : ops)
          {
            if (isNumericConst(o)) curCoef = lexical_cast<cpp_int>(o);
            else if (curVar != NULL) return;
            else curVar = o;
          }

          int varind = getVarIndex(curVar, vars);
          int coefind = getVarIndex(curCoef, intCoefs);

          if (varind == -1 || coefind == -1) return;

          s.vcs.push_back(varind);
          s.vcs.push_back(coefind);

        }

        for(int v : s.vcs) if (v < 0) return;

        if (s.vcs.size() != 2*(s.arity)) return;
        addDisjFilter(s, sample);
      }
    }

    cpp_int equalCoefs(LAterm& s)
    {
      cpp_int pat = intCoefs[ s.vcs[1] ];
      for (int j = 3; j < s.vcs.size(); j = j+2)
        if (pat != intCoefs[ s.vcs[j] ])
          return 0;

      return pat;
    }

    void invertTerm(LAterm& s, LAterm& t)
    {
      clone(s, t);
      for (int i = 1; i < s.vcs.size(); i = i+2)
      {
        auto coef = intCoefs[ s.vcs[i] ];
        int invcoef = getVarIndex(-coef, intCoefs);
        assert(invcoef != -1);

        t.vcs[i] = invcoef;
      }

      auto iconst = intConsts[ s.intconst ];
      int invconst = getVarIndex(-iconst, intConsts);
      assert(invconst != -1);

      t.intconst = invconst;
      t.cmpop = switchCmpOp(s.cmpop);
    }

    void invertDisj(LAdisj& s, LAdisj& t, int ind)
    {
      for (int i = 0; i < s.arity; i++)
      {
        if (i != ind)
        {
          t.addDisj(s.dstate[i]);
        }
        else
        {
          invertTerm(s.dstate[i], t.newDisj());
        }
      }
    }

    bool mergeDisj(LAdisj& s1, LAdisj& s2, LAdisj& t)
    {
      for (int i = 0; i < s1.arity; i++)
      {
        t.addDisj(s1.dstate[i]);
      }
      for (int i = 0; i < s2.arity; i++)
      {
        for (int j = 0; j < s1.arity; j++)
        {
          if (equivLinCom(s2.dstate[i], s1.dstate[j]))
            return false;
        }
        t.addDisj(s2.dstate[i]);
      }
      return true;
    }

    bool equivLinCom(LAterm& a, LAterm& b)
    {
      // decide equivalence gradually:

      if (a.arity != b.arity) return false;

      // check equivalence of vars
      for (int i = 0; i < a.vcs.size(); i = i + 2)
      {
        if (a.vcs[i] != b.vcs[i]) return false;
      }

      if (a.vcs.size() == 2) return (a.vcs[1] == b.vcs[1]);

      // finally, coefficients
      float c1 = (float)intCoefs[a.vcs[1]] / (float)intCoefs[b.vcs[1]];

      if (c1 < 0) return false;

      for (int i = 3; i < a.vcs.size(); i = i + 2)
      {
        float c2 = (float)intCoefs[a.vcs[i]] / (float)intCoefs[b.vcs[i]];
        if (c2 < 0) return false;

        if (fabs(c1 - c2) > 0.0001 ) return false; // hardcode here
      }

      return true;
    }

    // very approximate result as for equivLinCom (used in the aggressive mode)
    bool approxRedund(LAterm& a, LAterm& b)
    {
      // decide equivalence gradually:

      if (a.arity != b.arity) return false;

      // check equivalence of vars
      for (int i = 0; i < a.vcs.size(); i = i + 2)
      {
        if (a.vcs[i] != b.vcs[i]) return false;
      }

      for (int i = 1; i < a.vcs.size(); i = i + 2)
      {
        if (intCoefs[a.vcs[i]] >= 0 != intCoefs[b.vcs[i]] >= 0) return false;
      }

      return true;
    }

    // identifies some logical implications, e.g., x + 2y > 0 is stronger than x + 2y >= 10
    // false means "we don't know"
    bool stronger(LAterm& s, LAterm& t)
    {
      if (s.vcs.size() != t.vcs.size()) return false;

      for (int i = 0; i < s.vcs.size(); i++)
      {
        if (s.vcs[i] != t.vcs[i]) return false;
      }

      // Ax > b stronger than Ax >= b
      if (s.intconst == t.intconst)
        return (s.cmpop <= t.cmpop);  // the smaller index the stronger formula

      // Ax > / >= b stronger than Ax > / >= c iff b > c
      return (s.intconst > t.intconst);
    }

    // symmetric to stronger
    bool weaker(LAterm& s, LAterm& t)
    {
      if (s.vcs.size() != t.vcs.size()) return false;

      for (int i = 0; i < s.vcs.size(); i++)
      {
        if (s.vcs[i] != t.vcs[i]) return false;
      }

      if (s.intconst == t.intconst)
        return (s.cmpop >= t.cmpop);

      return (s.intconst < t.intconst);
    }

    void getEquivalentFormulas(LAdisj& sample, vector<LAdisj>& equivs)
    {
      equivs.push_back(sample);
      lincoms& id = sample.getId();

      for (int i = 0; i < sample.arity; i++)
      {
        LAterm& s = sample.dstate[i];
        Expr cmpop = cmpOps[ s.cmpop ];
        auto intconst = intConsts [ s.intconst ];

        // get the formulas equivalent to this one, and run the same procedure for them:

        // if (ax + ax > a) then we can replace a by b, c,... of the same sign

        cpp_int coef = equalCoefs(s);

        if (coef != 0 && coef == intconst)
        {
          for (int j = 0; j < intCoefs.size(); j++)
          {
            auto thisConst = intCoefs[j];
            if (thisConst == coef) continue;
            if ((thisConst<0) != (coef<0)) continue;

            int indProg = getVarIndex(thisConst, intConsts);  // GF?
            if (indProg == -1) continue;

            LAdisj c;
            clone(sample, c);
            c.dstate[i].intconst = indProg;
            for (int k = 0; k < c.dstate[i].vcs.size(); k ++)
            {
              if (k % 2 == 1) c.dstate[i].vcs[k] = j;
            }
            equivs.push_back(c);
          }
        }

        // if (ax + ax > 0) then we can replace a by b,c,... of the same sign

        else if (coef != 0 && 0 == intconst)
        {

          for (int j = 0; j < intCoefs.size(); j++)
          {
            auto thisConst = intCoefs[j];
            if (thisConst == coef) continue;
            if ((thisConst<0) != (coef<0)) continue;

            LAdisj c;
            clone(sample, c);
            for (int k = 0; k < c.dstate[i].vcs.size(); k ++)
            {
              if (k % 2 == 1) c.dstate[i].vcs[k] = j;
            }
            equivs.push_back(c);
          }
        }
      }
    }

    bool addDisjFilter(LAterm& s, LAdisj& d)
    {
      int skip = false;
      for (int j = 0; j < d.arity; j++)
      {
        LAterm& t = d.dstate[j];
        if (stronger(s, t))
        {
          // disjunction of s and t is equal t, so s can be ignored
          skip = true;
          break;
        }
        else if (weaker(s, t))
        {
          // disjunction of s and t is equal s, so swap these two guys:
          t.cmpop = s.cmpop;
          t.intconst = s.intconst;

          skip = true;
          break;
        }
        else
        {
          LAterm u;
          invertTerm(t, u);
          if (stronger(u, s))
          {
            // disjunction of s and t is equal to true, to the entire LAdisj& d is a tautology
            return false;
          }
        }
      }
      if (!skip)
      {
        d.addDisj(s);
      }
      return true;
    }

    // here, arity belongs to the whole candidate (incl. the boolean part),
    // while linArity is the number of clauses only in arithmetic
    bool guessTerm (LAdisj& curTerm, int arity, int linArity)
    {
      if (isEmpty(plusAritiesDensity[arity])) return false;

      vector<set<int>> varcombs;
      vector<LAterm> terms;

      // first, guess var combinations:

      for (int i = 0; i < linArity; i++)
      {
        terms.push_back(LAterm());
        LAterm& la = terms.back();
        la.arity = chooseByWeight(plusAritiesDensity[arity]);

        vector<set<int>>& varCombination = varCombinations[la.arity];
        int comb = chooseByWeight(varDensity[arity][la.arity]);
        varcombs.push_back(varCombination[comb]);
      }

      // then, guess coefficients to complete the lin. combination

      for (int i = 0; i < linArity; i++)
      {
        LAterm& la = terms[i];
        for (int v : varcombs[i])
        {
          la.vcs.push_back( v );
          int coef = chooseByWeight(coefDensity[arity][v]);
          la.vcs.push_back(coef);
        }

        if (i != 0)
        {
          for (int j = 0; j < i; j++)
          {

            if (!aggressivepruning && equivLinCom(la, curTerm.dstate[j]))
            {
              return false;
            }
            else if (aggressivepruning && approxRedund(la, curTerm.dstate[j]))
            {
              return false;
            }
          }
        }
        curTerm.addDisj(la);

      }

      // finally, guess operator and constant based on the information we learned from the previous samples:

      // WARNING: if aggressivepruning, we may skip checking some candidates
      if (aggressivepruning && isSampleVisitedWeak(curTerm)) return false;

      if (!aggressivepruning && isSampleVisitedStrong(curTerm)) return false;

      lincoms& id = curTerm.getId();

      for (int i = 0; i < linArity; i++)      // finally, guess operator and constant
      {
        LAterm& la = curTerm.dstate[i];
        guessNewInequality(id, i, la, arity);

        // GF: currently disabled:
        /* if (aggressivepruning)
        {
          for (int k = 0; k < learnedLemmas.size(); k++)
          {
            LAdisj& lcs = samples[ learnedLemmas [k] ];
            if (lcs.arity == 1 && lcs.dstate[0] == la) return false;
          }
        } */
      }
      return true;
    }

    void guessNewInequality (lincoms& id, int disj, LAterm& curLAterm, int ar)
    {
      vector<weights>& distrs = ineqPriors[id];
      initDistrs(distrs, id.size(), prVarsDistrRange);

      if (!aggressivepruning)
      {
        // re-initialize distribution (if empty)
        reInitialize(id, disj);
      }

      if (isDefault(distrs[disj]))       // if it's the first time we look at this lin.combination,
      {                                               // we might want to guess a candidate based on the code
        curLAterm.intconst = chooseByWeight(intConstDensity[ar]);
        curLAterm.cmpop = chooseByWeight(cmpOpDensity[ar]);
      }
      else                                            // otherwise, some info about this lin.combination
      {                                               // is already kmown from the previous checks
        int ch = chooseByWeight(distrs[disj]);
        double chd = (double)ch / 2;
        curLAterm.intconst = chd;
        curLAterm.cmpop = (ch % 2 == 0) ? getIndexGE() : getIndexGT();
      }
    }

    bool isSampleVisitedStrong(LAdisj& tmpl)
    {
      // we should exhaust the search space of all the disjuncts
      // before abandon the entire disjunction

      // currently, works for disjunctions with one disjunct
      // (for others, may keep throwing the same candidates again and again)
      lincoms& id = tmpl.getId();

      if (visited[id].size() == tmpl.arity)
      {
        return true;
      }
      return false;
    }

    bool isSampleVisitedWeak(LAdisj& tmpl)
    {
      // once the search space for one of the disjuncts is exhauseted
      // we abandoned the entire disjunction
      lincoms& id = tmpl.getId();

      if (visited[id].size() > 0)
      {
        return true;
      }
      return false;
    }

    bool isVisited(lincoms& id, int disj)
    {
      set<int>& s = visited[id];

      if (std::find(std::begin(s), std::end(s), disj) != std::end(s))
        return true;

      weights& d = ineqPriors[id][disj];

      if (ineqPriors[id].size() == 0)
      {
        outs() << "WARNING: Priorities are not set up here\n";
        return false;
      }

      for (int i = 0; i < d.size(); i++)
      {
        if (d[i] != PRIORNOVISIT) return false;
      }
      s.insert(disj);
      return true;
    }

    void reInitialize(lincoms& id, int disj, int def = 1000)
    {
      set<int>& s = visited[id];

      if (std::find(std::begin(s), std::end(s), disj) == std::end(s)) return;

      weights& d = ineqPriors[id][disj];

      for (int i = 0; i < d.size(); i++) d[i] = def;
    }

    void prioritiesBlocked(LAdisj& failed)
    {
      lincoms& id = failed.getId();
      vector<weights>& distrs = ineqPriors[id];

      initDistrs(distrs, failed.arity, prVarsDistrRange);

      for (int i = 0; i < failed.arity; i++)
      {
        LAterm& s = failed.dstate[i];
        distrs[i][s.intconst * 2 + (getIndexGT() == s.cmpop ? 1 : 0)] = PRIORNOVISIT;
        isVisited(id, i);
      }
    }

    void prioritiesFailed(LAdisj& failed)
    {
      lincoms& id = failed.getId();
      vector<weights>& distrs = ineqPriors[id];

      initDistrs(distrs, failed.arity, prVarsDistrRange);

      for (int i = 0; i < failed.arity; i++)
      {
        LAterm& s = failed.dstate[i];

        int lim = s.intconst * 2 + (getIndexGT() == s.cmpop ? 1 : 0);
        for (int j = 0; j < prVarsDistrRange ; j++)
        {
          if (j >= lim)
          {
            // block all constants which are greater or equal than intconst
            distrs[i][j] = PRIORNOVISIT;
          }
          else
          {
            // the farther constant from s.intconst the higher priority to visit it later
            distrs[i][j] = min ( distrs[i][j], (lim - j) * PRIORSTEP );
          }
        }

        isVisited(id, i);
      }
    }

    void prioritiesLearned(LAdisj& learned)
    {
      lincoms& id = learned.getId();
      vector<weights>& distrs = ineqPriors[id];

      initDistrs(distrs, learned.arity, prVarsDistrRange);

      for (int i = 0; i < learned.arity; i++)
      {
        LAterm& s = learned.dstate[i];

        int lim = s.intconst * 2 + (getIndexGT() == s.cmpop ? 1 : 0);
        for (int j = 0; j < prVarsDistrRange ; j++)
        {
          if (j < lim)
          {
            // block all constants which are less or equal than intconst
            distrs[i][j] = PRIORNOVISIT;
          }
          else
          {
            // the farther constant from intconst the higher priority to visit it later
            distrs[i][j] = min ( distrs[i][j], (j - lim) * PRIORSTEP );
          }
        }

        isVisited(id, i);
      }
    }

    void assignPrioritiesForLearned(LAdisj& learned)
    {
      if (!aggressivepruning) return;

      vector<LAdisj> eqs;
      getEquivalentFormulas(learned, eqs);
      for (auto &a : eqs) prioritiesLearned (a);

      if (learned.arity == 1)
      {
        LAdisj t;
        invertDisj (learned, t, 0);  // this is guaranteed to fail
        assignPrioritiesForFailed(t);
      }

      // GF: currently disabled
      /*
      else
      {
        vector<LAterm> invTerms;
        for (int i = 0; i < learned.arity; i++)
        {
          invTerms.push_back(LAterm());
          invertTerm(learned.dstate[i], invTerms.back());
        }

        for (int i = 0; i < learned.arity; i++)
        {
          bool canblock = true;
          for (int j = 0; j < learned.arity; j++)
          {
            if (i == j) continue;
            // search for invTerms[j] among learned lemmas
            bool found = false;
            for (int k = 0; k < learnedLemmas.size(); k++)
            {
              LAdisj& lcs = samples[ learnedLemmas [k] ];
              if (lcs.arity > 1) continue;
              if (stronger(lcs.dstate[0], invTerms[j]))
              {
                //                outs() << "stronger formula: " <<
                //                    *toExpr(lcs.dstate[0]) << "   ===>   " <<
                //                    *toExpr(invTerms[j]) << "\n";
                found = true;
                break;
              }
            }
            if (!found)
            {
              canblock = false;
              break;
            }
          }
          if (canblock)
          {
            LAdisj lcs;
            lcs.addDisj(invTerms[i]);
            assignPrioritiesForFailed(lcs);
          }
        }
      } */
    }

    void assignPrioritiesForFailed(LAdisj& failed)
    {
      if (!aggressivepruning) return;

      vector<LAdisj> eqs;
      getEquivalentFormulas(failed, eqs);
      for (auto &a : eqs) prioritiesFailed (a);
    }

    void assignPrioritiesForBlocked(LAdisj& failed)
    {
      if (!aggressivepruning) return;

      vector<LAdisj> eqs;
      getEquivalentFormulas(failed, eqs);
      for (auto &a : eqs) prioritiesBlocked (a);
    }

    void initDensities(set<int>& arities)
    {
      // preparing var combinations;
      varCombinations.push_back(vector<set<int>>());     // empty ones; not used
      for (int i = 1; i <= vars.size(); i++)
      {
        varCombinations.push_back(vector<set<int>>());
        getCombinations(varInds, 0, i, varCombinations.back());
      }

      for (auto ar : arities) initDensities(ar);
    }

    void initDensities(int ar)
    {
      for (int i = 1; i < vars.size() + 1; i++)
      {
        plusAritiesDensity[ar][i] = 0;

        for (int j = 0; j < intCoefs.size(); j++)
        {
          coefDensity[ar][i-1][j] = 0;
        }
      }

      for (int i = 0; i < intConsts.size(); i++)
      {
        intConstDensity[ar][i] = 0;
      }

      for (int i = 0; i < cmpOps.size(); i++)
      {
        cmpOpDensity[ar][i] = 0;
      }

      // preparing var densities;
      varDensity[ar].push_back(density());

      for (int i = 1; i <= vars.size(); i++)
      {
        varDensity[ar].push_back(density());

        for (int j = 0; j < varCombinations[i].size(); j++)
        {
          varDensity[ar].back()[j] = 0;
        }
      }
    }

    int getEpsilon(int min_freq, int num_zeros)
    {
      if (num_zeros == 0) return 1;

      // somewhat naive function; could be made dependent on other parameters,
      // not only on the minimum frequency and number of zero-frequencies...
      return 1 +
        ((min_freq == INT_MAX) ? 0 :
          guessUniformly(min_freq) / num_zeros / EPSILONFRACTION);
    }

    void stabilizeDensities(int ar, bool addEpsilon, bool freqs)
    {
      int freqCoef = freqs ? FREQCOEF : 1;
      int min_freq = INT_MAX;
      int num_zeros = 0;
      int eps = 0;

      for (auto & pl : plusAritiesDensity[ar])
      {
        if (pl.second == 0) num_zeros++;
        else
        {
          pl.second *= freqCoef;
          min_freq = min(min_freq, pl.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == plusAritiesDensity[ar].size()) eps = 1;
          else eps = 0;

      for (auto & pl : plusAritiesDensity[ar])
      {
        if (pl.second == 0) pl.second = eps;
      }

      for (int i = 0; i < vars.size(); i++)
      {
        min_freq = INT_MAX;
        num_zeros = 0;
        for (auto & c : coefDensity[ar][i])
        {
          if (c.second == 0) num_zeros++;
          else
          {
            c.second *= freqCoef;
            min_freq = min(min_freq, c.second);
          }
        }

        if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
          else if (num_zeros == coefDensity[ar][i].size()) eps = 1;
            else eps = 0;

        for (auto & c : coefDensity[ar][i])
        {
          if (c.second == 0) c.second = eps;
        }
      }

      min_freq = INT_MAX;
      num_zeros = 0;
      for (auto & c : intConstDensity[ar])
      {
        if (c.second == 0) num_zeros++;
        else
        {
          c.second *= freqCoef;
          min_freq = min(min_freq, c.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == intConstDensity[ar].size()) eps = 1;
          else eps = 0;

      for (auto & c : intConstDensity[ar])
      {
        if (c.second == 0) c.second = eps;
      }

      min_freq = INT_MAX;
      num_zeros = 0;
      for (auto & c : cmpOpDensity[ar])
      {
        if (c.second == 0) num_zeros++;
        else
        {
          c.second *= freqCoef;
          min_freq = min(min_freq, c.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == cmpOpDensity[ar].size()) eps = 1;
          else eps = 0;

      for (auto & c : cmpOpDensity[ar])
      {
        if (c.second == 0) c.second = eps;
      }

      for (int i = 0; i < varDensity[ar].size(); i++)
      {
        min_freq = INT_MAX;
        num_zeros = 0;
        for (auto &b : varDensity[ar][i])
        {
          if (b.second == 0) num_zeros++;
          else
          {
            b.second *= freqCoef;
            min_freq = min(min_freq, b.second);
          }
        }

        if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
          else if (num_zeros == varDensity[ar][i].size()) eps = 1;
            else eps = 0;

        for (auto &b : varDensity[ar][i])
        {
          if (b.second == 0) b.second = eps;
        }
      }
    }

    void calculateStatistics(LAdisj& lcs, int ar, bool freqs, bool addepsilon)
    {
      if (freqs)
      {
        // collect number of occurrences....

        for (auto & lc : lcs.dstate)
        {
          // of arities of application of PLUS
          plusAritiesDensity[ar][lc.arity] ++;

          // of constants
          intConstDensity[ar][lc.intconst] ++;

          // of comparison operations
          cmpOpDensity[ar][lc.cmpop] ++;

          set<int> vars;
          int vars_id = -1;
          for (int j = 0; j < lc.vcs.size(); j = j+2) vars.insert(lc.vcs[j]);
          for (int j = 0; j < varCombinations[lc.arity].size(); j++)
          {
            if (varCombinations[lc.arity][j] == vars)
            {
              vars_id = j;
              break;
            }
          }
          assert(vars_id >= 0);

          // of variable combinations
          varDensity[ar][lc.arity][vars_id] ++;

          // of variable coefficients
          for (int j = 1; j < lc.vcs.size(); j = j+2)
          {
            coefDensity[ ar ][ lc.vcs [j-1] ] [lc.vcs [j] ] ++;
          }
        }
      }
      else
      {
        // same thing as in above; but instead of precise frequencies, we gather a rough presence

        for (auto & lc : lcs.dstate)
        {
          // of arities of application of PLUS
          plusAritiesDensity[ar][lc.arity] = 1;

          // of constants
          intConstDensity[ar][lc.intconst] = 1;

          // of comparison operations
          cmpOpDensity[ar][lc.cmpop] = 1;

          set<int> vars;
          int vars_id = -1;
          for (int j = 0; j < lc.vcs.size(); j = j+2) vars.insert(lc.vcs[j]);
          for (int j = 0; j < varCombinations[lc.arity].size(); j++)
          {
            if (varCombinations[lc.arity][j] == vars)
            {
              vars_id = j;
              break;
            }
          }
          assert(vars_id >= 0);

          // of variable combinations
          varDensity[ar][lc.arity][vars_id] = 1;

          // of variable coefficients
          for (int j = 1; j < lc.vcs.size(); j = j+2)
          {
            coefDensity[ ar ][ lc.vcs [j-1] ] [lc.vcs [j] ] = 1;
          }
        }
      }
    }

    void printCodeStatistics(int ar)
    {
      outs () << "(OR arity = " << ar << "):\n";

      for (auto &a : plusAritiesDensity[ar])
      {
        outs() << " Plus arity density: " << a.first << " |--> " << a.second << "\n";
      }

      for (auto &a : intConstDensity[ar])
      {
        outs() << " IntConst density: " << *intConstsE[ a.first ] << " |--> " << a.second << "\n";
      }

      for (auto &a : cmpOpDensity[ar])
      {
        outs() << " Operator density: " << (a.first == indexGT ? ">" : ">=") << " |--> " << a.second << "\n";
      }

      for (int i = 0; i < varDensity[ar].size(); i++)
      {
        for (auto &b : varDensity[ar][i])
        {
          outs() << " Var Combination density: ";

          for (int j : varCombinations[i][b.first])
          {
            outs() << *vars[j] << ", ";
          }

          outs() << "\b\b |--> " << b.second << "\n";
        }
      }

      for (int i = 0; i < vars.size(); i++)
      {
        for (int j = 0; j < getIntCoefsSize(); j++)
        {
          outs() << " Var Coefficient density: [" << *intCoefsE[j] << " * "
            << *vars[i] << "] : " << coefDensity[ar][i][j] << "\n";
        }
      }
    }
  };
}


#endif
