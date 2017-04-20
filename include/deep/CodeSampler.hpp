#ifndef CODESAMPLER__HPP__
#define CODESAMPLER__HPP__

#define MAXVARNM 10
//#define MAXTSIZE 100

#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class CodeSampler
  {
    public:
    
    ExprSet candidates;
    
    set<int> intConsts;
    set<int> intCoefs;
    
    HornRuleExt& hr;
    Expr invDecl;
    ExprVector invVars;
    
    Expr zero;
    
    CodeSampler(HornRuleExt& r, Expr& d, ExprVector& v) : hr(r), invDecl(d), invVars(v)
    {
      // add some "universal" constants
      intConsts.insert(0);
      intConsts.insert(1);
      intConsts.insert(-1);
      
      // aux Expr const
      zero = mkTerm (mpz_class (0), invDecl->getFactory());
    };
    
    void addSampleHlp(Expr tmpl, ExprVector& vars, ExprSet& actualVars)
    {
      for (auto &v : actualVars)
      {
        int index = getVarIndex(v, vars);
        if (index >= 0)
        {
          tmpl = replaceAll(tmpl, v, invVars[index]);
        }
        else
        {
          return; // tmpl = replaceAll(tmpl, v, zero);
        }
      }
      Expr tmpl2 = normalizeDisj(tmpl, invVars);
      
      if (!isOpX<FALSE> (tmpl2) && !isOpX<TRUE> (tmpl2))
      {
        candidates.insert(tmpl2);
        
        // get int constants from the normalized candidate
        ExprSet intConstsE;
        expr::filter (tmpl2, bind::IsHardIntConst(), std::inserter (intConstsE, intConstsE.begin ()));
        
        for (auto &a : intConstsE)
        {
          intConsts.insert(lexical_cast<int>(a));
        }
        
        getLinCombCoefs(tmpl2, intCoefs);
      }
    }
    
    void processTransition(Expr tmpl, ExprVector& srcVars, ExprVector& dstVars, ExprSet& actualVars)
    {
      int found = false;
      // very simple check if there are some srcVars and dstVars in the tmpl
      
      for (auto &v0 : srcVars)
      {
        for (auto &v1 : actualVars)
        {
          if (v0 == v1)
          {
            found = true;
            break;
          }
        }
      }
      
      if (! found) return;
      
      found = false;
      for (auto &v0 : dstVars)
      {
        for (auto &v1 : actualVars)
        {
          if (v0 == v1)
          {
            found = true;
            break;
          }
        }
      }
      
      if (! found) return;
      
      ExprVector vars;
      for (auto &v : actualVars) vars.push_back(v);

      ExprSet intCoefsE;
      expr::filter (normalizeDisj(tmpl, vars), bind::IsHardIntConst(), std::inserter (intCoefsE, intCoefsE.begin ()));
      
      for (auto &a : intCoefsE)
      {
        intCoefs.insert(lexical_cast<int>(a));
      }
    }
    
    void addSample(Expr term)
    {
      //      if (treeSize(term) > MAXTSIZE) // don't consider too huge templates
      //      {
      //        return;
      //      }

      ExprSet actualVars;
      ExprSet subsetInvVars;
      
      expr::filter (term, bind::IsConst(), std::inserter (actualVars, actualVars.begin ()));
      
      bool locals = false;
      if (actualVars.size() == 0 || isTautology(term)) return;
      
      // split each term to two samples (for srcVars and dstVars)
      addSampleHlp(term, hr.srcVars, actualVars);
      addSampleHlp(term, hr.dstVars, actualVars);
      
      processTransition(term, hr.srcVars, hr.dstVars, actualVars);
    }
    
    void populateArityAndTemplates(Expr term)
    {
      if (isOpX<NEG>(term))
      {
        addSample(mkNeg(term->last()));             // massage the negated formula a bit
        populateArityAndTemplates(term->last());
      }
      else if (isOpX<OR>(term))
      {
        if (!containsOp<AND>(term))
        {
          addSample(term);        // add any disjunct as a sample;
        }
        else
        {
          if (term->arity() < 5)  // skip in case of big formulas (otherwise the formula blows up exponentially)
          {                       // constant is hardcoded.. we can try something larger
            Expr term2 = rewriteOrAnd(term);
            populateArityAndTemplates(term2);
          }
        }
      }
      else if (isOpX<AND>(term))
      {
        for (int i = 0; i < term->arity(); i++)
        {
          populateArityAndTemplates(term->arg(i));
        }
      }
      else if (isOpX<IMPL>(term))
      {
        Expr term2 = mk<OR>(mkNeg(term->left()), term->right());
        populateArityAndTemplates(convertToGEandGT(term2));
      }
      else if (isOpX<GT>(term) || isOpX<GEQ>(term))
      {
        addSample(term);      // get rid of ITEs first
      }
      else if (isOp<ComparissonOp>(term))
      {
        populateArityAndTemplates(convertToGEandGT(term));
      }
    }
    
    void shrinkConstantsSet()
    {
      if (intConsts.size() < MAXVARNM) return;
      
      Expr maxPosE;
      Expr minPosE;
      Expr maxNegE;
      Expr minNegE;
      
      int maxPos = 0;
      int minPos = INT_MAX;
      int maxNeg = INT_MIN;
      int minNeg = 0;
      
      
      bool hasPos = false;
      bool hasNeg = false;
      
      for (auto curint: intConsts)
      {
        if (curint > 0)
        {
          hasPos = true;
          maxPos = max (maxPos, curint);
          minPos = min (minPos, curint);
        }
        else if (curint < 0)
        {
          hasNeg = true;
          maxNeg = max (maxPos, curint);
          minNeg = min (minPos, curint);
        }
      }
      
      intConsts.clear();
      
      if (hasPos)
      {
        intConsts.insert(minPos);
        intConsts.insert(maxPos);
      }
      
      if (hasNeg)
      {
        intConsts.insert(minNeg);
        intConsts.insert(maxNeg);
      }
      
      // add again the "universal" constants
      intConsts.insert(0);
      intConsts.insert(1);
      intConsts.insert(-1);
    }
    
    // GF: here could be many possible heuristics; currently we use only constants
    void shrinkTemplatesSet()
    {
      ExprSet newTmpls;
      for (auto &tmpl : candidates)
      {
        ExprVector tmplConstsExpr;
        expr::filter (tmpl, bind::IsHardIntConst(), std::inserter (tmplConstsExpr, tmplConstsExpr.begin ()));
        
        bool found = (tmplConstsExpr.size() == 0);
        set<int>tmplConsts;
        for (auto &c : tmplConstsExpr) tmplConsts.insert(lexical_cast<int> (c));
        
        if (!found)       // if there are no constants in the template, keep it!
        {
          for (auto c1 : tmplConsts)
          {
            for (auto c2 : intConsts)
            {
              // GF: comparing the actual constant values:
              if (c1 == 0 || c1 ==-1 || c1 == 1 || c1 == c2)
              {
                found = true;
                break;
              }
            }
          }
        }
        if (found) newTmpls.insert(tmpl);
      }
      candidates = newTmpls;
    }
    
    // GF: todo: mine plus / minus numbers, check which signs of constants appear in the lhs / rhs of expressions
    
    void analyzeCode(bool samplecode, bool shrink)
    {
      if (false) // printing only
      {
        outs () << "\nAnalize CHC:\n";
        outs () << "src vars: ";
        for (int i = 0; i < hr.srcVars.size(); i++) outs() << "[" << *invVars[i] << "] = " << *hr.srcVars[i] << ", ";
        outs() <<"\n";
        outs () << "dst vars: ";
        for (int i = 0; i < hr.dstVars.size(); i++) outs() << "[" << *invVars[i] << "] = " << *hr.dstVars[i] << ", ";
        outs() <<"\n";
      }
      
      intCoefs.insert(1);
      intConsts.insert(0);
      
      // get samples and normalize
      if (samplecode)
      {
        // for the query: add a negation of the entire non-recursive part:
        if (hr.isQuery)
        {
          Expr massaged = unfoldITE(mkNeg(hr.body));
          massaged = convertToGEandGT(massaged);
          populateArityAndTemplates(massaged);
        }
        else
        {
          // for others: the entire non-recursive part
          for (auto &cnj : hr.lin)
          {
            // GF: todo: make sure all constants in the code are Ints (otherwise, z3 could be unpredictable)
            Expr massaged = unfoldITE(cnj);
            massaged = convertToGEandGT(massaged);
            populateArityAndTemplates(massaged);
          }
        }
      }
      else
      {
        // get int constants (and shrink later)
        // GF: todo: make sure all constants in the code are Ints (otherwise, z3 could be unpredictable)
        ExprSet allNums;
        expr::filter (hr.body, bind::IsHardIntConst(), std::inserter (allNums, allNums.begin ()));
        
        for (auto &a : allNums)
        {
          int c = lexical_cast<int>(a);
          intConsts.insert(c);
          if (c != 0) intCoefs.insert(c);
        }
      }
      
      if (shrink)
      {
        shrinkConstantsSet();
        shrinkTemplatesSet();
      }
    }
  };
}

#endif