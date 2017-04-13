#ifndef HORN__HPP__
#define HORN__HPP__

#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;
    
    ExprVector lin;
    Expr body;           // conjunction of lin
    Expr head;
    
    Expr srcRelation;
    Expr dstRelation;
    
    bool isFact;
    bool isQuery;
    bool isInductive;
    
    string suffix;
  };
  
  class CHCs
  {
    private:
    
    ExprFactory &m_efac;
    EZ3 &m_z3;
    
    Expr failDecl;
    
    public:
    
    vector<HornRuleExt> chcs;
    ExprSet decls;
    
    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3)  {};
 
    void preprocess (Expr term, ExprSet& srcVars, ExprVector& relations, Expr &srcRelation, ExprVector& lin)
    {
      if (isOpX<AND>(term))
      {
        for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it)
        {
          preprocess(*it, srcVars, relations, srcRelation, lin);
        }
      }
      else
      {
        if (isOpX<FAPP>(term))
        {
          if (term->arity () > 0)
          {
            if (isOpX<FDECL>(term->arg(0)))
            {
              for (auto &rel: relations)
              {
                if (rel == term->arg(0))
                {
                  srcRelation = rel->arg(0);
                  expr::filter (term, bind::IsConst(), std::inserter (srcVars, srcVars.begin ()));
                }
              }
            }
          }
        }
        else
        {
          lin.push_back(term);
        }
      }
    }
    
    void parse(string smt)
    {
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);
      
      string suff(""); //suff("_new");
      
      // a little hack here
      
      for (auto &a : fp.m_rels)
      {
        if (a->arity() == 2)
        {
          failDecl = a;
        }
        else
        {
          decls.insert(a);
        }
      }
      
      for (auto &r: fp.m_rules)
      {
        assert (isOpX<FORALL>(r));
        
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        
        hr.suffix = suff;
        hr.srcRelation = mk<TRUE>(m_efac);
        
        Expr rule = r->last();
        
        ExprVector args;
        
        for (int i = 0; i < r->arity() - 1; i++)
        {
          Expr var = r->arg(i);
          Expr name = bind::name (r->arg(i));
          Expr new_name = mkTerm<string> (lexical_cast<string> (name.get()) + suff, m_efac);
          Expr var_new = bind::fapp(bind::rename(var, new_name));
          args.push_back(var_new);
        }
        
        ExprVector actual_vars;
        expr::filter (rule, bind::IsVar(), std::inserter (actual_vars, actual_vars.begin ()));
        
        assert(actual_vars.size() == args.size());
        
        for (int i = 0; i < actual_vars.size(); i++)
        {
          string a1 = lexical_cast<string>(bind::name(actual_vars[i]));
          int ind = args.size() - 1 - atoi(a1.substr(1).c_str());
          rule = replaceAll(rule, actual_vars[i], args[ind]);
        }
        
        Expr body = rule->arg(0);
        Expr head = rule->arg(1);
        
        hr.head = head->arg(0);
        
        hr.dstRelation = head->arg(0)->arg(0);

        ExprSet srcVars;
        
        preprocess(body, srcVars, fp.m_rels, hr.srcRelation, hr.lin);
        
        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl->arg(0));
        hr.isInductive = (hr.srcRelation == hr.dstRelation);
        
        hr.body = conjoin(hr.lin, m_efac);
        
        for (auto &a : srcVars) hr.srcVars.push_back(a);
        
        if (!hr.isQuery)
        {
          expr::filter (head, bind::IsConst(), std::inserter (hr.dstVars, hr.dstVars.begin ()));
        }
        
        for(auto &a: args)
        {
          bool found = false;
          for (auto &b : hr.dstVars)
          {
            if (a == b) found = true;
          }
          if (! found)
          {
            for (auto &b : hr.srcVars)
            {
              if (a == b) found = true;
            }
          }
          if (!found)
          {
            hr.locVars.push_back(a);
          }
        }
      }
    }
    
    void print()
    {
      int num = 0;
      for (auto &hr: chcs){
        outs () << "\n=========================\n";
        outs () << "RULE #" << num++ << "\n";
        outs() << "\n body [" << * hr.body << "]  ->  " << * hr.head << "\n";
        outs() << "\n" << * hr.srcRelation << "  ->  " << * hr.dstRelation << "\n";
        
        outs() << "\n  SRC VARS: ";
        for(auto &a: hr.srcVars){
          outs() << *a << ", ";
        }
        outs() << "\n";
        outs() << "  DST VARS: ";
        for(auto a: hr.dstVars){
          outs() << *a << ", ";
        }
        outs() << "\n";
        outs() << "  LOCAL VARS: ";
        for(auto a: hr.locVars){
          outs() << *a << ", ";
        }
        
        outs () << "\n";
  
      }
    }
  };
}


#endif