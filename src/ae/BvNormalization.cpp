#include "ae/BvNormalization.hpp"

#include <cmath>

#include "ae/ExprBvUtils.hpp"

using namespace ufo;

CmpSplitter::CmpSplitter(Expr _exp, Expr var) : exp(_exp), r(exp->right())
{
  assert(isOp<BvUCmp>(exp));
  ExprVector terms;
  getBaddTerm(exp->left(), terms);
  for(auto t : terms)
  {
    if(contains(t, var))
      xPart.push_back(t);
    else
      yPart.push_back(t);
  }
  this->overflow = !bvTrySquashCoefs(xPart, var);
}

void CmpSplitter::split(splitedCmp &out)
{
  out.exp = exp;
  out.tx = mkbadd(xPart);
  out.y = mkbadd(yPart);
  out.r = r;
  this->nextSplit();
}

// t(x) + y <= r ---> t(x) <= r-y && y <= r
bool add1::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;
  Expr prem1 = mk<BULE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
  Expr prem2 = mk<BULE>(cmp.y, cmp.r);
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    // outs() << "Applied add1\n";
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// t(x) + y <= r ---> t(x) <= r-y && -y <= tx
bool add2::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;
  Expr prem1 = mk<BULE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
  Expr prem2 = mk<BULE>(mk<BNEG>(cmp.y), cmp.tx);
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    // outs() << "Applied add2\n";
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// t(x) + y <= r ---> -y <= t(x) && y <= r && y != 0
bool add3::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;

  Expr prem1 = mk<BULE>(mk<BNEG>(cmp.y), cmp.tx);
  Expr prem2 = mk<BULE>(cmp.y, cmp.r);
  Expr prem3 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
  if(
    isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) &&
    isOpX<TRUE>(m.eval(prem3)))
  {
    // outs() << "Applied add3\n";
    out.insert(prem1);
    out.insert(prem2);
    out.insert(prem3);
    return true;
  }
  return false;
}

// t(x) + y >= r ---> t(x) >= r-y && r <= y-1
bool add4::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BUGE>(cmp.exp))
    return false;

  Expr prem1 = mk<BUGE>(cmp.tx, mk<BSUB>(cmp.r, cmp.y));
  Expr prem2 = mk<BULE>(cmp.r, mk<BSUB>(cmp.y, bv::bvnum(1, bvSize, efac)));

  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    // outs() << "Applied add4\n";
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// t(x) + y >= r ---> t(x) >= r - y && t(x) <= -y -1 && y != 0
bool add5::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BUGE>(cmp.exp))
    return false;

  Expr prem1 = mk<BUGE>(cmp.tx, cmp.r);
  Expr prem2 =
    mk<BULE>(cmp.tx, mk<BSUB>(mk<BNEG>(cmp.y), bv::bvnum(1, bvSize, efac)));
  Expr prem3 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
  if(
    isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) &&
    isOpX<TRUE>(m.eval(prem3)))
  {
    // outs() << "Applied add5\n";
    out.insert(prem1);
    out.insert(prem2);
    out.insert(prem3);
    return true;
  }
  return false;
}

// t(x) + y >= r ---> y = 0 && r <= t(x)
bool add6::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BUGE>(cmp.exp))
    return false;

  Expr prem1 = mk<BULE>(cmp.y, bv::bvnum(0, bvSize, efac));
  Expr prem2 = mk<BULE>(cmp.r, cmp.tx);
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    // outs() << "Applied add6\n";
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// t(x) + y >= r ---> y != 0 && r <= y - 1 && t(x) <= -y-1
bool add7::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BUGE>(cmp.exp))
    return false;

  Expr prem1 = mk<BUGE>(cmp.y, bv::bvnum(1, bvSize, efac));
  Expr prem2 = mk<BULE>(cmp.r, mk<BSUB>(cmp.y, bv::bvnum(1, bvSize, efac)));
  Expr prem3 =
    mk<BULE>(cmp.tx, mk<BSUB>(mk<BNEG>(cmp.y), bv::bvnum(1, bvSize, efac)));
  if(
    isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) &&
    isOpX<TRUE>(m.eval(prem3)))
  {
    // outs() << "Applied add7\n";
    out.insert(prem1);
    out.insert(prem2);
    out.insert(prem3);
    return true;
  }
  return false;
}

// t(x) + y <= r(x) ---> y <= r(x)-t(x) && t(x) <= r(x)
bool both1::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;
  Expr prem1 = mk<BULE>(cmp.y, mk<BSUB>(cmp.r, cmp.tx));
  Expr prem2 = mk<BULE>(cmp.tx, cmp.r);
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// t(x) + y <= r(x) ---> y <= r(x)-t(x) && -t(x) <= y
bool both2::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;
  Expr prem1 = mk<BULE>(cmp.y, mk<BSUB>(cmp.r, cmp.tx));
  Expr prem2 = mk<BULE>(mk<BNEG>(cmp.tx), cmp.y);
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// t(x) + y <= r(x) ---> -t(x) <= y && t(x) <= r(x) && t(x) != 0
bool both3::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;
  Expr prem1 = mk<BULE>(mk<BNEG>(cmp.tx), cmp.y);
  Expr prem2 = mk<BULE>(cmp.tx, cmp.r);
  Expr prem3 = mk<BUGE>(cmp.tx, bv::bvnum(1, bvSize, efac));
  if(
    isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)) &&
    isOpX<TRUE>(m.eval(prem3)))
  {
    out.insert(prem1);
    out.insert(prem2);
    out.insert(prem3);
    return true;
  }
  return false;
}

// k1 * x <= k2 * x ---> x <= (2^n * k2) / k1
bool both4::apply(splitedCmp cmp, ExprSet &out)
{
  if(!isOpX<BULE>(cmp.exp))
    return false;
  if(!isBmulVar(cmp.exp->left(), var) || !isBmulVar(cmp.exp->right(), var))
    return false;

  int c = pow(2, bvSize);
  Expr k1 = getBmulVar(cmp.exp->left(), var);
  Expr k2 = getBmulVar(cmp.exp->right(), var);
  Expr r = mk<BUDIV>(mk<BMUL>(bv::bvnum(c, bvSize, efac), k2), k1);
  Expr prem1 = mk<BULE>(var, r);
  if(isOpX<TRUE>(m.eval(prem1)))
  {
    out.insert(prem1);
    return true;
  }
  return false;
}

// tx div y <= r ---> tx <= (r+1)*y - 1 && r < (2^n - 1) div y
bool div1::apply(splitedCmp cmp, ExprSet &out)
{
  Expr l = cmp.exp->left();
  if(!isOpX<BULE>(cmp.exp))
    return false;
  if(!isBdivVar(l, var) || contains(cmp.r, var))
    return false;

  Expr tx = l->left();
  Expr y = l->right();
  int c = pow(2, bvSize) - 1;
  Expr prem = mk<BULT>(cmp.r, mk<BUDIV>(bv::bvnum(c, bvSize, efac), y));
  if(isOpX<TRUE>(m.eval(prem)))
  {
    Expr bvOne = bv::bvnum(1, bvSize, efac);
    Expr xPart =
      mk<BULE>(tx, mk<BSUB>(mk<BMUL>(mk<BADD>(cmp.r, bvOne), y), bvOne));
    out.insert(prem);
    out.insert(xPart);
    return true;
  }
  return false;
}

// tx div y <= r ---> tx <= (r+1)*y - 1 && r < (2^n - 1) div y
bool div2::apply(splitedCmp cmp, ExprSet &out)
{
  Expr l = cmp.exp->left();
  if(!isOpX<BUGE>(cmp.exp))
    return false;
  if(!isBdivVar(l, var) || contains(cmp.r, var))
    return false;

  Expr tx = l->left();
  Expr y = l->right();
  int c = pow(2, bvSize) - 1;
  Expr prem = mk<BULT>(cmp.r, mk<BUDIV>(bv::bvnum(c, bvSize, efac), y));
  if(isOpX<TRUE>(m.eval(prem)))
  {
    Expr bvOne = bv::bvnum(1, bvSize, efac);
    Expr xPart =
      mk<BUGE>(tx, mk<BSUB>(mk<BMUL>(mk<BADD>(cmp.r, bvOne), y), bvOne));
    out.insert(prem);
    out.insert(xPart);
    return true;
  }
  return false;
}

// (tx div y) * a <= r ---> tx * a <= (r+1)*y -1 && d < (2^n - 1) div y
bool div3::apply(splitedCmp cmp, ExprSet &out)
{
  Expr l = cmp.exp->left();
  if(!isOpX<BULE>(cmp.exp))
    return false;
  if(!isBmulBdivVar(l, var) || contains(cmp.r, var))
    return false;

  Expr a, xdiv;
  if(bv::is_bvnum(l->right()))
  {
    a = l->right();
    xdiv = l->left();
  }
  else
  {
    a = l->left();
    xdiv = l->right();
  }

  int c = pow(2, bvSize) - 1;
  Expr bvOne = bv::bvnum(1, bvSize, efac);
  Expr prem1 =
    mk<BULT>(cmp.r, mk<BUDIV>(bv::bvnum(c, bvSize, efac), xdiv->right()));
  Expr mula = mkBmul(xdiv->left(), a);
  Expr prem2 = mk<BULE>(
    mula, mk<BSUB>(mk<BMUL>(mk<BADD>(cmp.r, bvOne), xdiv->right()), bvOne));
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

// (tx div y) * a >= r ---> tx * a >= (r+1)*y -1 && d < (2^n - 1) div y
bool div4::apply(splitedCmp cmp, ExprSet &out)
{
  Expr l = cmp.exp->left();
  if(!isOpX<BUGE>(cmp.exp))
    return false;
  if(!isBmulBdivVar(l, var) || contains(cmp.r, var))
    return false;

  Expr a, xdiv;
  if(bv::is_bvnum(l->right()))
  {
    a = l->right();
    xdiv = l->left();
  }
  else
  {
    a = l->left();
    xdiv = l->right();
  }

  int c = pow(2, bvSize) - 1;
  Expr bvOne = bv::bvnum(1, bvSize, efac);
  Expr prem1 =
    mk<BULT>(cmp.r, mk<BUDIV>(bv::bvnum(c, bvSize, efac), xdiv->right()));
  Expr mula = mkBmul(xdiv->left(), a);
  Expr prem2 = mk<BUGE>(
    mula, mk<BSUB>(mk<BMUL>(mk<BADD>(cmp.r, bvOne), xdiv->right()), bvOne));
  if(isOpX<TRUE>(m.eval(prem1)) && isOpX<TRUE>(m.eval(prem2)))
  {
    out.insert(prem1);
    out.insert(prem2);
    return true;
  }
  return false;
}

void normalizator::run_queue()
{
  while(!queue.empty())
  {
    // pop
    Expr curr = *queue.begin();
    queue.erase(curr);
    Expr lhs = curr->left();
    Expr rhs = curr->right();

    if(!contains(curr, var))
    {
      tmpOutSet.insert(curr);
    }
    else if(contains(rhs, var) && contains(lhs, var))
    {
      if(isOpX<BUGE>(curr))
        curr = bvFlipCmp(curr, lhs, rhs);
      CmpSplitter splitter(curr, var);
      ExprSet toQueue;
      bool res = false;

      while(splitter.canSplit())
      {
        splitedCmp s;
        splitter.split(s);
        for(auto r : both_rules)
        {
          res = r->apply(s, toQueue);
          if(res)
            break;
        }
        if(res)
          break;
      }

      if(!res)
      {
        // no rule is applicable, abort
        // TODO: backtracking
        set_failed();
        return;
      }
      else
      {
        for(auto e : toQueue)
          enqueue(e);
      }
    }
    else if(contains(lhs, var))
    {
      if(isBmulVar(lhs, var))
      {
        tmpOutSet.insert(curr);
        continue;
      }
      else if(isOpX<BNEG>(lhs))
      {
        // apply inv
        Expr next = bvReBuildCmp(curr, mk<BNEG>(rhs), lhs->left());
        if(!isOpX<TRUE>(m.eval(next)))
        {
          set_failed();
          return;
        }
        enqueue(next);
      }
      else
      {
        ExprSet toQueue;
        bool res = false;

        // firstly, try div rules
        splitedCmp s{curr, NULL, NULL, NULL};
        for(auto r : div_rules)
          res = r->apply(s, toQueue);

        CmpSplitter splitter(curr, var);
        while(splitter.canSplit() && !res)
        {
          splitter.split(s);
          for(auto r : add_rules)
            res = r->apply(s, toQueue);
        }

        if(!res)
        {
          // no rule is applicable, abort
          // TODO: backtracking
          set_failed();
          return;
        }
        else
        {
          for(auto e : toQueue)
            enqueue(e);
        }
      }
    }
    else if(contains(rhs, var))
    {
      enqueue(bvFlipCmp(curr, lhs, rhs));
    }
  }
}
