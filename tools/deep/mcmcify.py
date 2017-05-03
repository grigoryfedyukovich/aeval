#!/usr/bin/env python
from __future__ import print_function
import os
import sys
import argparse
import smtlibparser
from xml.dom import minidom
try:
    import xml.etree.cElementTree as ET
except ImportError:
    import xml.etree.ElementTree as ET


TOK_MAP = {
    '=': 'EQ',
    'not': 'NOT',
    'and': 'AND',
    'or': 'OR',
    '>=': 'GE',
    '>': 'GT',
    '<=': 'LE',
    '<': 'LT',
    '+': 'PLUS',
    '-': 'MINUS'
}


def dissolve(x):
    assert len(x) == 1
    return x[0]


def negate(rule):
    assert rule[0] != '=>'
    if rule[0] == 'not':
        return normalize(rule[1])
    else:
        return normalize(["not", rule])


def listmap(root, fn):
    if not isinstance(root, list):
        return root
    return fn([listmap(x, fn) for x in root])


def normalize(rule):
    """Returns `rule` as a disjunction of conjunctions.

    Simply wraps, or if a negation, applies de Morgan's. If
    already a positive disjunction, return `rule`.

    Note that this can result in a disjunction with one clause,
    e.g. `(or (= 1 a))`.
    """
    assert not deephas(rule, '=>')
    while 1:
        new_rule = listmap(rule, _inner_norm)
        if new_rule[0] != 'or':
            new_rule = ["or", new_rule]
        if new_rule == rule:
            return new_rule
        rule = new_rule


def _inner_norm(rule):
    if rule[0] == 'not' and rule[1][0] == 'not':
        return rule[1][1]
    elif rule[0] in ['or', 'and'] and rule[1][0] == rule[0]:
        return [rule[0]] + rule[1][1:]
    elif rule[0] == 'not' and rule[1][0] in ('and', 'or'):  # de Morgan's
        new_op = 'and'
        if rule[1][0] == 'and':
            new_op = 'or'
        return [new_op] + [["not"] + [x] for x in rule[1][1:]]
    else:
        return rule


def deephas(objs, name):
    if objs == name:
        return True
    try:
        if not isinstance(objs, basestring):
            for x in objs:
                if deephas(x, name):
                    return True
    except TypeError:
        pass
    return False


def _yank_rule(rules, match_fn):
    tgt, remaining = None, []
    for rule in rules:
        assert rule[0] == '=>'
        if match_fn(rule):
            # TODO: assert invariant has noly variables as terms
            assert tgt is None, "already set to %s" % str(tgt)
            tgt = rule
        else:
            remaining.append(rule)
    assert tgt
    return tgt, remaining


def get_good(rules, inv_name):
    def match_good(rule):
        return not deephas(rule[1], inv_name) and rule[2][0] == inv_name
    good, remaining = _yank_rule(rules, match_good)
    return good[1], good[2][1:], remaining


def get_bad(rules, inv_name):
    def match_bad(rule):
        return deephas(rule[1], inv_name) and not deephas(rule[2], inv_name)
    bad, remaining = _yank_rule(rules, match_bad)
    return bad[1], remaining


def get_implication(rules, inv_name):
    def match_impl(rule):
        return deephas(rule[1], inv_name) and deephas(rule[2], inv_name)
    r, remaining = _yank_rule(rules, match_impl)
    assert r[0] == '=>'
    return (r[1], r[2]), remaining


def pop_rel(expr, name):
    """Removes mention of relation named `name`, returning (expr, args).

    Raises Exception if relation is mentioned more than once in `expr`.
    """
    if isinstance(expr, basestring) or isinstance(expr, int):
        return (expr, None)

    # Recur first
    new_expr, subargs = [expr[0]], None
    for e in expr[1:]:
        s, a = pop_rel(e, name)
        if a:
            assert subargs is None, "multiple mentions in expr"
            subargs = a
        new_expr.append(s)

    # Propogate
    if new_expr[0] == name:
        return (None, new_expr[1:])
    elif len(new_expr) == 2 and new_expr[1] is None:
        return (None, subargs)
    else:
        return ([e for e in new_expr if e is not None], subargs)


def expr_to_xml(parent, expr):
    if isinstance(expr, list):
        e = ET.SubElement(parent, TOK_MAP[expr[0]])
        for sube in expr[1:]:
            expr_to_xml(e, sube)
        return e

    try:
        int(expr)
    except ValueError:
        pass
    else:
        e = ET.SubElement(parent, "INT")
        e.text = str(expr)
        return e

    e = ET.SubElement(parent, "VAR")
    e.text = expr
    return e


def names_to_vardecls(parent, names, rootname='VARDECLS'):
    top_var_root = ET.SubElement(parent, rootname)
    for var_name in names:
        vr = ET.SubElement(top_var_root, "VAR")
        vr.text = var_name


def translate(chctask, xmlfo, configfo):
    assert len(chctask.rels) == 2
    assert not deephas(chctask.rels, 'forall')

    # TODO: Need to lift integers out of relations

    # Guess invariant name
    # TODO: Should be only one rel with any params
    inv_name = None
    for c in ['itp', 'inv']:
        if deephas(chctask.rels, c):
            inv_name = c
    assert inv_name

    # Parse, break apart, negate, and sanitize.
    translated = [dissolve(r) for r in chctask.rules]
    good, good_args, translated = get_good(translated, inv_name)
    (impl_src, impl_dest), translated = get_implication(translated, inv_name)
    impl_src, impl_src_args = pop_rel(impl_src, inv_name)
    impl_dest, impl_dest_args = pop_rel(impl_dest, inv_name)
    bad, translated = get_bad(translated, inv_name)
    bad, bad_args = pop_rel(bad, inv_name)
    assert len(translated) == 0, "extra rules were present"

    # Start building the first.xml file for MCMC. Do the header.
    outtree = ET.ElementTree(ET.Element("VC"))
    top_fun_root = ET.SubElement(outtree.getroot(), "FUNDECLS")
    for (rel_name, args) in chctask.rels.items():
        if rel_name == 'fail':
            continue
        vr = ET.SubElement(top_fun_root, "FUNDECL")
        ar_r = ET.SubElement(vr, "ARITY")
        ar_r.text = str(len(args))
        name_r = ET.SubElement(vr, "NAME")
        name_r.text = rel_name
    names_to_vardecls(outtree.getroot(), chctask.vars)

    # Convert rules to ASSERTs
    good_assert = ET.SubElement(outtree.getroot(), "ASSERT", type="good 0")
    names_to_vardecls(good_assert, good_args)
    expr_to_xml(good_assert, negate(good))

    inv_assert = ET.SubElement(outtree.getroot(), "ASSERT", type="0 0")
    names_to_vardecls(inv_assert, impl_src_args, rootname='BEFORE')
    names_to_vardecls(inv_assert, impl_dest_args, rootname='AFTER')
    expr_to_xml(inv_assert, negate(impl_src))
    assert impl_dest is None

    bad_assert = ET.SubElement(outtree.getroot(), "ASSERT", type="bad 0")
    names_to_vardecls(bad_assert, bad_args)
    expr_to_xml(bad_assert, negate(bad))

    def prettify_xml(elem):
        """Return a pretty-printed XML string for the Element.
        """
        rough_string = ET.tostring(elem, 'utf-8')
        reparsed = minidom.parseString(rough_string)
        return reparsed.toprettyxml(indent="  ")
    print(prettify_xml(outtree.getroot()), file=xmlfo)

    # Build config
    # TODO: Re-read paper; figure out what these hyperparams mean:
    #       http://theory.stanford.edu/~aiken/publications/papers/cav14.pdf
    all_ints = set(int(x.text) for x in outtree.iter('INT'))
    all_ints = all_ints.union(set(-x for x in all_ints))
    print("DISJUNCTS", file=configfo)
    print("10", file=configfo)
    print("CONJUNCTS", file=configfo)
    print("10", file=configfo)
    print("COEFFICIENT BAG", file=configfo)
    print("3", file=configfo)
    print("-1 0 1", file=configfo)
    print("IMMEDIATE BAG", file=configfo)
    print(str(len(all_ints)), file=configfo)
    print(" ".join(str(x) for x in sorted(all_ints)), file=configfo)
    print("NOP PERCENT", file=configfo)
    print("90", file=configfo)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("SMTPATH")
    parser.add_argument("XMLOUT")
    parser.add_argument("CONFIGOUT")
    args = parser.parse_args()

    for p in [args.XMLOUT, args.CONFIGOUT]:
        if os.path.exists(p):
            print("'%s' already exists" % p, file=sys.stderr)
            return 1

    try:
        with open(args.SMTPATH, 'r') as smtfo, open(args.XMLOUT, 'w') as xmlfo, open(args.CONFIGOUT, 'w') as configfo:
            translate(smtlibparser.parse(smtfo), xmlfo, configfo)
    finally:
        for p in [args.XMLOUT, args.CONFIGOUT]:
            if os.stat(p).st_size == 0:
                os.remove(p)


if __name__ == '__main__':
    main()
