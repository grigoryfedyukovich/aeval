from pyparsing import Word, Group, Regex, Optional, OneOrMore, Forward, \
    ParseFatalException, Suppress, ZeroOrMore, dblQuotedString, removeQuotes, \
    hexnums, printables, alphanums, restOfLine
from base64 import b64decode
from collections import namedtuple, OrderedDict


def _verify_len(s, l, t):
    t = t[0]
    if t.len is not None:
        t1l = len(t[1])
        if t1l != t.len:
            raise ParseFatalException(
                s, l, "invalid data of length %d, expected %s" % (t1l, t.len))
    return t[1]


def _comb_b64d(t):
    return b64decode("".join(t))


# define punctuation literals
LPAR, RPAR, LBRK, RBRK, LBRC, RBRC, VBAR = map(Suppress, "()[]{}|")

decimal = Regex(r'0|[1-9]\d*').setParseAction(lambda t: int(t[0]))
hexadecimal = ("#" + OneOrMore(Word(hexnums)) + "#")\
                .setParseAction(lambda t: int("".join(t[1:-1]), 16))
bytes = Word(printables)
raw = Group(decimal("len") + Suppress(":") + bytes).setParseAction(_verify_len)
token = Word(alphanums + "-./_:*+=")

base64_ = Group(Optional(decimal | hexadecimal, default=None)("len") +
                VBAR +
                OneOrMore(Word(alphanums + "+/=")).setParseAction(_comb_b64d) +
                VBAR).setParseAction(_verify_len)

qString = Group(Optional(decimal, default=None)("len") +
                dblQuotedString.setParseAction(removeQuotes))
qString = qString.setParseAction(_verify_len)
simpleString = base64_ | raw | decimal | token | hexadecimal | qString

# extended definitions
decimal = Regex(r'-?0|[1-9]\d*').setParseAction(lambda t: int(t[0]))
real = Regex(r"[+-]?\d+\.\d*([eE][+-]?\d+)?")
real = real.setParseAction(lambda tokens: float(tokens[0]))
token = Word(alphanums + "-./_:*+=!<>")

simpleString = real | base64_ | raw | decimal | token | hexadecimal | qString

display = LBRK + simpleString + RBRK
string_ = Optional(display) + simpleString

sexp = Forward()
sexpList = Group(LPAR + ZeroOrMore(sexp) + RPAR)
sexp << (string_ | sexpList)
smtFile = OneOrMore(sexp).ignore(';' + restOfLine)


class ParseException(Exception):
    """An error parsing or interpreting the Horn-style SMT-LIB."""


CHCTask = namedtuple('CHCTask', 'vars rels rules')


CMD_STOPLIST = ['set-option', 'query']


def parse(fo, sorts=['Int', 'Bool']):
    sexprs = smtFile.parseFile(fo, parseAll=True).asList()
    v, r, rules = OrderedDict(), OrderedDict(), []
    for cmd in sexprs:
        assert len(cmd)
        if cmd[0] in CMD_STOPLIST:
            pass
        elif cmd[0] == 'declare-var':
            if cmd[1] in v:
                raise ParseException("re-declaration of var '%s'" % cmd[1])
            if cmd[2] not in sorts:
                raise ParseException("var '%s' had unknown sort '%s'" % (cmd[1], cmd[2]))
            v[cmd[1]] = cmd[2]
        elif cmd[0] == 'declare-rel':
            if cmd[1] in r:
                raise ParseException("re-declaration of rel '%s'" % cmd[1])
            for s in cmd[2]:
                if s not in sorts:
                    raise ParseException("rel '%s' had unknown sort '%s'" % (cmd[1], s))
            r[cmd[1]] = cmd[2]
        elif cmd[0] == 'rule':
            rules.append(cmd[1:])
        elif cmd[0] == 'set-logic':
            assert cmd[1].lower() == 'horn'
        else:
            raise ParseException("unrecogized '%s'" % cmd[0])
    return CHCTask(v, r, rules)
