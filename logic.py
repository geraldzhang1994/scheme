"""This module implements a declarative logic language using Scheme syntax.

Based on scmlog by Paul Hilfinger and the logic programming example in SICP.

All valid logic expressions are Scheme lists.  Valid forms include:

(fact ...):  Assert a consequent, followed by zero or more hypotheses
(query ...): Query zero or more relations simultaneously
(load PATH): Load a .logic file by evaluating its expressions
"""

from scheme import Frame
from scheme_reader import Pair, nil
from scheme_primitives import *
from ucb import main, trace

import scheme
import scheme_reader

facts = []

#############
# Inference #
#############

def do_query(clauses):
    """Return all bindings that simultaneously satisfy clauses."""
    for env in query(clauses, Frame(None), 0):
        yield [(v, bind(v, env)) for v in get_vars(clauses)]

DEPTH_LIMIT = 20
def query(clauses, env, depth):
    """Search for an application of rules to establish all the CLAUSES,
    non-destructively extending the unifier ENV.  Limit the search to
    the nested application of DEPTH rules."""
    if clauses is nil:
        yield env
    elif DEPTH_LIMIT is None or depth <= DEPTH_LIMIT:
        for fact in facts:
            fact = label(fact, get_unique_id())  # Rename variables
            env_head = Frame(env)
            if unify(fact.first, clauses.first, env_head):
                for env_rule in query(fact.second, env_head, depth+1):
                    for result in query(clauses.second, env_rule, depth+1):
                        yield result

def unify(e, f, env):
    """Destructively extend ENV so as to unify (make equal) e and f, returning
    True if this succeeds and False otherwise.  ENV may be modified in either
    case (its existing bindings are never changed)."""
    e = lookup(e, env)
    f = lookup(f, env)
    if e == f:
        return True
    elif isvar(e):
        env.define(e, f)
        return True
    elif isvar(f):
        env.define(f, e)
        return True
    elif scheme_atomp(e) or scheme_atomp(f):
        return False
    else:
        return unify(e.first, f.first, env) and unify(e.second, f.second, env)

################
# Environments #
################

def lookup(sym, env):
    """Look up a symbol repeatedly until it is fully resolved."""
    try:
        return lookup(env.lookup(sym), env)
    except:
        return sym

def bind(expr, env):
    """Bind all variables to their exprues in EXPR."""
    if scheme_symbolp(expr):
        resolved = lookup(expr, env)
        if expr != resolved:
            return bind(resolved, env)
        else:
            return expr
    elif scheme_pairp(expr):
        return Pair(bind(expr.first, env), bind(expr.second, env))
    else:
        return expr

#####################
# Support functions #
#####################

def get_vars(expr):
    """Return all logical vars in EXPR as a list."""
    if isvar(expr):
        return [expr]
    elif scheme_pairp(expr):
        vs = get_vars(expr.first)
        for v in get_vars(expr.second):
            if v not in vs:
                vs.append(v)
        return vs
    else:
        return []

IDENTIFIER = 0
def get_unique_id():
    """Return a unique identifier."""
    global IDENTIFIER
    IDENTIFIER += 1
    return IDENTIFIER

def label(expr, n):
    """Label all variables in EXPR with an identifier N."""
    if isvar(expr):
        return expr + '_' + str(n)
    elif scheme_pairp(expr):
        return Pair(label(expr.first, n), label(expr.second, n))
    else:
        return expr

def isvar(symbol):
    """Return whether SYMBOL is a logical variable."""
    return scheme_symbolp(symbol) and symbol.startswith("?")

##################
# User Interface #
##################

def process_input(expr, env):
    """Process an input EXPR, which may be a fact or query."""
    assert scheme_listp(expr)
    if expr.first in ("fact", "!"):
        facts.append(expr.second)
    elif expr.first in ("query", "?"):
        results = do_query(expr.second)
        success = False
        for result in results:
            if not success:
                print('Success!')
            success = True
            print("\t".join("{0}: {1}".format(k[1:], v) for k, v in result))
        if not success:
            print('Failed.')

    elif expr.first == "load":
        scheme.scheme_load(expr.second.first, env)
    else:
        print("Please provide a fact or query.")

@main
def run(*argv):
    scheme_reader.buffer_input.__defaults__ = ('logic> ',)
    scheme_reader.buffer_lines.__defaults__ = ('logic> ',)
    scheme.scheme_eval = process_input
    scheme.run(*argv)
