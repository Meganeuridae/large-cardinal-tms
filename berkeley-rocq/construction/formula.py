"""Capture-free construction of a finite pure-membership Berkeley sentence.

All macros expand to first-order formulas. No satisfaction predicate, class,
oracle, or schematic elementarity assertion survives expansion.
"""
from itertools import count
from functools import reduce

_names = count(100)
def fresh(n=1):
    vs = tuple(next(_names) for _ in range(n))
    return vs[0] if n == 1 else vs

def Eq(x, y): return ("eq", x, y)
def Mem(x, y): return ("mem", x, y)
def Not(p): return ("not", p)
def Imp(p, q): return ("imp", p, q)
def Iff(p, q): return ("iff", p, q)
def And(*ps): return reduce(lambda p, q: ("and", p, q), ps)
def Or(*ps): return reduce(lambda p, q: ("or", p, q), ps)
def All(v, p): return ("all", v, p)
def Ex(v, p): return ("ex", v, p)
def alls(vs, p): return reduce(lambda p, v: All(v, p), reversed(vs), p)
def exs(vs, p): return reduce(lambda p, v: Ex(v, p), reversed(vs), p)
def AIn(v, a, p): return All(v, Imp(Mem(v, a), p))
def EIn(v, a, p): return Ex(v, And(Mem(v, a), p))

def empty(a):
    x = fresh()
    return All(x, Not(Mem(x, a)))

def subset(a, b):
    x = fresh()
    return AIn(x, a, Mem(x, b))

def singleton(a, x):
    z = fresh()
    return All(z, Iff(Mem(z, a), Eq(z, x)))

def doubleton(a, x, y):
    z = fresh()
    return All(z, Iff(Mem(z, a), Or(Eq(z, x), Eq(z, y))))

def pair(p, x, y):
    """p = {{x},{x,y}}, with fresh witnesses."""
    u, v = fresh(2)
    return exs((u, v), And(singleton(u, x), doubleton(v, x, y),
                           doubleton(p, u, v)))

def rel(r, x, y):
    p = fresh()
    return Ex(p, And(pair(p, x, y), Mem(p, r)))

def node2(p, tag, x, y):
    q = fresh()
    return Ex(q, And(pair(q, x, y), pair(p, tag, q)))

def transitive(a):
    x, y = fresh(2)
    return AIn(x, a, AIn(y, x, Mem(y, a)))

def ordinal(a):
    x, y = fresh(2)
    return And(transitive(a), AIn(x, a, AIn(y, a,
                       Or(Mem(x, y), Eq(x, y), Mem(y, x)))))

def function(f, a, b):
    """Exact graph of a total single-valued function a -> b."""
    p, x, y, z = fresh(4)
    return And(
        AIn(p, f, EIn(x, a, EIn(y, b, pair(p, x, y)))),
        AIn(x, a, EIn(y, b, And(rel(f, x, y),
                  AIn(z, b, Imp(rel(f, x, z), Eq(z, y)))))))

def bijection(f, a, b):
    x, y, z = fresh(3)
    return And(function(f, a, b),
        AIn(y, b, EIn(x, a, rel(f, x, y))),
        AIn(x, a, AIn(z, a, AIn(y, b,
             Imp(And(rel(f, x, y), rel(f, z, y)), Eq(x, z))))))

def cardinal(d):
    a, f = fresh(2)
    return And(ordinal(d), AIn(a, d, Not(Ex(f, bijection(f, a, d)))))

def successor(y, x):
    z = fresh()
    return All(z, Iff(Mem(z, y), Or(Mem(z, x), Eq(z, x))))

def inductive(a):
    e, x, y = fresh(3)
    return And(EIn(e, a, empty(e)), AIn(x, a, EIn(y, a, successor(y, x))))

def omega(w):
    a = fresh()
    return And(inductive(w), All(a, Imp(inductive(a), subset(w, a))))

def closed_formulas(f, w, tags):
    """Closure under eq, mem, negation, implication, and named forall."""
    eq, mem, neg, imp, all_ = tags
    u, v, p, q, r = fresh(5)
    return And(
        AIn(u, w, AIn(v, w, EIn(p, f, node2(p, eq, u, v)))),
        AIn(u, w, AIn(v, w, EIn(p, f, node2(p, mem, u, v)))),
        AIn(p, f, EIn(q, f, pair(q, neg, p))),
        AIn(p, f, AIn(q, f, EIn(r, f, node2(r, imp, p, q)))),
        AIn(u, w, AIn(p, f, EIn(q, f, node2(q, all_, u, p)))))

def formulas(f, w, tags):
    g = fresh()
    return And(closed_formulas(f, w, tags),
               All(g, Imp(closed_formulas(g, w, tags), subset(f, g))))

def environments(e, w, m):
    s = fresh()
    return All(s, Iff(Mem(s, e), function(s, w, m)))

def update(s, t, u, w, m):
    """Environments s,t agree except possibly at u."""
    v, x = fresh(2)
    return AIn(v, w, Or(Eq(v, u), AIn(x, m,
                                  Iff(rel(s, v, x), rel(t, v, x)))))

def satisfaction(sat, e, f, w, m, tags):
    """Tarski recursion on the set f of all finite formula trees.

    Quantifiers range over the complete set e of environments omega -> m.
    No choice is required: each finite tuple extends to a constant-tail
    environment, and changing one coordinate is a finite replacement.
    """
    eq, mem, neg, imp, all_ = tags
    s, t, u, v, x, y, p, q, r = fresh(9)
    atom_eq = AIn(u, w, AIn(v, w, AIn(x, m, AIn(y, m, All(p,
        Imp(And(rel(s, u, x), rel(s, v, y), node2(p, eq, u, v)),
            Iff(rel(sat, p, s), Eq(x, y))))))))
    atom_mem = AIn(u, w, AIn(v, w, AIn(x, m, AIn(y, m, All(p,
        Imp(And(rel(s, u, x), rel(s, v, y), node2(p, mem, u, v)),
            Iff(rel(sat, p, s), Mem(x, y))))))))
    negation = AIn(p, f, All(q, Imp(pair(q, neg, p),
                                  Iff(rel(sat, q, s), Not(rel(sat, p, s))))))
    implication = AIn(p, f, AIn(q, f, All(r,
        Imp(node2(r, imp, p, q),
            Iff(rel(sat, r, s), Imp(rel(sat, p, s), rel(sat, q, s)))))))
    universal = AIn(u, w, AIn(p, f, All(q,
        Imp(node2(q, all_, u, p), Iff(rel(sat, q, s),
            AIn(t, e, Imp(update(s, t, u, w, m), rel(sat, p, t))))))))
    return AIn(s, e, And(atom_eq, atom_mem, negation, implication, universal))

def image_environment(j, s, t, w, m):
    u, x, y = fresh(3)
    return AIn(u, w, AIn(x, m, AIn(y, m,
        Imp(And(rel(s, u, x), rel(j, x, y)), rel(t, u, y)))))

def elementary(j, m, e, f, w, sat):
    p, s, t = fresh(3)
    return And(function(j, m, m),
        AIn(p, f, AIn(s, e, AIn(t, e,
            Imp(image_environment(j, s, t, w, m),
                Iff(rel(sat, p, s), rel(sat, p, t)))))))

def berkeley():
    w, z0, z1, z2, z3, z4, f, d, m, e, sat, eta, j, k, a = fresh(15)
    tags = (z0, z1, z2, z3, z4)
    crit = And(Mem(k, d), Mem(eta, k), Not(rel(j, k, k)),
               AIn(a, k, rel(j, a, a)))
    witnesses = AIn(eta, d, exs((j, k),
                    And(crit, elementary(j, m, e, f, w, sat))))
    local = exs((e, sat), And(environments(e, w, m),
                             satisfaction(sat, e, f, w, m, tags), witnesses))
    large_cardinal = Ex(d, And(cardinal(d), Mem(w, d),
                        All(m, Imp(And(transitive(m), Mem(d, m)), local))))
    return compact(exs((w, *tags, f), And(omega(w), empty(z0),
        *(successor(tags[i+1], tags[i]) for i in range(4)),
        formulas(f, w, tags), large_cardinal)))

def foundation():
    a, x, y = fresh(3)
    return compact(All(a, Imp(Ex(x, Mem(x, a)),
        EIn(x, a, AIn(y, x, Not(Mem(y, a)))))))

def compact(f):
    """Alpha-rename bound variables to lexical-depth numbers; reject free vars."""
    def go(p, env):
        op = p[0]
        if op in ("eq", "mem"):
            return (op, env[p[1]], env[p[2]])
        if op in ("all", "ex"):
            v = len(env)
            assert p[1] not in env, "a macro captured an already-bound variable"
            return (op, v, go(p[2], env | {p[1]: v}))
        return (op, *(go(q, env) for q in p[1:]))
    return go(f, {})

def free_variables(p, bound=frozenset()):
    op = p[0]
    if op in ("eq", "mem"):
        return set(p[1:]) - bound
    if op in ("all", "ex"):
        return free_variables(p[2], bound | {p[1]})
    if op == "hole": return set()  # schemata only
    return set().union(*(free_variables(q, bound) for q in p[1:]))

def expanded_primitives(p):
    """Eliminate all abbreviations to eq, mem, not, imp, all."""
    op = p[0]
    if op in ("eq", "mem", "hole"): return p
    if op == "all": return All(p[1], expanded_primitives(p[2]))
    if op == "ex": return Not(All(p[1], Not(expanded_primitives(p[2]))))
    if op == "not": return Not(expanded_primitives(p[1]))
    a, b = map(expanded_primitives, p[1:])
    if op == "imp": return Imp(a, b)
    if op == "and": return Not(Imp(a, Not(b)))
    if op == "or": return Imp(Not(a), b)
    if op == "iff": return Not(Imp(Imp(a, b), Not(Imp(b, a))))
    raise ValueError(op)

def sexpr(p):
    if not isinstance(p, tuple): return str(p)
    return "(" + " ".join(map(sexpr, p)) + ")"

def stats(p):
    nodes = set()
    count_nodes = 0
    maxvar = -1
    def go(q):
        nonlocal count_nodes, maxvar
        count_nodes += 1
        nodes.add(q)
        if q[0] in ("eq", "mem"):
            maxvar = max(maxvar, *q[1:])
        elif q[0] in ("all", "ex"):
            maxvar = max(maxvar, q[1]); go(q[2])
        elif q[0] != "hole":
            for r in q[1:]: go(r)
    go(p)
    return {"nodes": count_nodes, "distinct_subformulas": len(nodes),
            "variable_names": maxvar + 1}
