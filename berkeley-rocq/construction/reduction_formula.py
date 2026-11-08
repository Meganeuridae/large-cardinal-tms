"""Separately auditable formula transformations for the smaller candidates."""
from functools import lru_cache
from formula import *


def alpha_key(p, bound=()):
    """de Bruijn representation, including explicit free-variable markers."""
    def var(v):
        return ("bound", bound.index(v)) if v in bound else ("free", v)
    op = p[0]
    if op in ("eq", "mem"): return (op, var(p[1]), var(p[2]))
    if op in ("all", "ex"): return (op, alpha_key(p[2], (p[1],) + bound))
    if op == "hole": return p
    return (op, *(alpha_key(q, bound) for q in p[1:]))


def reuse_variables(f):
    """Reuse an outer variable name only when it is absent from this scope."""
    @lru_cache(None)
    def fv(p): return frozenset(free_variables(p))
    def go(p, env):
        op = p[0]
        if op in ("eq", "mem"): return (op, env[p[1]], env[p[2]])
        if op in ("all", "ex"):
            unavailable = {env[v] for v in fv(p)}
            v = 0
            while v in unavailable: v += 1
            return (op, v, go(p[2], env | {p[1]: v}))
        return (op, *(go(q, env) for q in p[1:]))
    assert not free_variables(f)
    result = go(f, {})
    assert alpha_key(result) == alpha_key(f)
    return result


def proto_berkeley():
    """Existence of a proto-Berkeley ordinal, using a moved ordinal witness.

    ZF proves equivalence with existence of a Berkeley cardinal by BKW,
    Theorem 3.3 and Remark 3.5(1). The full set-sized satisfaction encoding is
    retained. This mathematical reduction is not yet formalized in Rocq.
    """
    w, z0, z1, z2, z3, z4, f, d, m, e, sat, j, k = fresh(13)
    tags = (z0, z1, z2, z3, z4)
    moved = EIn(k, d, Not(rel(j, k, k)))
    local = exs((e, sat, j), And(environments(e, w, m),
        satisfaction(sat, e, f, w, m, tags),
        elementary(j, m, e, f, w, sat), moved))
    large_cardinal = Ex(d, And(ordinal(d),
        All(m, Imp(And(transitive(m), Mem(d, m)), local))))
    return compact(exs((w, *tags, f), And(omega(w), empty(z0),
        *(successor(tags[i+1], tags[i]) for i in range(4)),
        formulas(f, w, tags), large_cardinal)))
