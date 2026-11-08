"""Explicit axiom schemes; primitive variable/formula parameters share registers.

Logical schemes B1--B14 are S2 in Megill (1995), pp. 6--7 of the preprint.
All instances are enumerated; MP and generalization are the inference rules.
"""
from formula import *

def hole(n): return ("hole", n)
def meta(n): return ("param", n)

def logical_axioms():
    p, q, r = (hole(i) for i in (1, 2, 3))
    x, y, z = (meta(i) for i in (1, 2, 3))
    # In mixed schemes reserve param1/2 for variables and param3 for a formula.
    return [
        ("B1", Imp(p, Imp(q, p))),
        ("B2", Imp(Imp(p, Imp(q, r)), Imp(Imp(p, q), Imp(p, r)))),
        ("B3", Imp(Imp(Not(p), Not(q)), Imp(q, p))),
        ("B4", Imp(All(x, Imp(All(x, q), r)), Imp(All(x, q), All(x, r)))),
        ("B5", Imp(All(x, q), q)),
        ("B6", Imp(All(x, All(y, r)), All(y, All(x, r)))),
        ("B7", Imp(Not(q), All(x, Not(All(x, q))))),
        ("B8", Imp(Eq(x, y), Imp(Eq(x, z), Eq(y, z)))),
        ("B9", Imp(Not(All(x, Eq(x, y))), Imp(Not(All(x, Eq(x, z))),
                   Imp(Eq(y, z), All(x, Eq(y, z)))))),
        ("B10", Imp(All(x, Imp(Eq(x, y), All(x, r))), r)),
        ("B11", Imp(All(x, Eq(x, y)), Imp(All(x, r), All(y, r)))),
        ("B12", Imp(Eq(x, y), Imp(Mem(x, z), Mem(y, z)))),
        ("B13", Imp(Eq(x, y), Imp(Mem(z, x), Mem(z, y)))),
        ("B14", Imp(Not(All(x, Eq(x, y))), Imp(Not(All(x, Eq(x, z))),
                    Imp(Mem(y, z), All(x, Mem(y, z)))))),
    ]

def set_axioms():
    x, y, z, w = range(4)
    phi = hole(1)
    # Protect the bound output variable, exactly as in Metamath ax-rep.
    protected = All(y, phi)
    rep = Imp(All(w, Ex(y, All(z, Imp(protected, Eq(z, y))))),
              Ex(y, All(z, Iff(Mem(z, y),
                  Ex(w, And(Mem(w, x), protected))))))
    sep = Ex(y, All(z, Iff(Mem(z, y), And(Mem(z, x), protected))))
    return [
        ("Extensionality", Imp(All(z, Iff(Mem(z, x), Mem(z, y))), Eq(x, y))),
        ("Empty", Ex(x, All(y, Not(Mem(y, x))))),
        ("Pairing", Ex(z, All(w, Iff(Mem(w, z), Or(Eq(w, x), Eq(w, y)))))),
        ("Union", Ex(y, All(z, Iff(Mem(z, y), Ex(w, And(Mem(w, x), Mem(z, w))))))),
        ("Power", Ex(y, All(z, Iff(Mem(z, y), All(w, Imp(Mem(w, z), Mem(w, x))))))),
        ("Infinity", compact(Ex(x, inductive(x)))),
        ("Separation", sep),
        ("Replacement", rep),
        ("Foundation", foundation()),
    ]

def axioms(include_berkeley=True):
    result = logical_axioms() + set_axioms()
    if include_berkeley:
        result.append(("Berkeley", berkeley()))
    return result
