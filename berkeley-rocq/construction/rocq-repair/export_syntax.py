#!/usr/bin/env python3
"""Export repaired formulas and grammar as untrusted Rocq syntax data."""
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
from formula import expanded_primitives


def tuples(x):
    return tuple(map(tuples, x)) if isinstance(x, list) else x


def var(v):
    return f"(P {v[1]})" if isinstance(v, tuple) else f"(V {v})"


def form(p):
    op = p[0]
    if op in ("eq", "mem"):
        return f"(Atom {'true' if op == 'mem' else 'false'} {var(p[1])} {var(p[2])})"
    if op == "hole": return f"(Hole {p[1]})"
    if op == "not": return f"(Neg {form(p[1])})"
    if op == "imp": return f"(Imp {form(p[1])} {form(p[2])})"
    if op == "all": return f"(All {var(p[1])} {form(p[2])})"
    raise ValueError(op)


def symbol(t):
    if isinstance(t, int): return f"(Reference {t})"
    if t.startswith("var:"): n = 16 + int(t[4:])
    elif t.startswith("param:"): n = 8 + int(t[6:])
    else: n = {"eq": 0, "mem": 1, "not": 2, "imp": 3, "all": 4}[t]
    return f"(Terminal {n})"


def generate():
    folder = ROOT / "repairs/guarded-distinction"
    axioms = json.loads((folder / "axioms.json").read_text())
    cert = json.loads((folder / "certificate.json").read_text())
    lines = ["(* Repaired syntax and grammar, checked against source and original syntax separately. *)",
             "From Stdlib Require Import Lists.List.", "From Berkeley Require Import Syntax SyntaxData.",
             "Import ListNotations."]
    lines.append("Definition repair_axioms : list formula := [" +
        ";\n".join(form(expanded_primitives(tuples(a["formula"]))) for a in axioms) + "].")
    lines.append("Definition candidate_axioms := Berkeley.SyntaxData.candidate_axioms.")
    lines.append("Definition rules : list (symbol * symbol) := [" +
        ";\n".join(f"({symbol(a)}, {symbol(b)})" for a,b in cert["rules"]) + "].")
    lines.append("Definition residuals : list (list symbol) := [" +
        ";\n".join("["+";".join(map(symbol, xs))+"]" for xs in cert["residuals"]) + "].")
    path = HERE / "SyntaxData.v"
    path.write_text("\n".join(lines)+"\n")
    return {"axioms": len(axioms), "rules": len(cert["rules"]), "residuals": len(cert["residuals"]),
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


if __name__ == "__main__":
    print(json.dumps(generate(), indent=2))
