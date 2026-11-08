#!/usr/bin/env python3
"""Lossless grammar compression of the straight-line axiom emitters.

The original construction and its artifacts are left untouched. Grammar
terminals are calls to the original, closed constructor subroutines; no
relative break or continue instruction is moved across its scope.
"""
from collections import Counter
from functools import lru_cache
import argparse
import hashlib
import json
from pathlib import Path

from build import BerkeleyMachine, ROOT, save_machine
from formula import expanded_primitives
from reduction_formula import reuse_variables, proto_berkeley
from theory import axioms


def tokens(f):
    """The original emitter's exact postfix constructor-call sequence."""
    def var(v):
        return ("param:" + str(v[1])) if isinstance(v, tuple) else "var:" + str(v)
    op = f[0]
    if op == "hole": return ["param:" + str(f[1])]
    if op in ("eq", "mem"): return [var(f[1]), var(f[2]), op]
    if op in ("all", "ex"): return [var(f[1]), *tokens(f[2]), op]
    if op == "not": return [*tokens(f[1]), op]
    p, q = tokens(f[1]), tokens(f[2])
    if op in ("imp", "and"): return p + q + [op]
    if op == "or": return p + ["not"] + q + ["imp"]
    if op == "iff": return p + q + ["imp"] + q + p + ["imp", "and"]
    raise ValueError(op)


def repair(strings):
    """Deterministic pair grammar; each fresh nonterminal means two symbols."""
    strings = [list(s) for s in strings]
    rules = []
    while True:
        counts = Counter(pair for s in strings for pair in zip(s, s[1:]))
        if not counts: break
        # Insertion order is deterministic; no reliance on set/hash order.
        pair, count = max(counts.items(), key=lambda item: item[1])
        if count < 2: break
        code = len(rules)
        replacement_count = 0
        for k, s in enumerate(strings):
            new = []; i = 0
            while i < len(s):
                if i + 1 < len(s) and (s[i], s[i+1]) == pair:
                    new.append(code); i += 2; replacement_count += 1
                else:
                    new.append(s[i]); i += 1
            strings[k] = new
        rules.append(pair)
        # Even an overlapping aa pair is replaced at least once. Thus the
        # total residual length strictly decreases, giving termination.
        assert replacement_count
    return rules, strings


def lower_tokens(stream, level):
    """Expose safe, closed subroutine boundaries to the grammar compressor."""
    if level == "constructors": return stream
    def lower(t):
        if t.startswith("var:"):
            return ["push"] + ["inc"] * int(t[4:])
        if t.startswith("param:"): return [t]
        if t == "not": return ["push", "inc", "inc", "inc", "cons"]
        if t == "ex": return lower("not") + lower("all") + lower("not")
        if t == "and": return lower("not") + lower("imp") + lower("not")
        tag = {"eq": 0, "mem": 1, "imp": 2, "all": 4}[t]
        return ["cons", "push"] + ["inc"] * tag + ["cons"]
    return [x for t in stream for x in lower(t)]


class CompressedMachine(BerkeleyMachine):
    def __init__(self, axiom_list=None, start_search_at=0, primitive=False,
                 level="constructors"):
        super().__init__(axiom_list, start_search_at)
        self.primitive = primitive
        self.level = level
        self.streams = [lower_tokens(tokens(expanded_primitives(f) if primitive else f), level)
                        for _, f in self.axiom_list]
        self.rules, self.residuals = repair(self.streams)
        constructors = {"eq": "weq", "mem": "wel", "not": "wn",
                        "imp": "wim", "all": "wal", "ex": "wex", "and": "wa"}

        @lru_cache(None)
        def lower(symbol):
            if isinstance(symbol, int):
                return self.add_sequence(tuple(lower(c) for c in self.rules[symbol]))
            if symbol.startswith("var:"):
                return self.add_sequence(self.variable(int(symbol[4:])))
            if symbol.startswith("param:"):
                return self.add_sequence(getattr(self, "par" + symbol[6:])())
            if symbol == "push": return self.add_sequence(self.pushwff())
            if symbol == "cons": return self.add_sequence(self.cons())
            if symbol == "inc": return self.topwff.inc
            return self.add_sequence(getattr(self, constructors[symbol])())

        self.compressed = {
            f: self.add_sequence(tuple(lower(c) for c in s))
            for (_, f), s in zip(self.axiom_list, self.residuals)
        }

    def emit(self, f):
        if f in self.compressed:
            result = self.compressed[f]
            self.emitted[f] = result
            return result
        return super().emit(f)


def candidate_axioms(variant):
    result = axioms()
    if variant == "proto": result[-1] = ("Berkeley", proto_berkeley())
    if variant in ("alpha", "proto"):
        result[-1] = ("Berkeley", reuse_variables(result[-1][1]))
    return result


def quotient(table):
    """Largest exact transition congruence, including writes and directions."""
    part = [0] * len(table)
    while True:
        classes = {}; new = []
        for row in table:
            signature = tuple((w, d, -1 if q == -1 else part[q]) for w, d, q in row)
            new.append(classes.setdefault(signature, len(classes)))
        if new == part: break
        part = new
    result = [None] * len(set(part))
    for q, row in enumerate(table):
        target = [[w, d, -1 if n == -1 else part[n]] for w, d, n in row]
        if result[part[q]] is not None: assert result[part[q]] == target
        result[part[q]] = target
    assert part[0] == 0
    return result, part


def export(machine, out, variant):
    manifest = save_machine(machine, out)
    raw = json.loads((out / "machine.json").read_text())
    (out / "before-quotient.json").write_text(json.dumps(raw, separators=(",", ":")) + "\n")
    table, mapping = quotient(raw["table"])
    obj = raw | {"states": len(table), "table": table}
    (out / "machine.json").write_text(json.dumps(obj, separators=(",", ":")) + "\n")
    lines = ["#! start 0", "#! fill 0"]
    for q, row in enumerate(table):
        for b, (w, d, n) in enumerate(row):
            lines.append(f"{q} {b} {w} {d} {'HALT' if n == -1 else n}")
    (out / "machine.tm").write_text("\n".join(lines) + "\n")
    labels = json.loads((out / "state-labels.json").read_text())
    (out / "before-quotient-labels.json").write_text(json.dumps(labels, indent=2) + "\n")
    groups = [[] for _ in table]
    for name, q in zip(labels, mapping): groups[q].append(name)
    (out / "state-labels.json").write_text(json.dumps(groups, indent=2) + "\n")
    # The human-readable named table remains the raw compiler output.
    (out / "machine-labeled.tm").rename(out / "before-quotient-labeled.tm")
    certificate = {"variant": variant, "primitive": machine.primitive, "level": machine.level,
                   "rules": machine.rules, "residuals": machine.residuals,
                   "state_map": mapping}
    (out / "certificate.json").write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    manifest.update({"states": len(table), "before_quotient_states": len(raw["table"]),
        "baseline_states": 2845, "variant": variant,
        "baseline_machine_sha256": hashlib.sha256((ROOT / "artifacts/machine.json").read_bytes()).hexdigest(),
        "machine_json_sha256": hashlib.sha256((out / "machine.json").read_bytes()).hexdigest(),
        "grammar_rules": len(machine.rules), "tokens": sum(map(len, machine.streams)),
        "residual_tokens": sum(map(len, machine.residuals)),
        "files": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in sorted(out.iterdir()) if p.is_file() and p.name != "manifest.json"}})
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path)
    parser.add_argument("--variant", choices=("exact", "alpha", "proto"), default="alpha")
    parser.add_argument("--constructors", action="store_true", help="retain ex/and macro terminals")
    parser.add_argument("--level", choices=("constructors", "stack"), default="constructors")
    args = parser.parse_args()
    machine = CompressedMachine(candidate_axioms(args.variant), primitive=not args.constructors, level=args.level)
    manifest = export(machine, args.out or ROOT / "reductions" / args.variant, args.variant)
    print(json.dumps({"states": manifest["states"], "rules": len(machine.rules),
                      "tokens": sum(map(len, machine.streams)),
                      "residual_tokens": sum(map(len, machine.residuals)),
                      "sha256": manifest["machine_json_sha256"]}, indent=2))
