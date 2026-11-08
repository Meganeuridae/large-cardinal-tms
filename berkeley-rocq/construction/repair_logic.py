#!/usr/bin/env python3
"""Experimental guarded-distinction repair; no formal TM theorem for it yet.

The original 1385-state candidate and its source remain untouched. A new
opcode emits not forall x (x=y) only if the two numeric variable names differ;
otherwise it returns the existing reflexivity/default code 0.
"""
import argparse
import hashlib
import json
from pathlib import Path

from build import ROOT
from reduce import CompressedMachine, candidate_axioms, export
from formula import Not, All, Eq

DISTINCT = Not(All(("param", 1), Eq(("param", 1), ("param", 2))))

class GuardedDistinctionMachine(CompressedMachine):
    def __init__(self, start_search_at=0):
        super().__init__(candidate_axioms("alpha") + [("GuardedDistinction", DISTINCT)],
                         start_search_at=start_search_at, primitive=True)
        self.guarded_root = None

    def emit(self, f):
        plain = super().emit(f)
        if f != DISTINCT:
            return plain
        # Every emitter restores scratch1/scratch2 to 0; scratch3 is also
        # zero at dispatch entry. if_eq drains both comparison registers.
        # Equality must reject D(x,x), so replace the emitted top with 0.
        guarded = self.add_sequence([
            plain,
            self.while_decnz(self.param1, [self.scratch1.inc, self.scratch2.inc]),
            self.while_decnz(self.scratch1, self.param1.inc),
            self.while_decnz(self.param2, [self.scratch1.inc, self.scratch3.inc]),
            self.while_decnz(self.scratch1, self.param2.inc),
            self.if_eq(self.scratch2, self.scratch3, [self.while_decnz(self.topwff, ())]),
        ])
        self.guarded_root = guarded
        self.emitted[f] = guarded
        return guarded


def build(out):
    machine = GuardedDistinctionMachine()
    report = export(machine, out, "guarded-distinction-experimental")
    axiom_path = out / "axioms.json"
    axioms = json.loads(axiom_path.read_text())
    assert axioms[-1]["name"] == "GuardedDistinction" and axioms[-1]["opcode"] == 27
    axioms[-1]["guard"] = "param1 != param2"
    axioms[-1]["rejected_value"] = 0
    axiom_path.write_text(json.dumps(axioms, separators=(",", ":")) + "\n")
    sexpr = out / "axioms.sexpr"
    sexpr.write_text(sexpr.read_text().replace("; opcode 27: GuardedDistinction",
        "; opcode 27: GuardedDistinction [only if param1 != param2; otherwise return code 0]"))
    report["verification"] = "experimental executable construction and exact transition quotient; NOT covered by the 1385-state Rocq machine theorem"
    report["guarded_axioms"] = {"27": {"condition": "param1 != param2", "failure_result": 0}}
    report["repair_source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report["files"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in sorted(out.iterdir()) if p.is_file() and p.name != "manifest.json"}
    (out / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=ROOT / "repairs" / "guarded-distinction")
    args = parser.parse_args()
    report = build(args.out)
    print(json.dumps({k: report[k] for k in
        ("states", "before_quotient_states", "grammar_rules", "tokens", "residual_tokens", "machine_json_sha256", "verification")}, indent=2))
