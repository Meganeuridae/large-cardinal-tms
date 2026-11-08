#!/usr/bin/env python3
"""Compile ZF + Berkeley proof search to a blank-tape binary Turing machine."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "vendor" / "wade"))
from TMBuilder import subroutine
from zf2 import ZF2
from formula import expanded_primitives, free_variables, sexpr, stats
from theory import axioms

class BerkeleyMachine(ZF2):
    def __init__(self, axiom_list=None, start_search_at=0):
        super().__init__()
        self.axiom_list = axioms() if axiom_list is None else axiom_list
        self.emitted = {}
        self.start_search_at = start_search_at
        if start_search_at: self.started = self.reg("started")

    def build_machine(self):
        # Formula subroutines already share their DAG. Wade's optional global
        # substring search is prohibitively slow on this larger DAG; omitting
        # that optimization leaves the register-machine semantics unchanged.
        self.main()
        self.reduce_to_cons()
        self.name_sequences()
        self.generate()
        self.tm.gc()
        self.tm.statename = self.tm.start

    @subroutine
    def variable(self, n):
        if n == 0:
            return self.pushwff()
        return [self.variable(n - 1), self.topwff.inc]

    def var(self, n):
        if isinstance(n, tuple):
            assert n[0] == "param"
            return getattr(self, "par" + str(n[1]))()
        return self.variable(n)

    def emit(self, f):
        """A shared decision-DAG subroutine for each syntactic subformula."""
        if f in self.emitted:
            return self.emitted[f]
        op = f[0]
        if op == "hole":
            seq = getattr(self, "par" + str(f[1]))()
        elif op in ("eq", "mem"):
            seq = [self.var(f[1]), self.var(f[2]),
                   self.weq() if op == "eq" else self.wel()]
        elif op in ("all", "ex"):
            seq = [self.var(f[1]), self.emit(f[2]),
                   self.wal() if op == "all" else self.wex()]
        elif op == "not":
            seq = [self.emit(f[1]), self.wn()]
        elif op in ("imp", "and"):
            seq = [self.emit(f[1]), self.emit(f[2]),
                   self.wim() if op == "imp" else self.wa()]
        elif op == "or":
            seq = [self.emit(f[1]), self.wn(), self.emit(f[2]), self.wim()]
        elif op == "iff":
            p, q = self.emit(f[1]), self.emit(f[2])
            seq = [p, q, self.wim(), q, p, self.wim(), self.wa()]
        else:
            raise ValueError(op)
        result = self.add_sequence(seq)
        self.emitted[f] = result
        return result

    @subroutine
    def main(self):
        # Same fair proof-tree enumeration and stack instructions as Wade ZF2.
        seq = [self.if_not_decnz(self.prooflist, [
            self.while_decnz(self.nextproof, [self.scratch1.inc, self.prooflist.inc]),
            self.while_decnz(self.scratch1, self.nextproof.inc), self.nextproof.inc])]
        if self.start_search_at:
            # Test-only seeded enumeration, still starting on a blank tape.
            seq[:0] = [self.if_not_decnz(self.started,
                         [self.nextproof.inc] * self.start_search_at), self.started.inc]
        for reg in (self.axiomcode, self.param1, self.param2, self.param3):
            seq.append(self.while_decnz(reg, ()))
        for reg in (self.axiomcode, self.param1, self.param2, self.param3):
            seq.extend([self.unpair(self.scratch1, self.scratch2, self.prooflist),
                        self.while_decnz(self.scratch2, self.prooflist.inc),
                        self.while_decnz(self.scratch1, reg.inc)])
        seq.append(self.v_0())
        modus_ponens = [
            self.axiomcode.inc,
            # Opcode 1: modus ponens, consuming two previously proved formulas.
            self.cparam(self.param3), self.cparam(self.param2),
            self.par3(), self.par1(), self.wim(),
            self.while_decnz(self.topwff, self.scratch2.inc),
            self.while_decnz(self.param2, [self.scratch1.inc, self.scratch3.inc]),
            self.while_decnz(self.scratch1, self.param2.inc),
            self.if_eq(self.scratch2, self.scratch3, [
                self.while_decnz(self.param1, [self.scratch1.inc, self.topwff.inc]),
                self.while_decnz(self.scratch1, self.param1.inc)]),
            self.select(),
        ]
        generalization = [self.axiomcode.inc, self.cparam(self.param3),
                          self.par1(), self.par3(), self.wal(), self.select()]
        cases = [[], modus_ponens, generalization]
        cases.extend([self.axiomcode.inc, self.emit(f), self.select()]
                     for _name, f in self.axiom_list)
        # Build only the selected candidate. A zero or out-of-range opcode
        # leaves the reflexive default theorem. The outer label also makes
        # this a finite switch, not an unbounded search within an iteration.
        def binary_sequence(xs):
            if len(xs) == 1: return xs[0]
            return (xs[0], binary_sequence(xs[1:]))
        # Resolve labels on literal binary trees. The inherited label helper
        # only supports binary trees, not a long list or a memoized open label.
        branches = [self.label("case", (
            (self.axiomcode.decnz, "break_case"),
            binary_sequence([*body, "break_dispatch"]))) for body in cases]
        seq.append(self.label("dispatch", binary_sequence(branches)))
        seq.append([
            self.topwff.decnz,
            self.label("if", [[self.topwff.decnz,
                [[self.topwff.inc, self.topwff.inc], "break_if"]], "halt"])
        ])
        return seq

def normalize(machine):
    """Number deterministically; send unused framework slots to a loop."""
    todo = [machine.start]
    numbers = {machine.start: 0}
    result = []
    unused = []
    for state in todo:
        row = []
        for bit in ("0", "1"):
            if (state, bit) not in machine.states:
                if state != "__diverge__": unused.append([state, bit])
                from tm import Transition
                t = Transition(bit, "R", "__diverge__")
            else:
                t = machine.states[state, bit]
            assert t.write in ("0", "1") and t.direction in ("L", "R")
            if t.nextstate == "halt":
                target = -1
            else:
                if t.nextstate not in numbers:
                    numbers[t.nextstate] = len(todo); todo.append(t.nextstate)
                target = numbers[t.nextstate]
            row.append([int(t.write), t.direction, target])
        result.append(row)
    return result, todo, unused

def save_machine(builder, out):
    out.mkdir(parents=True, exist_ok=True)
    builder.build_machine()
    table, labels, unused = normalize(builder.tm)
    obj = {"model": "one tape, bi-infinite, binary, blank 0, moves L/R",
           "start": 0, "halt": -1, "states": len(table), "table": table}
    encoded = (json.dumps(obj, separators=(",", ":")) + "\n").encode()
    (out / "machine.json").write_bytes(encoded)
    lines = ["#! start 0", "#! fill 0"]
    for q, row in enumerate(table):
        for bit, (write, direction, target) in enumerate(row):
            lines.append(f"{q} {bit} {write} {direction} {'HALT' if target == -1 else target}")
    (out / "machine.tm").write_text("\n".join(lines) + "\n")
    (out / "state-labels.json").write_text(json.dumps(labels, indent=2) + "\n")
    builder.tm.save(str(out / "machine-labeled.tm"))
    axiom_docs = []
    for opcode, (name, f) in enumerate(builder.axiom_list, 3):
        axiom_docs.append({"opcode": opcode, "name": name,
                           "formula": f, "statistics": stats(f) if name == "Berkeley" else None})
    (out / "axioms.json").write_text(json.dumps(axiom_docs, separators=(",", ":")) + "\n")
    (out / "axioms.sexpr").write_text("\n\n".join(
        f"; opcode {i}: {name}\n{sexpr(f)}"
        for i, (name, f) in enumerate(builder.axiom_list, 3)) + "\n")
    for name, f in builder.axiom_list:
        if name == "Berkeley":
            assert not free_variables(f)
            (out / "berkeley-pure.sexpr").write_text(sexpr(expanded_primitives(f)) + "\n")
    manifest = {"states": len(table), "symbols": 2, "tapes": 1,
                "start": 0, "blank": 0, "halting_transitions": sum(t[2] == -1 for row in table for t in row),
                "machine_json_sha256": hashlib.sha256(encoded).hexdigest(),
                "unused_framework_slots_sent_to_divergence": unused,
                "files": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(out.iterdir()) if p.is_file() and p.name != "manifest.json"},
                "upstream": {"repository": "https://github.com/Saoi2/turing_machine_explorer",
                             "commit": "08d539123f4369ae74a76619fdd391adc82de90c"},
                "verification": "written mathematical argument plus executable checks; not an end-to-end proof-assistant theorem"}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=ROOT / "artifacts")
    args = parser.parse_args()
    manifest = save_machine(BerkeleyMachine(), args.out)
    print(json.dumps({k: manifest[k] for k in ("states", "halting_transitions", "machine_json_sha256")}, indent=2))
