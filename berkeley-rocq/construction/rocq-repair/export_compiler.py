#!/usr/bin/env python3
"""Rebuild the guarded-distinction builder's binary source DAG and export an untrusted witness.

This runs the same source construction, pair reduction, and naming as
BerkeleyMachine.build_machine.  It independently replays the generated raw
machine and quotient against the saved artifacts before emitting any data.
Rocq, not this exporter, checks the emitted DAG's local compilation equations.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
from build import normalize
from reduce import quotient
from repair_logic import GuardedDistinctionMachine, DISTINCT


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generate():
    folder = ROOT / "repairs" / "guarded-distinction"
    recorded = json.loads((folder / "certificate.json").read_text())
    raw = json.loads((folder / "before-quotient.json").read_text())
    final = json.loads((folder / "machine.json").read_text())
    labels = json.loads((folder / "before-quotient-labels.json").read_text())
    builder = GuardedDistinctionMachine()
    assert json.loads(json.dumps(builder.rules)) == recorded["rules"]
    assert builder.residuals == recorded["residuals"]

    builder.main()

    # Capture the actual closed constructor roots and compression-rule roots
    # before reduce_to_cons mutates the saved sequence bodies.  Rocq separately
    # checks that the rules and residuals assemble these roots in the DAG.
    def memo_root(key):
        return builder.add_sequence(builder.memo[key])

    routine_names = ("pushwff", "cons", "weq", "wel", "wn", "wim", "wal",
                     "par1", "par2", "par3")
    routine_roots = {name: memo_root((name,)) for name in routine_names}
    token_roots = {0: routine_roots["weq"], 1: routine_roots["wel"],
                   2: routine_roots["wn"], 3: routine_roots["wim"],
                   4: routine_roots["wal"]}
    for n in range(1, 4):
        token_roots[8 + n] = routine_roots[f"par{n}"]
    for n in range(11):
        token_roots[16 + n] = memo_root(("variable", n))

    def token_number(name):
        if name.startswith("var:"):
            return 16 + int(name[4:])
        if name.startswith("param:"):
            return 8 + int(name[6:])
        return {"eq": 0, "mem": 1, "not": 2, "imp": 3, "all": 4}[name]

    rule_roots = []
    for number, (left, right) in enumerate(builder.rules):
        def resolve(symbol):
            if isinstance(symbol, int):
                assert 0 <= symbol < number
                return rule_roots[symbol]
            return token_roots[token_number(symbol)]
        rule_roots.append(builder.sequence_lookup[resolve(left), resolve(right)])
    residual_roots = [builder.compressed[formula] for _, formula in builder.axiom_list]

    builder.reduce_to_cons()
    builder.name_sequences()
    reachable = list(builder.reachable())
    assert sorted(reachable) == list(range(len(builder.sequences)))
    assert all(len(seq.seq) == 2 for seq in builder.sequences)
    assert len(set(seq.name for seq in builder.sequences)) == len(reachable)
    number = {label: q for q, label in enumerate(labels)}
    assert len(number) == len(labels)
    states = [recorded["state_map"][number[seq.name]] for seq in builder.sequences]
    registers = {name: i for i, name in enumerate(builder.registers)}
    assert len(registers) == 11

    def atom(value):
        if isinstance(value, int):
            assert 0 <= value < len(builder.sequences)
            return f"(SNode {value})"
        if value == "halt":
            return "SHalt"
        if value.startswith("_break."):
            return f"(SBreak {int(value.split('.')[1])})"
        if value.startswith("_continue."):
            return f"(SContinue {int(value.split('.')[1])})"
        fields = value.split(".")
        assert len(fields) == 3 and fields[0] == "3" and fields[1] in registers
        assert fields[2] in ("inc", "decnz"), value
        kind = "SInc" if fields[2] == "inc" else "SDec"
        return f"({kind} {registers[fields[1]]})"

    pairs = [(atom(a), atom(b)) for a, b in (seq.seq for seq in builder.sequences)]
    root = builder.find_seq("main().0")

    # Rebuild the whole table: this anchors the extraction to the same exact
    # generator invocation, rather than trusting a name-only association.
    builder.generate()
    builder.tm.gc()
    builder.tm.statename = builder.tm.start
    generated, generated_labels, _ = normalize(builder.tm)
    assert generated == raw["table"] and generated_labels == labels
    reduced, mapping = quotient(generated)
    assert reduced == final["table"] and mapping == recorded["state_map"]
    assert states[root] == 73

    lines = [
        "(* Generated source-DAG candidate, not a trusted compiler proof. *)",
        "From Stdlib Require Import Lists.List.",
        "From Berkeley Require Import CompilerSyntax.",
        "Import ListNotations.",
        f"Definition source_root : nat := {root}.",
        f"Definition source_guarded_root : nat := {builder.guarded_root}.",
        f"Definition source_plain_distinction_root : nat := {builder.compressed[DISTINCT]}.",
        *[f"Definition source_{name}_root : nat := {value}."
          for name, value in routine_roots.items()],
        "Definition source_token_roots : list (nat * nat) := [" +
        ";".join(f"({code},{node})" for code, node in sorted(token_roots.items())) + "].",
        "Definition source_rule_roots : list nat := [" + ";".join(map(str, rule_roots)) + "].",
        "Definition source_residual_roots : list nat := [" + ";".join(map(str, residual_roots)) + "].",
        "Definition source_graph : list source_pair := [",
        ";\n".join(f"  ({a}, {b})" for a, b in pairs),
        "].",
        "Definition compiler_map : list nat := [" + ";".join(map(str, states)) + "].",
    ]
    return "\n".join(lines) + "\n", {
        "source_pairs": len(pairs),
        "grammar_rule_roots": len(rule_roots),
        "grammar_residual_roots": len(residual_roots),
        "root": root,
        "guarded_root": builder.guarded_root,
        "plain_distinction_root": builder.compressed[DISTINCT],
        "machine_state_at_root": states[root],
        "raw_machine_sha256": digest(folder / "before-quotient.json"),
        "machine_sha256": digest(folder / "machine.json"),
        "reduction_certificate_sha256": digest(folder / "certificate.json"),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare with the existing export")
    args = parser.parse_args()
    output, report = generate()
    path = HERE / "CompilerData.v"
    if args.check:
        assert path.read_text() == output, "Repair CompilerData.v is stale"
    else:
        path.write_text(output)
    report["compiler_data_sha256"] = digest(path)
    print(json.dumps(report, indent=2))
