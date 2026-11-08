#!/usr/bin/env python3
"""Export the exact repaired tables and old/framework label correspondences.

This produces untrusted inputs for separate Rocq checks. It does not modify
the original candidate, its build directory, or the repair artifacts.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / "reductions" / "alpha"
REPAIR = ROOT / "repairs" / "guarded-distinction"


def read(folder, name):
    return json.loads((folder / name).read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generate():
    raw = read(REPAIR, "before-quotient.json")
    repaired = read(REPAIR, "machine.json")
    certificate = read(REPAIR, "certificate.json")
    old = read(OLD, "machine.json")
    old_labels = read(OLD, "state-labels.json")
    new_labels = read(REPAIR, "state-labels.json")
    assert raw["states"] == 1400 and repaired["states"] == 1399
    assert len(raw["table"]) == raw["states"] and len(repaired["table"]) == repaired["states"]
    assert len(certificate["state_map"]) == raw["states"]
    assert len(old_labels) == old["states"] and len(new_labels) == repaired["states"]

    lines = ["(* Generated from repairs/guarded-distinction JSON; checked by Machine.v. *)",
             "From Stdlib Require Import Lists.List.",
             "From BusyCoq Require Import TM.",
             "From Berkeley Require Import FiniteMachine.", "Import ListNotations.",
             f"Definition old_count := {raw['states']}.",
             f"Definition new_count := {repaired['states']}."]
    for label, obj in (("old_table", raw), ("new_table", repaired)):
        def trans(t):
            w, direction, target = t
            assert w in (0, 1) and direction in ("L", "R") and -1 <= target < obj["states"]
            return f"({'true' if w else 'false'}, {direction}, {obj['states'] if target == -1 else target})"
        lines.append(f"Definition {label} : list row := [")
        lines.append(";\n".join("  (" + trans(row[0]) + ", " + trans(row[1]) + ")" for row in obj["table"]))
        lines.append("].")
    lines.append("Definition state_mapping : list nat := [" +
                 ";".join(map(str, certificate["state_map"] + [repaired["states"]])) + "].")
    data = HERE / "Data.v"
    data.write_text("\n".join(lines) + "\n")

    new_index = {name: q for q, names in enumerate(new_labels) for name in names}
    assert sum(map(len, new_labels)) == len(new_index)
    mapping, framework = [], []
    for q, names in enumerate(old_labels):
        options = {new_index[name] for name in names if name in new_index}
        assert len(options) <= 1
        mapping.append(next(iter(options), repaired["states"]))
        if any(name[0].isdigit() or name == "__diverge__" for name in names):
            assert options
            framework.append(q)
    mapping.append(repaired["states"])
    lines = ["(* Untrusted name-derived mapping, checked locally by Framework.v. *)",
             "From Stdlib Require Import Lists.List.", "Import ListNotations.",
             "Definition original_to_repair : list nat := [" + ";".join(map(str, mapping)) + "].",
             "Definition original_framework_states : list nat := [" + ";".join(map(str, framework)) + "]."]
    frame = HERE / "FrameworkData.v"
    frame.write_text("\n".join(lines) + "\n")
    return {"raw_states": raw["states"], "quotient_states": repaired["states"],
            "framework_states": len(framework),
            "raw_sha256": digest(REPAIR / "before-quotient.json"),
            "machine_sha256": digest(REPAIR / "machine.json"),
            "certificate_sha256": digest(REPAIR / "certificate.json"),
            "data_sha256": digest(data), "framework_data_sha256": digest(frame)}


if __name__ == "__main__":
    print(json.dumps(generate(), indent=2))
