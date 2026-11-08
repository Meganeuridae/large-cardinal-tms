#!/usr/bin/env python3
"""Untrusted finite graph certificates, checked against the literal table in Rocq."""
from functools import lru_cache
import hashlib
import heapq
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def generate():
    folder = HERE.parent / "repairs/guarded-distinction"
    table = json.loads((folder / "machine.json").read_text())["table"]
    labels = json.loads((folder / "state-labels.json").read_text())
    nodes = {q for q, names in enumerate(labels)
             if all(name[0] not in "0123456_" for name in names)}
    @lru_cache(None)
    def bounds(q):
        if q not in nodes: return 0, 0
        successors = [(1 + bounds(t)[0], (1-b) + bounds(t)[1])
                      for b, (_, d, t) in enumerate(table[q]) if d == "R"]
        return max([1] + [h for h,z in successors]), max([0] + [z for h,z in successors])
    values = [bounds(q) for q in range(len(table))]
    # A one-bit lower-bound potential: a zero must have been read before
    # reaching any register entry. All-ones reachability determines zeroes.
    all_ones = {73}
    q = 73
    while q in nodes and table[q][1][1] == "R":
        q = table[q][1][2]
        if q in all_ones: break
        all_ones.add(q)
    def min_bits(bit):
        ds = [3] * (len(table) + 1)
        ds[73] = 0
        todo = [(0, 73)]
        while todo:
            distance, q = heapq.heappop(todo)
            if distance != ds[q] or q not in nodes: continue
            for b, (_, direction, target) in enumerate(table[q]):
                cost = distance + (b == bit)
                if direction == "R" and cost < ds[target]:
                    ds[target] = cost
                    heapq.heappush(todo, (cost, target))
        return [str(d) for d in ds[:-1]]
    data = ["(* Generated candidate certificates; validated against Repair.Data.new_table. *)",
            "From Stdlib Require Import Lists.List.", "Import ListNotations."]
    for name, typ, entries in (
        ("node_flags", "bool", ["true" if q in nodes else "false" for q in range(len(table))]),
        ("node_heights", "nat", [str(h) for h,z in values]),
        ("node_zeros", "nat", [str(z) for h,z in values]),
        ("node_potential", "nat", ["0" if q in all_ones else "1" for q in range(len(table))]),
        ("node_min_zeros", "nat", min_bits(0)),
        ("node_min_ones", "nat", min_bits(1))):
        data.append(f"Definition {name} : list {typ} := [" + ";".join(entries) + "].")
    path = HERE / "RuntimeProgramData.v"
    path.write_text("\n".join(data) + "\n")
    return {"program_data_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "decision_nodes": len(nodes), "root_height": values[73][0], "root_max_zeros": values[73][1]}

if __name__ == "__main__": print(json.dumps(generate(), indent=2))
