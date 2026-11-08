#!/usr/bin/env python3
"""Offline, clean verification of the frozen Berkeley1399 proof package."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
STAGE = ROOT / ".build"
ROOTS = [("Repair", "TheoryTheorem"), ("Repair", "SemanticAudit")]
MAIN = "Repair.TheoryTheorem.repaired_blank_halts_iff_ZF_Berkeley_inconsistent"
IMPORT = re.compile(r"From\s+(Berkeley|Repair)\s+Require\s+(?:Import|Export)\s+([^.]+)\.")
PRINT = re.compile(r"(?m)^Print Assumptions ([A-Za-z0-9_]+)\.$")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def check_manifest():
    manifest = read_json(ROOT / "manifest.json")
    require(manifest["main_theorem"] == MAIN, "Unexpected endpoint in manifest")
    for name, expected in manifest["files"].items():
        path = ROOT / name
        require(path.is_file() and not path.is_symlink(), "Missing or linked input: " + name)
        require(digest(path) == expected, "Input hash mismatch: " + name)
    actual = {str(p.relative_to(ROOT)) for p in (ROOT / "coq").rglob("*.v")}
    pinned = {p for p in manifest["files"] if p.startswith("coq/") and p.endswith(".v")}
    require(actual == pinned, "Unpinned or missing proof sources")
    return manifest


def machine_table(path, count):
    data = read_json(path)
    require(data["states"] == count and len(data["table"]) == count, "Wrong state count")
    for row in data["table"]:
        require(len(row) == 2, "Every working state needs two transitions")
        for t in row:
            require(len(t) == 3 and t[0] in (0, 1) and t[1] in ("L", "R")
                    and type(t[2]) is int and -1 <= t[2] < count, "Malformed transition")
    return data["table"]


def check_tables():
    new = machine_table(ROOT / "machine/machine.json", 1399)
    old = machine_table(ROOT / "machine/before-quotient.json", 1400)
    tm = {}
    directives = []
    for line in (ROOT / "machine/machine.tm").read_text().splitlines():
        if line.startswith("#!"):
            directives.append(line)
            continue
        if not line.strip():
            continue
        fields = line.split()
        require(len(fields) == 5, "Malformed .tm row")
        q, b, w = map(int, fields[:3])
        d, n = fields[3:]
        require((q, b) not in tm, "Duplicate .tm transition")
        tm[q, b] = [w, d, -1 if n == "HALT" else int(n)]
    require(directives == ["#! start 0", "#! fill 0"], "Incorrect blank-input convention")
    require(tm == {(q, b): row[b] for q, row in enumerate(new) for b in (0, 1)},
            ".tm and JSON tables differ")
    text = (ROOT / "coq/Repair/Data.v").read_text()
    row_pattern = re.compile(r"\(\((true|false), (L|R), (\d+)\), \((true|false), (L|R), (\d+)\)\)")
    for name, table in (("old_table", old), ("new_table", new)):
        section = text.split(f"Definition {name} : list row := [", 1)[1].split("].", 1)[0]
        decoded = []
        for line in section.splitlines():
            line = line.strip().removesuffix(";")
            if not line:
                continue
            m = row_pattern.fullmatch(line)
            require(m is not None, "Unrecognized Rocq table row")
            f = m.groups()
            decoded.append([[int(f[j] == "true"), f[j+1],
                             -1 if int(f[j+2]) == len(table) else int(f[j+2])]
                            for j in (0, 3)])
        require(decoded == table, "Rocq literal and JSON differ: " + name)
    return {"working_states": len(new), "transitions": len(tm),
            "halt_transitions": sum(t[2] == -1 for row in new for t in row),
            "machine_json_sha256": digest(ROOT / "machine/machine.json"),
            "machine_tm_sha256": digest(ROOT / "machine/machine.tm")}


def source_closure():
    order, done, active = [], set(), set()

    def visit(ns, name):
        key = ns, name
        if key in done:
            return
        require(key not in active, "Cyclic proof import: " + ".".join(key))
        path = ROOT / "coq" / ns / (name + ".v")
        require(path.is_file(), "Missing proof dependency: " + ".".join(key))
        active.add(key)
        text = path.read_text()
        for dep_ns, group in IMPORT.findall(text):
            for dep in group.split():
                visit(dep_ns, dep)
        for forbidden in (r"\b(?:Admitted|admit|Abort)\s*\.", r"\bAxioms?\s+",
                          r"\b(?:native_cast_no_check|vm_cast_no_check)\b"):
            require(re.search(forbidden, text) is None, "Forbidden proof escape in " + str(path.relative_to(ROOT)))
        active.remove(key)
        done.add(key)
        order.append((ns, name, path, PRINT.findall(text)))

    for root in ROOTS:
        visit(*root)
    all_sources = {p for p in (ROOT / "coq").rglob("*.v")}
    require({p for _, _, p, _ in order} == all_sources, "Proof package is not exactly the endpoint closure")
    reports = {(ns, name): names for ns, name, _, names in order}
    require("repaired_blank_halts_iff_ZF_Berkeley_inconsistent" in reports[("Repair", "TheoryTheorem")],
            "Missing final theorem assumption audit")
    require("repaired_blank_halts_iff_not_Con_ZF_Berkeley" in reports[("Repair", "TheoryTheorem")],
            "Missing classical formulation audit")
    require("normalized_axiom_models_iff_ZF_Berkeley" in reports[("Repair", "TheoryTheorem")],
            "Missing semantic endpoint audit")
    return order


def check_toolchain(rocq):
    lock = read_json(ROOT / "toolchain.lock.json")
    version = subprocess.check_output([rocq, "--version"], text=True)
    require(re.search(r"version " + re.escape(lock["rocq"]["version"]) + r"\s", version),
            "Expected Rocq " + lock["rocq"]["version"] + "; found " + version.strip())
    require("compiled with OCaml " + lock["ocaml"] in version, "Unexpected OCaml compiler; see toolchain.lock.json")
    config = subprocess.check_output([rocq, "--config"], text=True)
    entries = dict(line.split("=", 1) for line in config.splitlines() if "=" in line)
    library = Path(entries["COQLIB"]) / "user-contrib" / "Stdlib"
    if os.environ.get("BERKELEY_STDLIB"):
        library = Path(os.environ["BERKELEY_STDLIB"])
    hashes = read_json(ROOT / "pins/stdlib-sources.json")
    for name, expected in hashes.items():
        path = library / name
        require(path.is_file() and digest(path) == expected,
                "Stdlib 9.2.0 source mismatch: " + name + "; see docs/toolchain.md")
    return {"rocq": version.strip(), "stdlib": lock["stdlib"]["version"],
            "stdlib_sources_checked": len(hashes)}, library


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources-only", action="store_true", help="Check frozen inputs and tables only; does NOT verify the proof")
    args = parser.parse_args()
    start = time.monotonic()
    manifest = check_manifest()
    manifest_sha = digest(ROOT / "manifest.json")
    tables = check_tables()
    sources = source_closure()
    print(f"Frozen inputs OK: {len(sources)} project proof modules; {tables['transitions']} transitions", flush=True)
    if args.sources_only:
        print("SOURCE CHECKS PASSED; Rocq compilation and kernel checking were not run.")
        return
    rocq = shutil.which("rocq")
    require(rocq is not None, "Install the pinned Rocq toolchain; see docs/toolchain.md")
    toolchain, stdlib = check_toolchain(rocq)
    # The build directory is disposable and never used as proof input.
    require(not STAGE.is_symlink(), ".build must not be a symlink")
    if STAGE.exists():
        shutil.rmtree(STAGE)
    for ns in ("BusyCoq", "Berkeley", "Repair"):
        (STAGE / ns).mkdir(parents=True)
    vendor = ROOT / "vendor/BusyCoq"
    provenance = read_json(vendor / "provenance.json")
    for name, expected in provenance["files"].items():
        require(digest(vendor / name) == expected, "BusyCoq provenance mismatch: " + name)
    jobs = []
    for name in ("LibTactics", "Helper", "TM"):
        text = (vendor / (name + ".v")).read_text()
        for old, new in provenance["build_only_compatibility_changes"].get(name + ".v", {}).items():
            require(old in text, "Missing BusyCoq compatibility pattern")
            text = text.replace(old, new)
        path = STAGE / "BusyCoq" / (name + ".v")
        path.write_text(text)
        jobs.append(("BusyCoq", name, path, None))
    for ns, name, original, reports in sources:
        path = STAGE / ns / (name + ".v")
        shutil.copyfile(original, path)
        jobs.append((ns, name, path, reports))
    flags = ["-Q", str(stdlib), "Stdlib"]
    for ns in ("BusyCoq", "Berkeley", "Repair"):
        flags += ["-Q", str(STAGE / ns), ns]
    with (STAGE / "compile.log").open("w") as log:
        for i, (ns, name, path, reports) in enumerate(jobs, 1):
            if i == 1 or i % 10 == 0 or i == len(jobs):
                print(f"Compiling {i}/{len(jobs)}: {ns}.{name}", flush=True)
            result = subprocess.run([rocq, "compile", "-q", "-w", "-all", *flags, str(path)],
                                    cwd=STAGE, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log.write(ns + "." + name + "\n" + result.stdout)
            log.flush()
            require(result.returncode == 0, f"Compilation failed: {ns}.{name}\n{result.stdout}")
            if reports is not None:
                require(result.stdout.count("Closed under the global context") == len(reports)
                        and "Axioms:" not in result.stdout, f"Assumption audit failed: {ns}.{name}")
    modules = [".".join(root) for root in ROOTS]
    print("Running the independent Rocq kernel checker...", flush=True)
    with (STAGE / "kernel-check.log").open("w") as log:
        subprocess.run([rocq, "check", "-silent", "-o", *flags, *modules],
                       cwd=STAGE, stdout=log, stderr=subprocess.STDOUT, check=True)
    text = (STAGE / "kernel-check.log").read_text()
    require("unsafe (co)fixpoints: <none>" in text and "type-in-type: <none>" in text,
            "Unsafe constants reported by the kernel checker")
    match = re.search(r"\* Axioms:(.*?)(?=\n\s*\* Constants/Inductives)", text, re.S)
    require(match is not None, "Missing kernel environment inventory")
    loaded_axioms = [s.strip() for s in match.group(1).splitlines() if s.strip() and s.strip() != "<none>"]
    require(check_manifest() == manifest and digest(ROOT / "manifest.json") == manifest_sha,
            "Frozen inputs changed during verification")
    report = {"success": True, "main_theorem": MAIN, "toolchain": toolchain,
              "manifest_sha256": manifest_sha, "machine": tables, "compiled_modules": len(jobs),
              "closed_assumption_reports": sum(len(names) for _, _, _, names in sources),
              "kernel_check": "passed", "kernel_checked_modules": modules,
              "kernel_loaded_library_axioms": loaded_axioms,
              "source_sha256": {ns + "." + name: digest(path) for ns, name, path, _ in jobs},
              "elapsed_seconds": round(time.monotonic() - start, 2)}
    (STAGE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"VERIFIED: {len(jobs)} modules; {report['closed_assumption_reports']} closed assumption reports; independent kernel check passed.")
    print("Logs and machine-readable report: .build/")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print("VERIFICATION FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
