# Reference validation

Checked locally on 2026-11-08 from the standalone package, using the command
`python3 verify.py`. This was a clean build, not reuse of the original research
checkout's compiled objects.

- Rocq 9.3.0, compiled with OCaml 5.5.2; Stdlib 9.2.0.
- All 350 frozen input hashes and 582 installed Stdlib source hashes matched.
- The text table, JSON table, and Rocq literal agree on all 2,798 transitions.
- All 305 proof modules compiled.
- All 897 printed theorem-assumption reports were closed; none reported axioms.
- The independent `rocq check` passed for both final roots and their dependencies.
- Recorded elapsed time: 381.62 seconds on the reference host.

The loaded-library axiom inventory is preserved in the report and checker log.
It is distinct from the final theorems' closed dependency reports, as explained
in [the proof overview](proof-overview.md#what-is-trusted-and-what-is-checked).

Files copied directly from the completed check:

- [Machine-readable report](../verification/verification.json)
- [Compilation and assumption-audit log](../verification/compile.log)
- [Independent kernel-check log](../verification/kernel-check.log)

Additional checks completed:

- The machine generator reproduced all nine exported machine/construction files byte for byte.
- The certificate exporters reproduced all five packaged finite Rocq witness files byte for byte.
- Five negative controls passed: unpinned edits, a rehashed wrong text table,
  a rehashed wrong Rocq table, an injected axiom, and a removed endpoint audit
  were all rejected.
- All 342 copied proof, vendor, construction, and machine files still matched
  the recorded research-source snapshots.
- The LaTeX source compiled to one PDF page without layout warnings; the
  rendered page was visually inspected.
- Documentation links were checked, and distributable sources were scanned
  for personal filesystem paths and common credential patterns.

This record describes the local reference run. Hosted verification is tracked
separately by the repository's [Verify Berkeley1399 workflow](https://github.com/Meganeuridae/large-cardinal-tms/actions/workflows/berkeley-rocq.yml).
Re-run the verification command to check a new download. `SHA256SUMS` covers
all distributed files other than itself, including documentation and this
record; it complements the proof-input manifest.
