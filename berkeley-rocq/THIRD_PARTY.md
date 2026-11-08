# Third-party sources and attribution

## BusyCoq

`vendor/BusyCoq/{LibTactics,Helper,TM}.v` are vendored from
[`ccz181078/Coq-BB5`](https://github.com/ccz181078/Coq-BB5), commit
`9142e219229baf2245d3f70851947230ea28a318`, directory `BusyCoq`.
The provenance file records the original byte hashes. The upstream files
remain unchanged. During staging only, `Lists.Streams` is changed to
`Streams.Streams`, and `Bool.Sumbool` to `Init.Sumbool`, where recorded in
that provenance file, for Rocq compatibility. The verifier checks that each
expected replacement exists.

Maja Kądziołka's BusyCoq MIT notice is retained as
`vendor/BusyCoq/LICENSE-BusyCoq`. Arthur Charguéraud's LibTactics MIT X11
notice is retained as `vendor/BusyCoq/LICENSE-LibTactics`.

## Machine construction

`construction/vendor/wade/` retains the files, README, provenance, and
MIT No Attribution license from
[`Saoi2/turing_machine_explorer`](https://github.com/Saoi2/turing_machine_explorer),
commit `08d539123f4369ae74a76619fdd391adc82de90c`.
The compiler is Andrew James Wade's. The included `subtle.py` records
Matthew House's earlier extension for comparison; it is not the Berkeley
axiom and is not imported by the Berkeley construction. The proof-enumerator
lineage includes Stefan O'Rear's work. The package does not claim authorship
of these upstream components.

## Mathematical references

- Joan Bagaria, Peter Koellner, W. Hugh Woodin, *Large Cardinals Beyond
  Choice*, Definition 3.4: [paper](https://par.nsf.gov/servlets/purl/10149501).
- Norman Megill, *A Finitely Axiomatized Formalization of Predicate Calculus
  with Equality*: [paper](https://us.metamath.org/downloads/finiteaxiom.pdf).
- [Metamath `ax-rep`](https://us.metamath.org/mpeuni/ax-rep.html), the
  protected-variable Replacement presentation underlying the source search.

## Project material

The package preserves third-party notices and makes no new blanket license
grant for the original Berkeley project material. A project-wide license
has not been selected. The presence of an MIT-licensed dependency does not
relicense the whole package.
