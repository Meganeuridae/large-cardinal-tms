# Berkeley1399: a verified machine for ZF plus a Berkeley cardinal

This package contains an exact **1,399-state, two-symbol Turing machine** and
Rocq proofs of its blank-tape halting equivalence with finite inconsistency
of an explicitly defined first-order presentation of **ZF + “there exists a
Berkeley cardinal.”** Foundation is included. Choice and dependent choice are
not added.

The main theorem is
[`Repair.TheoryTheorem.repaired_blank_halts_iff_ZF_Berkeley_inconsistent`](coq/Repair/TheoryTheorem.v):

```coq
New.halts new_tm New.c0 <-> ZF_BerkeleyInconsistent
```

`ZF_BerkeleyInconsistent` is defined as a formula and its negation both having
finite derivations in `BoundedReplacementND`. This endpoint has no hypotheses
and no additional axioms. The same file proves

```coq
(forall P : Prop, P \/ ~P) ->
  (New.halts new_tm New.c0 <-> ~ Con_ZF_Berkeley)
```

with excluded middle as an **explicit argument**, since Rocq's metatheory is
constructive. The development does not decide consistency or halting.

## Verify

Install the pinned toolchain: **Rocq 9.3.0, Stdlib 9.2.0, OCaml 5.5.2**, plus
Python 3.9 or later. See [toolchain instructions](docs/toolchain.md).
Then, from this directory, run the single verification command:

```sh
python3 verify.py
```

This command works offline and performs a fresh build every time. It:

1. Checks SHA-256 pins for the proof sources, machine data, included
   dependencies, and supporting verification inputs.
2. Compares all **2,798 transitions** of the `.tm` file with its JSON version
   and the literal Rocq table; also checks the 1,400-state pre-quotient table.
3. Checks the Rocq/OCaml versions and 582 pinned installed Stdlib source files.
4. Compiles the full endpoint dependency closure: **305 modules**, comprising
   195 `Berkeley`, 107 `Repair`, and 3 BusyCoq modules.
5. Checks **897** printed theorem-assumption reports for closure, including
   the final equivalence and semantic interpretation theorems.
6. Runs `rocq check`, the independent kernel checker, on both final roots.

Success ends with `VERIFIED`. Build products, complete logs, and the report
are in `.build/`. The [reference validation record](docs/validation.md) and
[included verification report](verification/verification.json) document the
fresh package build. A source check is available as `python3 verify.py --sources-only`;
it explicitly does **not** certify the proof. Verification does not run the
machine until it halts and does not use finite simulations as a consistency test.

## Exact machine

- [Transition table](machine/machine.tm): `state read write L/R next`.
- [JSON table](machine/machine.json): each row contains the 0 and 1 transitions.
- Working states are **0 through 1398**; initial state **0**; blank symbol **0**;
  one head on a bi-infinite tape; one distinct halting label.
- `HALT` in the text table and `-1` in JSON denote that label. The Rocq table
  uses state **1399** for it. There is one transition to halt.

The JSON SHA-256 is

```text
a566e4cc997869ef67e50025c3ea2b70aba90f5cd0618dcb047b946ae6885810
```

The text-table SHA-256 is

```text
db898cd6728f82a054ac13d7df3ded1f5083e6b89e169bbe67ed23acc7be8a59
```

This is the **guarded-distinction repair**, with a checked 1,400-to-1,399-state
quotient. The earlier 1,385-state candidate has a different transition table
and a weaker verified endpoint about its own presented calculus. It is not
the machine certified by this package's main theorem. See the
[repair explanation](docs/proof-overview.md#why-1399-states).

## Axiomatization and scope

The [one-page axiomatization](docs/axiomatization.pdf), with
[LaTeX source](docs/axiomatization.tex), lists all nine ZF axioms/schemas,
including parameterized Separation and bounded-domain partial-functional
Replacement, and the Berkeley sentence with its set-coded syntax and Tarski
truth clauses. These are schemas in ordinary classical first-order logic,
not a claim that ZF is finitely axiomatizable.

The proof uses a normalized variable-name presentation and proves separate
theorems giving arbitrary distinct-name Separation and Replacement
instances. Its Berkeley axiom is a **single finite membership-and-equality
sentence**: one embedding preserves all internally coded formulas. The
fully expanded sentence is in [berkeley-pure.sexpr](machine/berkeley-pure.sexpr).

The separately checked model theorem identifies models of the normalized
axiom presentation with the stated ZF prefix plus **internal all-code Berkeley
elementarity**, using explicit classical reasoning and an inhabited domain.
It derives the coding and satisfaction setup from ZF. External elementarity
for standard finite formulas follows; a converse for arbitrary nonstandard
models is not asserted. The [proof overview](docs/proof-overview.md) identifies
the relevant definitions, statements, and trust boundary precisely.

## Files

| Path | Role |
| --- | --- |
| `coq/Berkeley/`, `coq/Repair/` | The 302 project `.v` files in the endpoint closure, including committed finite certificates. |
| `machine/` | Literal machine, raw table, quotient/grammar certificates, source axioms, and expanded Berkeley sentence. |
| `vendor/BusyCoq/` | Three pinned upstream modules, their provenance, and license notices. |
| `construction/` | Original Python machine-construction code and pinned Wade compiler; optional for verification. |
| `tools/rebuild_machine.py` | Rebuild the table and construction data in a temporary directory and compare their bytes. |
| `tools/rebuild_certificates.py` | Regenerate five finite Rocq witness files and compare their bytes. |
| `manifest.json`, `toolchain.lock.json`, `pins/` | Frozen input hashes and dependency/toolchain pins. |
| `docs/` | Axiomatization, mathematical scope, checking instructions, and validation record. |
| `tests/`, [`../.github/workflows/berkeley-rocq.yml`](../.github/workflows/berkeley-rocq.yml) | Negative controls and the repository's pinned-action CI workflow. |

The bootstrap trace is committed as `BootstrapReplay.v` and checked in Rocq.
Its historical exporter is included; its expensive trace search is unnecessary
for verification. Some original generator status strings predate the completed
proof. The current theorem and fresh verification report determine the status.

Optional reproduction and verifier controls:

```sh
python3 tools/rebuild_machine.py
python3 tools/rebuild_certificates.py
python3 -m unittest discover -s tests -v
```

The verification command never changes a committed input. Maintainers who
intentionally change inputs can explicitly run `python3 tools/refresh_manifest.py`
and then reverify. Refreshing hashes alone proves nothing.

## Provenance and licenses

The project proof sources are byte-for-byte snapshots of the completed
research development; [provenance.json](provenance.json) records each source
path relative to that development and its hash. No original research checkout
is needed to verify or reproduce this package.

BusyCoq is pinned to [`Coq-BB5` commit
`9142e219229baf2245d3f70851947230ea28a318`](https://github.com/ccz181078/Coq-BB5/tree/9142e219229baf2245d3f70851947230ea28a318/BusyCoq).
The construction compiler is pinned to [`turing_machine_explorer` commit
`08d539123f4369ae74a76619fdd391adc82de90c`](https://github.com/Saoi2/turing_machine_explorer/tree/08d539123f4369ae74a76619fdd391adc82de90c).
See [THIRD_PARTY.md](THIRD_PARTY.md) for credits and preserved licenses.

The package layout follows the separation of literal machine, proofs,
certificate data, dependency pins, and checking instructions in
[Elliot Glazer's K230 package](https://github.com/elliotglazer/k230-rocq).
It is an independent Berkeley-machine development and does not reuse the
K230 theorem as a premise.
