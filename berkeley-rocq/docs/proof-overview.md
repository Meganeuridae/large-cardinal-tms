# Proof statement and reading guide

## Endpoint

`Repair.TheoryTheorem` defines

```coq
Definition ZF_BerkeleyInconsistent :=
  exists p, BoundedReplacementND [] p /\
            BoundedReplacementND [] (FNeg p).
Definition Con_ZF_Berkeley := ~ ZF_BerkeleyInconsistent.
```

It proves `New.halts new_tm New.c0 <-> ZF_BerkeleyInconsistent` without
hypotheses or additional axioms. The corollary replacing the right-hand
side by `~ Con_ZF_Berkeley` takes `(forall P : Prop, P \/ ~P)` explicitly;
closure of its assumption report does not erase that argument.

`BoundedReplacementND` is an explicit inductive classical first-order
natural-deduction calculus, with equality, capture-safe substitution,
quantifier freshness conditions, ZF axioms, and the literal Berkeley
sentence. Its rules build finite derivation objects. Separation is
unprotected, and Replacement is bounded-domain and partial-functional.
The internal presentations use fixed variable names; `ZFVariableTheorems`
derives arbitrary distinct-name Separation and Replacement instances.
`ZFBoundedReplacementND.conventional_iff_bounded_replacement_nd` supplies
the checked proof translation to and from the normalized global-domain
presentation.

## Dependency chain

| Layer | Useful entry points | Checked role |
| --- | --- | --- |
| Literal table and quotient | `Repair.Data`, `Repair.Machine` | The raw 1,400-state table and the exact 1,399-state quotient. |
| Blank bootstrap | `Repair.BootstrapReplay`, `Repair.BootstrapMachine` | Committed compressed trace to the interpreter invariant. |
| Register interpreter | `Repair.RuntimeSimulation`, `Repair.RuntimeEquivalence` | Both directions between register execution and TM behavior. |
| Source/compiler | `Repair.CompilerProof`, `Repair.CompilerReverse` | Concrete source graph and compiler execution. |
| Formula constructors | `Repair.ConstructorPair`, `ConstructorPush`, `ConstructorCons`, `ConstructorParam` | Actual arithmetic, stack, and parameter-copying behavior. |
| Grammar and proof search | `Repair.GrammarExecution`, `Repair.SearchMachineTheorem` | Full grammar execution, enumeration, and provability correspondence. |
| Logical translation | `Berkeley.StandardAugEquivalence`, `ZFConventionalND`, `ZFBoundedReplacementND` | Explicit-calculus equivalence and normalization of ZF schemas. |
| Final theorem | `Repair.TheoryTheorem` | Literal blank-tape halting iff contradictory finite derivations. |
| Berkeley semantics | `Berkeley.BerkeleySyntaxSetupFinal`, `ZFConventionalSemantics`, `Repair.SemanticAudit` | ZF construction of syntax/truth data and the internal Berkeley interpretation. |

The package includes exactly the project-source dependency closure of
`Repair.TheoryTheorem` and `Repair.SemanticAudit`: 302 project modules plus
three BusyCoq dependencies. Proof sources are copied without changing their
statements or proof terms. Generic components retain their original
`Berkeley` namespace, including some historical machine data needed by those
components. The final machine is always `Repair.Machine.new_tm`.

## The meaning of the Berkeley sentence

The formula uses the least set of syntax trees for equality, membership,
negation, implication, and universal quantification. Tags are the ordinals
0 through 4. Formula constructors and assignments are represented by
Kuratowski pairs and function graphs. Assignments range over the complete
set of maps from omega to the transitive set being considered.

A Tarski truth set supplies uniform satisfaction for that set-sized
structure. The embedding is selected before universally quantifying over
formula codes. It must preserve all of them with the same map. The formula
also requires an initial ordinal delta above omega and critical points
strictly between each eta below delta and delta itself. It quantifies over
every transitive set containing delta as an element, rather than just ranks.

The model theorem is

```coq
ConventionalModel R <->
  satisfies_zf_prefix R /\ RelUniformBerkeley R
```

with explicit classical reasoning and an inhabitant of the domain as
arguments. The existence of formula-coding and satisfaction data is derived
from ZF, rather than left as an extra hypothesis. Internal all-code
elementarity implies elementarity for ordinary externally finite formulas.
The development does not assert the converse for arbitrary nonstandard
models, whose internally finite formula codes can include nonstandard ones.
The printed one-page axiomatization uses this internal reading throughout.

This is a syntactic halting/inconsistency result plus the stated semantic
identification. It is not a proof of either consistency or inconsistency,
nor a separate arithmetization of the correctness theorem inside PA, nor
a formal derivation of Gödel's second incompleteness theorem.

## Why 1399 states

The original 1,385-state candidate implements an unrestricted logical
presentation without a needed guarded distinction scheme. An attempted
translation from that presentation to ordinary first-order completeness
treated object-language distinction antecedents as syntactic freshness
conditions. That step is not justified.

The repair adds the scheme `not (forall a, a = b)` when the numeric variable
names differ. Equal names are rejected to the existing default formula
code. This costs 14 states after quotienting. The guarded instruction's
actual execution, parameter restoration, and stack behavior are proved;
its logical validity follows in ordinary set theory from Empty and Pairing.
The package's final equivalence concerns this repaired table. It does not
transfer that theorem to the earlier table.

## What is trusted and what is checked

The mathematical trust boundary includes the meaning of the definitions
and theorem statements, Rocq's logic and kernel, and a correctly installed
toolchain. In particular, a reader should inspect the machine convention,
the natural-deduction rules, the axiom presentation, and the internal
Berkeley property. The Python verifier additionally checks that the public
text/JSON table is the literal table appearing in the theorem.

Generators and certificate searches supply data. Their outputs are
committed, and their finite correctness obligations are checked by Rocq;
their original search runs are not premises of the proof. The source
manifest detects unintended changes and fixes the reviewed snapshot, but
hash equality by itself is not a mathematical correctness argument.

The final theorem's assumption report is closed. The independent checker's
library-wide inventory can nevertheless list `inj_pair2`,
`proof_irrelevance`, and `eq_rect_eq` declarations in loaded libraries.
That inventory records declarations in the environment; it is not the
dependency list of the final theorem. Both the per-theorem audits and the
independent checker logs are retained in `.build/`.
