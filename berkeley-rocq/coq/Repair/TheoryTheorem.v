(** Final composition for a fully specified normalized first-order theory.
    Its independently written ZF schemas use fixed variable names and fresh
    formula parameters; its Berkeley sentence is identified semantically with
    internal, all-code elementary embeddings by the separately checked model
    theorem below. No semantic completeness premise is used in the halting
    equivalence. The original 1,385-state table is a different artifact. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import ProofFormula ZFConventionalND ZFConventionalSemantics
  BerkeleySyntaxZFBase BerkeleySyntaxUniform ZFVariableTheorems ZFBoundedReplacementND.
From Repair Require Import Machine SearchMachineTheorem.
Import ListNotations.

Definition NormalizedZF_BerkeleyInconsistent :=
  exists p, ConventionalND [] p /\ ConventionalND [] (FNeg p).
Definition NormalizedZF_BerkeleyConsistent := ~ NormalizedZF_BerkeleyInconsistent.

(** This presentation uses ordinary first-order ND, unprotected Separation
    and bounded-domain Replacement, with a fixed variable-name convention.
    ZFVariableTheorems proves arbitrary distinct-name instances. *)
Definition ZF_BerkeleyInconsistent :=
  exists p, BoundedReplacementND [] p /\ BoundedReplacementND [] (FNeg p).
Definition Con_ZF_Berkeley := ~ ZF_BerkeleyInconsistent.

Theorem repaired_blank_halts_iff_normalized_ZF_Berkeley_inconsistent :
  New.halts new_tm New.c0 <-> NormalizedZF_BerkeleyInconsistent.
Proof.
  rewrite repaired_blank_halts_iff_standard_presentation_inconsistency.
  unfold NormalizedZF_BerkeleyInconsistent. split; intros [p [P N]];
    exists p; split; now apply conventional_iff_standard_nd.
Qed.

Theorem repaired_blank_halts_iff_ZF_Berkeley_inconsistent :
  New.halts new_tm New.c0 <-> ZF_BerkeleyInconsistent.
Proof.
  rewrite repaired_blank_halts_iff_normalized_ZF_Berkeley_inconsistent.
  unfold NormalizedZF_BerkeleyInconsistent,ZF_BerkeleyInconsistent.
  split; intros [p [P N]]; exists p; split;
    now apply conventional_iff_bounded_replacement_nd.
Qed.

Theorem repaired_blank_halts_iff_not_Con_ZF_Berkeley
  (EM : forall P:Prop, P \/ ~P) :
  New.halts new_tm New.c0 <-> ~ Con_ZF_Berkeley.
Proof.
  rewrite repaired_blank_halts_iff_ZF_Berkeley_inconsistent.
  unfold Con_ZF_Berkeley. split.
  - intros H N. exact (N H).
  - intro NN. destruct (EM ZF_BerkeleyInconsistent); [assumption|contradiction].
Qed.

(** Consistency is a negation. Its negation is classically equivalent to
    existence of a finite contradictory derivation. EM is explicit because
    Rocq's metatheory is constructive; the preceding theorem needs no EM. *)
Theorem repaired_blank_halts_iff_not_normalized_ZF_Berkeley_consistent
  (EM : forall P:Prop, P \/ ~P) :
  New.halts new_tm New.c0 <-> ~ NormalizedZF_BerkeleyConsistent.
Proof.
  rewrite repaired_blank_halts_iff_normalized_ZF_Berkeley_inconsistent.
  unfold NormalizedZF_BerkeleyConsistent. split.
  - intros H N. exact (N H).
  - intro NN. destruct (EM NormalizedZF_BerkeleyInconsistent); [assumption|contradiction].
Qed.

Theorem normalized_axiom_models_iff_ZF_Berkeley {D:Type} (R:D->D->Prop)
  (EM : forall P:Prop, P \/ ~P) (seed:D) :
  ConventionalModel R <-> satisfies_zf_prefix R /\ RelUniformBerkeley R.
Proof. exact (conventional_model_iff_zf_uniform_berkeley R EM seed). Qed.

Print Assumptions repaired_blank_halts_iff_normalized_ZF_Berkeley_inconsistent.
Print Assumptions repaired_blank_halts_iff_ZF_Berkeley_inconsistent.
Print Assumptions repaired_blank_halts_iff_not_Con_ZF_Berkeley.
Print Assumptions repaired_blank_halts_iff_not_normalized_ZF_Berkeley_consistent.
Print Assumptions normalized_axiom_models_iff_ZF_Berkeley.
