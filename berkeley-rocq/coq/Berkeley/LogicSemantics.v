(** Classical semantic soundness of the fourteen concrete logical schemas.
    Classical reasoning is an explicit hypothesis, not a new Rocq axiom. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Arith.Compare_dec Lia.
From Berkeley Require Import Syntax SyntaxData TheorySchemas ProofFormula ProofSearchSyntax ProofPresentation LogicBridge FormulaSemantics.
Import ListNotations.

Section Semantics.
Context {D : Type} (R : D -> D -> Prop).
Notation holds := (FolHolds R).
Notation upd := (@update_variable D).

Lemma update_here rho x a : upd rho x a x = a.
Proof. unfold update_variable. now rewrite Nat.eqb_refl. Qed.
Lemma update_away rho x a y : y <> x -> upd rho x a y = rho y.
Proof. apply update_variable_neq. Qed.
Lemma update_overwrite rho x a b n : upd (upd rho x a) x b n = upd rho x b n.
Proof. unfold update_variable. destruct (Nat.eqb n x); reflexivity. Qed.
Lemma update_restore rho x n : upd rho x (rho x) n = rho n.
Proof.
  unfold update_variable. destruct (Nat.eqb n x) eqn:E; [apply Nat.eqb_eq in E; now subst|reflexivity].
Qed.
Lemma update_commute rho x y a b n : x <> y -> upd (upd rho x a) y b n = upd (upd rho y b) x a n.
Proof.
  intro H. unfold update_variable. destruct (Nat.eqb n x) eqn:X; destruct (Nat.eqb n y) eqn:Y; try reflexivity.
  apply Nat.eqb_eq in X. apply Nat.eqb_eq in Y. congruence.
Qed.
Lemma holds_overwrite rho x a b p :
  holds (upd (upd rho x a) x b) p <-> holds (upd rho x b) p.
Proof. apply FolHolds_ext. apply update_overwrite. Qed.
Lemma holds_restore rho x p : holds (upd rho x (rho x)) p <-> holds rho p.
Proof. apply FolHolds_ext. apply update_restore. Qed.
Lemma holds_commute rho x y a b p : x<>y ->
  (holds (upd (upd rho x a) y b) p <-> holds (upd (upd rho y b) x a) p).
Proof. intro H. apply FolHolds_ext. intro n. now apply update_commute. Qed.

Lemma semantic_b1 rho p q : holds rho (FImp p (FImp q p)).
Proof. cbn. auto. Qed.
Lemma semantic_b2 rho p q r : holds rho (FImp (FImp p (FImp q r)) (FImp (FImp p q) (FImp p r))).
Proof. cbn. auto. Qed.
Lemma semantic_b3 (classic : forall P : Prop, P \/ ~P) rho p q :
  holds rho (FImp (FImp (FNeg p) (FNeg q)) (FImp q p)).
Proof.
  cbn. intros H K. destruct (classic (holds rho p)); auto. exfalso. exact (H H0 K).
Qed.
Lemma semantic_b4 rho x p q :
  holds rho (FImp (FAll x (FImp (FAll x p) q)) (FImp (FAll x p) (FAll x q))).
Proof.
  cbn. intros H K a. apply (H a). intro b.
  apply (proj2 (holds_overwrite rho x a b p)). apply K.
Qed.
Lemma semantic_b5 rho x p : holds rho (FImp (FAll x p) p).
Proof. cbn. intro H. apply (proj1 (holds_restore rho x p)). apply H. Qed.
Lemma semantic_b6 rho x y p : holds rho (FImp (FAll x (FAll y p)) (FAll y (FAll x p))).
Proof.
  cbn. intros H a b. destruct (Nat.eq_dec x y) as [E|E].
  - subst. apply H.
  - apply (proj1 (holds_commute rho x y b a p E)). apply H.
Qed.
Lemma semantic_b7 rho x p : holds rho (FImp (FNeg p) (FAll x (FNeg (FAll x p)))).
Proof.
  cbn. intros H a K. apply H. apply (proj1 (holds_restore rho x p)).
  apply (proj1 (holds_overwrite rho x a (rho x) p)). apply K.
Qed.
Lemma semantic_b8 rho x y z : holds rho (FImp (FEqual x y) (FImp (FEqual x z) (FEqual y z))).
Proof. cbn. congruence. Qed.
Lemma semantic_distinctor_neq rho x y : holds rho (FNeg (FAll x (FEqual x y))) -> x<>y.
Proof. cbn. intros H E. subst. apply H. intro d. reflexivity. Qed.
Lemma semantic_b9 rho x y z : holds rho
  (FImp (FNeg (FAll x (FEqual x y)))
   (FImp (FNeg (FAll x (FEqual x z))) (FImp (FEqual y z) (FAll x (FEqual y z))))).
Proof.
  intros H K. pose proof (semantic_distinctor_neq rho x y H) as XY.
  pose proof (semantic_distinctor_neq rho x z K) as XZ.
  cbn. intros E a. rewrite !update_away by congruence. exact E.
Qed.
Lemma semantic_b10 rho x y p :
  holds rho (FImp (FAll x (FImp (FEqual x y) (FAll x p))) p).
Proof.
  cbn. intro H. specialize (H (rho y)).
  assert (E : upd rho x (rho y) x = upd rho x (rho y) y).
  { rewrite update_here. unfold update_variable. destruct (Nat.eqb y x); reflexivity. }
  specialize (H E (rho x)). apply (proj1 (holds_restore rho x p)).
  apply (proj1 (holds_overwrite rho x (rho y) (rho x) p)). exact H.
Qed.
Lemma semantic_b11 rho x y p :
  holds rho (FImp (FAll x (FEqual x y)) (FImp (FAll x p) (FAll y p))).
Proof.
  cbn. intros H K a. destruct (Nat.eq_dec x y) as [E|E].
  - subst. apply K.
  - assert (A : a=rho y).
    { specialize (H a). rewrite update_here, update_away in H by congruence. exact H. }
    subst a. apply (proj2 (holds_restore rho y p)).
    apply (proj1 (holds_restore rho x p)). apply K.
Qed.
Lemma semantic_b12 rho x y z :
  holds rho (FImp (FEqual x y) (FImp (FMember x z) (FMember y z))).
Proof. cbn. intros E H. now rewrite <- E. Qed.
Lemma semantic_b13 rho x y z :
  holds rho (FImp (FEqual x y) (FImp (FMember z x) (FMember z y))).
Proof. cbn. intros E H. now rewrite <- E. Qed.
Lemma semantic_b14 rho x y z : holds rho
  (FImp (FNeg (FAll x (FEqual x y)))
   (FImp (FNeg (FAll x (FEqual x z))) (FImp (FMember y z) (FAll x (FMember y z))))).
Proof.
  intros H K. pose proof (semantic_distinctor_neq rho x y H) as XY.
  pose proof (semantic_distinctor_neq rho x z K) as XZ.
  cbn. intros E a. rewrite !update_away by congruence. exact E.
Qed.

Lemma logical_schema_valid (classic : forall P : Prop, P \/ ~P) i f vars holes rho :
  nth_error logical_schemas i=Some f -> holds rho (independent_instance vars holes f).
Proof.
  intro E.
  do 14 (destruct i as [|i];
    [cbn [logical_schemas] in E; inversion E; subst f;
     cbn [independent_instance independent_variable];
     first [apply semantic_b1 | apply semantic_b2 | apply semantic_b3; exact classic |
       apply semantic_b4 | apply semantic_b5 | apply semantic_b6 | apply semantic_b7 |
       apply semantic_b8 | apply semantic_b9 | apply semantic_b10 | apply semantic_b11 |
       apply semantic_b12 | apply semantic_b13 | apply semantic_b14] |]).
  destruct i; discriminate.
Qed.
Theorem logical_sound (classic : forall P : Prop, P \/ ~P) f : LogicalProvable f ->
  forall rho, holds rho f.
Proof.
  intro H. induction H as [i f vars holes E|p q A IHA B IHB|x p A IH]; intro rho.
  - eapply logical_schema_valid; eassumption.
  - apply (IHA rho). apply IHB.
  - cbn. intro a. apply IH.
Qed.
(** Models must satisfy the exact nonlogical candidate schemas under every
    independent formula and variable parameter instance. *)
Definition satisfies_nonlogical_schemas : Prop :=
  forall i f vars holes rho, 14 <= i -> nth_error candidate_axioms i=Some f ->
    holds rho (independent_instance vars holes f).
Theorem presented_sound (classic : forall P : Prop, P \/ ~P) :
  satisfies_nonlogical_schemas -> forall f, PresentedProvable f -> forall rho, holds rho f.
Proof.
  intro Model. intros f H. induction H as [|i f vars holes E|p q A IHA B IHB|x p A IH]; intro rho.
  - cbn. reflexivity.
  - destruct (lt_dec i 14) as [Small|Large].
    + eapply logical_schema_valid; [exact classic|].
      rewrite <- candidate_logical_prefix, nth_error_firstn_lt by exact Small. exact E.
    + eapply (Model i f vars holes rho); [lia|exact E].
  - apply (IHA rho). apply IHB.
  - cbn. intro a. apply IH.
Qed.
Theorem numeric_inconsistent_model_consequence (classic : forall P : Prop, P \/ ~P) :
  satisfies_nonlogical_schemas -> NumericInconsistent -> forall rho, R (rho 0) (rho 0).
Proof.
  intros Model Inconsistent rho.
  change (holds rho (FMember 0 0)).
  apply (presented_sound classic Model (FMember 0 0)); apply (proj1 numeric_target_iff_presented_target); exact Inconsistent.
Qed.
Theorem nonlogical_model_irreflexive_consistency (classic : forall P : Prop, P \/ ~P) :
  satisfies_nonlogical_schemas -> forall rho, ~ R (rho 0) (rho 0) -> ~NumericInconsistent.
Proof.
  intros Model rho NotSelf H. apply NotSelf.
  now apply (numeric_inconsistent_model_consequence classic Model H rho).
Qed.
End Semantics.
Print Assumptions logical_schema_valid.
Print Assumptions logical_sound.

Print Assumptions presented_sound.
Print Assumptions numeric_inconsistent_model_consequence.
Print Assumptions nonlogical_model_irreflexive_consistency.
