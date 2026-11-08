(** First-order induction proves ordinal properties for every internal
    natural number; it does not identify internal omega with external nat. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase
  BerkeleySyntaxInterpretation BerkeleySyntaxSets BerkeleySyntaxOmega
  BerkeleySyntaxCardinal BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation BerkeleySyntaxZFOmega.
Import ListNotations.

Definition RelStrongOrdinal {D} (R:D->D->Prop) a :=
  RelOrdinal R a /\ forall x, R x a -> RelTransitive R x.
Definition strong_ordinal_builder a := b_and (b_ordinal a) (b_ain a (fun x => b_transitive x)).
Definition strong_ordinal_formula := instantiate_formula (fun _=>0) (fst (strong_ordinal_builder 2 3)).
Definition omega_subset_formula := instantiate_formula (fun _=>0) (fst (b_subset 2 0 3)).

Lemma strong_ordinal_fresh : fol_free 1 strong_ordinal_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma omega_subset_fresh : fol_free 1 omega_subset_formula=false.
Proof. vm_compute. reflexivity. Qed.

Section Order.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma strong_ordinal_holds rho : FolHolds R rho strong_ordinal_formula <-> RelStrongOrdinal R (rho 2).
Proof.
  change (FolHolds R rho strong_ordinal_formula) with (b_holds R rho (strong_ordinal_builder 2) 3).
  unfold strong_ordinal_builder,RelStrongOrdinal.
  rewrite (b_holds_and EM),(ordinal_builder_holds EM) by lia.
  assert (K : 3<=b_next (b_ordinal 2) 3) by apply b_good_ordinal.
  rewrite b_holds_ain by lia.
  setoid_rewrite transitive_builder_holds; [|lia].
  setoid_rewrite update_variable_eq. reflexivity.
Qed.

Lemma empty_strong_ordinal a : RelEmpty R a -> RelStrongOrdinal R a.
Proof.
  intro E. unfold RelStrongOrdinal,RelOrdinal,RelTransitive,RelOrdinalLinear.
  repeat split; intros; exfalso; eapply E; eassumption.
Qed.

Lemma successor_strong_ordinal a b : RelStrongOrdinal R a -> RelSuccessor R b a -> RelStrongOrdinal R b.
Proof.
  intros [[Trans Linear] Members] Succ. split; [split|].
  - intros x y X Y. apply (proj2 (Succ y)).
    apply (proj1 (Succ x)) in X. destruct X as [X|X].
    + left. exact (Trans x y X Y).
    + subst x. now left.
  - intros x y X Y. apply (proj1 (Succ x)) in X. apply (proj1 (Succ y)) in Y.
    destruct X as [X|X],Y as [Y|Y].
    + exact (Linear x y X Y).
    + subst y. now left; left.
    + subst x. now right.
    + subst x y. now left; right.
  - intros x X. apply (proj1 (Succ x)) in X. destruct X as [X|X]; [now apply Members|now subst x].
Qed.

Theorem zf_internal_natural_strong_ordinal w : RelOmega R w ->
  forall n, R n w -> RelStrongOrdinal R n.
Proof.
  intro Omega. set (rho := fun _ : nat => w).
  assert (All : forall n, R n w -> FolHolds R (update_variable rho 2 n) strong_ordinal_formula).
  { apply (zf_internal_omega_induction R EM Model w strong_ordinal_formula rho);
      [exact Omega|exact strong_ordinal_fresh|reflexivity| |].
    - intros e Empty. rewrite strong_ordinal_holds,update_variable_eq. now apply empty_strong_ordinal.
    - intros x y X Succ H. rewrite strong_ordinal_holds,update_variable_eq in H |- *.
      now apply successor_strong_ordinal with (a:=x). }
  intros n N. specialize (All n N). now rewrite strong_ordinal_holds,update_variable_eq in All.
Qed.

Lemma omega_subset_holds rho : FolHolds R rho omega_subset_formula <-> RelSubset R (rho 2) (rho 0).
Proof.
  change (FolHolds R rho omega_subset_formula) with (b_holds R rho (b_subset 2 0) 3).
  apply subset_builder_holds; lia.
Qed.

Theorem zf_internal_natural_subset_omega w : RelOmega R w ->
  forall n, R n w -> RelSubset R n w.
Proof.
  intro Omega. set (rho := fun _ : nat => w).
  assert (All : forall n, R n w -> FolHolds R (update_variable rho 2 n) omega_subset_formula).
  { apply (zf_internal_omega_induction R EM Model w omega_subset_formula rho);
      [exact Omega|exact omega_subset_fresh|reflexivity| |].
    - intros e Empty. rewrite omega_subset_holds,update_variable_eq,update_variable_neq by lia.
      intros x X. exfalso. exact (Empty x X).
    - intros x y X Succ H. rewrite omega_subset_holds,update_variable_eq,update_variable_neq in H |- * by lia.
      intros z Z. apply (proj1 (Succ z)) in Z. destruct Z as [Z|Z]; [exact (H z Z)|now subst z]. }
  intros n N. specialize (All n N).
  rewrite omega_subset_holds,update_variable_eq,update_variable_neq in All by lia. exact All.
Qed.

Theorem zf_internal_omega_transitive w : RelOmega R w -> RelTransitive R w.
Proof. intros Omega x y X Y. exact (zf_internal_natural_subset_omega w Omega x X y Y). Qed.
End Order.

Print Assumptions zf_internal_natural_strong_ordinal.
Print Assumptions zf_internal_natural_subset_omega.
Print Assumptions zf_internal_omega_transitive.
