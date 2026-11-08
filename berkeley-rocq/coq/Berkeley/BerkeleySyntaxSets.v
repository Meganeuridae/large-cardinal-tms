(** Basic relational interpretations of empty, subset, successor, and
    transitivity abbreviations. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation FormulaSemantics.
Import ListNotations.

Definition RelEmpty {D} (R:D->D->Prop) a := forall x, ~R x a.
Definition RelSubset {D} (R:D->D->Prop) a b := forall x, R x a -> R x b.
Definition RelSuccessor {D} (R:D->D->Prop) y x := forall z, R z y <-> R z x \/ z=x.
Definition RelTransitive {D} (R:D->D->Prop) a := forall x y, R x a -> R y x -> R y a.

Section Sets.
Variable D : Type.
Variable R : D->D->Prop.

Theorem empty_builder_holds rho a n : a<n ->
  (b_holds R rho (b_empty a) n <-> RelEmpty R (rho a)).
Proof.
  intro A. unfold b_empty,RelEmpty. rewrite b_holds_all. split; intros H x; specialize (H x).
  - rewrite b_holds_not,b_holds_mem in H. rewrite update_variable_eq,update_variable_neq in H by lia. exact H.
  - rewrite b_holds_not,b_holds_mem. rewrite update_variable_eq,update_variable_neq by lia. exact H.
Qed.

Theorem subset_builder_holds rho a b n : a<n -> b<n ->
  (b_holds R rho (b_subset a b) n <-> RelSubset R (rho a) (rho b)).
Proof.
  intros A B. unfold b_subset,RelSubset. rewrite b_holds_ain by exact A.
  split; intros H x X; specialize (H x X).
  - apply b_holds_mem in H. rewrite update_variable_eq,update_variable_neq in H by lia. exact H.
  - apply (proj2 (b_holds_mem _ _ _ _ _)). rewrite update_variable_eq,update_variable_neq by lia. exact H.
Qed.

Theorem successor_builder_holds (EM : forall P:Prop, P \/ ~P) rho y x n : y<n -> x<n ->
  (b_holds R rho (b_successor y x) n <-> RelSuccessor R (rho y) (rho x)).
Proof.
  intros Y X. unfold b_successor,RelSuccessor. rewrite b_holds_all. split; intros H z; specialize (H z).
  - apply (proj1 (b_holds_iff EM _ _ _ _ _)) in H.
    rewrite b_holds_mem, (b_holds_or EM),b_holds_mem,b_holds_eq in H.
    cbn [b_next b_mem] in H. rewrite !update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - apply (proj2 (b_holds_iff EM _ _ _ _ _)).
    rewrite b_holds_mem, (b_holds_or EM),b_holds_mem,b_holds_eq.
    cbn [b_next b_mem]. rewrite !update_variable_eq.
    repeat rewrite update_variable_neq by lia. exact H.
Qed.

Theorem transitive_builder_holds rho a n : a<n ->
  (b_holds R rho (b_transitive a) n <-> RelTransitive R (rho a)).
Proof.
  intro A. unfold b_transitive,RelTransitive. rewrite b_holds_ain by exact A. split.
  - intros H x y X Y. specialize (H x X). rewrite b_holds_ain in H by lia.
    specialize (H y). rewrite update_variable_eq in H. specialize (H Y).
    apply b_holds_mem in H. rewrite update_variable_eq in H.
    repeat rewrite update_variable_neq in H by lia. exact H.
  - intros H x X. rewrite b_holds_ain by lia. intros y Y.
    rewrite update_variable_eq in Y. apply (proj2 (b_holds_mem _ _ _ _ _)).
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. now apply H with (x:=x).
Qed.
End Sets.

Print Assumptions empty_builder_holds.
Print Assumptions subset_builder_holds.
Print Assumptions successor_builder_holds.
Print Assumptions transitive_builder_holds.
