(** Interpreting the hygienic syntax builder over an arbitrary membership
    relation. Classical reasoning is an explicit hypothesis, never an axiom. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase ProofFormula FormulaSemantics.
Import ListNotations.

Definition b_next (p : builder) n := snd (p n).
Definition b_holds {D : Type} (R : D -> D -> Prop) (rho : nat -> D) (p : builder) n : Prop :=
  FolHolds R rho (instantiate_formula (fun _ => 0) (fst (p n))).

Lemma b_holds_eq {D} (R : D->D->Prop) rho x y n :
  b_holds R rho (b_eq x y) n <-> rho x = rho y.
Proof. reflexivity. Qed.
Lemma b_holds_mem {D} (R : D->D->Prop) rho x y n :
  b_holds R rho (b_mem x y) n <-> R (rho x) (rho y).
Proof. reflexivity. Qed.
Lemma b_holds_not {D} (R : D->D->Prop) rho p n :
  b_holds R rho (b_not p) n <-> ~b_holds R rho p n.
Proof. unfold b_holds,b_not. destruct (p n). reflexivity. Qed.
Lemma b_holds_imp {D} (R : D->D->Prop) rho p q n :
  b_holds R rho (b_imp p q) n <-> (b_holds R rho p n -> b_holds R rho q (b_next p n)).
Proof.
  unfold b_holds,b_imp,b_binary,b_next. destruct (p n) as [a k]. cbn.
  destruct (q k) as [b m]. reflexivity.
Qed.
Lemma b_holds_all {D} (R : D->D->Prop) rho body n :
  b_holds R rho (b_all body) n <->
  forall a, b_holds R (update_variable rho n a) (body n) (S n).
Proof.
  unfold b_holds,b_all. destruct (body n (S n)). reflexivity.
Qed.

Section ClassicalDerivedConnectives.
Variable excluded_middle : forall P : Prop, P \/ ~P.

Lemma b_holds_and {D} (R : D->D->Prop) rho p q n :
  b_holds R rho (b_and p q) n <-> b_holds R rho p n /\ b_holds R rho q (b_next p n).
Proof.
  unfold b_holds,b_and,b_binary,b_next. destruct (p n) as [a k]. cbn.
  destruct (q k) as [b m].
  cbn [fst instantiate_formula FolHolds].
  set (P := FolHolds R rho (instantiate_formula (fun _ => 0) a)).
  set (Q := FolHolds R rho (instantiate_formula (fun _ => 0) b)).
  split.
  - intro H. split.
    + destruct (excluded_middle P); [assumption|]. exfalso. apply H. tauto.
    + destruct (excluded_middle Q); [assumption|]. exfalso. apply H. tauto.
  - intros [HP HQ] K. exact (K HP HQ).
Qed.

Lemma b_holds_or {D} (R : D->D->Prop) rho p q n :
  b_holds R rho (b_or p q) n <-> b_holds R rho p n \/ b_holds R rho q (b_next p n).
Proof.
  unfold b_holds,b_or,b_binary,b_next. destruct (p n) as [a k]. cbn.
  destruct (q k) as [b m].
  cbn [fst instantiate_formula FolHolds].
  set (P := FolHolds R rho (instantiate_formula (fun _ => 0) a)).
  set (Q := FolHolds R rho (instantiate_formula (fun _ => 0) b)).
  split.
  - intro H. destruct (excluded_middle P) as [T|F]; [now left|right; now apply H].
  - intros [T|T] N; [contradiction|exact T].
Qed.

Lemma b_holds_iff {D} (R : D->D->Prop) rho p q n :
  b_holds R rho (b_iff p q) n <-> (b_holds R rho p n <-> b_holds R rho q (b_next p n)).
Proof.
  unfold b_holds,b_iff,b_binary,b_next. destruct (p n) as [a k]. cbn.
  destruct (q k) as [b m].
  cbn [fst instantiate_formula FolHolds].
  set (P := FolHolds R rho (instantiate_formula (fun _ => 0) a)).
  set (Q := FolHolds R rho (instantiate_formula (fun _ => 0) b)).
  split.
  - intro H. split.
    + destruct (excluded_middle (P->Q)); [assumption|]. exfalso. apply H. tauto.
    + destruct (excluded_middle (Q->P)); [assumption|]. exfalso. apply H. tauto.
  - intros [A B] K. exact (K A B).
Qed.

Lemma b_holds_ex {D} (R : D->D->Prop) rho body n :
  b_holds R rho (b_ex body) n <->
  exists a, b_holds R (update_variable rho n a) (body n) (S n).
Proof.
  unfold b_ex. rewrite b_holds_not,b_holds_all. setoid_rewrite b_holds_not.
  split.
  - intro H. destruct (excluded_middle (exists a, b_holds R (update_variable rho n a) (body n) (S n))) as [E|E];
      [exact E|]. exfalso. apply H. intros a A. apply E. now exists a.
  - intros [a A] H. exact (H a A).
Qed.

Lemma b_holds_ain {D} (R : D->D->Prop) rho a body n : a<n ->
  (b_holds R rho (b_ain a body) n <->
   forall x, R x (rho a) -> b_holds R (update_variable rho n x) (body n) (S n)).
Proof.
  intro A. unfold b_ain. rewrite b_holds_all. split; intros H x; specialize (H x).
  - rewrite b_holds_imp,b_holds_mem in H. cbn [b_next b_mem] in H.
    rewrite update_variable_eq,update_variable_neq in H by lia. exact H.
  - rewrite b_holds_imp,b_holds_mem. cbn [b_next b_mem].
    rewrite update_variable_eq,update_variable_neq by lia. exact H.
Qed.

Lemma b_holds_ein {D} (R : D->D->Prop) rho a body n : a<n ->
  (b_holds R rho (b_ein a body) n <->
   exists x, R x (rho a) /\ b_holds R (update_variable rho n x) (body n) (S n)).
Proof.
  intro A. unfold b_ein. rewrite b_holds_ex. split.
  - intros [x H]. apply (proj1 (b_holds_and _ _ _ _ _)) in H as [M B].
    apply b_holds_mem in M. cbn [b_next b_mem] in B.
    rewrite update_variable_eq,update_variable_neq in M by lia. now exists x.
  - intros [x [M B]]. exists x. apply (proj2 (b_holds_and _ _ _ _ _)). split.
    + apply (proj2 (b_holds_mem _ _ _ _ _)).
      rewrite update_variable_eq,update_variable_neq by lia. exact M.
    + cbn [b_next b_mem]. exact B.
Qed.
End ClassicalDerivedConnectives.

Definition b_good (p : builder) := forall n, n <= b_next p n.
Lemma b_good_eq x y : b_good (b_eq x y).
Proof. intro n. reflexivity. Qed.
Lemma b_good_mem x y : b_good (b_mem x y).
Proof. intro n. reflexivity. Qed.
Lemma b_good_not p : b_good p -> b_good (b_not p).
Proof. unfold b_good,b_next,b_not. intro H. intro n. specialize (H n). destruct (p n). exact H. Qed.
Lemma b_good_binary op p q : b_good p -> b_good q -> b_good (b_binary op p q).
Proof.
  unfold b_good,b_next,b_binary. intros P Q n. specialize (P n). destruct (p n) as [a k].
  specialize (Q k). destruct (q k). simpl in *. lia.
Qed.
Lemma b_good_all body : (forall x, b_good (body x)) -> b_good (b_all body).
Proof.
  unfold b_good,b_next,b_all. intros H n. specialize (H n (S n)). destruct (body n (S n)). simpl in *. lia.
Qed.
Lemma b_good_ex body : (forall x, b_good (body x)) -> b_good (b_ex body).
Proof. intro H. unfold b_ex. apply b_good_not,b_good_all. intro x. now apply b_good_not. Qed.
Lemma b_good_ain a body : (forall x, b_good (body x)) -> b_good (b_ain a body).
Proof.
  intro H. unfold b_ain. apply b_good_all. intro x. unfold b_imp.
  apply b_good_binary; [apply b_good_mem|apply H].
Qed.
Lemma b_good_ein a body : (forall x, b_good (body x)) -> b_good (b_ein a body).
Proof.
  intro H. unfold b_ein. apply b_good_ex. intro x. unfold b_and.
  apply b_good_binary; [apply b_good_mem|apply H].
Qed.

Print Assumptions b_holds_and.
Print Assumptions b_holds_ex.
Print Assumptions b_holds_ain.
Print Assumptions b_holds_ein.
Print Assumptions b_good_binary.
Print Assumptions b_good_ain.
Print Assumptions b_good_ein.
