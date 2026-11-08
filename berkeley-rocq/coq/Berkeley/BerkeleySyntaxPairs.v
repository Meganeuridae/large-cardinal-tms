(** Semantic contracts for the set-theoretic pair/graph abbreviations.
    All claims hold over an arbitrary binary relation, with classical logic
    stated explicitly as a parameter. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation FormulaSemantics.
Import ListNotations.

Definition RelSingleton {D : Type} (R:D->D->Prop) a x := forall z, R z a <-> z=x.
Definition RelDoubleton {D : Type} (R:D->D->Prop) a x y := forall z, R z a <-> z=x \/ z=y.
Definition RelPair {D : Type} (R:D->D->Prop) p x y :=
  exists u v, RelSingleton R u x /\ RelDoubleton R v x y /\ RelDoubleton R p u v.
Definition RelGraph {D : Type} (R:D->D->Prop) r x y := exists p, RelPair R p x y /\ R p r.

Section Semantics.
Variable EM : forall P : Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem singleton_builder_holds rho a x n : a<n -> x<n ->
  (b_holds R rho (b_singleton a x) n <-> RelSingleton R (rho a) (rho x)).
Proof.
  intros A X. unfold b_singleton,RelSingleton. rewrite b_holds_all. split; intros H z; specialize (H z).
  - apply (proj1 (b_holds_iff EM _ _ _ _ _)) in H.
    rewrite b_holds_mem,b_holds_eq in H. cbn [b_next b_mem] in H.
    rewrite !update_variable_eq in H. rewrite !update_variable_neq in H by lia. exact H.
  - apply (proj2 (b_holds_iff EM _ _ _ _ _)).
    rewrite b_holds_mem,b_holds_eq. cbn [b_next b_mem].
    rewrite !update_variable_eq. rewrite !update_variable_neq by lia. exact H.
Qed.

Theorem doubleton_builder_holds rho a x y n : a<n -> x<n -> y<n ->
  (b_holds R rho (b_doubleton a x y) n <-> RelDoubleton R (rho a) (rho x) (rho y)).
Proof.
  intros A X Y. unfold b_doubleton,RelDoubleton. rewrite b_holds_all. split; intros H z; specialize (H z).
  - apply (proj1 (b_holds_iff EM _ _ _ _ _)) in H.
    rewrite b_holds_mem, (b_holds_or EM), !b_holds_eq in H. cbn [b_next b_mem b_eq] in H.
    rewrite !update_variable_eq in H. rewrite !update_variable_neq in H by lia. exact H.
  - apply (proj2 (b_holds_iff EM _ _ _ _ _)).
    rewrite b_holds_mem, (b_holds_or EM), !b_holds_eq. cbn [b_next b_mem b_eq].
    rewrite !update_variable_eq. rewrite !update_variable_neq by lia. exact H.
Qed.

Lemma pair_body_holds sigma p x y n : p<n -> x<n -> y<n ->
  (b_holds R sigma
    (b_and3 (b_singleton n x) (b_doubleton (S n) x y) (b_doubleton p n (S n))) (S(S n)) <->
   RelSingleton R (sigma n) (sigma x) /\
   RelDoubleton R (sigma (S n)) (sigma x) (sigma y) /\
   RelDoubleton R (sigma p) (sigma n) (sigma (S n))).
Proof.
  intros P X Y. unfold b_and3. rewrite !b_holds_and by exact EM.
  change ((b_holds R sigma (b_singleton n x) (S(S n)) /\
           b_holds R sigma (b_doubleton (S n) x y) (S(S(S n)))) /\
           b_holds R sigma (b_doubleton p n (S n)) (S(S(S(S n)))) <->
          RelSingleton R (sigma n) (sigma x) /\
          RelDoubleton R (sigma (S n)) (sigma x) (sigma y) /\
          RelDoubleton R (sigma p) (sigma n) (sigma (S n))).
  rewrite singleton_builder_holds by lia. rewrite !doubleton_builder_holds by lia. tauto.
Qed.

Theorem pair_builder_holds rho p x y n : p<n -> x<n -> y<n ->
  (b_holds R rho (b_pair p x y) n <-> RelPair R (rho p) (rho x) (rho y)).
Proof.
  intros P X Y. unfold b_pair. rewrite (b_holds_ex EM). split.
  - intros [u H]. apply (proj1 (b_holds_ex EM _ _ _ _)) in H. destruct H as [v H].
    set (sigma := update_variable (update_variable rho n u) (S n) v) in *.
    apply (proj1 (pair_body_holds sigma p x y n P X Y)) in H.
    assert (Su : sigma n=u) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sv : sigma (S n)=v) by (unfold sigma; apply update_variable_eq).
    assert (Sp : sigma p=rho p) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sx : sigma x=rho x) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sy : sigma y=rho y) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    rewrite Su,Sv,Sp,Sx,Sy in H. unfold RelPair. eauto.
  - intros [u [v [H1 [H2 H3]]]]. exists u.
    apply (proj2 (b_holds_ex EM _ _ _ _)). exists v.
    set (sigma := update_variable (update_variable rho n u) (S n) v).
    change (b_holds R sigma (b_and3 (b_singleton n x) (b_doubleton (S n) x y)
      (b_doubleton p n (S n))) (S(S n))).
    apply (proj2 (pair_body_holds sigma p x y n P X Y)).
    assert (Su : sigma n=u) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sv : sigma (S n)=v) by (unfold sigma; apply update_variable_eq).
    assert (Sp : sigma p=rho p) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sx : sigma x=rho x) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    assert (Sy : sigma y=rho y) by (unfold sigma; rewrite !update_variable_neq by lia; reflexivity).
    now rewrite Su,Sv,Sp,Sx,Sy.
Qed.

Theorem relation_builder_holds rho r x y n : r<n -> x<n -> y<n ->
  (b_holds R rho (b_rel r x y) n <-> RelGraph R (rho r) (rho x) (rho y)).
Proof.
  intros Hr Hx Hy. unfold b_rel. rewrite (b_holds_ex EM). split.
  - intros [p H]. apply (proj1 (b_holds_and EM _ _ _ _ _)) in H as [Pair Mem].
    apply (proj1 (pair_builder_holds (update_variable rho n p) n x y (S n) ltac:(lia) ltac:(lia) ltac:(lia))) in Pair.
    apply b_holds_mem in Mem. rewrite update_variable_eq in Pair,Mem.
    repeat rewrite update_variable_neq in Pair by lia.
    repeat rewrite update_variable_neq in Mem by lia.
    unfold RelGraph. eauto.
  - intros [p [Pair Mem]]. exists p. apply (proj2 (b_holds_and EM _ _ _ _ _)). split.
    + apply (proj2 (pair_builder_holds (update_variable rho n p) n x y (S n) ltac:(lia) ltac:(lia) ltac:(lia))).
      rewrite update_variable_eq, !update_variable_neq by lia. exact Pair.
    + apply (proj2 (b_holds_mem _ _ _ _ _)).
      rewrite update_variable_eq, update_variable_neq by lia. exact Mem.
Qed.

Lemma b_next_pair p x y n : b_next (b_pair p x y) n = n+5.
Proof.
  unfold b_next,b_pair,b_ex,b_not,b_all,b_and3,b_and,b_binary,b_singleton,b_doubleton,b_iff,b_or,b_eq,b_mem.
  cbn. lia.
Qed.

Definition RelNode2 {D : Type} (R:D->D->Prop) p tag x y :=
  exists q, RelPair R q x y /\ RelPair R p tag q.

Theorem node2_builder_holds rho p tag x y n : p<n -> tag<n -> x<n -> y<n ->
  (b_holds R rho (b_node2 p tag x y) n <-> RelNode2 R (rho p) (rho tag) (rho x) (rho y)).
Proof.
  intros Hp Ht Hx Hy. unfold b_node2. rewrite (b_holds_ex EM). split.
  - intros [q H]. apply (proj1 (b_holds_and EM _ _ _ _ _)) in H as [A B].
    apply (proj1 (pair_builder_holds (update_variable rho n q) n x y (S n) ltac:(lia) ltac:(lia) ltac:(lia))) in A.
    rewrite b_next_pair in B.
    apply (proj1 (pair_builder_holds (update_variable rho n q) p tag n (S n+5) ltac:(lia) ltac:(lia) ltac:(lia))) in B.
    rewrite update_variable_eq in A,B.
    repeat rewrite update_variable_neq in A by lia.
    repeat rewrite update_variable_neq in B by lia.
    unfold RelNode2. eauto.
  - intros [q [A B]]. exists q. apply (proj2 (b_holds_and EM _ _ _ _ _)). split.
    + apply (proj2 (pair_builder_holds (update_variable rho n q) n x y (S n) ltac:(lia) ltac:(lia) ltac:(lia))).
      rewrite update_variable_eq, !update_variable_neq by lia. exact A.
    + rewrite b_next_pair.
      apply (proj2 (pair_builder_holds (update_variable rho n q) p tag n (S n+5) ltac:(lia) ltac:(lia) ltac:(lia))).
      rewrite update_variable_eq, !update_variable_neq by lia. exact B.
Qed.
End Semantics.

Print Assumptions singleton_builder_holds.
Print Assumptions doubleton_builder_holds.
Print Assumptions pair_builder_holds.
Print Assumptions relation_builder_holds.
Print Assumptions node2_builder_holds.
