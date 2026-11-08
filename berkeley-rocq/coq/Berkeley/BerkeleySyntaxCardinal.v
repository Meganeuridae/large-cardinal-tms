(** The ordinal and cardinal components as relational semantic predicates. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxSets
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxBijection FormulaSemantics.
Import ListNotations.

Definition ordinal_linear_builder a := b_ain a (fun x => b_ain a (fun y =>
  b_or3 (b_mem x y) (b_eq x y) (b_mem y x))).
Definition RelOrdinalLinear {D} (R:D->D->Prop) a :=
  forall x y, R x a -> R y a -> (R x y \/ x=y) \/ R y x.
Definition RelOrdinal {D} (R:D->D->Prop) a := RelTransitive R a /\ RelOrdinalLinear R a.
Definition RelCardinal {D} (R:D->D->Prop) d :=
  RelOrdinal R d /\ forall a, R a d -> ~exists f, RelBijection R f a d.

Lemma b_good_transitive a : b_good (b_transitive a).
Proof. unfold b_transitive. apply b_good_ain. intro x. apply b_good_ain. intro y. apply b_good_mem. Qed.
Lemma b_good_ordinal_linear a : b_good (ordinal_linear_builder a).
Proof.
  unfold ordinal_linear_builder. apply b_good_ain. intro x. apply b_good_ain. intro y.
  unfold b_or3,b_or. apply b_good_binary; [apply b_good_binary; [apply b_good_mem|apply b_good_eq]|apply b_good_mem].
Qed.
Lemma b_good_ordinal a : b_good (b_ordinal a).
Proof.
  unfold b_ordinal. change (b_good (b_and (b_transitive a) (ordinal_linear_builder a))).
  unfold b_and. apply b_good_binary; [apply b_good_transitive|apply b_good_ordinal_linear].
Qed.

Section CardinalSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem ordinal_linear_builder_holds rho a n : a<n ->
  (b_holds R rho (ordinal_linear_builder a) n <-> RelOrdinalLinear R (rho a)).
Proof.
  intro A. unfold ordinal_linear_builder,RelOrdinalLinear. rewrite b_holds_ain by exact A. split.
  - intros H x y X Y. specialize (H x X). rewrite b_holds_ain in H by lia.
    specialize (H y). rewrite update_variable_neq in H by lia. specialize (H Y).
    unfold b_or3 in H. rewrite !(b_holds_or EM),!b_holds_mem,b_holds_eq in H.
    cbn [b_next b_or b_binary b_mem b_eq] in H.
    set (sigma := update_variable (update_variable rho n x) (S n) y) in H.
    assert (Sx : sigma n=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    now rewrite Sx,Sy in H.
  - intros H x X. rewrite b_holds_ain by lia. intros y Y.
    rewrite update_variable_neq in Y by lia.
    unfold b_or3. rewrite !(b_holds_or EM),!b_holds_mem,b_holds_eq.
    cbn [b_next b_or b_binary b_mem b_eq].
    set (sigma := update_variable (update_variable rho n x) (S n) y).
    change ((R (sigma n) (sigma (S n)) \/ sigma n=sigma (S n)) \/ R (sigma (S n)) (sigma n)).
    assert (Sx : sigma n=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S n)=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sx,Sy. now apply H.
Qed.

Theorem ordinal_builder_holds rho a n : a<n ->
  (b_holds R rho (b_ordinal a) n <-> RelOrdinal R (rho a)).
Proof.
  intro A. unfold b_ordinal,RelOrdinal.
  change (b_holds R rho (b_and (b_transitive a) (ordinal_linear_builder a)) n <->
    RelTransitive R (rho a) /\ RelOrdinalLinear R (rho a)).
  rewrite (b_holds_and EM),transitive_builder_holds by exact A.
  assert (K : n <= b_next (b_transitive a) n) by apply b_good_transitive.
  rewrite ordinal_linear_builder_holds by lia. reflexivity.
Qed.

Lemma no_bijection_builder_holds rho a d n : a<n -> d<n ->
  (b_holds R rho (b_not (b_ex (fun f => b_bijection f a d))) n <->
   ~exists f, RelBijection R f (rho a) (rho d)).
Proof.
  intros A D0. rewrite b_holds_not,(b_holds_ex EM). split.
  - intros H [f Bij]. apply H. exists f. rewrite (bijection_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact Bij.
  - intros H [f Bij]. apply H. exists f. rewrite (bijection_builder_holds EM) in Bij by lia.
    rewrite update_variable_eq in Bij. repeat rewrite update_variable_neq in Bij by lia. exact Bij.
Qed.

Theorem cardinal_builder_holds rho d n : d<n ->
  (b_holds R rho (b_cardinal d) n <-> RelCardinal R (rho d)).
Proof.
  intro D0. unfold b_cardinal,RelCardinal. rewrite (b_holds_and EM),ordinal_builder_holds by exact D0.
  assert (K : n <= b_next (b_ordinal d) n) by apply b_good_ordinal.
  rewrite b_holds_ain by lia. split; intros [Ord H]; split; try assumption; intros a A; specialize (H a A).
  - apply (proj1 (no_bijection_builder_holds (update_variable rho (b_next (b_ordinal d) n) a)
      (b_next (b_ordinal d) n) d (S (b_next (b_ordinal d) n)) ltac:(lia) ltac:(lia))) in H.
    rewrite update_variable_eq in H. rewrite update_variable_neq in H by lia. exact H.
  - apply (proj2 (no_bijection_builder_holds (update_variable rho (b_next (b_ordinal d) n) a)
      (b_next (b_ordinal d) n) d (S (b_next (b_ordinal d) n)) ltac:(lia) ltac:(lia))).
    rewrite update_variable_eq,update_variable_neq by lia. exact H.
Qed.
End CardinalSemantics.

Print Assumptions ordinal_builder_holds.
Print Assumptions cardinal_builder_holds.
