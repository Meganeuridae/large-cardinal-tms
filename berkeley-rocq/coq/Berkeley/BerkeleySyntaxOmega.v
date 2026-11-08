(** Relational interpretation of the finite inductive-set and omega clauses. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxSets FormulaSemantics.
Import ListNotations.

Definition inductive_zero_builder a := b_ein a (fun e => b_empty e).
Definition inductive_successor_builder a := b_ain a (fun x => b_ein a (fun y => b_successor y x)).
Definition RelInductive {D} (R:D->D->Prop) a :=
  (exists e, R e a /\ RelEmpty R e) /\
  (forall x, R x a -> exists y, R y a /\ RelSuccessor R y x).
Definition RelOmega {D} (R:D->D->Prop) w :=
  RelInductive R w /\ forall a, RelInductive R a -> RelSubset R w a.

Lemma b_good_empty a : b_good (b_empty a).
Proof. unfold b_empty. apply b_good_all. intro x. apply b_good_not,b_good_mem. Qed.
Lemma b_good_successor y x : b_good (b_successor y x).
Proof.
  unfold b_successor. apply b_good_all. intro z. unfold b_iff,b_or.
  apply b_good_binary; [apply b_good_mem|]. apply b_good_binary; [apply b_good_mem|apply b_good_eq].
Qed.
Lemma b_good_inductive_zero a : b_good (inductive_zero_builder a).
Proof. unfold inductive_zero_builder. apply b_good_ein. intro e. apply b_good_empty. Qed.
Lemma b_good_inductive_successor a : b_good (inductive_successor_builder a).
Proof.
  unfold inductive_successor_builder. apply b_good_ain. intro x. apply b_good_ein. intro y. apply b_good_successor.
Qed.
Lemma b_good_inductive a : b_good (b_inductive a).
Proof.
  unfold b_inductive. change (b_good (b_and (inductive_zero_builder a) (inductive_successor_builder a))).
  unfold b_and. apply b_good_binary; [apply b_good_inductive_zero|apply b_good_inductive_successor].
Qed.

Section OmegaSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem inductive_zero_builder_holds rho a n : a<n ->
  (b_holds R rho (inductive_zero_builder a) n <-> exists e, R e (rho a) /\ RelEmpty R e).
Proof.
  intro A. unfold inductive_zero_builder. rewrite (b_holds_ein EM) by exact A. split.
  - intros [e [M E]]. rewrite empty_builder_holds in E by lia. rewrite update_variable_eq in E. now exists e.
  - intros [e [M E]]. exists e. split; [exact M|]. rewrite empty_builder_holds by lia.
    rewrite update_variable_eq. exact E.
Qed.

Theorem inductive_successor_builder_holds rho a n : a<n ->
  (b_holds R rho (inductive_successor_builder a) n <->
   forall x, R x (rho a) -> exists y, R y (rho a) /\ RelSuccessor R y x).
Proof.
  intro A. unfold inductive_successor_builder. rewrite b_holds_ain by exact A. split.
  - intros H x X. specialize (H x X). rewrite (b_holds_ein EM) in H by lia.
    destruct H as [y [Y S]]. rewrite (@successor_builder_holds D R EM) in S by lia.
    rewrite update_variable_neq in Y by lia.
    rewrite update_variable_eq in S. rewrite update_variable_neq in S by lia.
    rewrite update_variable_eq in S. exists y. auto.
  - intros H x X. specialize (H x X). destruct H as [y [Y S]].
    rewrite (b_holds_ein EM) by lia. exists y. split.
    + rewrite update_variable_neq by lia. exact Y.
    + rewrite (@successor_builder_holds D R EM) by lia.
      rewrite update_variable_eq,update_variable_neq by lia. rewrite update_variable_eq. exact S.
Qed.

Theorem inductive_builder_holds rho a n : a<n ->
  (b_holds R rho (b_inductive a) n <-> RelInductive R (rho a)).
Proof.
  intro A. unfold b_inductive,RelInductive.
  change (b_holds R rho (b_and (inductive_zero_builder a) (inductive_successor_builder a)) n <->
    (exists e, R e (rho a) /\ RelEmpty R e) /\
    (forall x, R x (rho a) -> exists y, R y (rho a) /\ RelSuccessor R y x)).
  rewrite (b_holds_and EM),inductive_zero_builder_holds by exact A.
  assert (K : n <= b_next (inductive_zero_builder a) n) by apply b_good_inductive_zero.
  rewrite inductive_successor_builder_holds by lia. reflexivity.
Qed.

Theorem omega_builder_holds rho w n : w<n ->
  (b_holds R rho (b_omega w) n <-> RelOmega R (rho w)).
Proof.
  intro W. unfold b_omega,RelOmega. rewrite (b_holds_and EM),inductive_builder_holds by exact W.
  assert (K : n <= b_next (b_inductive w) n) by apply b_good_inductive.
  rewrite b_holds_all. split; intros [Ind H]; split; try assumption; intros a.
  - specialize (H a). rewrite b_holds_imp in H.
    rewrite inductive_builder_holds in H by lia.
    assert (J : S (b_next (b_inductive w) n) <=
      b_next (b_inductive (b_next (b_inductive w) n)) (S (b_next (b_inductive w) n)))
      by apply b_good_inductive.
    rewrite subset_builder_holds in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - specialize (H a). rewrite b_holds_imp.
    rewrite inductive_builder_holds by lia.
    assert (J : S (b_next (b_inductive w) n) <=
      b_next (b_inductive (b_next (b_inductive w) n)) (S (b_next (b_inductive w) n)))
      by apply b_good_inductive.
    rewrite subset_builder_holds by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.
End OmegaSemantics.

Print Assumptions inductive_builder_holds.
Print Assumptions omega_builder_holds.
