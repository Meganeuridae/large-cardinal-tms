(** Concrete finite membership paths and their well-founded consequences.
    Only finite sets are collected; no external well-foundedness of an
    arbitrary first-order model is assumed. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ProofFormula ProofPresentation FormulaSemantics BerkeleySyntaxBase
  BerkeleySyntaxInterpretation BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxZFBase BerkeleySyntaxZFUnion BerkeleySyntaxZFFoundation.
Import ListNotations.

Inductive MembershipPath {D} (R:D->D->Prop) : nat->D->D->Prop :=
| path_refl a : MembershipPath R 0 a a
| path_step n a b c : R a b -> MembershipPath R n b c -> MembershipPath R (S n) a c.

Lemma pair_operand_paths {D} (R:D->D->Prop) p x y : RelPair R p x y ->
  MembershipPath R 2 x p /\ MembershipPath R 2 y p.
Proof.
  intros [u [v [U [V P]]]].
  assert (Vx : R x v) by (apply (proj2 (V x)); now left).
  assert (Vy : R y v) by (apply (proj2 (V y)); now right).
  assert (Vp : R v p) by (apply (proj2 (P v)); now right).
  split; eapply path_step; [exact Vx|eapply path_step; [exact Vp|constructor]|exact Vy|eapply path_step; [exact Vp|constructor]].
Qed.
Lemma membership_path_append {D} (R:D->D->Prop) n m a b c :
  MembershipPath R n a b -> MembershipPath R m b c -> MembershipPath R (n+m) a c.
Proof. intros A B. induction A; cbn; [exact B|econstructor; eauto]. Qed.
Lemma node_operand_paths {D} (R:D->D->Prop) p tag x y : RelNode2 R p tag x y ->
  MembershipPath R 4 x p /\ MembershipPath R 4 y p.
Proof.
  intros [q [Q P]]. destruct (pair_operand_paths R q x y Q) as [X Y].
  destruct (pair_operand_paths R p tag q P) as [_ QP]. split.
  - exact (@membership_path_append D R 2 2 x q p X QP).
  - exact (@membership_path_append D R 2 2 y q p Y QP).
Qed.

Section FinitePaths.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Lemma zf_prefix_empty_exists (seed:D) : exists e, RelEmpty R e.
Proof.
  set (rho := fun _ : nat => seed).
  pose proof (Model 15 (nth 15 candidate_axioms (Hole 0)) (fun n=>n) (fun _=>FEqual 0 0) rho
    ltac:(lia) ltac:(reflexivity)) as H.
  change (b_holds R rho (b_ex (fun e => b_empty e)) 0) in H.
  rewrite (b_holds_ex EM) in H. destruct H as [e H]. rewrite empty_builder_holds in H by lia.
  rewrite update_variable_eq in H. now exists e.
Qed.
Lemma zf_finite_set_exists (seed:D) (xs:list D) : exists a, forall x, R x a <-> In x xs.
Proof.
  induction xs as [|x xs IH].
  - destruct (zf_prefix_empty_exists seed) as [a A]. exists a. intro z. cbn. split; [apply A|tauto].
  - destruct IH as [a A]. destruct (zf_prefix_singleton_exists R EM Model x) as [one One].
    destruct (zf_prefix_binary_union_exists R EM Model one a) as [b B]. exists b. intro z.
    rewrite (B z),(One z),(A z). cbn. split; intros [E|E]; [left; symmetry|right|left; symmetry|right]; assumption.
Qed.

Lemma membership_path_covered n a b : MembershipPath R n a b -> exists xs:list D,
  In a xs /\ In b xs /\ forall x, In x xs -> x=a \/ exists y, In y xs /\ R y x.
Proof.
  intro Path. induction Path as [a|n a b c Edge Path IH].
  - exists [a]. cbn. repeat split; auto. intros x [E|E]; [now left|contradiction].
  - destruct IH as [xs [B [C Cover]]]. exists (a::xs). split; [now left|]. split; [now right|].
    intros x [Eq|In]; [left; now symmetry|]. destruct (Cover x In) as [Eq|[y [Y Yx]]].
    + subst x. right. exists a. split; [now left|exact Edge].
    + right. exists y. split; [now right|exact Yx].
Qed.

Theorem zf_no_finite_membership_cycle n a : n>0 -> ~MembershipPath R n a a.
Proof.
  intros Positive Path. destruct n as [|n]; [lia|].
  inversion Path as [|n' a' mid final Edge Rest]; subst.
  destruct (membership_path_covered n mid a Rest) as [xs [B [A Cover]]].
  destruct (zf_finite_set_exists a xs) as [set Setspec].
  assert (Nonempty : exists x, R x set) by (exists a; apply (proj2 (Setspec a)); exact A).
  destruct (zf_prefix_foundation R EM Model set Nonempty) as [v [V Min]].
  apply (proj1 (Setspec v)) in V. destruct (Cover v V) as [Eq|[y [Y Edge']]].
  - subst v. apply (Min a Edge),(proj2 (Setspec a)),A.
  - apply (Min y Edge'),(proj2 (Setspec y)),Y.
Qed.
End FinitePaths.

Print Assumptions pair_operand_paths.
Print Assumptions node_operand_paths.
Print Assumptions zf_no_finite_membership_cycle.
