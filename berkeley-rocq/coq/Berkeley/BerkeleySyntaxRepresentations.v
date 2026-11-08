(** Standard finite formulas are members of any extensionally interpreted set
    closed under the five represented syntax constructors. This uses only the
    inclusion of standard numerals in internal omega, never its exhaustiveness. *)
From Stdlib Require Import Arith.Arith.
From Berkeley Require Import ProofFormula BerkeleySyntaxPairs BerkeleySyntaxFormulaSet.

Definition RelExtensional {D} (R:D->D->Prop) :=
  forall a b, (forall x, R x a <-> R x b) -> a=b.

Lemma relational_singleton_unique {D} (R:D->D->Prop) : RelExtensional R -> forall a b x,
  RelSingleton R a x -> RelSingleton R b x -> a=b.
Proof. intros Ext a b x A B. apply Ext. intro z. specialize (A z). specialize (B z). tauto. Qed.
Lemma relational_doubleton_unique {D} (R:D->D->Prop) : RelExtensional R -> forall a b x y,
  RelDoubleton R a x y -> RelDoubleton R b x y -> a=b.
Proof. intros Ext a b x y A B. apply Ext. intro z. specialize (A z). specialize (B z). tauto. Qed.
Lemma relational_pair_unique {D} (R:D->D->Prop) : RelExtensional R -> forall p q x y,
  RelPair R p x y -> RelPair R q x y -> p=q.
Proof.
  intros Ext p q x y [a [b [A [B C]]]] [a' [b' [A' [B' C']]]].
  assert (E1 : a=a') by (eapply relational_singleton_unique; eassumption).
  assert (E2 : b=b') by (eapply relational_doubleton_unique; eassumption).
  subst a' b'. eapply relational_doubleton_unique; eassumption.
Qed.
Lemma relational_node_unique {D} (R:D->D->Prop) : RelExtensional R -> forall p q tag x y,
  RelNode2 R p tag x y -> RelNode2 R q tag x y -> p=q.
Proof.
  intros Ext p q tag x y [a [A P]] [b [B Q]].
  assert (a=b) by (eapply relational_pair_unique; eassumption). subst b.
  eapply relational_pair_unique; eassumption.
Qed.

Theorem standard_formulas_in_closed_set {D} (R:D->D->Prop) number code f w te tm tn ti ta :
  RelExtensional R -> (forall x, R (number x) w) -> RelClosedFormulas R f w te tm tn ti ta ->
  (forall x y, RelNode2 R (code (FEqual x y)) te (number x) (number y)) ->
  (forall x y, RelNode2 R (code (FMember x y)) tm (number x) (number y)) ->
  (forall p, RelPair R (code (FNeg p)) tn (code p)) ->
  (forall p q, RelNode2 R (code (FImp p q)) ti (code p) (code q)) ->
  (forall x p, RelNode2 R (code (FAll x p)) ta (number x) (code p)) ->
  forall p, R (code p) f.
Proof.
  intros Ext Number [Eq [Mem [Neg [Imp All]]]] CE CM CN CI CA p.
  induction p as [x y|x y|p IH|p IH q JH|x p IH].
  - destruct (Eq (number x) (number y) (Number x) (Number y)) as [z [In Node]].
    assert (z=code (FEqual x y)) by (eapply relational_node_unique; [exact Ext|exact Node|apply CE]).
    now subst z.
  - destruct (Mem (number x) (number y) (Number x) (Number y)) as [z [In Node]].
    assert (z=code (FMember x y)) by (eapply relational_node_unique; [exact Ext|exact Node|apply CM]).
    now subst z.
  - destruct (Neg (code p) IH) as [z [In Pair]].
    assert (z=code (FNeg p)) by (eapply relational_pair_unique; [exact Ext|exact Pair|apply CN]).
    now subst z.
  - destruct (Imp (code p) (code q) IH JH) as [z [In Node]].
    assert (z=code (FImp p q)) by (eapply relational_node_unique; [exact Ext|exact Node|apply CI]).
    now subst z.
  - destruct (All (number x) (code p) (Number x) IH) as [z [In Node]].
    assert (z=code (FAll x p)) by (eapply relational_node_unique; [exact Ext|exact Node|apply CA]).
    now subst z.
Qed.

Print Assumptions relational_pair_unique.
Print Assumptions relational_node_unique.
Print Assumptions standard_formulas_in_closed_set.
