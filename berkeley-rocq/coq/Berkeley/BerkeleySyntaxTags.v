(** Constructor tags and operands are uniquely recoverable from their actual
    internal Kuratowski representations. The five finite tags are distinct by
    Foundation; no assumption that internal omega is standard is used. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxPairInject BerkeleySyntaxSets BerkeleySyntaxOmega
  BerkeleySyntaxSentence BerkeleySyntaxNumerals BerkeleySyntaxZFBase.
Import ListNotations.

Definition RelHasTag {D} (R:D->D->Prop) p tag := exists payload, RelPair R p tag payload.
Lemma node_has_tag {D} (R:D->D->Prop) p tag a b : RelNode2 R p tag a b -> RelHasTag R p tag.
Proof. intros [q [_ P]]. now exists q. Qed.
Lemma pair_has_tag {D} (R:D->D->Prop) p tag q : RelPair R p tag q -> RelHasTag R p tag.
Proof. intro P. now exists q. Qed.
Theorem tag_unique {D} (R:D->D->Prop) p tag tag' :
  RelHasTag R p tag -> RelHasTag R p tag' -> tag=tag'.
Proof.
  intros [q Q] [q' Q']. exact (proj1 (relational_pair_components R p tag q tag' q' Q Q')).
Qed.
Theorem node_operands_unique {D} (R:D->D->Prop) p tag a b a' b' :
  RelNode2 R p tag a b -> RelNode2 R p tag a' b' -> a=a' /\ b=b'.
Proof.
  intros [q [Q P]] [q' [Q' P']].
  assert (q=q') by (exact (proj2 (relational_pair_components R p tag q tag q' P P'))). subst q'.
  exact (relational_pair_components R q a b a' b' Q Q').
Qed.
Theorem unary_operand_unique {D} (R:D->D->Prop) p tag a b : RelPair R p tag a -> RelPair R p tag b -> a=b.
Proof. intros A B. exact (proj2 (relational_pair_components R p tag a tag b A B)). Qed.

Lemma actual_tags_numerals {D} (R:D->D->Prop) w z0 z1 z2 z3 z4 : RelTags R w z0 z1 z2 z3 z4 ->
  forall n z, nth_error [z0;z1;z2;z3;z4] n=Some z -> RelNumeral R n z.
Proof.
  intros [_ [Empty [S1 [S2 [S3 S4]]]]] n z N.
  assert (N0 : RelNumeral R 0 z0) by exact Empty.
  assert (N1 : RelNumeral R 1 z1) by (now exists z0).
  assert (N2 : RelNumeral R 2 z2) by (now exists z1).
  assert (N3 : RelNumeral R 3 z3) by (now exists z2).
  assert (N4 : RelNumeral R 4 z4) by (now exists z3).
  destruct n as [|[|[|[|[|n]]]]]; cbn in N; try (inversion N; subst; assumption). destruct n; discriminate.
Qed.
Theorem actual_tags_distinct {D} (R:D->D->Prop) (EM:forall P:Prop,P\/ ~P) (Model:satisfies_zf_prefix R)
  w z0 z1 z2 z3 z4 : RelTags R w z0 z1 z2 z3 z4 -> forall i j a b,
  i<>j -> nth_error [z0;z1;z2;z3;z4] i=Some a -> nth_error [z0;z1;z2;z3;z4] j=Some b -> a<>b.
Proof.
  intros Tags i j a b Ne A B. eapply (zf_standard_numeral_indices_distinct R EM Model i j a b Ne);
    eapply actual_tags_numerals; eassumption.
Qed.

Print Assumptions node_operands_unique.
Print Assumptions actual_tags_distinct.
