(** Extend an internal partial valuation through an actual negation node. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxSets BerkeleySyntaxSentence BerkeleySyntaxTags BerkeleySyntaxFormulaSet
  BerkeleySyntaxZFBase BerkeleySyntaxPartialTruth BerkeleySyntaxPartialUnion BerkeleySyntaxPartialExtend
  BerkeleySyntaxTruthSlice BerkeleySyntaxTruthSlices.
Import ListNotations.

Lemma pair_node_tag_conflict {D} (R:D->D->Prop) p a b q x y :
  a<>b -> RelPair R p a q -> RelNode2 R p b x y -> False.
Proof.
  intros Ne Pair Node. apply Ne. eapply tag_unique; [apply (pair_has_tag R p a q Pair)|apply (node_has_tag R p b x y Node)].
Qed.

Section PartialNegation.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_extend_negation f w m e te tm tn ti ta g h q p :
  RelTags R w te tm tn ti ta -> RelPartialEvaluation R h g e f w m te tm tn ti ta ->
  R q g -> R q f -> R p f -> RelPair R p tn q ->
  exists g' h', RelPartialEvaluation R h' g' e f w m te tm tn ti ta /\ R p g' /\ R q g'.
Proof.
  intros Tags Eval Qg Qf Pf Pair. destruct (EM (R p g)) as [Already|NotIn].
  - exists g,h. tauto.
  - pose proof (actual_tags_distinct R EM Model w te tm tn ti ta Tags) as Dist.
    assert (NE : tn<>te) by (eapply (Dist 2 0); [lia|reflexivity|reflexivity]).
    assert (NM : tn<>tm) by (eapply (Dist 2 1); [lia|reflexivity|reflexivity]).
    assert (NI : tn<>ti) by (eapply (Dist 2 3); [lia|reflexivity|reflexivity]).
    assert (NA : tn<>ta) by (eapply (Dist 2 4); [lia|reflexivity|reflexivity]).
    destruct (zf_negative_truth_slice R EM Model e h q) as [slice Slice].
    assert (SliceSub : RelSubset R slice e) by (intros s S; exact (proj1 (proj1 (Slice s) S))).
    pose proof Eval as [_ [_ [_ Bound]]].
    destruct (zf_add_truth_slice R EM Model h g e p slice Bound NotIn SliceSub) as [g' [h' [G [Graph [Old [Row NewBound]]]]]].
    assert (Allowed : RelAllowedChildren R p g f tn ti ta).
    { split.
      - intros r Rf Other. assert (r=q) by (symmetry; eapply unary_operand_unique; eassumption). now subst.
      - split.
        + intros r t Rf Tf Node. exfalso. exact (pair_node_tag_conflict R p tn ti q r t NI Pair Node).
        + intros x r Rf Node. exfalso. exact (pair_node_tag_conflict R p tn ta q x r NA Pair Node). }
    assert (TruthAt : RelTruthAt R h' p e f w m te tm tn ti ta).
    { intros s S. split.
      - intros x y a b X Y A B Ga Gb Node. exfalso. exact (pair_node_tag_conflict R p tn te q x y NE Pair Node).
      - split.
        + intros x y a b X Y A B Ga Gb Node. exfalso. exact (pair_node_tag_conflict R p tn tm q x y NM Pair Node).
        + split.
          * intros r Rf Other. assert (r=q) by (symmetry; eapply unary_operand_unique; eassumption). subst r.
            rewrite (Row s),(Slice s),(Old q s Qg). tauto.
          * split.
            -- intros r t Rf Tf Node. exfalso. exact (pair_node_tag_conflict R p tn ti q r t NI Pair Node).
            -- intros x r X Rf Node. exfalso. exact (pair_node_tag_conflict R p tn ta q x r NA Pair Node). }
    exists g',h'. split.
    + eapply partial_evaluation_extend; eassumption.
    + split; apply (proj2 (G _)); [now right|now left].
Qed.
End PartialNegation.

Print Assumptions zf_partial_extend_negation.
