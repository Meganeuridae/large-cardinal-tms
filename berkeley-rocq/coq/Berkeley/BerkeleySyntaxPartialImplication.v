(** Extend an internal partial valuation through an implication node. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxSets BerkeleySyntaxSentence BerkeleySyntaxTags BerkeleySyntaxFormulaSet
  BerkeleySyntaxZFBase BerkeleySyntaxPartialTruth BerkeleySyntaxPartialUnion BerkeleySyntaxPartialExtend
  BerkeleySyntaxPartialNegation BerkeleySyntaxTruthSlice BerkeleySyntaxTruthSlices.
Import ListNotations.

Lemma node_node_tag_conflict {D} (R:D->D->Prop) p a b x y u v :
  a<>b -> RelNode2 R p a x y -> RelNode2 R p b u v -> False.
Proof.
  intros Ne A B. apply Ne. eapply tag_unique; [apply (node_has_tag R p a x y A)|apply (node_has_tag R p b u v B)].
Qed.

Section PartialImplication.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_extend_implication f w m e te tm tn ti ta g h q r p :
  RelTags R w te tm tn ti ta -> RelPartialEvaluation R h g e f w m te tm tn ti ta ->
  R q g -> R r g -> R q f -> R r f -> R p f -> RelNode2 R p ti q r ->
  exists g' h', RelPartialEvaluation R h' g' e f w m te tm tn ti ta /\ R p g' /\ R q g' /\ R r g'.
Proof.
  intros Tags Eval Qg Rg Qf Rf Pf Node. destruct (EM (R p g)) as [Already|NotIn].
  - exists g,h. tauto.
  - pose proof (actual_tags_distinct R EM Model w te tm tn ti ta Tags) as Dist.
    assert (NE : ti<>te) by (eapply (Dist 3 0); [lia|reflexivity|reflexivity]).
    assert (NM : ti<>tm) by (eapply (Dist 3 1); [lia|reflexivity|reflexivity]).
    assert (NN : tn<>ti) by (eapply (Dist 2 3); [lia|reflexivity|reflexivity]).
    assert (NA : ti<>ta) by (eapply (Dist 3 4); [lia|reflexivity|reflexivity]).
    destruct (zf_implication_truth_slice R EM Model e h q r) as [slice Slice].
    assert (SliceSub : RelSubset R slice e) by (intros s S; exact (proj1 (proj1 (Slice s) S))).
    pose proof Eval as [_ [_ [_ Bound]]].
    destruct (zf_add_truth_slice R EM Model h g e p slice Bound NotIn SliceSub) as [g' [h' [G [Graph [Old [Row NewBound]]]]]].
    assert (Allowed : RelAllowedChildren R p g f tn ti ta).
    { split.
      - intros child Cf Pair. exfalso. exact (pair_node_tag_conflict R p tn ti child q r NN Pair Node).
      - split.
        + intros a b Af Bf Other. destruct (node_operands_unique R p ti q r a b Node Other) as [A B]. now subst.
        + intros x child Cf Other. exfalso. exact (node_node_tag_conflict R p ti ta q r x child NA Node Other). }
    assert (TruthAt : RelTruthAt R h' p e f w m te tm tn ti ta).
    { intros s S. split.
      - intros x y a b X Y A B Ga Gb Other. exfalso. exact (node_node_tag_conflict R p ti te q r x y NE Node Other).
      - split.
        + intros x y a b X Y A B Ga Gb Other. exfalso. exact (node_node_tag_conflict R p ti tm q r x y NM Node Other).
        + split.
          * intros child Cf Pair. exfalso. exact (pair_node_tag_conflict R p tn ti child q r NN Pair Node).
          * split.
            -- intros a b Af Bf Other. destruct (node_operands_unique R p ti q r a b Node Other) as [A B]. subst a b.
               rewrite (Row s),(Slice s),(Old q s Qg),(Old r s Rg). tauto.
            -- intros x child X Cf Other. exfalso. exact (node_node_tag_conflict R p ti ta q r x child NA Node Other). }
    exists g',h'. split.
    + eapply partial_evaluation_extend; eassumption.
    + repeat split; apply (proj2 (G _)); [now right|now left|now left].
Qed.
End PartialImplication.

Print Assumptions zf_partial_extend_implication.
