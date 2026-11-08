(** Extend an internal partial valuation through a universal formula node. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxSets BerkeleySyntaxSentence BerkeleySyntaxTags BerkeleySyntaxFormulaSet
  BerkeleySyntaxZFBase BerkeleySyntaxPartialTruth BerkeleySyntaxPartialUnion BerkeleySyntaxPartialExtend
  BerkeleySyntaxPartialNegation BerkeleySyntaxPartialImplication BerkeleySyntaxTruthSlice BerkeleySyntaxTruthSlices.
Import ListNotations.

Section PartialUniversal.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_extend_universal f w m e te tm tn ti ta g h u q p :
  RelTags R w te tm tn ti ta -> RelPartialEvaluation R h g e f w m te tm tn ti ta ->
  R u w -> R q g -> R q f -> R p f -> RelNode2 R p ta u q ->
  exists g' h', RelPartialEvaluation R h' g' e f w m te tm tn ti ta /\ R p g' /\ R q g'.
Proof.
  intros Tags Eval U Qg Qf Pf Node. destruct (EM (R p g)) as [Already|NotIn].
  - exists g,h. tauto.
  - pose proof (actual_tags_distinct R EM Model w te tm tn ti ta Tags) as Dist.
    assert (NE : ta<>te) by (eapply (Dist 4 0); [lia|reflexivity|reflexivity]).
    assert (NM : ta<>tm) by (eapply (Dist 4 1); [lia|reflexivity|reflexivity]).
    assert (NN : tn<>ta) by (eapply (Dist 2 4); [lia|reflexivity|reflexivity]).
    assert (NI : ta<>ti) by (eapply (Dist 4 3); [lia|reflexivity|reflexivity]).
    destruct (zf_universal_truth_slice R EM Model e h w m u q) as [slice Slice].
    assert (SliceSub : RelSubset R slice e) by (intros s S; exact (proj1 (proj1 (Slice s) S))).
    pose proof Eval as [_ [_ [_ Bound]]].
    destruct (zf_add_truth_slice R EM Model h g e p slice Bound NotIn SliceSub) as [g' [h' [G [Graph [Old [Row NewBound]]]]]].
    assert (Allowed : RelAllowedChildren R p g f tn ti ta).
    { split.
      - intros child Cf Pair. exfalso. exact (pair_node_tag_conflict R p tn ta child u q NN Pair Node).
      - split.
        + intros a b Af Bf Other. exfalso. exact (node_node_tag_conflict R p ta ti u q a b NI Node Other).
        + intros x child Cf Other. destruct (node_operands_unique R p ta u q x child Node Other) as [X C]. now subst. }
    assert (TruthAt : RelTruthAt R h' p e f w m te tm tn ti ta).
    { intros s S. split.
      - intros x y a b X Y A B Ga Gb Other. exfalso. exact (node_node_tag_conflict R p ta te u q x y NE Node Other).
      - split.
        + intros x y a b X Y A B Ga Gb Other. exfalso. exact (node_node_tag_conflict R p ta tm u q x y NM Node Other).
        + split.
          * intros child Cf Pair. exfalso. exact (pair_node_tag_conflict R p tn ta child u q NN Pair Node).
          * split.
            -- intros a b Af Bf Other. exfalso. exact (node_node_tag_conflict R p ta ti u q a b NI Node Other).
            -- intros x child X Cf Other. destruct (node_operands_unique R p ta u q x child Node Other) as [X0 C]. subst x child.
               rewrite (Row s),(Slice s). split.
               ++ intros [_ Cond] t T Up. apply (proj2 (Old q t Qg)),Cond; assumption.
               ++ intro Cond. split; [exact S|]. intros t T Up. apply (proj1 (Old q t Qg)),Cond; assumption. }
    exists g',h'. split.
    + eapply partial_evaluation_extend; eassumption.
    + split; apply (proj2 (G _)); [now right|now left].
Qed.
End PartialUniversal.

Print Assumptions zf_partial_extend_universal.
