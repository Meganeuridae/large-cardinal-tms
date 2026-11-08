(** Atomic partial evaluations, using exact first-order equality/membership rows. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxSets BerkeleySyntaxSentence BerkeleySyntaxTags BerkeleySyntaxFormulaSet
  BerkeleySyntaxEnvironment BerkeleySyntaxSatisfactionAtomic BerkeleySyntaxZFBase BerkeleySyntaxZFPaths BerkeleySyntaxPartialTruth
  BerkeleySyntaxPartialUnion BerkeleySyntaxPartialExtend BerkeleySyntaxPartialNegation BerkeleySyntaxPartialImplication
  BerkeleySyntaxTruthSlice BerkeleySyntaxAtomicSlices.
Import ListNotations.

Lemma empty_partial_evaluation {D} (R:D->D->Prop) empty e f w m te tm tn ti ta : RelEmpty R empty ->
  RelPartialEvaluation R empty empty e f w m te tm tn ti ta.
Proof.
  intro Empty. unfold RelPartialEvaluation,RelSubset,RelPartialDownward,RelPartialTruth,RelTruthGraphBound. split.
  - intros p P. exfalso. exact (Empty p P).
  - split.
    + split.
      * intros p q P. exfalso. exact (Empty p P).
      * split; [intros p q r P|intros p x q P]; exfalso; exact (Empty p P).
    + split.
      * intros s S. split.
        -- intros u v x y p P. exfalso. exact (Empty p P).
        -- split.
           ++ intros u v x y p P. exfalso. exact (Empty p P).
           ++ split.
              ** intros p q Q. exfalso. exact (Empty q Q).
              ** split.
                 --- intros p q r T. exfalso. exact (Empty r T).
                 --- intros u p q Q. exfalso. exact (Empty q Q).
      * intros p s [q [_ Q]]. exfalso. exact (Empty q Q).
Qed.

Section PartialAtomic.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_extend_atomic (member:bool) f w m e te tm tn ti ta g h u v p :
  RelTags R w te tm tn ti ta -> RelEnvironments R e w m ->
  RelPartialEvaluation R h g e f w m te tm tn ti ta -> R u w -> R v w -> R p f ->
  RelNode2 R p (if member then tm else te) u v ->
  exists g' h', RelPartialEvaluation R h' g' e f w m te tm tn ti ta /\ R p g'.
Proof.
  intros Tags Env Eval U V Pf Node. destruct (EM (R p g)) as [Already|NotIn].
  - exists g,h. tauto.
  - pose proof (actual_tags_distinct R EM Model w te tm tn ti ta Tags) as Dist.
    assert (EN : te<>tm) by (eapply (Dist 0 1); [lia|reflexivity|reflexivity]).
    assert (ME : tm<>te) by (eapply (Dist 1 0); [lia|reflexivity|reflexivity]).
    assert (NN : tn<>(if member then tm else te)).
    { destruct member; [eapply (Dist 2 1); [lia|reflexivity|reflexivity]|eapply (Dist 2 0); [lia|reflexivity|reflexivity]]. }
    assert (NI : (if member then tm else te)<>ti).
    { destruct member; [eapply (Dist 1 3); [lia|reflexivity|reflexivity]|eapply (Dist 0 3); [lia|reflexivity|reflexivity]]. }
    assert (NA : (if member then tm else te)<>ta).
    { destruct member; [eapply (Dist 1 4); [lia|reflexivity|reflexivity]|eapply (Dist 0 4); [lia|reflexivity|reflexivity]]. }
    destruct (zf_atomic_truth_slice R EM Model member e m u v) as [slice Slice].
    assert (SliceSub : RelSubset R slice e) by (intros s S; exact (proj1 (proj1 (Slice s) S))).
    pose proof Eval as [_ [_ [_ Bound]]].
    destruct (zf_add_truth_slice R EM Model h g e p slice Bound NotIn SliceSub) as [g' [h' [G [Graph [Old [Row NewBound]]]]]].
    assert (Allowed : RelAllowedChildren R p g f tn ti ta).
    { split.
      - intros child Cf Pair. exfalso. exact (pair_node_tag_conflict R p tn _ child u v NN Pair Node).
      - split.
        + intros a b Af Bf Other. exfalso. exact (node_node_tag_conflict R p _ ti u v a b NI Node Other).
        + intros x child Cf Other. exfalso. exact (node_node_tag_conflict R p _ ta u v x child NA Node Other). }
    assert (TruthAt : RelTruthAt R h' p e f w m te tm tn ti ta).
    { intros s S. split.
      - intros x y a b X Y A B Ga Gb Other. destruct member.
        + exfalso. exact (node_node_tag_conflict R p tm te u v x y ME Node Other).
        + destruct (node_operands_unique R p te u v x y Node Other) as [X0 Y0]. subst x y.
          pose proof (atomic_value_matches_function R false s w m u v a b (proj1 (Env s) S) A B Ga Gb) as Match.
          cbn [atom_truth] in Match. rewrite (Row s),(Slice s). tauto.
      - split.
        + intros x y a b X Y A B Ga Gb Other. destruct member.
          * destruct (node_operands_unique R p tm u v x y Node Other) as [X0 Y0]. subst x y.
            pose proof (atomic_value_matches_function R true s w m u v a b (proj1 (Env s) S) A B Ga Gb) as Match.
            cbn [atom_truth] in Match. rewrite (Row s),(Slice s). tauto.
          * exfalso. exact (node_node_tag_conflict R p te tm u v x y EN Node Other).
        + split.
          * intros child Cf Pair. exfalso. exact (pair_node_tag_conflict R p tn _ child u v NN Pair Node).
          * split.
            -- intros a b Af Bf Other. exfalso. exact (node_node_tag_conflict R p _ ti u v a b NI Node Other).
            -- intros x child X Cf Other. exfalso. exact (node_node_tag_conflict R p _ ta u v x child NA Node Other). }
    exists g',h'. split.
    + eapply partial_evaluation_extend; eassumption.
    + apply (proj2 (G p)). now right.
Qed.

Theorem zf_partial_atomic_base (member:bool) f w m e te tm tn ti ta u v p :
  RelTags R w te tm tn ti ta -> RelEnvironments R e w m -> R u w -> R v w -> R p f ->
  RelNode2 R p (if member then tm else te) u v ->
  exists g h, RelPartialEvaluation R h g e f w m te tm tn ti ta /\ R p g.
Proof.
  intros Tags Env U V Pf Node. destruct (zf_prefix_empty_exists R EM Model p) as [empty E].
  eapply zf_partial_extend_atomic; [exact Tags|exact Env|apply empty_partial_evaluation; exact E|exact U|exact V|exact Pf|exact Node].
Qed.
End PartialAtomic.

Print Assumptions empty_partial_evaluation.
Print Assumptions zf_partial_extend_atomic.
Print Assumptions zf_partial_atomic_base.
