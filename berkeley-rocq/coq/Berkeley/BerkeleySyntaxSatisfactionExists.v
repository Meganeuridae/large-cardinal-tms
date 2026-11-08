(** Construct the full internal Tarski truth graph from all finite partial
    witnesses. The selecting property is a concrete first-order formula;
    internal formulas are never assumed externally well-founded or standard. *)
From Stdlib Require Import Lists.List Arith.Arith.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxPairs BerkeleySyntaxPairInject BerkeleySyntaxRepresentations BerkeleySyntaxFormulaSet
  BerkeleySyntaxSentence BerkeleySyntaxEnvironment BerkeleySyntaxSatisfactionAtomic BerkeleySyntaxSatisfactionLogical BerkeleySyntaxSatisfactionAll BerkeleySyntaxSatisfactionSemantics BerkeleySyntaxZFBase
  BerkeleySyntaxZFUnion BerkeleySyntaxZFPowerset BerkeleySyntaxZFEnvironments BerkeleySyntaxZFSeparation BerkeleySyntaxPartialTruth
  BerkeleySyntaxPartialUnion BerkeleySyntaxPartialWitnessFormula BerkeleySyntaxPartialWitness BerkeleySyntaxTruthGraphFormula.
Import ListNotations.

Lemma closed_node_member {D} (R:D->D->Prop) f a b tag x y p : RelExtensional R ->
  RelNodeClosure R f a b tag -> R x a -> R y b -> RelNode2 R p tag x y -> R p f.
Proof.
  intros Ext Closed X Y Node. destruct (Closed x y X Y) as [q [Q Other]].
  assert (q=p) by (eapply relational_node_unique; eassumption). now subst q.
Qed.
Lemma closed_unary_member {D} (R:D->D->Prop) f tag q p : RelExtensional R ->
  RelUnaryClosure R f tag -> R q f -> RelPair R p tag q -> R p f.
Proof.
  intros Ext Closed Q Pair. destruct (Closed q Q) as [r [R0 Other]].
  assert (r=p) by (eapply relational_pair_unique; eassumption). now subst r.
Qed.

Section SatisfactionExistence.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_witness_truth_graph f e w m te tm tn ti ta : exists sat,
  forall p s, R p f -> R s e ->
    (RelGraph R sat p s <-> RelPartialTruthValue R p s e f w m te tm tn ti ta).
Proof.
  destruct (zf_prefix_binary_union_exists R EM Model f e) as [bound B].
  destruct (zf_prefix_powerset_exists R EM Model bound) as [p1 P1].
  destruct (zf_prefix_powerset_exists R EM Model p1) as [p2 P2].
  set (rho := update_variable (update_variable (update_variable (update_variable (update_variable (update_variable
    (update_variable (update_variable (update_variable (update_variable (fun _ : nat => f) 0 p2) 3 f) 4 e) 5 w) 6 m) 7 te) 8 tm) 9 tn) 10 ti) 11 ta).
  destruct (zf_prefix_formula_separation R EM Model truth_member_formula rho truth_member_output_fresh) as [sat Sat].
  assert (Mem : forall z, R z sat <-> R z p2 /\ RelTruthMember R z e f w m te tm tn ti ta).
  { intro z. specialize (Sat z). rewrite (@truth_member_formula_holds D R EM) in Sat. unfold rho in Sat.
    cbv [update_variable Nat.eqb] in Sat. exact Sat. }
  exists sat. intros p s Pf Se. split.
  - intros [z [Pair In]]. apply (proj1 (Mem z)) in In. destruct In as [_ [q [t [Q [T [Other Val]]]]]].
    destruct (relational_pair_components R z p s q t Pair Other) as [P S]. subst q t. exact Val.
  - intro Val. destruct (zf_prefix_kuratowski_pair_exists R EM Model p s) as [z Pair].
    exists z. split; [exact Pair|]. apply (proj2 (Mem z)). split.
    + eapply pair_in_powerset_bound; eassumption.
    + now exists p,s.
Qed.

Lemma witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p s :
  RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  (forall q t, R q f -> R t e -> (RelGraph R sat q t <-> RelPartialTruthValue R q t e f w m te tm tn ti ta)) ->
  RelPartialEvaluation R h g e f w m te tm tn ti ta -> R p f -> R p g -> R s e ->
  (RelGraph R sat p s <-> RelGraph R h p s).
Proof.
  intros Formulas Env Sat Eval Pf Pg Se. rewrite (Sat p s Pf Se). split.
  - intros [g' [h' [Pg' [Eval' At]]]].
    destruct Eval as [_ [Down [Truth _]]]. destruct Eval' as [_ [Down' [Truth' _]]].
    apply (proj2 (zf_partial_truth_agrees_on_overlap R EM Model f w m e te tm tn ti ta g g' h h'
      Formulas Env Down Down' Truth Truth' p s Pf Pg Pg' Se)),At.
  - intro At. exists g,h. tauto.
Qed.

Theorem zf_prefix_satisfaction_exists f e w m te tm tn ti ta :
  RelTags R w te tm tn ti ta -> RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  exists sat, RelSatisfaction R sat e f w m te tm tn ti ta.
Proof.
  intros Tags Formulas Env. pose proof (proj1 Formulas) as [CE [CM [CN [CI CA]]]].
  pose proof (zf_prefix_extensional R EM Model) as Ext.
  destruct (zf_witness_truth_graph f e w m te tm tn ti ta) as [sat Sat]. exists sat.
  unfold RelSatisfaction,RelSatisfactionClauses,RelAtomicClause,RelNegClause,RelImpClause,RelAllClause. intros s Se. split.
  - intros u v x y p U V X Y Gu Gv Node.
    assert (Pf : R p f) by (exact (closed_node_member R f w w te u v p Ext CE U V Node)).
    destruct (zf_partial_witness_exists R EM Model f w m e te tm tn ti ta Tags Formulas Env p Pf) as [g [h [Pg Eval]]].
    pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p s Formulas Env Sat Eval Pf Pg Se) as Eq.
    destruct Eval as [_ [_ [Truth _]]]. destruct (Truth s Se) as [Atomic _].
    specialize (Atomic u v x y p Pg U V X Y Gu Gv Node). cbn [atom_truth]. now rewrite Eq.
  - split.
    + intros u v x y p U V X Y Gu Gv Node.
      assert (Pf : R p f) by (exact (closed_node_member R f w w tm u v p Ext CM U V Node)).
      destruct (zf_partial_witness_exists R EM Model f w m e te tm tn ti ta Tags Formulas Env p Pf) as [g [h [Pg Eval]]].
      pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p s Formulas Env Sat Eval Pf Pg Se) as Eq.
      destruct Eval as [_ [_ [Truth _]]]. destruct (Truth s Se) as [_ [Atomic _]].
      specialize (Atomic u v x y p Pg U V X Y Gu Gv Node). cbn [atom_truth]. now rewrite Eq.
    + split.
      * intros p q Pf Pair.
        assert (Qf : R q f) by (exact (closed_unary_member R f tn p q Ext CN Pf Pair)).
        destruct (zf_partial_witness_exists R EM Model f w m e te tm tn ti ta Tags Formulas Env q Qf) as [g [h [Qg Eval]]].
        pose proof Eval as [_ [[NDown _] [Truth _]]]. pose proof (NDown q p Qg Pf Pair) as Pg.
        pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h q s Formulas Env Sat Eval Qf Qg Se) as EqQ.
        pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p s Formulas Env Sat Eval Pf Pg Se) as EqP.
        destruct (Truth s Se) as [_ [_ [Neg _]]]. specialize (Neg p q Qg Pf Pair). now rewrite EqQ,EqP.
      * split.
        -- intros p q r Pf Qf Node.
           assert (Rf : R r f) by (exact (closed_node_member R f f f ti p q r Ext CI Pf Qf Node)).
           destruct (zf_partial_witness_exists R EM Model f w m e te tm tn ti ta Tags Formulas Env r Rf) as [g [h [Rg Eval]]].
           pose proof Eval as [_ [[_ [IDown _]] [Truth _]]]. destruct (IDown r p q Rg Pf Qf Node) as [Pg Qg].
           pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h r s Formulas Env Sat Eval Rf Rg Se) as EqR.
           pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p s Formulas Env Sat Eval Pf Pg Se) as EqP.
           pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h q s Formulas Env Sat Eval Qf Qg Se) as EqQ.
           destruct (Truth s Se) as [_ [_ [_ [Imp _]]]]. specialize (Imp p q r Rg Pf Qf Node). now rewrite EqR,EqP,EqQ.
        -- intros u p q U Pf Node.
           assert (Qf : R q f) by (exact (closed_node_member R f w f ta u p q Ext CA U Pf Node)).
           destruct (zf_partial_witness_exists R EM Model f w m e te tm tn ti ta Tags Formulas Env q Qf) as [g [h [Qg Eval]]].
           pose proof Eval as [_ [[_ [_ ADown]] [Truth _]]]. pose proof (ADown q u p Qg Pf Node) as Pg.
           pose proof (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h q s Formulas Env Sat Eval Qf Qg Se) as EqQ.
           destruct (Truth s Se) as [_ [_ [_ [_ All]]]]. specialize (All u p q Qg U Pf Node).
           rewrite EqQ,All. split; intros H t Te Up.
           ++ apply (proj2 (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p t Formulas Env Sat Eval Pf Pg Te)),H; assumption.
           ++ apply (proj1 (witness_graph_agrees_partial f e w m te tm tn ti ta sat g h p t Formulas Env Sat Eval Pf Pg Te)),H; assumption.
Qed.
End SatisfactionExistence.

Print Assumptions zf_witness_truth_graph.
Print Assumptions witness_graph_agrees_partial.
Print Assumptions zf_prefix_satisfaction_exists.
