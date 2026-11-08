(** A universe closed under Kuratowski pairing bounds the internal formula
    constructors. The bound will be supplied by first-order omega iteration. *)
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxPairs
  BerkeleySyntaxFormulaSet BerkeleySyntaxZFBase BerkeleySyntaxZFFormulaSet.

Definition RelPairClosed {D} (R:D->D->Prop) bound :=
  forall x y, R x bound -> R y bound -> exists p, R p bound /\ RelPair R p x y.

Section Bound.
Context {D:Type} (R:D->D->Prop).

Lemma pair_closed_node bound : RelPairClosed R bound ->
  forall tag x y, R tag bound -> R x bound -> R y bound ->
    exists p, R p bound /\ RelNode2 R p tag x y.
Proof.
  intros Closed tag x y T X Y. destruct (Closed x y X Y) as [q [Q Pair]].
  destruct (Closed tag q T Q) as [p [P Outer]]. exists p. split; [exact P|now exists q].
Qed.

Theorem pair_closed_bounds_formulas bound w te tm tn ti ta :
  RelPairClosed R bound -> RelSubset R w bound ->
  R te bound -> R tm bound -> R tn bound -> R ti bound -> R ta bound ->
  RelClosedFormulas R bound w te tm tn ti ta.
Proof.
  intros Closed Sub TE TM TN TI TA. unfold RelClosedFormulas.
  split; [|split; [|split; [|split]]].
  - intros x y X Y. apply pair_closed_node; auto.
  - intros x y X Y. apply pair_closed_node; auto.
  - intros p P. exact (Closed tn p TN P).
  - intros x y X Y. apply pair_closed_node; auto.
  - intros x y X Y. apply pair_closed_node; auto.
Qed.

Theorem zf_formula_set_from_pair_closed (EM:forall P:Prop,P \/ ~P) (Model:satisfies_zf_prefix R)
  bound w te tm tn ti ta :
  RelPairClosed R bound -> RelSubset R w bound ->
  R te bound -> R tm bound -> R tn bound -> R ti bound -> R ta bound ->
  exists f, RelFormulas R f w te tm tn ti ta.
Proof.
  intros Closed Sub TE TM TN TI TA.
  apply (zf_prefix_formula_set_from_closed R EM Model bound w te tm tn ti ta).
  now apply pair_closed_bounds_formulas.
Qed.
End Bound.

Print Assumptions pair_closed_bounds_formulas.
Print Assumptions zf_formula_set_from_pair_closed.
