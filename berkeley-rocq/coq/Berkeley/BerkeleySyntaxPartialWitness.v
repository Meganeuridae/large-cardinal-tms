(** Every internal formula admits a compatible partial truth valuation. The
    induction property is the explicitly compiled first-order witness formula. *)
From Stdlib Require Import Lists.List Arith.Arith.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxSentence BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment
  BerkeleySyntaxZFBase BerkeleySyntaxFormulaInduction BerkeleySyntaxPartialUnion BerkeleySyntaxPartialNegation
  BerkeleySyntaxPartialImplication BerkeleySyntaxPartialUniversal BerkeleySyntaxPartialAtomic BerkeleySyntaxPartialWitnessFormula.
Import ListNotations.

Section PartialWitnesses.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_partial_witness_exists f w m e te tm tn ti ta :
  RelTags R w te tm tn ti ta -> RelFormulas R f w te tm tn ti ta -> RelEnvironments R e w m ->
  forall p, R p f -> RelPartialWitness R p e f w m te tm tn ti ta.
Proof.
  intros Tags Formulas Env.
  set (rho := update_variable (update_variable (update_variable (update_variable (update_variable (update_variable
    (update_variable (update_variable (fun _ : nat => f) 3 e) 4 w) 5 m) 6 te) 7 tm) 8 tn) 9 ti) 10 ta).
  assert (Interpret : forall p, RelFormulaProperty R partial_witness_formula rho p <->
    RelPartialWitness R p e f w m te tm tn ti ta).
  { intro p. unfold RelFormulaProperty. rewrite (@partial_witness_formula_holds D R EM). unfold rho.
    cbv [update_variable Nat.eqb]. reflexivity. }
  assert (All : forall p, R p f -> RelFormulaProperty R partial_witness_formula rho p).
  { eapply (zf_internal_formula_induction R EM Model f w te tm tn ti ta partial_witness_formula rho);
      [reflexivity|exact partial_witness_output_fresh|exact Formulas| | | | |].
    - intros x y p X Y Pf Node. apply (proj2 (Interpret p)).
      destruct (zf_partial_atomic_base R EM Model false f w m e te tm tn ti ta x y p Tags Env X Y Pf Node)
        as [g [h [Eval Pg]]]. now exists g,h.
    - intros x y p X Y Pf Node. apply (proj2 (Interpret p)).
      destruct (zf_partial_atomic_base R EM Model true f w m e te tm tn ti ta x y p Tags Env X Y Pf Node)
        as [g [h [Eval Pg]]]. now exists g,h.
    - intros q p Qf Qp Pf Pair. apply (proj2 (Interpret p)).
      destruct (proj1 (Interpret q) Qp) as [g [h [Qg Eval]]].
      destruct (zf_partial_extend_negation R EM Model f w m e te tm tn ti ta g h q p Tags Eval Qg Qf Pf Pair)
        as [g' [h' [Eval' [Pg _]]]]. now exists g',h'.
    - intros q r p Qf Qp Rf Rp Pf Node. apply (proj2 (Interpret p)).
      destruct (proj1 (Interpret q) Qp) as [g1 [h1 [Q1 Eval1]]].
      destruct (proj1 (Interpret r) Rp) as [g2 [h2 [R2 Eval2]]].
      destruct (zf_partial_evaluations_union R EM Model f w m e te tm tn ti ta g1 g2 h1 h2 Formulas Env Eval1 Eval2)
        as [g [h [Eval [G H]]]].
      assert (Qg : R q g) by (apply (proj2 (G q)); now left).
      assert (Rg : R r g) by (apply (proj2 (G r)); now right).
      destruct (zf_partial_extend_implication R EM Model f w m e te tm tn ti ta g h q r p Tags Eval Qg Rg Qf Rf Pf Node)
        as [g' [h' [Eval' [Pg _]]]]. now exists g',h'.
    - intros x q p X Qf Qp Pf Node. apply (proj2 (Interpret p)).
      destruct (proj1 (Interpret q) Qp) as [g [h [Qg Eval]]].
      destruct (zf_partial_extend_universal R EM Model f w m e te tm tn ti ta g h x q p Tags Eval X Qg Qf Pf Node)
        as [g' [h' [Eval' [Pg _]]]]. now exists g',h'. }
  intros p P. now apply (proj1 (Interpret p)),All.
Qed.
End PartialWitnesses.

Print Assumptions zf_partial_witness_exists.
