(** Internal induction proves a pair-stage history is nested at all internal
    natural indices, not just at externally standard numerals. *)
From Stdlib Require Import Arith.Arith.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxZFBase BerkeleySyntaxZFOmega
  BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageNested BerkeleySyntaxZFStageNestedFormula.
Section StageNesting.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem zf_history_nested w seed k h : RelOmega R w -> R k w -> RelPairStageRun R h k seed ->
  forall n, R n w -> RelNestedAt R h k n.
Proof.
  intros Omega K Run.
  set (rho:=fun n:nat=>match n with 0=>w | 3=>k | _=>h end).
  assert (All : forall n, R n w -> FolHolds R (update_variable rho 2 n) nested_at_formula).
  { eapply (zf_internal_omega_induction R EM Model w nested_at_formula rho);
      [exact Omega|exact nested_at_output_fresh|reflexivity| |].
    - intros e Empty. rewrite (nested_at_formula_holds R EM). cbv [rho update_variable Nat.eqb].
      now apply zf_nested_empty.
    - intros x y X Next Prev. rewrite (nested_at_formula_holds R EM) in Prev |- *.
      cbv [rho update_variable Nat.eqb] in Prev |- *.
      eapply (zf_nested_successor R EM Model w seed k h x y); eassumption. }
  intros n N. specialize (All n N). rewrite (nested_at_formula_holds R EM) in All.
  cbv [rho update_variable Nat.eqb] in All. exact All.
Qed.
End StageNesting.
Print Assumptions zf_history_nested.
