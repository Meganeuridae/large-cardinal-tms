(** Internal first-order induction proves all pair-stage histories agree on
    common omega indices, including nonstandard internal indices. *)
From Stdlib Require Import Arith.Arith.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxPairs BerkeleySyntaxOmega BerkeleySyntaxZFBase BerkeleySyntaxZFOmega
  BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageAgreement BerkeleySyntaxZFStageLocal BerkeleySyntaxZFStageLocalFormula.
Section Uniqueness.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem zf_history_runs_agree w seed k1 k2 h1 h2 :
  RelOmega R w -> R k1 w -> R k2 w -> RelPairStageRun R h1 k1 seed -> RelPairStageRun R h2 k2 seed ->
  forall n, R n w -> RelLocalAgreement R h1 h2 k1 k2 n.
Proof.
  intros Omega K1 K2 Run1 Run2.
  set (rho := fun n:nat => match n with 0=>w | 3=>k1 | 4=>k2 | 5=>h1 | _=>h2 end).
  assert (All : forall n, R n w -> FolHolds R (update_variable rho 2 n) local_agreement_formula).
  { eapply (zf_internal_omega_induction R EM Model w local_agreement_formula rho);
      [exact Omega|exact local_agreement_output_fresh|reflexivity| |].
    - intros e Empty. rewrite (local_agreement_formula_holds R EM).
      cbv [rho update_variable Nat.eqb]. eapply zf_local_agreement_empty; eassumption.
    - intros x y X Next Prev. rewrite (local_agreement_formula_holds R EM) in Prev |- *.
      cbv [rho update_variable Nat.eqb] in Prev |- *.
      eapply (zf_local_agreement_successor R EM Model w seed k1 k2 h1 h2 x y); eassumption. }
  intros n N. specialize (All n N). rewrite (local_agreement_formula_holds R EM) in All.
  cbv [rho update_variable Nat.eqb] in All. exact All.
Qed.
Theorem zf_history_endpoint_unique w seed n h1 h2 a b :
  RelOmega R w -> R n w -> RelPairStageRun R h1 n seed -> RelPairStageRun R h2 n seed ->
  RelGraph R h1 n a -> RelGraph R h2 n b -> a=b.
Proof.
  intros Omega N Run1 Run2 A B.
  pose proof (zf_history_runs_agree w seed n n h1 h2 Omega N N Run1 Run2 n N) as H.
  apply (H (or_introl eq_refl) (or_introl eq_refl) a b A B).
Qed.
End Uniqueness.
Print Assumptions zf_history_runs_agree.
Print Assumptions zf_history_endpoint_unique.
