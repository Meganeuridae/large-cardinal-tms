(** Internal omega induction over the explicitly coded stage-run predicate. *)
From Stdlib Require Import Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxZFBase
  BerkeleySyntaxZFOmega BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageFormula.
Section InternalRuns.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem zf_pair_stage_history_exists w seed : RelOmega R w ->
  forall n, R n w -> exists h, RelPairStageRun R h n seed.
Proof.
  intro Omega. set (rho:=update_variable (fun _ : nat => seed) 0 w).
  assert (At : rho 0=w) by (unfold rho;apply update_variable_eq).
  assert (Seed : rho 3=seed) by (unfold rho;rewrite update_variable_neq by lia;reflexivity).
  pose proof (zf_internal_omega_induction R EM Model w pair_run_formula rho Omega
    pair_run_formula_output_fresh At) as Ind.
  assert (Base : forall e, RelEmpty R e -> FolHolds R (update_variable rho 2 e) pair_run_formula).
  { intros e Empty. rewrite (pair_run_formula_holds R EM). rewrite update_variable_eq,update_variable_neq by lia.
    rewrite Seed. now apply (zf_stage_run_base R EM Model). }
  assert (Step : forall x y, R x w -> RelSuccessor R y x ->
    FolHolds R (update_variable rho 2 x) pair_run_formula -> FolHolds R (update_variable rho 2 y) pair_run_formula).
  { intros x y WX Next Prev. rewrite (pair_run_formula_holds R EM) in Prev |- *.
    rewrite !update_variable_eq in Prev. rewrite !update_variable_neq in Prev by lia. rewrite Seed in Prev.
    rewrite !update_variable_eq. rewrite !update_variable_neq by lia. rewrite Seed.
    destruct Prev as [h H]. exact (zf_stage_run_extend R EM Model h x y seed H Next). }
  specialize (Ind Base Step). intros n N. specialize (Ind n N).
  rewrite (pair_run_formula_holds R EM) in Ind. rewrite update_variable_eq,update_variable_neq in Ind by lia.
  rewrite Seed in Ind. exact Ind.
Qed.
End InternalRuns.
Print Assumptions zf_pair_stage_history_exists.
