(** First-order Replacement collects the uniquely determined end stage of
    every internal natural-number history. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofFormula FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxBijection BerkeleySyntaxOmega BerkeleySyntaxFormulaSet
  BerkeleySyntaxZFBase BerkeleySyntaxZFSeparation BerkeleySyntaxZFReplacement BerkeleySyntaxZFPairStage BerkeleySyntaxZFFiniteGraph
  BerkeleySyntaxZFStageRun BerkeleySyntaxZFStageFormula BerkeleySyntaxZFStageInduction BerkeleySyntaxZFStageUniqueness.
Import ListNotations.
Definition RelPairStageEnd {D} (R:D->D->Prop) seed n v :=
  exists h, RelPairStageRun R h n seed /\ RelGraph R h n v.
Definition b_stage_end n seed v := b_ex (fun h => b_and (b_stage_run h n seed) (b_rel h n v)).
Definition pair_end_replacement_builder := b_and (b_mem 3 5) (b_stage_end 3 4 2).
Definition pair_end_replacement_formula := instantiate_formula (fun _=>0) (fst (pair_end_replacement_builder 6)).
Lemma pair_end_replacement_fresh : fol_free 1 pair_end_replacement_formula=false.
Proof. vm_compute. reflexivity. Qed.
Lemma b_good_stage_run h n seed : b_good (b_stage_run h n seed).
Proof.
  unfold b_stage_run. apply b_good_ex. intro dom. unfold b_run_domain,b_and4,b_and3.
  repeat apply b_good_and; try apply b_good_successor; try apply b_good_partial_function;
    try apply b_good_run_zero; apply b_good_run_steps.
Qed.
Section StageCollection.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.
Theorem stage_end_builder_holds rho n seed v k : n<k -> seed<k -> v<k ->
  (b_holds R rho (b_stage_end n seed v) k <-> RelPairStageEnd R (rho seed) (rho n) (rho v)).
Proof.
  intros N Seed V. unfold b_stage_end,RelPairStageEnd. rewrite (b_holds_ex EM). split.
  - intros [h H]. rewrite (b_holds_and EM) in H. destruct H as [Run Graph].
    rewrite (stage_run_builder_holds R EM) in Run by lia.
    assert (K:S k<=b_next (b_stage_run k n seed) (S k)) by apply b_good_stage_run.
    rewrite (relation_builder_holds EM) in Graph by lia.
    rewrite update_variable_eq in Run,Graph. repeat rewrite update_variable_neq in Run by lia.
    repeat rewrite update_variable_neq in Graph by lia. now exists h.
  - intros [h [Run Graph]]. exists h. rewrite (b_holds_and EM). split.
    + rewrite (stage_run_builder_holds R EM) by lia. rewrite update_variable_eq.
      repeat rewrite update_variable_neq by lia. exact Run.
    + assert (K:S k<=b_next (b_stage_run k n seed) (S k)) by apply b_good_stage_run.
      rewrite (relation_builder_holds EM) by lia. rewrite update_variable_eq.
      repeat rewrite update_variable_neq by lia. exact Graph.
Qed.
Theorem pair_end_replacement_formula_holds rho : FolHolds R rho pair_end_replacement_formula <->
  R (rho 3) (rho 5) /\ RelPairStageEnd R (rho 4) (rho 3) (rho 2).
Proof.
  change (b_holds R rho pair_end_replacement_builder 6 <->
    R (rho 3) (rho 5) /\ RelPairStageEnd R (rho 4) (rho 3) (rho 2)).
  unfold pair_end_replacement_builder. rewrite (b_holds_and EM),b_holds_mem.
  replace (b_next (b_mem 3 5) 6) with 6 by reflexivity. rewrite stage_end_builder_holds by lia. reflexivity.
Qed.
Lemma zf_pair_stage_end_exists w seed n : RelOmega R w -> R n w -> exists v, RelPairStageEnd R seed n v.
Proof.
  intros Omega N. destruct (zf_pair_stage_history_exists R EM Model w seed Omega n N) as [h [dom [Next [[cod [Graph Total]] Rest]]]].
  assert (In:R n dom) by (apply (proj2 (Next n));now right).
  destruct (Total n In) as [v [V [At Unique]]]. exists v,h. split; [|exact At].
  exists dom. split; [exact Next|]. split; [exists cod;now split|exact Rest].
Qed.
Theorem zf_pair_stage_end_unique w seed n a b : RelOmega R w -> R n w ->
  RelPairStageEnd R seed n a -> RelPairStageEnd R seed n b -> a=b.
Proof.
  intros Omega N [h1 [Run1 A]] [h2 [Run2 B]].
  exact (zf_history_endpoint_unique R EM Model w seed n h1 h2 a b Omega N Run1 Run2 A B).
Qed.
Theorem zf_pair_stage_collection_exists w seed : RelOmega R w ->
  exists stages, forall v, R v stages <-> exists n, R n w /\ RelPairStageEnd R seed n v.
Proof.
  intro Omega. set (rho:=update_variable (update_variable (fun _ : nat=>seed) 0 w) 5 w).
  assert (Func : forall input, exists out, forall z,
    FolHolds R (update_variable (update_variable rho 3 input) 2 z) pair_end_replacement_formula -> z=out).
  { intro input. destruct (EM (R input w)) as [In|NotIn].
    - destruct (zf_pair_stage_end_exists w seed input Omega In) as [out End]. exists out. intros z H.
      rewrite pair_end_replacement_formula_holds in H. unfold rho in H. cbv [update_variable Nat.eqb] in H.
      destruct H as [_ End']. eapply zf_pair_stage_end_unique; eassumption.
    - exists seed. intros z H. rewrite pair_end_replacement_formula_holds in H.
      unfold rho in H. cbv [update_variable Nat.eqb] in H. tauto. }
  destruct (zf_prefix_formula_replacement R EM Model pair_end_replacement_formula rho
    pair_end_replacement_fresh Func) as [stages Stages]. exists stages. intro v. specialize (Stages v).
  unfold rho in Stages. cbv [update_variable Nat.eqb] in Stages. split.
  - intro V. destruct (proj1 Stages V) as [n [N H]]. rewrite pair_end_replacement_formula_holds in H.
    cbv [update_variable Nat.eqb] in H. exists n. tauto.
  - intros [n [N End]]. apply (proj2 Stages). exists n. split; [exact N|].
    rewrite pair_end_replacement_formula_holds. cbv [update_variable Nat.eqb]. tauto.
Qed.
End StageCollection.
Print Assumptions pair_end_replacement_fresh.
Print Assumptions pair_end_replacement_formula_holds.
Print Assumptions zf_pair_stage_end_unique.
Print Assumptions zf_pair_stage_collection_exists.
