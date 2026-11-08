(** Construction of D(a,b) by the repaired compression grammar followed by
    the actual guarded comparison source subtree. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax CompilerReverse CompilerRegisters ConstructorArithmetic
  ConstructorRegisters ConstructorStreams ProofSearchSyntax.
From Repair Require Import SyntaxData Certificate CompilerData CompilerContexts ConstructorStreams ConstructorCons ConstructorTokens
  GrammarExecutionBlocks GrammarExecutionRules GrammarExecution GrammarExecutionConcrete
  SourceExecution CompilerLoopBase ConstructorControl GuardTail Frame.
Import ListNotations.

Definition guard_formula_code a b := code_neg (code_all a (code_eq a b)).

Lemma guarded_formula_residual :
  nth_error residuals 24=Some [Reference 322] /\
  nth_error source_residual_roots 24=Some source_plain_distinction_root /\
  expand_word full_grammar_environment [Reference 322]=emit guarded_distinction_formula.
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem repaired_plain_distinction_nonempty params frame ctx rs t s :
  SourcePrefix source_graph source_root ctx source_plain_distinction_root ->
  constructor_view params frame (CR t s 0 0) rs ->
  exists mid result, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    constructor_view params frame (CR (guard_formula_code (params 1) (params 2)) (cantor t s) 0 0) result.
Proof.
  intros Prefix View. destruct guarded_formula_residual as [Word [Root Expansion]].
  pose proof (source_grammar_residual_block params (constructor_view params frame)
    (actual_source_token_block params frame) 24 [Reference 322] source_plain_distinction_root Word Root) as Block.
  rewrite Expansion in Block.
  assert (Exec : run_tokens params (emit guarded_distinction_formula) (CR t s 0 0) =
    Some (CR (guard_formula_code (params 1) (params 2)) (cantor t s) 0 0)).
  { pose proof (emitted_formula_constructs_code params guarded_distinction_formula eq_refl t s) as E.
    exact E. }
  exact (Block ctx rs _ _ Prefix View Exec).
Qed.

Theorem repaired_guarded_distinction_nonempty params frame ctx rs t s :
  SourcePrefix source_graph source_root ctx source_guarded_root ->
  constructor_view params frame (CR t s 0 0) rs -> nth_error rs 10=Some 0 ->
  exists mid result, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    constructor_view params frame
      (CR (if Nat.eqb (params 1) (params 2) then 0 else guard_formula_code (params 1) (params 2))
          (cantor t s) 0 0) result /\ nth_error result 10=Some 0 /\
    exists k, skipn 11 result=skipn 11 rs++repeat 0 k.
Proof.
  intros Prefix View S10.
  destruct guard_tail_source_shape as [Pair _].
  assert (Pplain : SourcePrefix source_graph source_root (ctx++[false]) source_plain_distinction_root).
  { eapply source_prefix_extend; [exact Prefix|exact Pair|reflexivity]. }
  assert (Ptail : SourcePrefix source_graph source_root (ctx++[true]) 852).
  { eapply source_prefix_extend; [exact Prefix|exact Pair|reflexivity]. }
  destruct (repaired_plain_distinction_nonempty params frame (ctx++[false]) rs t s Pplain View)
    as [mid [r1 [First [Run1 V1]]]].
  rewrite sequence_left_return in Run1.
  destruct View as [Len [Top [Stack [X [Y [X0 [Y0 [F0 Params0]]]]]]]].
  destruct V1 as [L1 [T1 [S1 [X1 [Y1 [X01 [Y01 [F1 Params1]]]]]]]].
  cbn [top stack scratch1 scratch2] in *.
  assert (S101 : nth_error r1 10=Some 0).
  { rewrite (F1 10) by lia. rewrite <- (F0 10) by lia. exact S10. }
  assert (A1 : nth_error r1 5=Some(params 1)) by (apply (Params1 1); lia).
  assert (B1 : nth_error r1 6=Some(params 2)) by (apply (Params1 2); lia).
  destruct (repaired_guard_tail_nonempty (ctx++[true]) (params 1) (params 2)
    (guard_formula_code (params 1) (params 2)) r1 Ptail L1 T1 A1 B1 X1 Y1 S101)
    as [result [mid2 [Next [Run2 [L2 [T2 [F2 _]]]]]]].
  rewrite sequence_right_return in Run2.
  assert (Initial : SourceProgramStep (ctx,rs) mid).
  { eapply constructor_unpad_first_step with (pad:=1). cbn [repeat]. exact First. }
  assert (Rest : SourceProgramRuns mid (loop_return ctx,result)).
  { eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next; eassumption. }
  assert (Full : SourceProgramRuns (ctx,rs) (loop_return ctx,result))
    by (eapply source_program_next; eassumption).
  destruct (repair_source_runs_zero_suffix _ _ Full Len) as [pad [Suffix Length]].
  exists mid,result. split; [exact Initial|]. split; [exact Rest|]. split.
  - unfold constructor_view. cbn [top stack scratch1 scratch2]. repeat split; try assumption.
    + rewrite F2 by lia. exact S1.
    + rewrite F2 by lia. exact X1.
    + rewrite F2 by lia. exact Y1.
    + unfold outside_cons. intros i I I2 I3 I8 I9. rewrite F2 by lia. now apply F1.
    + intros n N. rewrite F2 by lia. now apply Params1.
  - split.
    + rewrite F2 by lia. exact S101.
    + cbn [snd] in Suffix. now exists pad.
Qed.

Print Assumptions guarded_formula_residual.
Print Assumptions repaired_plain_distinction_nonempty.
Print Assumptions repaired_guarded_distinction_nonempty.
