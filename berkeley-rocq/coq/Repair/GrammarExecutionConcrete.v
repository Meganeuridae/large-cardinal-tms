(** Concrete token contracts instantiate the compressed-source execution. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorRegisters CompilerReverse.
From Repair Require Import SyntaxData CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorControl ConstructorStreams ConstructorCons ConstructorFrame ConstructorTokens GrammarExecutionBlocks GrammarExecution GrammarExecutionDispatch GrammarExecutionAxioms SourceExecution.
Import ListNotations.
Local Opaque source_graph source_residual_roots source_token_roots candidate_axioms.

Theorem actual_source_token_block params frame tok root :
  In (tok,root) source_token_roots -> SourceBlock params (constructor_view params frame) root [tok].
Proof.
  intros InRoot ctx rs initial final Prefix View Exec.
  cbn [run_tokens bind] in Exec.
  destruct (token_step params tok initial) as [result|] eqn:E; [|discriminate].
  cbn [bind run_tokens] in Exec. inversion Exec; subst result.
  destruct (source_token_nonempty params frame tok root ctx rs initial final
    InRoot Prefix View E) as [mid [rs' [First [Tail [V _]]]]].
  exists mid,rs'. auto.
Qed.

Lemma nth_after_dispatch rs pad i : 11<=length rs -> i<11 -> i<>4 ->
  nth_error (set_register 4 1 rs ++ repeat 0 pad) i = nth_error rs i.
Proof.
  intros Len I Ne. rewrite nth_error_app1 by (rewrite set_register_length; lia).
  apply nth_error_set_other. congruence.
Qed.

Lemma constructor_view_after_dispatch params frame r rs pad :
  constructor_view params frame r rs ->
  constructor_view params (set_register 4 1 rs ++ repeat 0 pad) r
    (set_register 4 1 rs ++ repeat 0 pad).
Proof.
  intros [Len [Top [Stack [X [Y [X0 [Y0 [Frame Params]]]]]]]].
  unfold constructor_view. repeat split; try assumption.
  - rewrite app_length, set_register_length, repeat_length. lia.
  - rewrite nth_after_dispatch by lia. exact Top.
  - rewrite nth_after_dispatch by lia. exact Stack.
  - rewrite nth_after_dispatch by lia. exact X.
  - rewrite nth_after_dispatch by lia. exact Y.
  - intros n H. rewrite nth_after_dispatch by lia. now apply Params.
Qed.

Definition unchanged_outside_axiom (before after : list nat) := forall i, i<11 ->
  i<>2 -> i<>3 -> i<>4 -> i<>8 -> i<>9 -> nth_error after i = nth_error before i.

Theorem actual_source_switch_constructs_axiom params frame i f root rs t s :
  nth_error candidate_axioms i = Some f -> nth_error source_residual_roots i = Some root ->
  nth_error rs 4 = Some (3+i) -> constructor_view params frame (CR t s 0 0) rs ->
  exists rs' pad,
    SourceProgramRuns (main_switch_pc,rs) (axiom_parent_pc i++[true],rs') /\
    constructor_view params (set_register 4 1 rs ++ repeat 0 (3+i))
      (CR (formula_code params f) (cantor t s) 0 0) rs' /\
    unchanged_outside_axiom rs rs' /\
    skipn 11 rs' = skipn 11 rs ++ repeat 0 pad.
Proof.
  intros F Root Code View.
  assert (I : i < 24).
  { rewrite <- candidate_axioms_count. apply nth_error_Some. rewrite F. discriminate. }
  destruct View as [Len Other].
  assert (View : constructor_view params frame (CR t s 0 0) rs) by (split; assumption).
  set (r0 := set_register 4 1 rs ++ repeat 0 (3+i)).
  pose proof (switch_axiom_dispatch i rs I Len Code) as Dispatch.
  assert (V0 : constructor_view params r0 (CR t s 0 0) r0).
  { unfold r0. now apply constructor_view_after_dispatch with (frame:=frame). }
  pose proof (axiom_dispatch_context_is_source_prefix i root Root) as Prefix.
  rewrite (axiom_context_after_parent i I) in Prefix.
  destruct (source_residual_constructs_formula_conditional params (constructor_view params r0)
    (actual_source_token_block params r0) i f root (axiom_parent_pc i++[false]) r0 t s
    F Root Prefix V0) as [mid [rs' [Step [Tail Result]]]].
  rewrite sequence_left_return in Tail.
  assert (Runs : SourceProgramRuns (main_switch_pc,rs) (axiom_parent_pc i++[true],rs')).
  { eapply source_program_runs_trans; [exact Dispatch|].
    eapply source_program_next with (t:=mid); [|exact Tail].
    eapply constructor_unpad_first_step with (pad:=1). cbn [repeat]. exact Step. }
  destruct (source_runs_zero_suffix _ _ Runs Len) as [pad [Suffix _]].
  exists rs',pad. split; [exact Runs|]. split; [exact Result|]. split; [|exact Suffix].
  destruct Result as [_ [_ [_ [_ [_ [_ [_ [Frame _]]]]]]]].
  unfold unchanged_outside_axiom. intros j J N2 N3 N4 N8 N9.
  rewrite (Frame j J N2 N3 N8 N9). unfold r0. now apply nth_after_dispatch.
Qed.

Print Assumptions actual_source_token_block.
Print Assumptions constructor_view_after_dispatch.
Print Assumptions actual_source_switch_constructs_axiom.
