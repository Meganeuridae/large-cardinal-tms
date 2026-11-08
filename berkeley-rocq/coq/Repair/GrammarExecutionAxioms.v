(** Actual axiom-switch execution composed with the compressed emitter. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorRegisters CompilerReverse.
From Repair Require Import SyntaxData CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorControl ConstructorStreams GrammarExecutionBlocks GrammarExecution GrammarExecutionDispatch SourceExecution.
Import ListNotations.
Lemma candidate_axioms_count : length candidate_axioms = 24.
Proof. vm_compute. reflexivity. Qed.
Local Opaque source_graph source_residual_roots candidate_axioms.

Section AxiomExecution.
Variable params : nat -> nat.
Variable View : constructor_registers -> list nat -> Prop.
Hypothesis token_blocks : forall tok root, In (tok,root) source_token_roots ->
  SourceBlock params View root [tok].
Hypothesis dispatch_view : forall r rs n, 11 <= length rs -> View r rs ->
  View r (set_register 4 1 rs ++ repeat 0 n).

Theorem source_switch_constructs_axiom i f root rs t s :
  nth_error candidate_axioms i = Some f -> nth_error source_residual_roots i = Some root ->
  11 <= length rs -> nth_error rs 4 = Some (3+i) -> View (CR t s 0 0) rs ->
  exists rs', SourceProgramRuns (main_switch_pc,rs) (axiom_parent_pc i++[true],rs') /\
    View (CR (formula_code params f) (cantor t s) 0 0) rs'.
Proof.
  intros F Root Len Code V.
  assert (I : i < 24).
  { rewrite <- candidate_axioms_count. apply nth_error_Some. rewrite F. discriminate. }
  pose proof (switch_axiom_dispatch i rs I Len Code) as Dispatch.
  set (r0 := set_register 4 1 rs ++ repeat 0 (3+i)).
  assert (V0 : View (CR t s 0 0) r0).
  { unfold r0. apply dispatch_view; assumption. }
  pose proof (axiom_dispatch_context_is_source_prefix i root Root) as Prefix.
  rewrite (axiom_context_after_parent i I) in Prefix.
  destruct (source_residual_constructs_formula_conditional params View token_blocks
    i f root (axiom_parent_pc i++[false]) r0 t s F Root Prefix V0)
    as [mid [rs' [Step [Tail Result]]]].
  rewrite sequence_left_return in Tail.
  exists rs'. split; [|exact Result].
  eapply source_program_runs_trans; [exact Dispatch|].
  eapply source_program_next with (t:=mid); [|exact Tail].
  eapply constructor_unpad_first_step with (pad:=1). cbn [repeat]. exact Step.
Qed.
End AxiomExecution.

Print Assumptions source_switch_constructs_axiom.
