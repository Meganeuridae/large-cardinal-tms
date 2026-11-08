(** Composing nonempty constructor blocks in the actual source PC semantics. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl CompilerSyntax CompilerRegisters ConstructorPC ConstructorRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorControl ConstructorStreams SourceExecution.
Import ListNotations.
Local Opaque source_graph.

Lemma source_prefix_extend program start ctx q p b next :
  SourcePrefix program start ctx q -> nth_error program q = Some p ->
  select_branch p b = SNode next -> SourcePrefix program start (ctx++[b]) next.
Proof.
  intros P Pair Branch. induction P as [i|i p0 b0 j bits last A B P IH].
  - simpl. eapply source_prefix_cons; [exact Pair|exact Branch|constructor].
  - simpl. eapply source_prefix_cons; [exact A|exact B|]. apply IH; assumption.
Qed.

Lemma sequence_left_return ctx : loop_return (ctx++[false]) = ctx++[true].
Proof.
  destruct (constructor_child_return ctx 0) as [E W]. cbn [repeat app] in E.
  unfold loop_return. rewrite E. exact W.
Qed.
Lemma sequence_right_return ctx : loop_return (ctx++[true]) = loop_return ctx.
Proof.
  unfold loop_return. rewrite rev_app_distr. cbn [rev app break_pc].
  destruct (break_pc 0 (rev ctx++[false])) as [[out n]|]; reflexivity.
Qed.

Section Blocks.
Variable params : nat -> nat.
Variable View : constructor_registers -> list nat -> Prop.

(** Every block takes at least one actual normalized source step.  This is
    needed to lift the left child's initial false bit into the parent PC. *)
Definition SourceBlock root tokens : Prop :=
  forall ctx rs initial final,
    SourcePrefix source_graph source_root ctx root -> View initial rs ->
    run_tokens params tokens initial = Some final ->
    exists mid rs', SourceProgramStep (ctx,rs) mid /\
      SourceProgramRuns mid (loop_return ctx,rs') /\ View final rs'.

Theorem source_blocks_pair root left right xs ys :
  nth_error source_graph root = Some(SNode left,SNode right) ->
  SourceBlock left xs -> SourceBlock right ys -> SourceBlock root (xs++ys).
Proof.
  intros Pair Left Right ctx rs initial final Prefix V Exec.
  rewrite run_tokens_append in Exec. unfold bind in Exec.
  destruct (run_tokens params xs initial) as [intermediate|] eqn:A; [|discriminate].
  assert (PL : SourcePrefix source_graph source_root (ctx++[false]) left).
  { eapply source_prefix_extend; [exact Prefix|exact Pair|reflexivity]. }
  assert (PR : SourcePrefix source_graph source_root (ctx++[true]) right).
  { eapply source_prefix_extend; [exact Prefix|exact Pair|reflexivity]. }
  destruct (Left _ _ _ _ PL V A) as [mid1 [rs1 [Step1 [Tail1 V1]]]].
  rewrite sequence_left_return in Tail1.
  destruct (Right _ _ _ _ PR V1 Exec) as [mid2 [rs2 [Step2 [Tail2 V2]]]].
  rewrite sequence_right_return in Tail2.
  exists mid1,rs2. split.
  - eapply constructor_unpad_first_step with (pad:=1). cbn [repeat]. exact Step1.
  - split; [|exact V2].
    eapply source_program_runs_trans; [exact Tail1|].
    eapply source_program_next; [exact Step2|exact Tail2].
Qed.
End Blocks.

Print Assumptions source_prefix_extend.
Print Assumptions sequence_left_return.
Print Assumptions sequence_right_return.
Print Assumptions source_blocks_pair.
