(** Actual source execution of the positive branch of select's opcode test. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPush ConstructorFrame ConstructorParam SearchPrimitivesDrain SearchSelectControl SourceExecution.
Import ListNotations.

Definition outside_select_if (before after : list nat) := forall i, i<11 ->
  i<>2 -> i<>4 -> i<>8 -> nth_error after i = nth_error before i.

Theorem source_select_if_positive_nonempty ctx rs old saved n :
  SourcePrefix source_graph source_root ctx 678 -> 11<=length rs ->
  nth_error rs 2=Some old -> nth_error rs 4=Some(S n) -> nth_error rs 8=Some saved ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 2=Some saved /\ nth_error result 4=Some n /\
    nth_error result 8=Some 0 /\ outside_select_if rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros P L Top Code Scratch.
  set (r1 := set_register 4 n rs++[0]).
  pose proof (select_if_positive_step ctx rs n P Code) as First. fold r1 in First.
  assert (L1 : 11<=length r1) by (unfold r1; rewrite length_app,set_register_length; cbn; lia).
  assert (T1 : nth_error r1 2=Some old).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Top. }
  assert (C1 : nth_error r1 4=Some n).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  assert (X1 : nth_error r1 8=Some saved).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Scratch. }
  destruct select_source_prefixes as [_ [_ [_ [_ [_ [DrainPrefix MovePrefix]]]]]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P DrainPrefix) as Pdrain.
  destruct (source_drain_nonempty (ctx++[true;false]) 675 2 r1 old
    Pdrain select_top_drain_tree ltac:(lia) L1 T1) as [mid2 [DrainFirst DrainRun]].
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in DrainRun by now rewrite <- app_assoc.
  rewrite constructor_loop_return_false in DrainRun. rewrite <- app_assoc in DrainRun. cbn [app] in DrainRun.
  set (r2 := set_register 2 0 r1++repeat 0 old).
  change (SourceProgramRuns mid2 (ctx++[true;true],r2)) in DrainRun.
  assert (L2 : 11<=length r2) by (unfold r2; rewrite length_app,repeat_length,set_register_length; lia).
  assert (T2 : nth_error r2 2=Some 0).
  { unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  assert (C2 : nth_error r2 4=Some n).
  { unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact C1. }
  assert (X2 : nth_error r2 8=Some saved).
  { unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact X1. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P MovePrefix) as Pmove.
  pose proof (while1_transfer (ctx++[true;true]) 676 r2 8 2 saved 0
    Pmove select_scratch_move_tree ltac:(lia) ltac:(lia) ltac:(lia) L2 X2 T2) as MoveRun.
  rewrite loop_return_two_true in MoveRun.
  set (result := set_register 2 saved (set_register 8 0 r2)++repeat 0 saved).
  change (SourceProgramRuns (ctx++[true;true],r2) (loop_return ctx,result)) in MoveRun.
  assert (Tail : SourceProgramRuns (ctx++[true],r1) (loop_return ctx,result)).
  { eapply source_program_next with (t:=mid2).
    - eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
      rewrite <- app_assoc. exact DrainFirst.
    - eapply source_program_runs_trans; eassumption. }
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next; eassumption. }
  destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
  exists result,(ctx++[true],r1). repeat split; try assumption.
  - unfold result. rewrite length_app,repeat_length,!set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact C2.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
  - unfold outside_select_if. intros i I I2 I4 I8.
    unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia.
    unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia.
    unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    now rewrite nth_error_set_other by lia.
  - now exists pad.
Qed.
Print Assumptions source_select_if_positive_nonempty.

Definition selected_top (code old computed : nat) : nat := match code with 0 => old | S _ => computed end.
Definition selected_scratch (code computed : nat) : nat := match code with 0 => computed | S _ => 0 end.

Theorem source_select_if_nonempty ctx rs old computed code :
  SourcePrefix source_graph source_root ctx 678 -> 11<=length rs ->
  nth_error rs 2=Some old -> nth_error rs 4=Some code -> nth_error rs 8=Some computed ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 2=Some(selected_top code old computed) /\
    nth_error result 4=Some(pred code) /\
    nth_error result 8=Some(selected_scratch code computed) /\ outside_select_if rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros P L T C X. destruct code as [|n].
  - exists rs,(loop_return ctx,rs). cbn [selected_top selected_scratch pred].
    repeat split; try assumption.
    + apply select_if_zero_step; assumption.
    + constructor.
    + exists 0. cbn [repeat]. now rewrite app_nil_r.
  - exact (source_select_if_positive_nonempty ctx rs old computed n P L T C X).
Qed.
Print Assumptions source_select_if_nonempty.
