(** Repaired source execution of the two loops that copy a parameter into a
    comparison register while restoring the parameter and scratch register. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerReverse CompilerRegisters ConstructorUnpair ConstructorPush.
From Repair Require Import ConstructorGraph CompilerData SourceExecution CompilerTrees CompilerLoops ConstructorControl Frame.
Import ListNotations.

Definition copy_frame (before after : list nat) output :=
  forall i, i<11 -> i<>output -> nth_error after i=nth_error before i.

Theorem guarded_copy_nonempty ctx first second p output rs value :
  SourcePrefix source_graph source_root (ctx++[false]) first ->
  SourcePrefix source_graph source_root (ctx++[true;false]) second ->
  unfold_root first=Some(tree_while2 p 8 output) -> unfold_root second=Some(tree_while1 8 p) ->
  p<11 -> output<11 -> p<>8 -> p<>output -> 8<>output -> 11<=length rs ->
  nth_error rs p=Some value -> nth_error rs 8=Some 0 -> nth_error rs output=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (ctx++[true;true],result) /\
    11<=length result /\ nth_error result output=Some value /\ copy_frame rs result output /\
    exists k, skipn 11 result=skipn 11 rs++repeat 0 k.
Proof.
  intros Prefix1 Prefix2 Tree1 Tree2 P O P8 PO O8 Len Val Scratch Out.
  destruct (while2_transfer_nonempty (ctx++[false]) first rs p 8 output value 0 0
    Prefix1 Tree1 P ltac:(lia) O P8 PO O8 Len Val Scratch Out) as [mid [First Run1]].
  cbn [Nat.add_0_l] in Run1. rewrite constructor_loop_return_false in Run1.
  set (r1:=set_register output value (set_register 8 value (set_register p 0 rs))++repeat 0 value).
  change (SourceProgramRuns mid (ctx++[true],r1)) in Run1.
  assert (L1 : 11<=length r1).
  { unfold r1. rewrite app_length,repeat_length,!set_register_length. lia. }
  assert (P1 : nth_error r1 p=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (S1 : nth_error r1 8=Some value).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (O1 : nth_error r1 output=Some value).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite !set_register_length. lia. }
  assert (F1 : forall i, i<11 -> i<>p -> i<>8 -> i<>output -> nth_error r1 i=nth_error rs i).
  { intros i I Ip I8 Io. unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. reflexivity. }
  destruct (while1_transfer_nonempty (ctx++[true;false]) second r1 8 p value 0
    Prefix2 Tree2 ltac:(lia) P ltac:(lia) L1 S1 P1) as [mid2 [Second Run2]].
  cbn [Nat.add_0_l] in Run2.
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in Run2 by now rewrite <- app_assoc.
  rewrite constructor_loop_return_false in Run2. rewrite <- app_assoc in Run2. cbn [app] in Run2.
  set (result:=set_register p value (set_register 8 0 r1)++repeat 0 value).
  change (SourceProgramRuns mid2 (ctx++[true;true],result)) in Run2.
  assert (Combined : SourceProgramRuns mid (ctx++[true;true],result)).
  { eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next; [|exact Run2].
    eapply constructor_unpad_first_step with (pad:=1).
    change (SourceProgramStep ((ctx++[true])++[false],r1) mid2). rewrite <- app_assoc. exact Second. }
  assert (Initial : SourceProgramStep (ctx,rs) mid).
  { eapply constructor_unpad_first_step with (pad:=1). exact First. }
  assert (Full : SourceProgramRuns (ctx,rs) (ctx++[true;true],result))
    by (eapply source_program_next; eassumption).
  destruct (repair_source_runs_zero_suffix _ _ Full Len) as [pad [Suffix Length]].
  exists result,mid. split; [exact Initial|]. split; [exact Combined|].
  cbn [snd] in Suffix,Length. repeat split; try lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact O1.
  - unfold copy_frame. intros i I Io.
    destruct (Nat.eq_dec i p) as [->|Ip].
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_same by (rewrite set_register_length; lia). now symmetry.
    + destruct (Nat.eq_dec i 8) as [->|I8].
      * unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
        rewrite nth_error_set_other by lia. rewrite nth_error_set_same by lia. now symmetry.
      * unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
        rewrite !nth_error_set_other by lia. now apply F1.
  - now exists pad.
Qed.

Print Assumptions guarded_copy_nonempty.
