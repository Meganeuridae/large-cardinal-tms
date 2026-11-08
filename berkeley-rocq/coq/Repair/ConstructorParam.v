(** Concrete source execution of the three parameter-copy constructors. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorData ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPush ConstructorFrame SourceExecution.
Import ListNotations.

Record param_layout root p transfer restore : Prop := {
  param_push_prefix : SourcePrefix source_graph root [false] source_pushwff_root;
  param_transfer_prefix : SourcePrefix source_graph root [true;false] transfer;
  param_restore_prefix : SourcePrefix source_graph root [true;true] restore;
  param_transfer_tree : unfold_root transfer = Some (tree_while2 p 2 8);
  param_restore_tree : unfold_root restore = Some (tree_while1 8 p)
}.

Local Transparent unfold_small constructor_nodes.
Lemma param_layout_1 : param_layout 17 5 14 16.
Proof.
  constructor; try (apply source_prefix_find_sound; vm_compute; reflexivity);
    apply unfold_small_root_sound; vm_compute; reflexivity.
Qed.
Lemma param_layout_2 : param_layout 21 6 18 20.
Proof.
  constructor; try (apply source_prefix_find_sound; vm_compute; reflexivity);
    apply unfold_small_root_sound; vm_compute; reflexivity.
Qed.
Lemma param_layout_3 : param_layout 51 7 48 50.
Proof.
  constructor; try (apply source_prefix_find_sound; vm_compute; reflexivity);
    apply unfold_small_root_sound; vm_compute; reflexivity.
Qed.

Lemma loop_return_two_true ctx : loop_return (ctx++[true;true]) = loop_return ctx.
Proof.
  replace (ctx++[true;true]) with ((ctx++[true])++[true]) by now rewrite <- app_assoc.
  now rewrite !constructor_loop_return_true.
Qed.

Theorem source_parameter_nonempty ctx root p transfer restore rs t s value :
  param_layout root p transfer restore ->
  SourcePrefix source_graph source_root ctx root ->
  p<11 -> p<>2 -> p<>3 -> p<>8 -> 11<=length rs ->
  nth_error rs 2=Some t -> nth_error rs 3=Some s -> nth_error rs 8=Some 0 ->
  nth_error rs p=Some value ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\
    11<=length result /\ nth_error result 2=Some value /\
    nth_error result 3=Some (cantor t s) /\ nth_error result 8=Some 0 /\
    outside_push rs result /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Layout P Hp Hp2 Hp3 Hp8 L Top Stack Scratch Param.
  destruct Layout as [PushPrefix TransferPrefix RestorePrefix TransferTree RestoreTree].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P PushPrefix) as Ppush.
  destruct (source_push_nonempty (ctx++[false]) rs t s Ppush L Top Stack Scratch)
    as [r1 [mid [First [PushRun [L1 [T1 [S1 [X1 F1]]]]]]]].
  rewrite constructor_loop_return_false in PushRun.
  assert (V1 : nth_error r1 p=Some value).
  { rewrite (F1 p) by lia. exact Param. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P TransferPrefix) as Ptransfer.
  destruct (while2_transfer_nonempty (ctx++[true;false]) transfer r1 p 2 8 value 0 0
    Ptransfer TransferTree Hp ltac:(lia) ltac:(lia) Hp2 Hp8 ltac:(lia) L1 V1 T1 X1)
    as [mid2 [TransferFirst TransferRun]].
  cbn [Nat.add_0_l] in TransferRun.
  replace (ctx++[true;false]) with ((ctx++[true])++[false]) in TransferRun by now rewrite <- app_assoc.
  rewrite constructor_loop_return_false in TransferRun.
  rewrite <- app_assoc in TransferRun. cbn [app] in TransferRun.
  set (r2 := set_register 8 value (set_register 2 value (set_register p 0 r1)) ++ repeat 0 value).
  change (SourceProgramRuns mid2 (ctx++[true;true],r2)) in TransferRun.
  assert (L2 : 11<=length r2).
  { unfold r2. rewrite length_app, repeat_length, !set_register_length. lia. }
  assert (V2 : nth_error r2 p=Some 0).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (T2 : nth_error r2 2=Some value).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same.
    rewrite set_register_length. lia. }
  assert (S2 : nth_error r2 3=Some (cantor t s)).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact S1. }
  assert (X2 : nth_error r2 8=Some value).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite !set_register_length. lia. }
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P RestorePrefix) as Prestore.
  pose proof (while1_transfer (ctx++[true;true]) restore r2 8 p value 0
    Prestore RestoreTree ltac:(lia) Hp ltac:(lia) L2 X2 V2) as RestoreRun.
  cbn [Nat.add_0_l] in RestoreRun. rewrite loop_return_two_true in RestoreRun.
  set (result := set_register p value (set_register 8 0 r2) ++ repeat 0 value).
  change (SourceProgramRuns (ctx++[true;true],r2) (loop_return ctx,result)) in RestoreRun.
  assert (AllRun : SourceProgramRuns (ctx,rs) (loop_return ctx,result)).
  { eapply source_program_next.
    - eapply constructor_unpad_first_step with (pad:=1). exact First.
    - eapply source_program_runs_trans; [exact PushRun|].
      eapply source_program_next with (t:=mid2); [|].
      + eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
        rewrite <- app_assoc. exact TransferFirst.
      +
      eapply source_program_runs_trans; eassumption. }
  destruct (source_runs_zero_suffix _ _ AllRun L) as [pad [Pad _]].
  exists result,mid. repeat split.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - eapply source_program_runs_trans; [exact PushRun|].
    eapply source_program_next with (t:=mid2); [|].
    + eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
      rewrite <- app_assoc. exact TransferFirst.
    +
    eapply source_program_runs_trans; eassumption.
  - unfold result. rewrite length_app, repeat_length, !set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact T2.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact S2.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
  - unfold outside_push. intros i I I2 I3 I8.
    destruct (Nat.eq_dec i p) as [->|D].
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_same by (rewrite set_register_length; lia). symmetry. exact Param.
    + unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia.
      unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite !nth_error_set_other by lia. now apply F1.
  - exists pad. exact Pad.
Qed.
Print Assumptions source_parameter_nonempty.
