(** One actual proof-list field extraction, including both restore loops. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair ConstructorPairFull ConstructorUnpairGenericFull ConstructorUnpairGenericInstances SourceExecution.
Import ListNotations.

Definition decode_frame target (before after : list nat) :=
  forall r, r<11 -> r<>0 -> r<>8 -> r<>9 -> r<>target -> nth_error after r = nth_error before r.

Theorem source_decode_component_nonempty ctx target target_root a b old rs :
  SourcePrefix source_graph source_root (ctx++[false]) 636 ->
  SourcePrefix source_graph source_root (ctx++[true;false]) 638 ->
  SourcePrefix source_graph source_root (ctx++[true;true;false]) target_root ->
  unfold_root 638 = Some (tree_while1 9 0) ->
  unfold_root target_root = Some (tree_while1 8 target) ->
  target<11 -> target<>0 -> target<>8 -> target<>9 -> 11<=length rs ->
  nth_error rs 0 = Some (cantor a b) -> nth_error rs 8 = Some 0 ->
  nth_error rs 9 = Some 0 -> nth_error rs target = Some old ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (ctx++[true;true;true],result) /\
    11<=length result /\ nth_error result 0=Some b /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    nth_error result target=Some (old+a) /\ decode_frame target rs result.
Proof.
  intros P1 P2 P3 T2 T3 I I0 I8 I9 L N X Y Z.
  destruct (source_unpair_generic_cantor_nonempty (ctx++[false]) 636 0 8 9 a b rs
    P1 source_unpair_prooflist_tree ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) L N X Y)
    as [r1 [mid [First [Unpair [L1 [N1 [X1 [Y1 F1]]]]]]]].
  rewrite constructor_loop_return_false in Unpair.
  assert (Z1 : nth_error r1 target = Some old) by (rewrite F1 by lia; exact Z).
  destruct (while1_transfer_nonempty (ctx++[true;false]) 638 r1 9 0 b 0
    P2 T2 ltac:(lia) ltac:(lia) ltac:(lia) L1 Y1 N1) as [mid2 [Step2 Run2]].
  cbn [Nat.add_0_l] in Run2.
  set (r2 := set_register 0 b (set_register 9 0 r1) ++ repeat 0 b).
  fold r2 in Run2.
  assert (Ret2 : loop_return (ctx++[true;false]) = ctx++[true;true]).
  { replace (ctx++[true;false]) with ((ctx++[true])++[false]) by (rewrite <- app_assoc; reflexivity).
    rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
  rewrite Ret2 in Run2.
  assert (L2 : 11<=length r2) by (unfold r2; rewrite app_length,repeat_length,!set_register_length; lia).
  assert (N2 : nth_error r2 0 = Some b).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (X2 : nth_error r2 8 = Some a).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact X1. }
  assert (Y2 : nth_error r2 9 = Some 0).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (Z2 : nth_error r2 target = Some old).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact Z1. }
  destruct (while1_transfer_nonempty (ctx++[true;true;false]) target_root r2 8 target a old
    P3 T3 ltac:(lia) I ltac:(lia) L2 X2 Z2) as [mid3 [Step3 Run3]].
  set (result := set_register target (old+a) (set_register 8 0 r2) ++ repeat 0 a).
  fold result in Run3.
  assert (Ret3 : loop_return (ctx++[true;true;false]) = ctx++[true;true;true]).
  { replace (ctx++[true;true;false]) with ((ctx++[true;true])++[false])
      by (rewrite <- app_assoc; reflexivity).
    rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
  rewrite Ret3 in Run3. exists result,mid. repeat split.
  - eapply constructor_unpad_first_step with (pad:=1). exact First.
  - eapply source_program_runs_trans; [exact Unpair|].
    eapply source_program_next with (t:=mid2).
    + eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],r1) mid2).
      rewrite <- app_assoc. exact Step2.
    + eapply source_program_runs_trans; [exact Run2|].
      eapply source_program_next with (t:=mid3).
      * eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true;true])++[false],r2) mid3).
        rewrite <- app_assoc. exact Step3.
      * exact Run3.
  - unfold result. rewrite app_length,repeat_length,!set_register_length. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact N2.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact Y2.
  - unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia.
  - unfold decode_frame, result. intros r R R0 R8 R9 RT.
    rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. unfold r2.
    rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply F1; assumption.
Qed.

Definition decode_target n := nth n [4;5;6;7] 0.
Definition decode_target_root n := nth n [640;16;20;50] 0.
Definition decode_cursor n := repeat true (5+3*n).

Lemma decode_cursor_next n : decode_cursor n ++ [true;true;true] = decode_cursor (S n).
Proof.
  unfold decode_cursor. replace (5+3*S n) with ((5+3*n)+3) by lia.
  rewrite (repeat_app true (5+3*n) 3). reflexivity.
Qed.

Local Transparent source_graph unfold_root.
Lemma decode_component_paths n : n<4 ->
  SourcePrefix source_graph source_root (decode_cursor n++[false]) 636 /\
  SourcePrefix source_graph source_root (decode_cursor n++[true;false]) 638 /\
  SourcePrefix source_graph source_root (decode_cursor n++[true;true;false]) (decode_target_root n).
Proof.
  intro H. do 4 (destruct n as [|n]; [repeat split; apply source_prefix_find_sound; vm_compute; reflexivity|]). lia.
Qed.

Lemma decode_component_trees n : n<4 ->
  unfold_root 638 = Some (tree_while1 9 0) /\
  unfold_root (decode_target_root n) = Some (tree_while1 8 (decode_target n)).
Proof.
  intro H. do 4 (destruct n as [|n]; [vm_compute; repeat split; reflexivity|]). lia.
Qed.

Lemma decode_target_bounds n : n<4 -> decode_target n < 11 /\
  decode_target n <> 0 /\ decode_target n <> 8 /\ decode_target n <> 9.
Proof. intro H. do 4 (destruct n as [|n]; [vm_compute; repeat split; lia|]). lia. Qed.

Theorem source_decode_field_nonempty n a b old rs : n<4 -> 11<=length rs ->
  nth_error rs 0 = Some (cantor a b) -> nth_error rs 8 = Some 0 ->
  nth_error rs 9 = Some 0 -> nth_error rs (decode_target n) = Some old ->
  exists result mid, SourceProgramStep (decode_cursor n,rs) mid /\
    SourceProgramRuns mid (decode_cursor (S n),result) /\
    11<=length result /\ nth_error result 0=Some b /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    nth_error result (decode_target n)=Some (old+a) /\ decode_frame (decode_target n) rs result.
Proof.
  intros H L N X Y Z.
  destruct (decode_component_paths n H) as [P1 [P2 P3]].
  destruct (decode_component_trees n H) as [T2 T3].
  destruct (decode_target_bounds n H) as [I [I0 [I8 I9]]].
  destruct (source_decode_component_nonempty (decode_cursor n) (decode_target n)
    (decode_target_root n) a b old rs P1 P2 P3 T2 T3 I I0 I8 I9 L N X Y Z)
    as [result [mid [Step [Run Facts]]]].
  rewrite decode_cursor_next in Run. exists result,mid. auto.
Qed.

Print Assumptions source_decode_component_nonempty.
Print Assumptions source_decode_field_nonempty.
