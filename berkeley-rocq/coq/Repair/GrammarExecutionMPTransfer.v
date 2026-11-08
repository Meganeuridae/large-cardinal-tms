(** Actual MP comparison preparation: save implication and copy major proof. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic ProofSearchSyntax.
From Repair Require Import CompilerData CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorControl ConstructorFrame GrammarExecutionBodies SourceExecution.
Import ListNotations.

Local Transparent source_graph unfold_root.
Lemma mp_transfer_trees :
  unfold_root 653 = Some(tree_while1 2 9) /\
  unfold_root 656 = Some(tree_while2 6 8 10) /\
  unfold_root 20 = Some(tree_while1 8 6).
Proof. vm_compute. repeat split; reflexivity. Qed.
Local Opaque source_graph unfold_root.

Definition outside_mp_transfer (before after : list nat) := forall i, i<11 ->
  i<>2 -> i<>6 -> i<>8 -> i<>9 -> i<>10 -> nth_error after i=nth_error before i.

Theorem source_mp_transfer_nonempty rs minor a major rest :
  11<=length rs -> nth_error rs 2=Some(code_imp minor a) -> nth_error rs 3=Some(cantor 0 rest) ->
  nth_error rs 4=Some 1 -> nth_error rs 5=Some a -> nth_error rs 6=Some major ->
  nth_error rs 7=Some minor -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result mid, SourceProgramStep (special_body_cursor 1 5,rs) mid /\
    SourceProgramRuns mid (special_body_cursor 1 8,result) /\ 11<=length result /\
    nth_error result 2=Some 0 /\ nth_error result 3=Some(cantor 0 rest) /\
    nth_error result 4=Some 1 /\ nth_error result 5=Some a /\ nth_error result 6=Some major /\
    nth_error result 7=Some minor /\ nth_error result 8=Some 0 /\
    nth_error result 9=Some(code_imp minor a) /\ nth_error result 10=Some major /\
    outside_mp_transfer rs result /\ exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y Z.
  destruct mp_transfer_trees as [T1 [T2 T3]].
  pose proof (special_body_paths 1 5 653 (or_introl eq_refl) ltac:(reflexivity)) as P1.
  destruct (while1_transfer_nonempty (special_body_context 1 5) 653 rs 2 9
    (code_imp minor a) 0 P1 T1 ltac:(lia) ltac:(lia) ltac:(lia) Len Top Y)
    as [mid1 [First1 Tail1]]. cbn [Nat.add_0_l] in Tail1.
  set (r1 := set_register 9 (code_imp minor a) (set_register 2 0 rs) ++ repeat 0 (code_imp minor a)).
  fold r1 in Tail1. rewrite special_body_context_return in Tail1.
  assert (Len1 : 11<=length r1) by (unfold r1; rewrite app_length,repeat_length,!set_register_length; lia).
  assert (F1 : forall i, i<11 -> i<>2 -> i<>9 -> nth_error r1 i=nth_error rs i).
  { unfold r1. intros. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    now rewrite !nth_error_set_other by lia. }
  assert (Top1 : nth_error r1 2=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (Y1 : nth_error r1 9=Some(code_imp minor a)).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (B1 : nth_error r1 6=Some major) by (rewrite F1 by lia; exact B).
  assert (X1 : nth_error r1 8=Some 0) by (rewrite F1 by lia; exact X).
  assert (Z1 : nth_error r1 10=Some 0) by (rewrite F1 by lia; exact Z).
  pose proof (special_body_paths 1 6 656 (or_introl eq_refl) ltac:(reflexivity)) as P2.
  destruct (while2_transfer_nonempty (special_body_context 1 6) 656 r1 6 8 10 major 0 0
    P2 T2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len1 B1 X1 Z1)
    as [mid2 [First2 Tail2]]. cbn [Nat.add_0_l] in Tail2.
  set (r2 := set_register 10 major (set_register 8 major (set_register 6 0 r1)) ++ repeat 0 major).
  fold r2 in Tail2. rewrite special_body_context_return in Tail2.
  assert (Len2 : 11<=length r2) by (unfold r2; rewrite app_length,repeat_length,!set_register_length; lia).
  assert (F2 : forall i, i<11 -> i<>6 -> i<>8 -> i<>10 -> nth_error r2 i=nth_error r1 i).
  { unfold r2. intros. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    now rewrite !nth_error_set_other by lia. }
  assert (B2 : nth_error r2 6=Some 0).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (X2 : nth_error r2 8=Some major).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (Z2 : nth_error r2 10=Some major).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite !set_register_length. lia. }
  pose proof (special_body_paths 1 7 20 (or_introl eq_refl) ltac:(reflexivity)) as P3.
  destruct (while1_transfer_nonempty (special_body_context 1 7) 20 r2 8 6 major 0
    P3 T3 ltac:(lia) ltac:(lia) ltac:(lia) Len2 X2 B2) as [mid3 [First3 Tail3]].
  cbn [Nat.add_0_l] in Tail3.
  set (result := set_register 6 major (set_register 8 0 r2) ++ repeat 0 major).
  fold result in Tail3. rewrite special_body_context_return in Tail3.
  assert (Len3 : 11<=length result) by (unfold result; rewrite app_length,repeat_length,!set_register_length; lia).
  assert (F3 : forall i, i<11 -> i<>6 -> i<>8 -> nth_error result i=nth_error r2 i).
  { unfold result. intros. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    now rewrite !nth_error_set_other by lia. }
  assert (B3 : nth_error result 6=Some major).
  { unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (X3 : nth_error result 8=Some 0).
  { unfold result. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (AllTail : SourceProgramRuns mid1 (special_body_cursor 1 8,result)).
  { eapply source_program_runs_trans; [exact Tail1|].
    eapply source_program_next with (t:=mid2).
    - eapply constructor_unpad_first_step with (pad:=1). exact First2.
    - eapply source_program_runs_trans; [exact Tail2|].
      eapply source_program_next with (t:=mid3).
      + eapply constructor_unpad_first_step with (pad:=1). exact First3.
      + exact Tail3. }
  assert (First : SourceProgramStep (special_body_cursor 1 5,rs) mid1).
  { eapply constructor_unpad_first_step with (pad:=1). exact First1. }
  assert (All : SourceProgramRuns (special_body_cursor 1 5,rs) (special_body_cursor 1 8,result)).
  { eapply source_program_next; eassumption. }
  destruct (source_runs_zero_suffix _ _ All Len) as [pad [Suffix _]].
  exists result,mid1. repeat split; try assumption.
  - rewrite F3,F2 by lia. exact Top1.
  - rewrite F3,F2,F1 by lia. exact Stack.
  - rewrite F3,F2,F1 by lia. exact Code.
  - rewrite F3,F2,F1 by lia. exact A.
  - rewrite F3,F2,F1 by lia. exact C.
  - rewrite F3,F2 by lia. exact Y1.
  - rewrite F3 by lia. exact Z2.
  - unfold outside_mp_transfer. intros i I I2 I6 I8 I9 I10.
    rewrite F3,F2,F1 by lia. reflexivity.
  - now exists pad.
Qed.

Print Assumptions source_mp_transfer_nonempty.
