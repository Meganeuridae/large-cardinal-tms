(** Actual modus-ponens body, including cparam, formula construction,
    register comparison, conditional copy, select, and relative return. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerRegisters ConstructorArithmetic ProofSearchSyntax.
From Repair Require Import CompilerExecution CompilerLoopBase ConstructorFrame ConstructorControl SearchSelect SearchSelectBranch SearchPrimitivesEqBody GrammarExecutionDispatch GrammarExecutionBodies GrammarExecutionMPParameters GrammarExecutionMPTokens GrammarExecutionMPTransfer SourceExecution.
Import ListNotations.

Definition mp_candidate minor major a := if Nat.eqb major (code_imp minor a) then a else 0.

Theorem source_mp_body_nonempty rs minor major rest a b c :
  11<=length rs -> nth_error rs 2=Some 0 ->
  nth_error rs 3=Some(cantor minor (cantor major rest)) -> nth_error rs 4=Some 1 ->
  nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 -> nth_error rs 10=Some 0 ->
  exists result mid, SourceProgramStep (special_body_cursor 1 0,rs) mid /\
    SourceProgramRuns mid (loop_return main_switch_pc,result) /\ 11<=length result /\
    nth_error result 2=Some(mp_candidate minor major a) /\ nth_error result 3=Some rest /\
    nth_error result 4=Some 0 /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    nth_error result 10=Some 0 /\ nth_error result 0=nth_error rs 0 /\
    nth_error result 1=nth_error rs 1 /\
    exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y Z.
  destruct (source_mp_parameters_nonempty rs a b c minor major rest Len Top Stack Code A B C X Y)
    as [r1 [mid1 H1]].
  destruct H1 as [First1 H1]. destruct H1 as [Tail1 H1]. destruct H1 as [Len1 H1].
  destruct H1 as [Top1 H1]. destruct H1 as [Stack1 H1]. destruct H1 as [Code1 H1].
  destruct H1 as [A1 H1]. destruct H1 as [B1 H1]. destruct H1 as [C1 H1].
  destruct H1 as [X1 H1]. destruct H1 as [Y1 H1]. destruct H1 as [Frame1 Suffix1].
  assert (Z1 : nth_error r1 10=Some 0) by (rewrite (Frame1 10) by lia; exact Z).
  destruct (source_mp_tokens_nonempty r1 a major minor rest Len1 Top1 Stack1 Code1 A1 B1 C1 X1 Y1)
    as [r2 [mid2 H2]].
  destruct H2 as [First2 H2]. destruct H2 as [Tail2 H2]. destruct H2 as [Len2 H2].
  destruct H2 as [Top2 H2]. destruct H2 as [Stack2 H2]. destruct H2 as [Code2 H2].
  destruct H2 as [A2 H2]. destruct H2 as [B2 H2]. destruct H2 as [C2 H2].
  destruct H2 as [X2 H2]. destruct H2 as [Y2 H2]. destruct H2 as [Frame2 Suffix2].
  assert (Z2 : nth_error r2 10=Some 0) by (rewrite (Frame2 10) by lia; exact Z1).
  destruct (source_mp_transfer_nonempty r2 minor a major rest Len2 Top2 Stack2 Code2 A2 B2 C2 X2 Y2 Z2)
    as [r3 [mid3 H3]].
  destruct H3 as [First3 H3]. destruct H3 as [Tail3 H3]. destruct H3 as [Len3 H3].
  destruct H3 as [Top3 H3]. destruct H3 as [Stack3 H3]. destruct H3 as [Code3 H3].
  destruct H3 as [A3 H3]. destruct H3 as [B3 H3]. destruct H3 as [C3 H3].
  destruct H3 as [X3 H3]. destruct H3 as [Y3 H3]. destruct H3 as [Z3 H3].
  destruct H3 as [Frame3 Suffix3].
  pose proof (special_body_paths 1 8 670 (or_introl eq_refl) ltac:(reflexivity)) as EqPrefix.
  destruct (source_mp_if_eq_nonempty (special_body_context 1 8) (code_imp minor a) major 0 a r3
    EqPrefix Len3 Top3 A3 X3 Y3 Z3) as [r4 [mid4 H4]].
  destruct H4 as [First4 H4]. destruct H4 as [Tail4 H4]. destruct H4 as [Len4 H4].
  destruct H4 as [Top4 H4]. destruct H4 as [A4 H4]. destruct H4 as [X4 H4].
  destruct H4 as [Y4 [Z4 Frame4]]. rewrite special_body_context_return in Tail4.
  assert (Candidate4 : nth_error r4 2=Some(mp_candidate minor major a)).
  { unfold mp_candidate. rewrite Nat.eqb_sym. cbn [Nat.add_0_l] in Top4. exact Top4. }
  assert (Stack4 : nth_error r4 3=Some(cantor 0 rest)) by (rewrite (Frame4 3) by lia; exact Stack3).
  assert (Code4 : nth_error r4 4=Some 1) by (rewrite (Frame4 4) by lia; exact Code3).
  pose proof (special_body_paths 1 9 680 (or_introl eq_refl) ltac:(reflexivity)) as SelectPrefix.
  destruct (source_select_nonempty (special_body_context 1 9) r4 (mp_candidate minor major a) 0 rest 1
    SelectPrefix Len4 Candidate4 Stack4 Code4 X4 Y4) as [result [mid5 H5]].
  destruct H5 as [First5 H5]. destruct H5 as [Tail5 H5]. destruct H5 as [Len5 H5].
  destruct H5 as [Top5 H5]. destruct H5 as [Stack5 H5]. destruct H5 as [Code5 H5].
  destruct H5 as [X5 H5]. destruct H5 as [Y5 [Frame5 Suffix5]].
  cbn [selected_top Nat.pred] in Top5,Code5. rewrite special_body_context_return in Tail5.
  assert (Z5 : nth_error result 10=Some 0) by (rewrite (Frame5 10) by lia; exact Z4).
  assert (Frame0 : nth_error result 0=nth_error rs 0).
  { rewrite (Frame5 0) by lia. rewrite (Frame4 0) by lia. rewrite (Frame3 0) by lia.
    rewrite (Frame2 0) by lia. now apply Frame1; lia. }
  assert (Frame1' : nth_error result 1=nth_error rs 1).
  { rewrite (Frame5 1) by lia. rewrite (Frame4 1) by lia. rewrite (Frame3 1) by lia.
    rewrite (Frame2 1) by lia. now apply Frame1; lia. }
  assert (AllTail : SourceProgramRuns mid1 (loop_return main_switch_pc,result)).
  { eapply source_program_runs_trans; [exact Tail1|]. eapply source_program_next with (t:=mid2); [exact First2|].
    eapply source_program_runs_trans; [exact Tail2|]. eapply source_program_next with (t:=mid3); [exact First3|].
    eapply source_program_runs_trans; [exact Tail3|]. eapply source_program_next with (t:=mid4).
    - eapply constructor_unpad_first_step with (pad:=1). exact First4.
    - eapply source_program_runs_trans; [exact Tail4|]. eapply source_program_next with (t:=mid5).
      + eapply constructor_unpad_first_step with (pad:=1). exact First5.
      + eapply source_program_runs_trans; [exact Tail5|].
        eapply source_program_next; [apply special_body_break; now left|constructor]. }
  assert (All : SourceProgramRuns (special_body_cursor 1 0,rs) (loop_return main_switch_pc,result)).
  { eapply source_program_next; eassumption. }
  destruct (source_runs_zero_suffix _ _ All Len) as [pad [Suffix _]].
  exists result,mid1. repeat split; try assumption. now exists pad.
Qed.

Print Assumptions source_mp_body_nonempty.
