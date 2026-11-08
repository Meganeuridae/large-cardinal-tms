(** Actual-source execution of the GEN proof-search body. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters ConstructorArithmetic ConstructorRegisters ProofSearchSyntax ProofSearchProgram CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerExecution CompilerLoopBase ConstructorStreams ConstructorControl ConstructorFrame ConstructorCons ConstructorTokens SearchCParamControl SearchCParamOne SearchCParam SearchSelect SearchSelectBranch GrammarExecutionBlocks GrammarExecutionDispatch GrammarExecutionBodies GrammarExecutionConcrete SourceExecution.
Import ListNotations.

Definition outside_gen (before after : list nat) := forall i, i<11 ->
  i<>2 -> i<>3 -> i<>4 -> i<>7 -> i<>8 -> i<>9 ->
  nth_error after i=nth_error before i.

Local Transparent source_token_roots.
Lemma gen_token_roots : In (9,17) source_token_roots /\
  In (11,51) source_token_roots /\ In (4,61) source_token_roots.
Proof. vm_compute. intuition congruence. Qed.

Theorem source_gen_body_nonempty rs old prior a b c :
  11<=length rs -> nth_error rs 2=Some 0 ->
  nth_error rs 3=Some(cantor old prior) -> nth_error rs 4=Some 1 ->
  nth_error rs 5=Some a -> nth_error rs 6=Some b -> nth_error rs 7=Some c ->
  nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  exists result mid, SourceProgramStep (special_body_cursor 2 0,rs) mid /\
    SourceProgramRuns mid (loop_return main_switch_pc,result) /\ 11<=length result /\
    nth_error result 2=Some(code_all a old) /\ nth_error result 3=Some prior /\
    nth_error result 4=Some 0 /\ nth_error result 5=Some a /\ nth_error result 6=Some b /\
    nth_error result 7=Some old /\ nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\
    outside_gen rs result /\ exists pad, skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y.
  pose proof (special_body_paths 2 0 650 (or_intror eq_refl) ltac:(reflexivity)) as P1.
  destruct (source_cparam_nonempty (special_body_context 2 0) 650 7 635 50 rs 1
    (cantor old prior) c cparam_layout_3 P1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Len Code Stack C X Y)
    as [r1 [mid [First [Run1 [L1 [C1 [S1 [P1v [X1 [Y1 [F1 Tail1]]]]]]]]]]].
  cbn [cparam_stack_after cparam_value_after Nat.eqb] in S1,P1v.
  rewrite uncantor_cantor in S1,P1v. cbn [fst snd] in S1,P1v.
  rewrite special_body_context_return in Run1.
  assert (T1 : nth_error r1 2=Some 0) by (rewrite (F1 2) by lia; exact Top).
  assert (A1 : nth_error r1 5=Some a) by (rewrite (F1 5) by lia; exact A).
  assert (B1 : nth_error r1 6=Some b) by (rewrite (F1 6) by lia; exact B).
  set (params := instruction_params a b old).
  assert (View1 : constructor_view params r1 (CR 0 prior 0 0) r1).
  { unfold constructor_view. cbn [top stack scratch1 scratch2]. repeat split; try assumption.
    intros n Hn. destruct n as [|[|[|[|n]]]]; try lia; unfold params, instruction_params; cbn; assumption. }
  destruct gen_token_roots as [Root1 [Root3 RootAll]].
  assert (E1 : run_tokens params [9] (CR 0 prior 0 0) = Some (CR a (cantor 0 prior) 0 0)).
  { change (bind (token_step params (8+1) (CR 0 prior 0 0)) (run_tokens params []) =
      Some (CR a (cantor 0 prior) 0 0)).
    rewrite parameter_token_correct by lia. unfold params,instruction_params. reflexivity. }
  destruct (special_body_block params (constructor_view params r1) 2 1 17 [9]
    (CR 0 prior 0 0) (CR a (cantor 0 prior) 0 0) r1
    (or_intror eq_refl) ltac:(reflexivity) (actual_source_token_block params r1 9 17 Root1) View1 E1)
    as [mid2 [r2 [First2 [Run2 View2]]]].
  assert (E2 : run_tokens params [11] (CR a (cantor 0 prior) 0 0) =
      Some (CR old (cantor a (cantor 0 prior)) 0 0)).
  { change (bind (token_step params (8+3) (CR a (cantor 0 prior) 0 0)) (run_tokens params []) =
      Some (CR old (cantor a (cantor 0 prior)) 0 0)).
    rewrite parameter_token_correct by lia. unfold params,instruction_params. reflexivity. }
  destruct (special_body_block params (constructor_view params r1) 2 2 51 [11]
    (CR a (cantor 0 prior) 0 0) (CR old (cantor a (cantor 0 prior)) 0 0) r2
    (or_intror eq_refl) ltac:(reflexivity) (actual_source_token_block params r1 11 51 Root3) View2 E2)
    as [mid3 [r3 [First3 [Run3 View3]]]].
  assert (E3 : run_tokens params [4] (CR old (cantor a (cantor 0 prior)) 0 0) =
      Some (CR (code_all a old) (cantor 0 prior) 0 0)).
  { cbn [run_tokens token_step bind]. unfold code_all. now rewrite source_binary_correct. }
  destruct (special_body_block params (constructor_view params r1) 2 3 61 [4]
    (CR old (cantor a (cantor 0 prior)) 0 0) (CR (code_all a old) (cantor 0 prior) 0 0) r3
    (or_intror eq_refl) ltac:(reflexivity) (actual_source_token_block params r1 4 61 RootAll) View3 E3)
    as [mid4 [r4 [First4 [Run4 View4]]]].
  destruct View4 as [L4 [T4 [S4 [X4 [Y4 [X0 [Y0 [F4 Params4]]]]]]]].
  cbn [top stack scratch1 scratch2] in T4,S4,X4,Y4.
  assert (C4 : nth_error r4 4=Some 1) by (rewrite (F4 4) by lia; exact C1).
  pose proof (special_body_paths 2 4 680 (or_intror eq_refl) ltac:(reflexivity)) as Pselect.
  destruct (source_select_nonempty (special_body_context 2 4) r4 (code_all a old) 0 prior 1
    Pselect L4 T4 S4 C4 X4 Y4) as [result [mid5 [First5 [Run5 [L5 [T5 [S5 [C5 [X5 [Y5 [F5 Tail5]]]]]]]]]]].
  cbn [selected_top pred] in T5,C5. rewrite special_body_context_return in Run5.
  assert (A4 : nth_error r4 5=Some a) by (rewrite (F4 5) by lia; exact A1).
  assert (B4 : nth_error r4 6=Some b) by (rewrite (F4 6) by lia; exact B1).
  assert (P4 : nth_error r4 7=Some old) by (rewrite (F4 7) by lia; exact P1v).
  assert (A5 : nth_error result 5=Some a) by (rewrite (F5 5) by lia; exact A4).
  assert (B5 : nth_error result 6=Some b) by (rewrite (F5 6) by lia; exact B4).
  assert (P5 : nth_error result 7=Some old) by (rewrite (F5 7) by lia; exact P4).
  assert (AllTail : SourceProgramRuns mid (loop_return main_switch_pc,result)).
  { eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next; [exact First2|].
    eapply source_program_runs_trans; [exact Run2|]. eapply source_program_next; [exact First3|].
    eapply source_program_runs_trans; [exact Run3|]. eapply source_program_next; [exact First4|].
    eapply source_program_runs_trans; [exact Run4|]. eapply source_program_next with (t:=mid5).
    - eapply constructor_unpad_first_step with (pad:=1). unfold special_body_context in First5. exact First5.
    - eapply source_program_runs_trans; [exact Run5|].
      eapply source_program_next; [apply special_body_break; right; reflexivity|constructor]. }
  assert (AllRun : SourceProgramRuns (special_body_cursor 2 0,rs) (loop_return main_switch_pc,result)).
  { eapply source_program_next; [eapply constructor_unpad_first_step with (pad:=1);
      unfold special_body_context in First; exact First|exact AllTail]. }
  destruct (source_runs_zero_suffix _ _ AllRun Len) as [pad [Pad _]].
  exists result,mid. repeat split; try assumption.
  - eapply constructor_unpad_first_step with (pad:=1). unfold special_body_context in First. exact First.
  - unfold outside_gen. intros i I I2 I3 I4 I7 I8 I9.
    rewrite (F5 i) by lia. rewrite (F4 i) by lia. now apply F1.
  - now exists pad.
Qed.
Print Assumptions source_gen_body_nonempty.
