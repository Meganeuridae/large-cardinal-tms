(** Opcode 27: switch countdown, guarded D construction, select, and return. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import Syntax RuntimeControl RuntimeCalls CompilerSyntax CompilerReverse CompilerRegisters ConstructorArithmetic
  ConstructorRegisters ConstructorStreams ProofSearchSyntax.
From Repair Require Import CompilerData SourceExecution CompilerContexts CompilerLoopBase ConstructorControl
  ConstructorCons ConstructorTokens ConstructorFrame SearchSelectBranch SearchSelect GrammarExecutionBlocks GrammarExecutionDispatch
  GrammarExecutionOpcodes GrammarExecutionSelect GrammarExecutionConcrete GrammarExecutionMPTokens GuardEmitter.
Import ListNotations.

Definition guard_parent_pc := switch_pc 27++[true;true].
Definition guard_select_pc := guard_parent_pc++[true;false].
Definition guard_break_pc := guard_parent_pc++[true;true].
Definition guard_result a b := if Nat.eqb a b then 0 else guard_formula_code a b.

Local Transparent source_graph.
Lemma guard_instruction_paths :
  SourcePrefix source_graph source_root (guard_parent_pc++[false]) source_guarded_root /\
  SourcePrefix source_graph source_root guard_select_pc 680 /\
  SourceSelect source_graph source_root guard_break_pc (SBreak 0).
Proof.
  repeat split; try (apply source_prefix_find_sound); try (apply leaf_matches_sound);
    vm_compute; reflexivity.
Qed.
Local Opaque source_graph.

Lemma guard_select_return : loop_return guard_select_pc=guard_break_pc.
Proof.
  unfold guard_select_pc,guard_break_pc.
  replace (guard_parent_pc++[true;false]) with ((guard_parent_pc++[true])++[false])
    by now rewrite <- app_assoc.
  rewrite sequence_left_return. now rewrite <- app_assoc.
Qed.

Lemma guard_break_return rs : SourceProgramStep (guard_break_pc,rs) (loop_return main_switch_pc,rs).
Proof.
  pose proof (proj2 (proj2 guard_instruction_paths)) as Selection.
  destruct (loop_return_spec (switch_pc 27)) as [out [n [Ret Word]]].
  assert (Eq : return_word out=loop_return main_switch_pc).
  { rewrite <- Word. apply switch_loop_return. }
  rewrite <- Eq. unfold guard_break_pc,guard_parent_pc in *.
  replace ((switch_pc 27++[true;true])++[true;true]) with
    ((switch_pc 27++[true;true;true])++[true]) by (repeat rewrite <- app_assoc; reflexivity).
  eapply source_program_break_step with (level:=0) (out:=out) (n:=S(S(S n))).
  - repeat rewrite <- app_assoc in Selection |- *. cbn [app] in Selection |- *. exact Selection.
  - now apply final_follow_break_return.
Qed.

Theorem repaired_guard_instruction rs old prior a b c :
  11<=length rs -> nth_error rs 2=Some 0 -> nth_error rs 3=Some(cantor old prior) ->
  nth_error rs 4=Some 27 -> nth_error rs 5=Some a -> nth_error rs 6=Some b ->
  nth_error rs 7=Some c -> nth_error rs 8=Some 0 -> nth_error rs 9=Some 0 ->
  nth_error rs 10=Some 0 ->
  exists result pad,
    SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result) /\
    11<=length result /\ nth_error result 2=Some(guard_result a b) /\
    nth_error result 3=Some(cantor old prior) /\ nth_error result 4=Some 0 /\
    nth_error result 8=Some 0 /\ nth_error result 9=Some 0 /\ nth_error result 10=Some 0 /\
    nth_error result 0=nth_error rs 0 /\ nth_error result 1=nth_error rs 1 /\
    skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros Len Top Stack Code A B C X Y Z.
  set (params:=instruction_params a b c).
  assert (View : constructor_view params rs (CR 0 (cantor old prior) 0 0) rs).
  { unfold params. eapply mp_initial_constructor_view; eassumption. }
  set (r0:=set_register 4 0 rs++repeat 0 27).
  pose proof (switch_countdown 0 27 rs ltac:(lia) Len Code) as Count.
  unfold switch_pc at 1 in Count. cbn [repeat] in Count. rewrite app_nil_r in Count.
  cbn [Nat.add_0_l] in Count. change (SourceProgramRuns (main_switch_pc,rs) (switch_pc 27,r0)) in Count.
  assert (V0 : nth_error r0 4=Some 0).
  { unfold r0. rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia. }
  assert (Final : set_register 4 1 r0=set_register 4 1 rs++repeat 0 27).
  { unfold r0. rewrite set_register_append by (rewrite set_register_length; lia). now rewrite set_register_twice. }
  pose proof (final_axiom_entry r0 V0) as Entry. rewrite Final in Entry.
  set (rstart:=set_register 4 1 rs++repeat 0 27).
  change (SourceProgramRuns (switch_pc 27,r0) (guard_parent_pc,rstart)) in Entry.
  assert (ViewStart : constructor_view params rstart (CR 0 (cantor old prior) 0 0) rstart).
  { unfold rstart. now apply constructor_view_after_dispatch with (frame:=rs). }
  assert (Zstart : nth_error rstart 10=Some 0).
  { unfold rstart. rewrite nth_after_dispatch by lia. exact Z. }
  destruct (repaired_guarded_distinction_nonempty params rstart (guard_parent_pc++[false]) rstart
    0 (cantor old prior) (proj1 guard_instruction_paths) ViewStart Zstart)
    as [mid [r1 [First [Emit [View1 [Z1 _]]]]]].
  rewrite sequence_left_return in Emit.
  cbn [params instruction_params] in View1.
  change (constructor_view params rstart (CR (guard_result a b) (cantor 0 (cantor old prior)) 0 0) r1) in View1.
  destruct View1 as [L1 [T1 [S1 [X1 [Y1 [X01 [Y01 [Frame1 Params1]]]]]]]].
  cbn [top stack scratch1 scratch2] in T1,S1,X1,Y1.
  assert (Code1 : nth_error r1 4=Some 1).
  { rewrite (Frame1 4) by lia. unfold rstart.
    rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia. }
  destruct (source_select_nonempty guard_select_pc r1 (guard_result a b) 0 (cantor old prior) 1
    (proj1 (proj2 guard_instruction_paths)) L1 T1 S1 Code1 X1 Y1)
    as [result [mid2 [First2 [Tail [L2 [T2 [S2 [C2 [X2 [Y2 [Frame2 _]]]]]]]]]]].
  cbn [selected_top Nat.pred] in T2,C2. rewrite guard_select_return in Tail.
  assert (RunGuard : SourceProgramRuns (guard_parent_pc,rstart) (guard_parent_pc++[true],r1)).
  { eapply source_program_next with (t:=mid); [|exact Emit].
    eapply constructor_unpad_first_step with (pad:=1). cbn [repeat]. exact First. }
  assert (RunSelect : SourceProgramRuns (guard_parent_pc++[true],r1) (guard_break_pc,result)).
  { eapply source_program_next with (t:=mid2); [|exact Tail].
    eapply constructor_unpad_first_step with (pad:=1). unfold guard_select_pc in First2.
    change (SourceProgramStep ((guard_parent_pc++[true])++[false],r1) mid2).
    rewrite <- app_assoc. exact First2. }
  assert (Run : SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,result)).
  { eapply source_program_runs_trans; [exact Count|].
    eapply source_program_runs_trans; [exact Entry|].
    eapply source_program_runs_trans; [exact RunGuard|].
    eapply source_program_runs_trans; [exact RunSelect|].
    eapply source_program_next; [apply guard_break_return|constructor]. }
  destruct (source_runs_zero_suffix _ _ Run Len) as [pad [Suffix _]].
  assert (Z2 : nth_error result 10=Some 0) by (rewrite (Frame2 10) by lia; exact Z1).
  assert (F0 : nth_error result 0=nth_error rs 0).
  { rewrite (Frame2 0) by lia. rewrite (Frame1 0) by lia. unfold rstart. now rewrite nth_after_dispatch by lia. }
  assert (F1 : nth_error result 1=nth_error rs 1).
  { rewrite (Frame2 1) by lia. rewrite (Frame1 1) by lia. unfold rstart. now rewrite nth_after_dispatch by lia. }
  exists result,pad. repeat split; assumption.
Qed.

Print Assumptions guard_instruction_paths.
Print Assumptions guard_break_return.
Print Assumptions repaired_guard_instruction.
