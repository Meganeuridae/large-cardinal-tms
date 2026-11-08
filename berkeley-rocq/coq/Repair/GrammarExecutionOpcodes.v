(** The other branches of the literal main opcode switch. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeTraces CompilerSyntax CompilerRegisters ConstructorPC.
From Repair Require Import CompilerData CompilerInstance CompilerExecution CompilerLoopBase ConstructorControl GrammarExecutionDispatch SourceExecution.
Import ListNotations.

Lemma special_opcode_paths_certificate :
  andb (leaf_matches (switch_pc 0++[false;true]) (SBreak 1))
  (andb (leaf_matches (switch_pc 1++[false;true;false]) (SInc 4))
  (andb (leaf_matches (switch_pc 2++[false;true;false]) (SInc 4))
        (leaf_matches (switch_pc 27++[false;true]) (SBreak 1)))) = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque source_graph.

Lemma default_break_path :
  SourceSelect source_graph source_root (switch_pc 0++[false;true]) (SBreak 1).
Proof.
  pose proof special_opcode_paths_certificate as C. apply andb_true_iff in C as [C _].
  now apply leaf_matches_sound.
Qed.

Lemma regular_body_inc_path j : 1 <= j -> j < 27 ->
  SourceSelect source_graph source_root (switch_pc j++[false;true;false]) (SInc 4).
Proof.
  intros Lo Hi. destruct (le_lt_dec 3 j) as [B|B]; [now apply regular_axiom_inc_path|].
  assert (j=1 \/ j=2) by lia. destruct H as [A|A]; subst j.
  - pose proof special_opcode_paths_certificate as C. apply andb_true_iff in C as [_ C].
    apply andb_true_iff in C as [C _]. now apply leaf_matches_sound.
  - pose proof special_opcode_paths_certificate as C. apply andb_true_iff in C as [_ C].
    apply andb_true_iff in C as [_ C]. apply andb_true_iff in C as [C _].
    now apply leaf_matches_sound.
Qed.

Lemma final_skip_break_path :
  SourceSelect source_graph source_root (switch_pc 27++[false;true]) (SBreak 1).
Proof.
  pose proof special_opcode_paths_certificate as C. apply andb_true_iff in C as [_ C].
  apply andb_true_iff in C as [_ C]. apply andb_true_iff in C as [_ C].
  now apply leaf_matches_sound.
Qed.

Lemma regular_body_entry j rs : 1 <= j -> j < 27 -> nth_error rs 4 = Some 0 ->
  SourceProgramRuns (switch_pc j,rs) (switch_pc j++[false;true;true],set_register 4 1 rs).
Proof.
  intros Lo Hi V. destruct (regular_skip_paths j Hi) as [D _].
  pose proof (regular_body_inc_path j Lo Hi) as I.
  destruct (regular_case_zero_return (switch_pc j)) as [Dret Dword].
  destruct (regular_case_inc_return (switch_pc j)) as [Iret Iword].
  eapply source_program_next with (t:=(switch_pc j++[false;true],rs)).
  - rewrite <- Dword. eapply constructor_step_dec_zero with (pad:=3) (i:=4)
      (out:=true::false::rev(switch_pc j)++[false]) (count:=1).
    + cbn [repeat]. exact D.
    + lia.
    + exact V.
    + cbn [repeat]. exact Dret.
  - eapply source_program_next with (t:=(switch_pc j++[false;true;true],set_register 4 1 rs));
      [|constructor].
    rewrite <- Iword. eapply constructor_step_inc with (pad:=1) (i:=4) (value:=0)
      (out:=true::rev(switch_pc j++[false;true])++[false]) (count:=0).
    + cbn [repeat]. rewrite <- app_assoc. exact I.
    + lia.
    + exact V.
    + cbn [repeat]. rewrite <- app_assoc. exact Iret.
Qed.

Theorem switch_special_opcode_entry j rs : 1 <= j -> j <= 2 -> 11 <= length rs ->
  nth_error rs 4 = Some j ->
  SourceProgramRuns (main_switch_pc,rs)
    (switch_pc j++[false;true;true],set_register 4 1 rs ++ repeat 0 j).
Proof.
  intros Lo Hi Len V. set (r0 := set_register 4 0 rs ++ repeat 0 j).
  pose proof (switch_countdown 0 j rs ltac:(lia) Len V) as Count.
  unfold switch_pc at 1 in Count. cbn [repeat] in Count. rewrite app_nil_r in Count.
  cbn [Nat.add_0_l] in Count.
  change (SourceProgramRuns (main_switch_pc,rs) (switch_pc j,r0)) in Count.
  assert (V0 : nth_error r0 4 = Some 0).
  { unfold r0. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  assert (Final : set_register 4 1 r0 = set_register 4 1 rs ++ repeat 0 j).
  { unfold r0. rewrite set_register_append by (rewrite set_register_length; lia).
    now rewrite set_register_twice. }
  pose proof (regular_body_entry j r0 Lo ltac:(lia) V0) as Entry.
  rewrite Final in Entry. eapply source_program_runs_trans; eassumption.
Qed.

Theorem switch_default_opcode rs : nth_error rs 4 = Some 0 ->
  SourceProgramRuns (main_switch_pc,rs) (loop_return main_switch_pc,rs).
Proof.
  intro V. destruct (regular_skip_paths 0 ltac:(lia)) as [D _].
  pose proof default_break_path as B.
  destruct (regular_case_zero_return (switch_pc 0)) as [Dret Dword].
  destruct (loop_return_spec (switch_pc 0)) as [out [n [Ret Word]]].
  assert (Z : switch_pc 0 = main_switch_pc).
  { unfold switch_pc. cbn [repeat]. now rewrite app_nil_r. }
  rewrite Z in D, B, Dret, Dword, Ret, Word.
  eapply source_program_next with (t:=(main_switch_pc++[false;true],rs)).
  - rewrite <- Dword. eapply constructor_step_dec_zero with (pad:=3) (i:=4)
      (out:=true::false::rev main_switch_pc++[false]) (count:=1).
    + cbn [repeat]. exact D.
    + lia.
    + exact V.
    + cbn [repeat]. exact Dret.
  - eapply source_program_next with (t:=(loop_return main_switch_pc,rs)); [|constructor].
    eapply source_program_step with (n:=0). rewrite app_nil_r, Word.
    replace (main_switch_pc++[false;true]) with ((main_switch_pc++[false])++[true])
      by now rewrite <- app_assoc.
    eapply source_break with (k:=1) (out:=out) (n:=S n).
    + now rewrite <- app_assoc.
    + now apply constructor_first_test_return.
Qed.

Theorem switch_countdown_partial j n rest rs : j+n <= 27 -> 11 <= length rs ->
  nth_error rs 4 = Some (n+rest) ->
  SourceProgramRuns (switch_pc j,rs)
    (switch_pc (j+n),set_register 4 rest rs ++ repeat 0 n).
Proof.
  revert j rs. induction n as [|n IH]; intros j rs Bound Len V.
  - cbn [Nat.add repeat] in V |- *. rewrite Nat.add_0_r, app_nil_r, (set_register_noop _ _ _ V).
    constructor.
  - set (r1 := set_register 4 (n+rest) rs ++ [0]).
    pose proof (switch_skip_positive j rs (n+rest) ltac:(lia) Len V) as Cycle.
    change (SourceProgramRuns (switch_pc j,rs) (switch_pc (S j),r1)) in Cycle.
    assert (Len1 : 11 <= length r1).
    { unfold r1. rewrite app_length, set_register_length. simpl. lia. }
    assert (V1 : nth_error r1 4 = Some (n+rest)).
    { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      apply nth_error_set_same. lia. }
    pose proof (IH (S j) r1 ltac:(lia) Len1 V1) as Tail.
    replace (S j+n) with (j+S n) in Tail by lia.
    assert (Final : set_register 4 rest r1 ++ repeat 0 n =
      set_register 4 rest rs ++ repeat 0 (S n)).
    { unfold r1. rewrite set_register_append by (rewrite set_register_length; lia).
      rewrite set_register_twice. cbn [repeat]. now rewrite <- app_assoc. }
    rewrite Final in Tail. eapply source_program_runs_trans; eassumption.
Qed.

Lemma final_positive_dec_return ctx :
  break_pc 0 (rev(ctx++[false;false])++[false]) =
    Some(true::rev(ctx++[false])++[false],0) /\
  return_word (true::rev(ctx++[false])++[false]) = ctx++[false;true].
Proof.
  pose proof (constructor_child_return (ctx++[false]) 0) as [E W].
  cbn [repeat app] in E,W. rewrite <- app_assoc in E,W. cbn [app] in E,W. auto.
Qed.
Lemma final_switch_loop_return : loop_return (switch_pc 27) = loop_return main_switch_pc.
Proof. vm_compute. reflexivity. Qed.

Lemma final_case_positive rs v : 11 <= length rs -> nth_error rs 4 = Some(S v) ->
  SourceProgramRuns (switch_pc 27,rs)
    (loop_return main_switch_pc,set_register 4 v rs ++ [0]).
Proof.
  intros Len V. destruct final_axiom_paths as [D _]. pose proof final_skip_break_path as B.
  destruct (final_positive_dec_return (switch_pc 27)) as [Dret Dword].
  destruct (loop_return_spec (switch_pc 27)) as [out [n [Ret Word]]].
  eapply source_program_next with
    (t:=(switch_pc 27++[false;true],set_register 4 v rs ++ [0])).
  - rewrite <- Dword. eapply constructor_step_dec_positive with (pad:=2) (i:=4) (value:=v)
      (out:=true::rev(switch_pc 27++[false])++[false]) (count:=0).
    + cbn [repeat]. exact D.
    + lia.
    + exact V.
    + cbn [repeat]. exact Dret.
  - eapply source_program_next with
      (t:=(loop_return main_switch_pc,set_register 4 v rs ++ [0])); [|constructor].
    eapply source_program_step with (n:=0). rewrite app_nil_r.
    rewrite <- final_switch_loop_return, Word.
    replace (switch_pc 27++[false;true]) with ((switch_pc 27++[false])++[true])
      by now rewrite <- app_assoc.
    eapply source_break with (k:=1) (out:=out) (n:=S n).
    + now rewrite <- app_assoc.
    + now apply constructor_first_test_return.
Qed.

Theorem switch_out_of_range k rs : 11 <= length rs -> nth_error rs 4 = Some (28+k) ->
  SourceProgramRuns (main_switch_pc,rs)
    (loop_return main_switch_pc,set_register 4 k rs ++ repeat 0 28).
Proof.
  intros Len V. set (r0 := set_register 4 (S k) rs ++ repeat 0 27).
  pose proof (switch_countdown_partial 0 27 (S k) rs ltac:(lia) Len ltac:(replace (27+S k) with (28+k) by lia; exact V)) as Count.
  unfold switch_pc at 1 in Count. cbn [repeat] in Count. rewrite app_nil_r in Count.
  cbn [Nat.add_0_l] in Count.
  change (SourceProgramRuns (main_switch_pc,rs) (switch_pc 27,r0)) in Count.
  assert (Len0 : 11 <= length r0).
  { unfold r0. rewrite app_length, set_register_length, repeat_length. lia. }
  assert (V0 : nth_error r0 4 = Some(S k)).
  { unfold r0. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  pose proof (final_case_positive r0 k Len0 V0) as Last.
  assert (Final : set_register 4 k r0 ++ [0] = set_register 4 k rs ++ repeat 0 28).
  { unfold r0. rewrite set_register_append by (rewrite set_register_length; lia).
    rewrite set_register_twice. rewrite <- app_assoc.
    replace (repeat 0 28) with (repeat 0 27 ++ [0]) by reflexivity. reflexivity. }
  rewrite Final in Last. eapply source_program_runs_trans; eassumption.
Qed.

Print Assumptions switch_special_opcode_entry.
Print Assumptions switch_default_opcode.
Print Assumptions switch_countdown_partial.
Print Assumptions switch_out_of_range.
