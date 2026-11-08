(** Literal post-dispatch halting test and its source return behavior. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls CompilerSyntax CompilerRegisters CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerInstance CompilerExecution CompilerTrees ConstructorGraph ConstructorControl SourceExecution.
Import ListNotations.

Definition post_cursor := repeat true 19.
Definition tree_post_test := CTSeq (CTDec 2)
  (CTSeq (CTSeq (CTDec 2) (CTSeq (CTSeq (CTInc 2) (CTInc 2)) (CTBreak 1))) CTHalt).
Local Transparent source_graph unfold_root.
Lemma source_post_tree : unfold_root 813 = Some tree_post_test.
Proof. vm_compute. reflexivity. Qed.
Lemma source_post_context : SourcePrefix source_graph source_root post_cursor 813.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Local Opaque source_graph unfold_root.

Lemma source_post_leaves :
  SourceSelect source_graph source_root (post_cursor++[false]) (SDec 2) /\
  SourceSelect source_graph source_root (post_cursor++[true;false;false]) (SDec 2) /\
  SourceSelect source_graph source_root (post_cursor++[true;false;true;false;false]) (SInc 2) /\
  SourceSelect source_graph source_root (post_cursor++[true;false;true;false;true]) (SInc 2) /\
  SourceSelect source_graph source_root (post_cursor++[true;false;true;true]) (SBreak 1) /\
  SourceSelect source_graph source_root (post_cursor++[true;true]) SHalt.
Proof.
  repeat split.
  - eapply source_select_in_context; [exact source_post_context|]. eapply root_unfold_selection; [exact source_post_tree|].
    unfold tree_post_test. apply tree_select_left,tree_select_dec.
  - eapply source_select_in_context; [exact source_post_context|]. eapply root_unfold_selection; [exact source_post_tree|].
    unfold tree_post_test. apply tree_select_right,tree_select_left,tree_select_left,tree_select_dec.
  - eapply source_select_in_context; [exact source_post_context|]. eapply root_unfold_selection; [exact source_post_tree|].
    unfold tree_post_test. apply tree_select_right,tree_select_left,tree_select_right,tree_select_left,tree_select_left,tree_select_inc.
  - eapply source_select_in_context; [exact source_post_context|]. eapply root_unfold_selection; [exact source_post_tree|].
    unfold tree_post_test. apply tree_select_right,tree_select_left,tree_select_right,tree_select_left,tree_select_right,tree_select_inc.
  - eapply source_select_in_context; [exact source_post_context|]. eapply root_unfold_selection; [exact source_post_tree|].
    unfold tree_post_test. apply tree_select_right,tree_select_left,tree_select_right,tree_select_right,tree_select_break.
  - eapply source_select_in_context; [exact source_post_context|]. eapply root_unfold_selection; [exact source_post_tree|].
    unfold tree_post_test. apply tree_select_right,tree_select_right,tree_select_halt.
Qed.

Lemma source_post_zero_step rs : nth_error rs 2=Some 0 -> SourceProgramStep (post_cursor,rs) ([],rs).
Proof.
  intro N. change (SourceProgramStep (post_cursor,rs) (return_word [true],rs)).
  eapply constructor_step_dec_zero with (pad:=1) (i:=2) (count:=20).
  - change (SourceSelect source_graph source_root (post_cursor++[false]) (SDec 2)).
    exact (proj1 source_post_leaves).
  - lia.
  - exact N.
  - unfold post_cursor. vm_compute. reflexivity.
Qed.

Lemma source_post_first_positive rs n : nth_error rs 2=Some(S n) ->
  SourceProgramStep (post_cursor,rs) (post_cursor++[true],set_register 2 n rs++[0]).
Proof.
  intro N. change (SourceProgramStep (post_cursor,rs)
    (return_word (true::rev post_cursor++[false]),set_register 2 n rs++[0])).
  eapply constructor_step_dec_positive with (pad:=1) (i:=2) (count:=0).
  - change (SourceSelect source_graph source_root (post_cursor++[false]) (SDec 2)). exact (proj1 source_post_leaves).
  - lia.
  - exact N.
  - unfold post_cursor. vm_compute. reflexivity.
Qed.

Lemma source_post_second_zero rs : nth_error rs 2=Some 0 ->
  SourceProgramStep (post_cursor++[true],rs) (post_cursor++[true;true],rs).
Proof.
  intro N. change (SourceProgramStep (post_cursor++[true],rs)
    (return_word (true::true::rev post_cursor++[false]),rs)).
  eapply constructor_step_dec_zero with (pad:=2) (i:=2) (count:=1).
  - change (SourceSelect source_graph source_root ((post_cursor++[true])++[false;false]) (SDec 2)).
    rewrite <- app_assoc. exact (proj1 (proj2 source_post_leaves)).
  - lia.
  - exact N.
  - unfold post_cursor. vm_compute. reflexivity.
Qed.

Lemma source_post_second_positive rs n : nth_error rs 2=Some(S n) ->
  SourceProgramStep (post_cursor++[true],rs)
    (post_cursor++[true;false;true],set_register 2 n rs++[0]).
Proof.
  intro N. change (SourceProgramStep (post_cursor++[true],rs)
    (return_word (true::rev (post_cursor++[true;false])++[false]),set_register 2 n rs++[0])).
  eapply constructor_step_dec_positive with (pad:=2) (i:=2) (count:=0).
  - change (SourceSelect source_graph source_root ((post_cursor++[true])++[false;false]) (SDec 2)).
    rewrite <- app_assoc. exact (proj1 (proj2 source_post_leaves)).
  - lia.
  - exact N.
  - unfold post_cursor. vm_compute. reflexivity.
Qed.

Lemma source_post_increment_first rs n : nth_error rs 2=Some n ->
  SourceProgramStep (post_cursor++[true;false;true],rs)
    (post_cursor++[true;false;true;false;true],set_register 2 (S n) rs).
Proof.
  intro N. change (SourceProgramStep (post_cursor++[true;false;true],rs)
    (return_word (true::rev (post_cursor++[true;false;true;false])++[false]),set_register 2 (S n) rs)).
  eapply constructor_step_inc with (pad:=2) (i:=2) (count:=0).
  - change (SourceSelect source_graph source_root ((post_cursor++[true;false;true])++[false;false]) (SInc 2)).
    rewrite <- app_assoc. exact (proj1 (proj2 (proj2 source_post_leaves))).
  - lia.
  - exact N.
  - unfold post_cursor. vm_compute. reflexivity.
Qed.

Lemma source_post_increment_second rs n : nth_error rs 2=Some n ->
  SourceProgramStep (post_cursor++[true;false;true;false;true],rs)
    (post_cursor++[true;false;true;true],set_register 2 (S n) rs).
Proof.
  intro N. change (SourceProgramStep (post_cursor++[true;false;true;false;true],rs)
    (return_word (true::rev (post_cursor++[true;false;true])++[false]),set_register 2 (S n) rs)).
  eapply constructor_step_inc with (pad:=0) (i:=2) (count:=1).
  - rewrite app_nil_r. exact (proj1 (proj2 (proj2 (proj2 source_post_leaves)))).
  - lia.
  - exact N.
  - rewrite app_nil_r. unfold post_cursor. vm_compute. reflexivity.
Qed.

Lemma source_post_break rs : SourceProgramStep (post_cursor++[true;false;true;true],rs) ([],rs).
Proof.
  change (SourceProgramStep (post_cursor++[true;false;true;true],rs) (return_word [true],rs)).
  replace (post_cursor++[true;false;true;true]) with ((post_cursor++[true;false;true])++[true])
    by (rewrite <- app_assoc; reflexivity).
  eapply source_program_step with (n:=0). rewrite app_nil_r.
  eapply source_break with (k:=1) (n:=22).
  - rewrite <- app_assoc. exact (proj1 (proj2 (proj2 (proj2 (proj2 source_post_leaves))))).
  - unfold post_cursor. vm_compute. reflexivity.
Qed.

Theorem source_post_at_least_two_returns rs n : 11<=length rs -> nth_error rs 2=Some(S(S n)) ->
  exists mid, SourceProgramStep (post_cursor,rs) mid /\
    SourceProgramRuns mid ([],rs++[0;0]).
Proof.
  intros L N.
  set (r1:=set_register 2 (S n) rs++[0]).
  set (r2:=set_register 2 n r1++[0]).
  set (r3:=set_register 2 (S n) r2).
  set (r4:=set_register 2 (S(S n)) r3).
  assert (L1 : 11<=length r1) by (unfold r1; rewrite app_length,set_register_length; simpl; lia).
  assert (L2 : 11<=length r2) by (unfold r2; rewrite app_length,set_register_length; simpl; lia).
  assert (L3 : 11<=length r3) by (unfold r3; rewrite set_register_length; exact L2).
  assert (N1 : nth_error r1 2=Some(S n)).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia. }
  assert (N2 : nth_error r2 2=Some n).
  { unfold r2. rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia. }
  assert (N3 : nth_error r3 2=Some(S n)) by (unfold r3; apply nth_error_set_same; lia).
  assert (Final : r4=rs++[0;0]).
  { unfold r4,r3,r2,r1. rewrite set_register_twice.
    rewrite set_register_append by (repeat (rewrite set_register_length || rewrite app_length); simpl; lia).
    rewrite set_register_append by (repeat (rewrite set_register_length || rewrite app_length); simpl; lia).
    rewrite set_register_append by (repeat (rewrite set_register_length || rewrite app_length); simpl; lia).
    rewrite !set_register_twice, (set_register_noop _ _ _ N). now rewrite <- app_assoc. }
  exists (post_cursor++[true],r1). split; [apply source_post_first_positive,N|].
  rewrite <- Final.
  eapply source_program_next; [apply source_post_second_positive,N1|].
  eapply source_program_next; [apply source_post_increment_first,N2|].
  eapply source_program_next; [apply source_post_increment_second,N3|].
  eapply source_program_next; [apply source_post_break|constructor].
Qed.

Theorem source_post_one_terminal_nonempty rs : 11<=length rs -> nth_error rs 2=Some 1 ->
  exists mid, SourceProgramStep (post_cursor,rs) mid /\
    SourceProgramRuns mid (post_cursor++[true;true],set_register 2 0 rs++[0]) /\
    SourceProgramTerminal (post_cursor++[true;true],set_register 2 0 rs++[0]).
Proof.
  intros L N. set (r1:=set_register 2 0 rs++[0]).
  assert (Z : nth_error r1 2=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia. }
  exists (post_cursor++[true],r1). repeat split.
  - apply source_post_first_positive,N.
  - eapply source_program_next; [apply source_post_second_zero,Z|constructor].
  - exists 0. cbn [fst snd repeat]. rewrite app_nil_r.
    exact (proj2 (proj2 (proj2 (proj2 (proj2 source_post_leaves))))).
Qed.

Theorem source_post_one_halts rs : 11<=length rs -> nth_error rs 2=Some 1 ->
  SourceProgramHalts (post_cursor,rs).
Proof.
  intros L N. destruct (source_post_one_terminal_nonempty rs L N) as [mid [First [Run Terminal]]].
  exists (post_cursor++[true;true],set_register 2 0 rs++[0]). split; [|exact Terminal].
  eapply source_program_next; eassumption.
Qed.

Theorem source_post_zero_returns rs : nth_error rs 2=Some 0 ->
  SourceProgramRuns (post_cursor,rs) ([],rs).
Proof. intro H. eapply source_program_next; [now apply source_post_zero_step|constructor]. Qed.

Print Assumptions source_post_one_halts.
Print Assumptions source_post_one_terminal_nonempty.
Print Assumptions source_post_zero_returns.
Print Assumptions source_post_at_least_two_returns.
