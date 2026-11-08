(** Source control for main's proof-list refill/decrement branch. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls CompilerSyntax CompilerRegisters ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerInstance CompilerExecution CompilerLoopBase CompilerLoops CompilerTrees ConstructorGraph ConstructorPaths ConstructorControl ConstructorUnpair SourceExecution.
Import ListNotations.

Definition tree_search_setup :=
  CTSeq (CTSeq (CTDec 0) (CTBreak 1))
    (CTSeq (tree_while2 1 8 0) (CTSeq (tree_while1 8 1) (CTInc 1))).
Local Transparent source_graph unfold_root.
Lemma source_setup_trees : unfold_root 631 = Some tree_search_setup /\
  unfold_root 626 = Some (tree_while2 1 8 0) /\ unfold_root 628 = Some (tree_while1 8 1).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma source_setup_loop_prefixes : SourcePrefix source_graph 631 [true;false] 626 /\
  SourcePrefix source_graph 631 [true;true;false] 628 /\ SourcePrefix source_graph source_root [false] 631.
Proof. repeat split; apply source_prefix_find_sound; vm_compute; reflexivity. Qed.

Lemma source_setup_leaves ctx : SourcePrefix source_graph source_root ctx 631 ->
  SourceSelect source_graph source_root (ctx++[false;false]) (SDec 0) /\
  SourceSelect source_graph source_root (ctx++[false;true]) (SBreak 1) /\
  SourceSelect source_graph source_root (ctx++[true;true;true]) (SInc 1).
Proof.
  intro P. destruct source_setup_trees as [T _]. repeat split.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact T|].
    unfold tree_search_setup. apply tree_select_left,tree_select_left,tree_select_dec.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact T|].
    unfold tree_search_setup. apply tree_select_left,tree_select_right,tree_select_break.
  - eapply source_select_in_context; [exact P|]. eapply root_unfold_selection; [exact T|].
    unfold tree_search_setup. apply tree_select_right,tree_select_right,tree_select_right,tree_select_inc.
Qed.

Lemma source_setup_break_step pre rs out count :
  SourceSelect source_graph source_root (pre++[true]) (SBreak 1) ->
  break_pc 1 (rev pre++[false]) = Some(out,count) ->
  SourceProgramStep (pre++[true],rs) (return_word out,rs).
Proof.
  intros S E. eapply source_program_step with (n:=0). rewrite app_nil_r.
  eapply source_break; eassumption.
Qed.

Definition setup_frame (before after : list nat) :=
  forall r, r<11 -> r<>0 -> r<>1 -> r<>8 -> nth_error after r = nth_error before r.

Theorem source_setup_pending_nonempty ctx rs n next :
  SourcePrefix source_graph source_root ctx 631 -> 11<=length rs ->
  nth_error rs 0=Some(S n) -> nth_error rs 1=Some next -> nth_error rs 8=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 0=Some n /\ nth_error result 1=Some next /\ nth_error result 8=Some 0 /\
    setup_frame rs result.
Proof.
  intros P L N Next Scratch. destruct (source_setup_leaves ctx P) as [Dec [Break Inc]].
  destruct (loop_return_spec ctx) as [out [count [Ret E]]].
  set (result:=set_register 0 n rs ++ [0]).
  exists result,(ctx++[false;true],result). repeat split.
  - replace (ctx++[false;true]) with (return_word (true::rev (ctx++[false])++[false]))
      by (rewrite constructor_return_word, <- app_assoc; reflexivity).
    unfold result. eapply constructor_step_dec_positive with (pad:=2) (i:=0) (count:=0).
    + change (SourceSelect source_graph source_root (ctx++[false;false]) (SDec 0)). exact Dec.
    + lia.
    + exact N.
    + change (break_pc 0 (rev (ctx++[false;false])++[false]) =
       Some(true::rev (ctx++[false])++[false],0)).
      pose proof (proj1 (constructor_child_return (ctx++[false]) 0)) as C.
      rewrite app_nil_r in C. rewrite <- app_assoc in C. exact C.
  - rewrite E. eapply source_program_next; [|constructor].
    replace (ctx++[false;true]) with ((ctx++[false])++[true]) by (rewrite <- app_assoc; reflexivity).
    eapply source_setup_break_step with (count:=S count).
    + rewrite <- app_assoc. exact Break.
    + now apply constructor_first_test_return.
  - unfold result. rewrite app_length,set_register_length. simpl. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia). apply nth_error_set_same. lia.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Next.
  - unfold result. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    rewrite nth_error_set_other by lia. exact Scratch.
  - unfold setup_frame, result. intros r R R0 R1 R8.
    rewrite nth_error_app1 by (rewrite set_register_length; lia). now rewrite nth_error_set_other by lia.
Qed.

Lemma source_setup_zero_step ctx rs :
  SourcePrefix source_graph source_root ctx 631 -> nth_error rs 0=Some 0 ->
  SourceProgramStep (ctx,rs) (ctx++[true],rs).
Proof.
  intros P N. destruct (source_setup_leaves ctx P) as [Dec _]. rewrite <- constructor_return_word.
  eapply constructor_step_dec_zero with (pad:=2) (i:=0) (count:=1).
  - change (SourceSelect source_graph source_root (ctx++[false;false]) (SDec 0)). exact Dec.
  - lia.
  - exact N.
  - change (break_pc 1 (rev (ctx++[false;false])++[false]) = Some(true::rev ctx++[false],1)).
    rewrite rev_app_distr. reflexivity.
Qed.

Lemma source_setup_increment_step ctx rs next :
  SourcePrefix source_graph source_root ctx 631 -> nth_error rs 1=Some next ->
  SourceProgramStep (ctx++[true;true;true],rs) (loop_return ctx,set_register 1 (S next) rs).
Proof.
  intros P N. destruct (source_setup_leaves ctx P) as [_ [_ Inc]].
  destruct (loop_return_spec ctx) as [out [count [Ret E]]]. rewrite E.
  eapply constructor_step_inc with (pad:=0) (i:=1) (count:=S(S(S count))).
  - rewrite app_nil_r. exact Inc.
  - lia.
  - exact N.
  - rewrite app_nil_r, rev_app_distr. cbn [rev app break_pc]. now rewrite Ret.
Qed.

Theorem source_setup_fresh_nonempty ctx rs next :
  SourcePrefix source_graph source_root ctx 631 -> 11<=length rs ->
  nth_error rs 0=Some 0 -> nth_error rs 1=Some next -> nth_error rs 8=Some 0 ->
  exists result mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid (loop_return ctx,result) /\ 11<=length result /\
    nth_error result 0=Some next /\ nth_error result 1=Some(S next) /\ nth_error result 8=Some 0 /\
    setup_frame rs result.
Proof.
  intros P L N Next Scratch. destruct source_setup_trees as [_ [T1 T2]].
  destruct source_setup_loop_prefixes as [P1 [P2 _]].
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P P1) as Q1.
  pose proof (constructor_source_prefix_concat _ _ _ _ _ _ P P2) as Q2.
  destruct (while2_transfer_nonempty (ctx++[true;false]) 626 rs 1 8 0 next 0 0
    Q1 T1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    L Next Scratch N) as [mid1 [Step1 Run1]].
  cbn [Nat.add_0_l] in Run1.
  set (r1:=set_register 0 next (set_register 8 next (set_register 1 0 rs)) ++ repeat 0 next).
  fold r1 in Run1.
  assert (Ret1 : loop_return (ctx++[true;false])=ctx++[true;true]).
  { replace (ctx++[true;false]) with ((ctx++[true])++[false]) by (rewrite <- app_assoc; reflexivity).
    rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
  rewrite Ret1 in Run1.
  assert (L1 : 11<=length r1) by (unfold r1; rewrite app_length,repeat_length,!set_register_length; lia).
  assert (N1 : nth_error r1 0=Some next).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite !set_register_length. lia. }
  assert (X1 : nth_error r1 8=Some next).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. rewrite set_register_length. lia. }
  assert (V1 : nth_error r1 1=Some 0).
  { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. apply nth_error_set_same. lia. }
  destruct (while1_transfer_nonempty (ctx++[true;true;false]) 628 r1 8 1 next 0
    Q2 T2 ltac:(lia) ltac:(lia) ltac:(lia) L1 X1 V1) as [mid2 [Step2 Run2]].
  cbn [Nat.add_0_l] in Run2.
  set (r2:=set_register 1 next (set_register 8 0 r1) ++ repeat 0 next). fold r2 in Run2.
  assert (Ret2 : loop_return (ctx++[true;true;false])=ctx++[true;true;true]).
  { replace (ctx++[true;true;false]) with ((ctx++[true;true])++[false]) by (rewrite <- app_assoc; reflexivity).
    rewrite constructor_loop_return_false, <- app_assoc. reflexivity. }
  rewrite Ret2 in Run2.
  assert (L2 : 11<=length r2) by (unfold r2; rewrite app_length,repeat_length,!set_register_length; lia).
  assert (N2 : nth_error r2 0=Some next).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. exact N1. }
  assert (X2 : nth_error r2 8=Some 0).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite nth_error_set_other by lia. apply nth_error_set_same. lia. }
  assert (V2 : nth_error r2 1=Some next).
  { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    apply nth_error_set_same. rewrite set_register_length. lia. }
  set (result:=set_register 1 (S next) r2). exists result,(ctx++[true],rs). repeat split.
  - now apply source_setup_zero_step.
  - eapply source_program_next with (t:=mid1).
    + eapply constructor_unpad_first_step with (pad:=1).
      change (SourceProgramStep ((ctx++[true])++[false],rs) mid1). rewrite <- app_assoc. exact Step1.
    + eapply source_program_runs_trans; [exact Run1|]. eapply source_program_next with (t:=mid2).
      * eapply constructor_unpad_first_step with (pad:=1).
        change (SourceProgramStep ((ctx++[true;true])++[false],r1) mid2). rewrite <- app_assoc. exact Step2.
      * eapply source_program_runs_trans; [exact Run2|].
        eapply source_program_next; [eapply source_setup_increment_step; eassumption|constructor].
  - unfold result. rewrite set_register_length. exact L2.
  - unfold result. rewrite nth_error_set_other by lia. exact N2.
  - unfold result. apply nth_error_set_same. lia.
  - unfold result. rewrite nth_error_set_other by lia. exact X2.
  - unfold setup_frame, result. intros r R R0 R1 R8.
    rewrite nth_error_set_other by lia. unfold r2.
    rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    rewrite !nth_error_set_other by lia. unfold r1.
    rewrite nth_error_app1 by (rewrite !set_register_length; lia).
    now rewrite !nth_error_set_other by lia.
Qed.

Print Assumptions source_setup_pending_nonempty.
Print Assumptions source_setup_fresh_nonempty.
