(** Source execution of the builder's literal countdown-loop subtrees. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps RuntimeTraces
  CompilerSyntax CompilerData CompilerReverse CompilerContexts CompilerTrees CompilerExecution
  CompilerRegisters CompilerLoopBase ConstructorGraph ConstructorPC ConstructorControl.
Import ListNotations.

Lemma while1_zero_step ctx root rs input output :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while1 input output) ->
  input < 11 -> nth_error rs input = Some 0 ->
  SourceProgramStep (ctx,rs) (loop_return ctx,rs).
Proof.
  intros Prefix Tree I V.
  destruct (while1_context_selections _ _ _ _ Prefix Tree) as [D _].
  destruct (loop_return_spec ctx) as [out [n [E Return]]].
  rewrite Return.
  eapply constructor_step_dec_zero with (pad:=1) (i:=input) (out:=out) (count:=S n).
  - cbn [repeat]. exact D.
  - exact I.
  - exact V.
  - cbn [repeat]. now apply constructor_first_test_return.
Qed.

Lemma while1_zero ctx root rs input output :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while1 input output) ->
  input < 11 -> nth_error rs input = Some 0 ->
  SourceProgramRuns (ctx,rs) (loop_return ctx,rs).
Proof.
  intros. eapply source_program_next; [eapply while1_zero_step; eassumption|constructor].
Qed.

Lemma while1_positive_cycle ctx root rs input output v x :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while1 input output) ->
  input < 11 -> output < 11 -> input <> output -> 11 <= length rs ->
  nth_error rs input = Some(S v) -> nth_error rs output = Some x ->
  SourceProgramRuns (ctx,rs)
    (ctx,set_register output (S x) (set_register input v rs) ++ [0]).
Proof.
  intros Prefix Tree I O Dist Len Vi Vx.
  destruct (while1_context_selections _ _ _ _ Prefix Tree) as [D [Inc Cont]].
  destruct (loop_first_child_return ctx) as [Dret Dword].
  set (r1 := set_register input v rs ++ [0]).
  set (r2 := set_register output (S x) (set_register input v rs) ++ [0]).
  eapply source_program_next with (t:=(ctx++[true],r1)).
  - unfold r1. rewrite <- Dword.
    eapply constructor_step_dec_positive with (pad:=1) (i:=input) (value:=v)
      (out:=true::rev ctx++[false]) (count:=0).
    + cbn [repeat]. exact D.
    + exact I.
    + exact Vi.
    + cbn [repeat]. exact Dret.
  - assert (Vx1 : nth_error r1 output = Some x).
    { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      rewrite nth_error_set_other by exact Dist. exact Vx. }
    assert (IncRet := constructor_child_return (ctx++[true]) 0).
    cbn [repeat app] in IncRet. destruct IncRet as [E W].
    rewrite <- app_assoc in W. cbn [app] in W.
    eapply source_program_next with (t:=(ctx++[true;true],r2)).
    + unfold r2. rewrite <- set_register_append by (rewrite set_register_length; lia).
      rewrite <- W. eapply constructor_step_inc with (pad:=1) (i:=output) (value:=x)
        (out:=true::rev(ctx++[true])++[false]) (count:=0).
      * cbn [repeat]. rewrite <- app_assoc. exact Inc.
      * exact O.
      * exact Vx1.
      * cbn [repeat]. exact E.
    + eapply source_program_next with (t:=(ctx,r2)); [|constructor].
      replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
      replace (ctx++[true;true]) with ((ctx++[true])++[true]) by now rewrite <- app_assoc.
      eapply constructor_step_continue with (k:=1) (out:=rev ctx) (count:=1).
      * now rewrite <- app_assoc.
      * apply loop_continue_return.
Qed.

Theorem while1_transfer ctx root rs input output n x :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while1 input output) ->
  input < 11 -> output < 11 -> input <> output -> 11 <= length rs ->
  nth_error rs input = Some n -> nth_error rs output = Some x ->
  SourceProgramRuns (ctx,rs)
    (loop_return ctx, set_register output (x+n) (set_register input 0 rs) ++ repeat 0 n).
Proof.
  intros Prefix Tree I O Dist.
  revert rs x. induction n as [|n IH]; intros rs x Len Vi Vx.
  - cbn [repeat]. rewrite Nat.add_0_r, app_nil_r.
    rewrite (set_register_noop _ _ _ Vi), (set_register_noop _ _ _ Vx).
    eapply while1_zero; eassumption.
  - set (r1 := set_register output (S x) (set_register input n rs) ++ [0]).
    pose proof (while1_positive_cycle ctx root rs input output n x
      Prefix Tree I O Dist Len Vi Vx) as Cycle.
    change (SourceProgramRuns (ctx,rs) (ctx,r1)) in Cycle.
    assert (Len1 : 11 <= length r1).
    { unfold r1. rewrite app_length, !set_register_length. simpl. lia. }
    assert (Vi1 : nth_error r1 input = Some n).
    { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_other by congruence. apply nth_error_set_same. lia. }
    assert (Vx1 : nth_error r1 output = Some (S x)).
    { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      apply nth_error_set_same. rewrite set_register_length. lia. }
    pose proof (IH r1 (S x) Len1 Vi1 Vx1) as Tail.
    assert (Final :
      set_register output (S x+n) (set_register input 0 r1) ++ repeat 0 n =
      set_register output (x+S n) (set_register input 0 rs) ++ repeat 0 (S n)).
    { unfold r1.
      rewrite set_register_append by (rewrite !set_register_length; lia).
      rewrite set_register_commute by exact Dist.
      rewrite set_register_twice.
      rewrite set_register_append by (rewrite !set_register_length; lia).
      rewrite set_register_twice.
      replace (S x+n) with (x+S n) by lia.
      cbn [repeat]. now rewrite <- app_assoc. }
    rewrite Final in Tail. eapply source_program_runs_trans; eassumption.
Qed.

Lemma source_runs_nonempty_when_distinct a b : SourceProgramRuns a b -> a <> b ->
  exists mid, SourceProgramStep a mid /\ SourceProgramRuns mid b.
Proof.
  intros Runs Ne. destruct Runs as [s|s t u Step Tail]; [contradiction|].
  exists t. auto.
Qed.

Theorem while1_transfer_nonempty ctx root rs input output n x :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while1 input output) ->
  input < 11 -> output < 11 -> input <> output -> 11 <= length rs ->
  nth_error rs input = Some n -> nth_error rs output = Some x ->
  exists mid, SourceProgramStep (ctx,rs) mid /\
    SourceProgramRuns mid
      (loop_return ctx, set_register output (x+n) (set_register input 0 rs) ++ repeat 0 n).
Proof.
  intros Prefix Tree I O Dist Len Vi Vx. destruct n as [|n].
  - cbn [repeat]. rewrite Nat.add_0_r, app_nil_r.
    rewrite (set_register_noop _ _ _ Vi), (set_register_noop _ _ _ Vx).
    exists (loop_return ctx,rs). split; [eapply while1_zero_step; eassumption|constructor].
  - eapply source_runs_nonempty_when_distinct.
    + eapply while1_transfer; eassumption.
    + intro E. apply (f_equal (fun s => length (snd s))) in E. cbn [snd] in E.
      rewrite app_length, repeat_length, !set_register_length in E. lia.
Qed.

Lemma while2_zero_step ctx root rs input output1 output2 :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while2 input output1 output2) ->
  input < 11 -> nth_error rs input = Some 0 ->
  SourceProgramStep (ctx,rs) (loop_return ctx,rs).
Proof.
  intros Prefix Tree I V.
  destruct (while2_context_selections _ _ _ _ _ Prefix Tree) as [D _].
  destruct (loop_return_spec ctx) as [out [n [E Return]]].
  rewrite Return. eapply constructor_step_dec_zero with (pad:=1) (i:=input) (out:=out) (count:=S n).
  - cbn [repeat]. exact D.
  - exact I.
  - exact V.
  - cbn [repeat]. now apply constructor_first_test_return.
Qed.

Lemma while2_first_inc_return ctx :
  break_pc 0 (rev (ctx++[true;false;false])++[false]) =
    Some(true::rev(ctx++[true;false])++[false],0) /\
  return_word (true::rev(ctx++[true;false])++[false]) = ctx++[true;false;true].
Proof.
  pose proof (constructor_child_return (ctx++[true;false]) 0) as [E W].
  cbn [repeat app] in E, W. rewrite <- app_assoc in E, W. cbn [app] in E, W. auto.
Qed.
Lemma while2_second_inc_return ctx :
  break_pc 0 (rev (ctx++[true;false;true])++[false]) =
    Some(true::rev(ctx++[true])++[false],1) /\
  return_word (true::rev(ctx++[true])++[false]) = ctx++[true;true].
Proof.
  pose proof (constructor_child_return (ctx++[true]) 1) as [E W].
  cbn [repeat app] in E, W. rewrite <- app_assoc in E, W. cbn [app] in E, W. auto.
Qed.

Lemma while2_positive_cycle ctx root rs input output1 output2 v x y :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while2 input output1 output2) ->
  input < 11 -> output1 < 11 -> output2 < 11 ->
  input <> output1 -> input <> output2 -> output1 <> output2 -> 11 <= length rs ->
  nth_error rs input = Some(S v) -> nth_error rs output1 = Some x -> nth_error rs output2 = Some y ->
  SourceProgramRuns (ctx,rs)
    (ctx,set_register output2 (S y) (set_register output1 (S x) (set_register input v rs)) ++ [0]).
Proof.
  intros Prefix Tree I O1 O2 D1 D2 D12 Len Vi Vx Vy.
  destruct (while2_context_selections _ _ _ _ _ Prefix Tree) as [D [Inc1 [Inc2 Cont]]].
  destruct (loop_first_child_return ctx) as [Dret Dword].
  destruct (while2_first_inc_return ctx) as [I1ret I1word].
  destruct (while2_second_inc_return ctx) as [I2ret I2word].
  set (r1 := set_register input v rs ++ [0]).
  set (r2 := set_register output1 (S x) (set_register input v rs) ++ [0]).
  set (r3 := set_register output2 (S y) (set_register output1 (S x) (set_register input v rs)) ++ [0]).
  eapply source_program_next with (t:=(ctx++[true],r1)).
  - unfold r1. rewrite <- Dword.
    eapply constructor_step_dec_positive with (pad:=1) (i:=input) (value:=v)
      (out:=true::rev ctx++[false]) (count:=0).
    + cbn [repeat]. exact D.
    + exact I.
    + exact Vi.
    + cbn [repeat]. exact Dret.
  - assert (Vx1 : nth_error r1 output1 = Some x).
    { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      rewrite nth_error_set_other by exact D1. exact Vx. }
    eapply source_program_next with (t:=(ctx++[true;false;true],r2)).
    + unfold r2. rewrite <- set_register_append by (rewrite set_register_length; lia).
      rewrite <- I1word. eapply constructor_step_inc with (pad:=2) (i:=output1) (value:=x)
        (out:=true::rev(ctx++[true;false])++[false]) (count:=0).
      * cbn [repeat]. rewrite <- app_assoc. exact Inc1.
      * exact O1.
      * exact Vx1.
      * cbn [repeat]. rewrite <- app_assoc. exact I1ret.
    + assert (Vy2 : nth_error r2 output2 = Some y).
      { unfold r2. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
        rewrite nth_error_set_other by exact D12. rewrite nth_error_set_other by exact D2. exact Vy. }
      eapply source_program_next with (t:=(ctx++[true;true],r3)).
      * unfold r3. rewrite <- set_register_append by (rewrite !set_register_length; lia).
        rewrite <- I2word. eapply constructor_step_inc with (pad:=0) (i:=output2) (value:=y)
          (out:=true::rev(ctx++[true])++[false]) (count:=1).
        -- cbn [repeat]. now rewrite app_nil_r.
        -- exact O2.
        -- exact Vy2.
        -- cbn [repeat]. now rewrite app_nil_r.
      * eapply source_program_next with (t:=(ctx,r3)); [|constructor].
        replace ctx with (rev (rev ctx)) at 2 by apply rev_involutive.
        replace (ctx++[true;true]) with ((ctx++[true])++[true]) by now rewrite <- app_assoc.
        eapply constructor_step_continue with (k:=1) (out:=rev ctx) (count:=1).
        -- now rewrite <- app_assoc.
        -- apply loop_continue_return.
Qed.

Theorem while2_transfer ctx root rs input output1 output2 n x y :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while2 input output1 output2) ->
  input < 11 -> output1 < 11 -> output2 < 11 ->
  input <> output1 -> input <> output2 -> output1 <> output2 -> 11 <= length rs ->
  nth_error rs input = Some n -> nth_error rs output1 = Some x -> nth_error rs output2 = Some y ->
  SourceProgramRuns (ctx,rs)
    (loop_return ctx,
      set_register output2 (y+n) (set_register output1 (x+n) (set_register input 0 rs)) ++ repeat 0 n).
Proof.
  intros Prefix Tree I O1 O2 D1 D2 D12.
  revert rs x y. induction n as [|n IH]; intros rs x y Len Vi Vx Vy.
  - cbn [repeat]. rewrite !Nat.add_0_r, app_nil_r.
    rewrite (set_register_noop _ _ _ Vi), (set_register_noop _ _ _ Vx), (set_register_noop _ _ _ Vy).
    eapply source_program_next; [eapply while2_zero_step; eassumption|constructor].
  - set (r1 := set_register output2 (S y) (set_register output1 (S x) (set_register input n rs)) ++ [0]).
    pose proof (while2_positive_cycle ctx root rs input output1 output2 n x y
      Prefix Tree I O1 O2 D1 D2 D12 Len Vi Vx Vy) as Cycle.
    change (SourceProgramRuns (ctx,rs) (ctx,r1)) in Cycle.
    assert (Len1 : 11 <= length r1).
    { unfold r1. rewrite app_length, !set_register_length. simpl. lia. }
    assert (Vi1 : nth_error r1 input = Some n).
    { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_other by congruence. rewrite nth_error_set_other by congruence.
      apply nth_error_set_same. lia. }
    assert (Vx1 : nth_error r1 output1 = Some (S x)).
    { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      rewrite nth_error_set_other by congruence. apply nth_error_set_same.
      rewrite set_register_length. lia. }
    assert (Vy1 : nth_error r1 output2 = Some (S y)).
    { unfold r1. rewrite nth_error_app1 by (rewrite !set_register_length; lia).
      apply nth_error_set_same. rewrite !set_register_length. lia. }
    pose proof (IH r1 (S x) (S y) Len1 Vi1 Vx1 Vy1) as Tail.
    assert (Final :
      set_register output2 (S y+n) (set_register output1 (S x+n) (set_register input 0 r1)) ++ repeat 0 n =
      set_register output2 (y+S n) (set_register output1 (x+S n) (set_register input 0 rs)) ++ repeat 0 (S n)).
    { unfold r1.
      rewrite set_register_append by (rewrite !set_register_length; lia).
      rewrite (set_register_commute input output2 0 (S y)) by exact D2.
      rewrite (set_register_commute input output1 0 (S x)) by exact D1.
      rewrite set_register_twice.
      rewrite set_register_append by (rewrite !set_register_length; lia).
      rewrite (set_register_commute output1 output2 (S x+n) (S y)) by exact D12.
      rewrite set_register_twice.
      rewrite set_register_append by (rewrite !set_register_length; lia).
      rewrite set_register_twice.
      replace (S x+n) with (x+S n) by lia.
      replace (S y+n) with (y+S n) by lia.
      cbn [repeat]. now rewrite <- app_assoc. }
    rewrite Final in Tail. eapply source_program_runs_trans; eassumption.
Qed.

Theorem while2_transfer_nonempty ctx root rs input output1 output2 n x y :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some(tree_while2 input output1 output2) ->
  input < 11 -> output1 < 11 -> output2 < 11 ->
  input <> output1 -> input <> output2 -> output1 <> output2 -> 11 <= length rs ->
  nth_error rs input = Some n -> nth_error rs output1 = Some x -> nth_error rs output2 = Some y ->
  exists mid, SourceProgramStep (ctx,rs) mid /\ SourceProgramRuns mid
    (loop_return ctx,
      set_register output2 (y+n) (set_register output1 (x+n) (set_register input 0 rs)) ++ repeat 0 n).
Proof.
  intros Prefix Tree I O1 O2 D1 D2 D12 Len Vi Vx Vy. destruct n as [|n].
  - cbn [repeat]. rewrite !Nat.add_0_r, app_nil_r.
    rewrite (set_register_noop _ _ _ Vi), (set_register_noop _ _ _ Vx), (set_register_noop _ _ _ Vy).
    exists (loop_return ctx,rs). split; [eapply while2_zero_step; eassumption|constructor].
  - eapply source_runs_nonempty_when_distinct.
    + eapply while2_transfer; eassumption.
    + intro E. apply (f_equal (fun s => length (snd s))) in E. cbn [snd] in E.
      rewrite app_length, repeat_length, !set_register_length in E. lia.
Qed.

Print Assumptions while1_zero.
Print Assumptions while1_positive_cycle.
Print Assumptions while1_transfer.
Print Assumptions while1_transfer_nonempty.
Print Assumptions while2_transfer.
Print Assumptions while2_transfer_nonempty.
