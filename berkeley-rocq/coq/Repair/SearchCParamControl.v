(** Checked source contexts and primitive control for cparam's two concrete
    parameter registers.  The source root 648 is their shared conditional. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps CompilerSyntax CompilerRegisters ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerInstance CompilerExecution CompilerLoopBase CompilerLoops ConstructorGraph ConstructorPaths ConstructorControl ConstructorPush ConstructorTokensV SearchPrimitivesDrain SourceExecution.
Import ListNotations.

Record cparam_layout root p clear copy : Prop := {
  cparam_inner_prefix : SourcePrefix source_graph root [false] 648;
  cparam_clear_prefix : SourcePrefix source_graph root [true;false] clear;
  cparam_copy_prefix : SourcePrefix source_graph root [true;true] copy;
  cparam_clear_tree : unfold_root clear = Some(tree_drain p);
  cparam_copy_tree : unfold_root copy = Some(tree_while1 8 p)
}.
Local Transparent source_graph unfold_root.
Lemma cparam_layout_2 : cparam_layout 652 6 634 20.
Proof. constructor; try (apply source_prefix_find_sound; vm_compute; reflexivity); vm_compute; reflexivity. Qed.
Lemma cparam_layout_3 : cparam_layout 650 7 635 50.
Proof. constructor; try (apply source_prefix_find_sound; vm_compute; reflexivity); vm_compute; reflexivity. Qed.

Lemma cparam_inner_first : SourceSelect source_graph 648 [false;false] (SDec 4).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_break : SourceSelect source_graph 648 [true] (SBreak 1).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_second : SourceSelect source_graph 648 [false;true;false;false] (SDec 4).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_restore_one : SourceSelect source_graph 648 [false;true;true;false;false] (SInc 4).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_unpair : SourcePrefix source_graph 648 [false;true;true;false;true;false] 29.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_stack_restore : SourcePrefix source_graph 648 [false;true;true;false;true;true] 30.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_break_test : SourceSelect source_graph 648 [false;true;true;true] (SBreak 1).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_inc_first : SourceSelect source_graph 648 [false;true;false;true;false;false] (SInc 4).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_inc_second : SourceSelect source_graph 648 [false;true;false;true;false;true] (SInc 4).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.
Lemma cparam_inner_break_inner : SourceSelect source_graph 648 [false;true;false;true;true] (SBreak 1).
Proof. apply source_find_leaf_sound. vm_compute. reflexivity. Qed.

Lemma cparam_step_break pre rs k out count :
  SourceSelect source_graph source_root (pre++[true]) (SBreak k) ->
  break_pc k (rev pre++[false])=Some(out,count) ->
  SourceProgramStep (pre++[true],rs) (return_word out,rs).
Proof.
  intros P E. eapply source_program_step with (n:=0). rewrite app_nil_r.
  eapply source_break; eassumption.
Qed.
Lemma cparam_first_zero_return ctx :
  break_pc 1 (rev(ctx++[false;false])++[false]) = Some(true::rev ctx++[false],1) /\
  return_word (true::rev ctx++[false]) = ctx++[true].
Proof. split; [repeat rewrite rev_app_distr; reflexivity|apply constructor_return_word]. Qed.
Lemma cparam_first_positive_return ctx :
  break_pc 0 (rev(ctx++[false;false])++[false]) = Some(true::rev(ctx++[false])++[false],0) /\
  return_word (true::rev(ctx++[false])++[false]) = ctx++[false;true].
Proof. split; [repeat rewrite rev_app_distr; reflexivity|rewrite constructor_return_word,<-app_assoc; reflexivity]. Qed.
Lemma cparam_second_zero_return ctx :
  break_pc 1 (rev(ctx++[false;true;false;false])++[false]) =
    Some(true::rev(ctx++[false;true])++[false],1) /\
  return_word (true::rev(ctx++[false;true])++[false]) = ctx++[false;true;true].
Proof. split; [repeat rewrite rev_app_distr; reflexivity|rewrite constructor_return_word,<-app_assoc; reflexivity]. Qed.
Lemma cparam_second_positive_return ctx :
  break_pc 0 (rev(ctx++[false;true;false;false])++[false]) =
    Some(true::rev(ctx++[false;true;false])++[false],0) /\
  return_word (true::rev(ctx++[false;true;false])++[false]) = ctx++[false;true;false;true].
Proof. split; [repeat rewrite rev_app_distr; reflexivity|rewrite constructor_return_word,<-app_assoc; reflexivity]. Qed.

Lemma cparam_inner_first_zero ctx rs : SourcePrefix source_graph source_root ctx 648 ->
  nth_error rs 4=Some 0 -> SourceProgramStep (ctx,rs) (ctx++[true],rs).
Proof.
  intros P N. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_first) as Sel.
  destruct (cparam_first_zero_return ctx) as [E W]. rewrite <-W.
  eapply constructor_step_dec_zero with (pad:=2) (i:=4) (count:=1).
  - exact Sel.
  - lia.
  - exact N.
  - exact E.
Qed.
Lemma cparam_inner_first_positive ctx rs n : SourcePrefix source_graph source_root ctx 648 ->
  nth_error rs 4=Some(S n) ->
  SourceProgramStep (ctx,rs) (ctx++[false;true],set_register 4 n rs++[0]).
Proof.
  intros P N. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_first) as Sel.
  destruct (cparam_first_positive_return ctx) as [E W]. rewrite <-W.
  eapply constructor_step_dec_positive with (pad:=2) (i:=4) (value:=n) (count:=0).
  - exact Sel.
  - lia.
  - exact N.
  - exact E.
Qed.

Lemma cparam_inner_second_zero ctx rs : SourcePrefix source_graph source_root ctx 648 ->
  nth_error rs 4=Some 0 ->
  SourceProgramStep (ctx++[false;true],rs) (ctx++[false;true;true],rs).
Proof.
  intros P N. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_second) as Sel.
  destruct (cparam_second_zero_return ctx) as [E W]. rewrite <-W.
  eapply constructor_step_dec_zero with (pad:=2) (i:=4) (count:=1).
  - change (SourceSelect source_graph source_root ((ctx++[false;true])++[false;false]) (SDec 4)).
    now rewrite <-app_assoc.
  - lia.
  - exact N.
  - change (break_pc 1 (rev((ctx++[false;true])++[false;false])++[false]) =
       Some(true::rev(ctx++[false;true])++[false],1)).
    rewrite <-app_assoc. exact E.
Qed.
Lemma cparam_inner_second_positive ctx rs n : SourcePrefix source_graph source_root ctx 648 ->
  nth_error rs 4=Some(S n) ->
  SourceProgramStep (ctx++[false;true],rs)
    (ctx++[false;true;false;true],set_register 4 n rs++[0]).
Proof.
  intros P N. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_second) as Sel.
  destruct (cparam_second_positive_return ctx) as [E W]. rewrite <-W.
  eapply constructor_step_dec_positive with (pad:=2) (i:=4) (value:=n) (count:=0).
  - change (SourceSelect source_graph source_root ((ctx++[false;true])++[false;false]) (SDec 4)).
    now rewrite <-app_assoc.
  - lia.
  - exact N.
  - change (break_pc 0 (rev((ctx++[false;true])++[false;false])++[false]) =
       Some(true::rev(ctx++[false;true;false])++[false],0)).
    rewrite <-app_assoc. exact E.
Qed.
Print Assumptions cparam_layout_2.
Print Assumptions cparam_layout_3.
Print Assumptions cparam_inner_first_zero.
Print Assumptions cparam_inner_second_positive.

Lemma cparam_increment_padded pc pad prefix k rs n :
  pc++repeat false pad = prefix++[false]++repeat true k ->
  SourceSelect source_graph source_root (pc++repeat false pad) (SInc 4) ->
  nth_error rs 4=Some n ->
  SourceProgramStep (pc,rs) (prefix++[true],set_register 4 (S n) rs).
Proof.
  intros P Sel N. destruct (constructor_child_return prefix k) as [E W]. rewrite <-W.
  eapply constructor_step_inc with (pad:=pad) (i:=4) (value:=n) (count:=k).
  - exact Sel.
  - lia.
  - exact N.
  - now rewrite P.
Qed.

Lemma cparam_break_inner_return ctx :
  break_pc 1 (rev(ctx++[false;true;false;true])++[false]) =
    Some(true::rev ctx++[false],3) /\
  return_word (true::rev ctx++[false]) = ctx++[true].
Proof. split; [repeat rewrite rev_app_distr; reflexivity|apply constructor_return_word]. Qed.
Lemma cparam_break_test_return ctx out n : break_pc 0 (rev ctx++[false])=Some(out,n) ->
  break_pc 1 (rev(ctx++[false;true;true])++[false])=Some(out,S(S(S n))).
Proof. intro E. rewrite rev_app_distr. cbn [rev app break_pc]. now rewrite E. Qed.

Lemma cparam_inner_break_inner_step ctx rs : SourcePrefix source_graph source_root ctx 648 ->
  SourceProgramStep (ctx++[false;true;false;true;true],rs) (ctx++[true],rs).
Proof.
  intro P. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_break_inner) as Sel.
  destruct (cparam_break_inner_return ctx) as [E W]. rewrite <-W.
  replace (ctx++[false;true;false;true;true]) with ((ctx++[false;true;false;true])++[true])
    by now rewrite <-app_assoc.
  eapply cparam_step_break with (k:=1) (count:=3).
  - now rewrite <-app_assoc.
  - exact E.
Qed.
Lemma cparam_inner_break_test_step ctx rs : SourcePrefix source_graph source_root ctx 648 ->
  SourceProgramStep (ctx++[false;true;true;true],rs) (loop_return ctx,rs).
Proof.
  intro P. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_break_test) as Sel.
  destruct (loop_return_spec ctx) as [out [n [E R]]]. rewrite R.
  replace (ctx++[false;true;true;true]) with ((ctx++[false;true;true])++[true])
    by now rewrite <-app_assoc.
  eapply cparam_step_break with (k:=1) (count:=S(S(S n))).
  - now rewrite <-app_assoc.
  - now apply cparam_break_test_return.
Qed.
Lemma cparam_outer_break_step ctx rs : SourcePrefix source_graph source_root (ctx++[false]) 648 ->
  SourceProgramStep (ctx++[false;true],rs) (loop_return ctx,rs).
Proof.
  intro P. pose proof (source_select_in_context _ _ _ _ _ _ P cparam_inner_break) as Sel.
  destruct (loop_return_spec ctx) as [out [n [E R]]]. rewrite R.
  replace (ctx++[false;true]) with ((ctx++[false])++[true]) by now rewrite <-app_assoc.
  eapply cparam_step_break with (k:=1) (count:=S n).
  - exact Sel.
  - now apply constructor_first_test_return.
Qed.
Print Assumptions cparam_outer_break_step.
Print Assumptions cparam_inner_break_inner_step.
Print Assumptions cparam_inner_break_test_step.
