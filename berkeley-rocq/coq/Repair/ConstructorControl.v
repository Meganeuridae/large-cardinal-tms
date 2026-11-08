(** Source-program primitive steps, with optional PC zero-padding and the
    physical zero register appended by a successful decrement. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerRegisters RuntimeControl RuntimeCalls RuntimeJumps.
From Repair Require Import CompilerData SourceExecution.
Import ListNotations.

Theorem constructor_step_inc pc pad rs i value out count :
  SourceSelect source_graph source_root (pc++repeat false pad) (SInc i) ->
  i < 11 -> nth_error rs i = Some value ->
  break_pc 0 (rev (pc++repeat false pad)++[false]) = Some(out,count) ->
  SourceProgramStep (pc,rs) (return_word out,set_register i (S value) rs).
Proof.
  intros Sel Hi N Ret. destruct (nth_error_split rs i N) as [before [after [E L]]].
  subst rs. subst i. rewrite set_register_split.
  eapply source_program_step with (n:=pad).
  eapply source_increment; eassumption.
Qed.

Theorem constructor_step_dec_zero pc pad rs i out count :
  SourceSelect source_graph source_root (pc++repeat false pad) (SDec i) ->
  i < 11 -> nth_error rs i = Some 0 ->
  break_pc 1 (rev (pc++repeat false pad)++[false]) = Some(out,count) ->
  SourceProgramStep (pc,rs) (return_word out,rs).
Proof.
  intros Sel Hi N Ret. destruct (nth_error_split rs i N) as [before [after [E L]]].
  subst rs. subst i.
  eapply source_program_step with (n:=pad).
  eapply source_decrement_zero; eassumption.
Qed.

Theorem constructor_step_dec_positive pc pad rs i value out count :
  SourceSelect source_graph source_root (pc++repeat false pad) (SDec i) ->
  i < 11 -> nth_error rs i = Some (S value) ->
  break_pc 0 (rev (pc++repeat false pad)++[false]) = Some(out,count) ->
  SourceProgramStep (pc,rs) (return_word out,set_register i value rs ++ [0]).
Proof.
  intros Sel Hi N Ret. destruct (nth_error_split rs i N) as [before [after [E L]]].
  subst rs. subst i. rewrite set_register_split, <- app_assoc. simpl.
  eapply source_program_step with (n:=pad).
  eapply source_decrement_positive; eassumption.
Qed.

Theorem constructor_step_continue pre rs k out count :
  SourceSelect source_graph source_root (pre++[true]) (SContinue (S k)) ->
  continue_pc k (rev pre) = Some(out,count) ->
  SourceProgramStep (pre++[true],rs) (rev out,rs).
Proof.
  intros Sel Ret. eapply source_program_step with (n:=0).
  rewrite app_nil_r. eapply source_continue; eassumption.
Qed.

(** A pending suffix of zero bits is a representation choice.  This lemma
    lifts an actual first instruction after padding into one normalized
    source-program step; it does not identify the two PC words as states. *)
Lemma constructor_unpad_first_step pc pad rs target :
  SourceProgramStep (pc++repeat false pad,rs) target ->
  SourceProgramStep (pc,rs) target.
Proof.
  intro H. inversion H as [w n rs' b S]; subst.
  eapply source_program_step with (n:=pad+n).
  rewrite repeat_app, app_assoc. exact S.
Qed.

Lemma constructor_unpad_nonempty_run pc pad rs target :
  SourceProgramRuns (pc++repeat false pad,rs) target ->
  target <> (pc++repeat false pad,rs) -> SourceProgramRuns (pc,rs) target.
Proof.
  intros R Different. remember (pc++repeat false pad,rs) as from eqn:E.
  destruct R as [s|s mid finish Step Tail]; subst.
  - contradiction.
  - eapply source_program_next; [eapply constructor_unpad_first_step, Step|exact Tail].
Qed.

Print Assumptions constructor_step_inc.
Print Assumptions constructor_step_dec_zero.
Print Assumptions constructor_step_dec_positive.
Print Assumptions constructor_step_continue.
Print Assumptions constructor_unpad_first_step.
Print Assumptions constructor_unpad_nonempty_run.
