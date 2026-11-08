(** Selecting while-loop instructions within any outer source context. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps RuntimeTraces
  CompilerSyntax CompilerData CompilerReverse CompilerContexts CompilerTrees
  CompilerExecution ConstructorGraph ConstructorPC.
Import ListNotations.

Lemma source_program_runs_trans a b c : SourceProgramRuns a b -> SourceProgramRuns b c ->
  SourceProgramRuns a c.
Proof.
  intro A. induction A as [s|s t u Step Runs IH]; intros B; [exact B|].
  eapply source_program_next with (t:=t); [exact Step|]. apply IH. exact B.
Qed.

Lemma while1_context_selections ctx root input output :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some (tree_while1 input output) ->
  SourceSelect source_graph source_root (ctx++[false]) (SDec input) /\
  SourceSelect source_graph source_root (ctx++[true;false]) (SInc output) /\
  SourceSelect source_graph source_root (ctx++[true;true]) (SContinue 2).
Proof.
  intros P U. destruct (while1_source_selections _ _ _ U) as [D [I C]].
  repeat split; eapply source_select_in_context; eassumption.
Qed.
Lemma while2_context_selections ctx root input output1 output2 :
  SourcePrefix source_graph source_root ctx root ->
  unfold_root root = Some (tree_while2 input output1 output2) ->
  SourceSelect source_graph source_root (ctx++[false]) (SDec input) /\
  SourceSelect source_graph source_root (ctx++[true;false;false]) (SInc output1) /\
  SourceSelect source_graph source_root (ctx++[true;false;true]) (SInc output2) /\
  SourceSelect source_graph source_root (ctx++[true;true]) (SContinue 2).
Proof.
  intros P U. destruct (while2_source_selections _ _ _ _ U) as [D [I1 [I2 C]]].
  repeat split; eapply source_select_in_context; eassumption.
Qed.

Lemma loop_first_child_return ctx :
  break_pc 0 (rev (ctx++[false])++[false]) = Some(true::rev ctx++[false],0) /\
  return_word (true::rev ctx++[false]) = ctx++[true].
Proof.
  pose proof (constructor_child_return ctx 0) as H. cbn [repeat app] in H. exact H.
Qed.
Lemma loop_continue_return ctx :
  continue_pc 1 (rev (ctx++[true])) = Some(rev ctx,1).
Proof. rewrite rev_app_distr. cbn [rev app continue_pc]. destruct (rev ctx); reflexivity. Qed.

Print Assumptions while1_context_selections.
Print Assumptions while2_context_selections.
Print Assumptions loop_continue_return.
