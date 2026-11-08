(** Normalized instructions: zero-padding is representation equality, while
    every executed instruction makes strictly positive TM progress. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From Berkeley Require Import Data Machine RuntimeTape RuntimeControl RuntimeProgram
  RuntimeSimulation RuntimeTraces RuntimeProgress RuntimePC.
Import ListNotations.

Inductive MacroStep : ir_state -> ir_state -> Prop :=
| macro_step w n rs b : GoodPC (w++repeat false n) ->
    IRStep (w++repeat false n,rs) b -> MacroStep (w,rs) b.
Definition MacroTerminal (s : ir_state) := exists n,
  IRTerminal (fst s++repeat false n,snd s).
Inductive MacroRuns : ir_state -> ir_state -> Prop :=
| macro_refl s : MacroRuns s s
| macro_next s t u : MacroStep s t -> MacroRuns t u -> MacroRuns s u.
Definition MacroHalts s := exists t, MacroRuns s t /\ MacroTerminal t.
Definition WellFormed (s : ir_state) := GoodPC(fst s) /\ 11<=length(snd s).

Lemma ir_is_macro a b : GoodPC (fst a) -> IRStep a b -> MacroStep a b.
Proof.
  destruct a as [w rs]. intros G H.
  replace (w,rs) with (w++repeat false 0,rs) in H by (simpl; now rewrite app_nil_r).
  apply (macro_step w 0 rs b); [simpl; now rewrite app_nil_r|exact H].
Qed.
Theorem macro_preserves_wellformed a b : WellFormed a -> MacroStep a b -> WellFormed b.
Proof.
  intros [G H] S. destruct S. unfold WellFormed. split.
  - eapply ir_step_preserves_good; exact H1.
  - pose proof (ir_step_register_count _ _ H1) as C. cbn [snd] in *. lia.
Qed.
Theorem macro_progress width a b : 404<=width -> MacroStep a b ->
  Progress (encode width a) (encode width b).
Proof.
  intros W S. destruct S as [w n rs b G H].
  pose proof (good_pc_bound _ G) as L. rewrite app_length,repeat_length in L.
  unfold encode at 1. cbn [fst snd]. rewrite (normal_zero_extension width w n rs) by lia.
  apply (ir_step_progress width (w++repeat false n,rs) b);
    [unfold fits; cbn [fst]; rewrite app_length,repeat_length; lia|exact H].
Qed.
Lemma progress_runs a b : Progress a b -> Runs a b.
Proof.
  intro P. induction P.
  - apply New.evstep_one,H.
  - eapply New.evstep_step; eassumption.
Qed.
Theorem macro_trace_simulation width a b : 404<=width -> MacroRuns a b ->
  Runs (encode width a) (encode width b).
Proof.
  intros W R. induction R; [apply runs_refl|].
  eapply runs_trans; [apply progress_runs; eapply macro_progress; eassumption|exact IHR].
Qed.
Lemma macro_terminal_halts width s : 404<=width -> MacroTerminal s ->
  New.halts new_tm (encode width s).
Proof.
  destruct s as [w rs]. intros W [n T].
  assert (G : GoodPC (w++repeat false n)) by (apply (good_read _ 1385); exact T).
  pose proof (good_pc_bound _ G) as L. rewrite app_length,repeat_length in L.
  unfold encode. cbn [fst snd]. rewrite (normal_zero_extension width w n rs) by lia.
  apply (terminal_halts width (w++repeat false n,rs)),T.
Qed.
Theorem macro_halting_implies_tm width s : 404<=width -> MacroHalts s ->
  New.halts new_tm (encode width s).
Proof.
  intros W [t [R T]].
  apply (proj2 (RuntimeCalls.runs_preserve_halting _ _ (macro_trace_simulation _ _ _ W R))).
  apply macro_terminal_halts; assumption.
Qed.

Print Assumptions macro_preserves_wellformed.
Print Assumptions macro_progress.
Print Assumptions macro_trace_simulation.
Print Assumptions macro_halting_implies_tm.
