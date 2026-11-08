(** Literal repaired source control semantics, before any TM-simulation
    theorem. Program-counter zero padding matches the original framework. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps RuntimeTraces CompilerSyntax.
From Repair Require Import CompilerData.
Import ListNotations.

Inductive SourceStep : ir_state -> ir_state -> Prop :=
| source_increment w before v after out n :
    SourceSelect source_graph source_root w (SInc (length before)) ->
    break_pc 0 (rev w++[false]) = Some(out,n) ->
    SourceStep (w,before++v::after) (return_word out,before++S v::after)
| source_decrement_zero w before after out n :
    SourceSelect source_graph source_root w (SDec (length before)) ->
    break_pc 1 (rev w++[false]) = Some(out,n) ->
    SourceStep (w,before++0::after) (return_word out,before++0::after)
| source_decrement_positive w before v after out n :
    SourceSelect source_graph source_root w (SDec (length before)) ->
    break_pc 0 (rev w++[false]) = Some(out,n) ->
    SourceStep (w,before++S v::after) (return_word out,before++v::(after++[0]))
| source_continue w k out n rs :
    SourceSelect source_graph source_root (w++[true]) (SContinue (S k)) ->
    continue_pc k (rev w) = Some(out,n) ->
    SourceStep (w++[true],rs) (rev out,rs)
| source_break w k out n rs :
    SourceSelect source_graph source_root (w++[true]) (SBreak k) ->
    break_pc k (rev w++[false]) = Some(out,n) ->
    SourceStep (w++[true],rs) (return_word out,rs).

Inductive SourceProgramStep : ir_state -> ir_state -> Prop :=
| source_program_step w n rs b : SourceStep (w++repeat false n,rs) b ->
    SourceProgramStep (w,rs) b.
Definition SourceProgramTerminal (s : ir_state) := exists n,
  SourceSelect source_graph source_root (fst s++repeat false n) SHalt.
Inductive SourceProgramRuns : ir_state -> ir_state -> Prop :=
| source_program_refl s : SourceProgramRuns s s
| source_program_next s t u : SourceProgramStep s t -> SourceProgramRuns t u -> SourceProgramRuns s u.
Definition SourceProgramHalts s := exists t, SourceProgramRuns s t /\ SourceProgramTerminal t.

Lemma source_program_runs_trans a b c : SourceProgramRuns a b -> SourceProgramRuns b c ->
  SourceProgramRuns a c.
Proof.
  intro A. induction A as [s|s t u Step Runs IH]; intros B; [exact B|].
  eapply source_program_next with (t:=t); [exact Step|]. apply IH. exact B.
Qed.
Print Assumptions source_program_runs_trans.
