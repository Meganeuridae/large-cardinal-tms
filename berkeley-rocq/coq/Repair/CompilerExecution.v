(** Complete execution semantics of the extracted source DAG. Zero extension
    selects the next instruction from a returned source PC prefix. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax.
From Repair Require Import Machine RuntimeProgram RuntimeTraces RuntimePC RuntimeMacro RuntimeEquivalence CompilerData CompilerProof CompilerInstance CompilerReverse SourceExecution.
Import ListNotations.

Lemma ir_step_input_good a b : IRStep a b -> GoodPC (fst a).
Proof.
  intro H. destruct H; cbn [fst].
  - eapply good_read; eassumption.
  - eapply good_read; eassumption.
  - eapply good_read; eassumption.
  - destruct (source_read_left_prefix _ _ _ _ H H0) as [i [_ M]].
    eapply good_jump; [exact H|eapply compiler_map_points_to_node; exact M|exact H0].
  - destruct (source_read_left_prefix _ _ _ _ H H0) as [i [_ M]].
    eapply good_jump; [exact H|eapply compiler_map_points_to_node; exact M|exact H0].
Qed.

(** The source semantics here mentions source selection, register arithmetic,
    and finite PC words. No TM run, table lookup, or TM-halting predicate is
    included as a premise of an execution rule. *)
Theorem source_program_step_equivalence a b : SourceProgramStep a b <-> MacroStep a b.
Proof.
  split.
  - intro S. destruct S. pose proof (source_step_implies_ir _ _ H) as I.
    apply (macro_step w n rs b); [exact (ir_step_input_good _ _ I)|exact I].
  - intro S. destruct S. apply (source_program_step w n rs b). apply ir_step_implies_source,H0.
Qed.
Theorem source_program_terminal_equivalence s : SourceProgramTerminal s <-> MacroTerminal s.
Proof.
  unfold SourceProgramTerminal,MacroTerminal. split; intros [n H]; exists n.
  - apply (proj1 (source_ir_terminal_equivalence (fst s++repeat false n,snd s))). exact H.
  - change (SourceTerminal (fst s++repeat false n,snd s)).
    apply (proj2 (source_ir_terminal_equivalence (fst s++repeat false n,snd s))). exact H.
Qed.
Theorem source_program_runs_equivalence a b : SourceProgramRuns a b <-> MacroRuns a b.
Proof.
  split; intro R; induction R; [constructor| |constructor|].
  - eapply macro_next; [apply source_program_step_equivalence,H|exact IHR].
  - eapply source_program_next; [apply source_program_step_equivalence,H|exact IHR].
Qed.
Theorem source_program_halting_equivalence s : SourceProgramHalts s <-> MacroHalts s.
Proof.
  unfold SourceProgramHalts,MacroHalts. split; intros [t [R T]]; exists t; split.
  - apply source_program_runs_equivalence,R.
  - apply source_program_terminal_equivalence,T.
  - apply source_program_runs_equivalence,R.
  - apply source_program_terminal_equivalence,T.
Qed.

Theorem blank_halting_iff_source_program :
  New.halts new_tm New.c0 <-> SourceProgramHalts initial_register_state.
Proof.
  rewrite blank_halting_iff_normalized_program. symmetry. apply source_program_halting_equivalence.
Qed.

Print Assumptions source_program_step_equivalence.
Print Assumptions source_program_halting_equivalence.
Print Assumptions blank_halting_iff_source_program.
