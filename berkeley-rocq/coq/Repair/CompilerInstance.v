(** Instantiation of the generic compiler checker on the reconstructed alpha
    source program and the literal 1,385-state decision graph. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine CompilerSyntax.
From Repair Require Import Data Machine RuntimeTape RuntimeRegisters RuntimeControl RuntimeCalls RuntimeProgram RuntimeJumps RuntimeTraces CompilerProof CompilerData SourceExecution.
Import ListNotations.

Lemma source_compiler_certificate : compiler_check source_graph compiler_map = true.
Proof. vm_compute. reflexivity. Qed.
Lemma source_root_maps_to_dispatch : nth_error compiler_map source_root = Some 73.
Proof. vm_compute. reflexivity. Qed.

Theorem source_program_selection bits a : SourceSelect source_graph source_root bits a ->
  realizes 73 bits a.
Proof.
  intro S. eapply source_selection_compiles; [apply source_compiler_certificate|
    apply source_root_maps_to_dispatch|exact S].
Qed.

(** These are source-level register and relative-control operations selected
    structurally from the DAG.  PC return functions manipulate finite words;
    they do not inspect the machine's transition table. *)
Theorem source_step_implies_ir a b : SourceStep a b -> IRStep a b.
Proof.
  intro H. destruct H.
  - pose proof (source_program_selection _ _ H) as [B P].
    econstructor; eassumption.
  - pose proof (source_program_selection _ _ H) as [B P].
    eapply ir_decrement_zero; eassumption.
  - pose proof (source_program_selection _ _ H) as [B P].
    eapply ir_decrement_positive; eassumption.
  - pose proof (source_program_selection _ _ H) as [_ [K [pre [q [E [P T]]]]]].
    apply app_inv_tail in E. subst pre. cbn in T.
    eapply ir_continue; [exact P|exact T|lia|exact H0].
  - pose proof (source_program_selection _ _ H) as [K [pre [q [E [P T]]]]].
    apply app_inv_tail in E. subst pre.
    eapply ir_break; eassumption.
Qed.

Inductive SourceRuns : ir_state -> ir_state -> Prop :=
| source_refl s : SourceRuns s s
| source_next s t u : SourceStep s t -> SourceRuns t u -> SourceRuns s u.
Definition SourceTerminal (s : ir_state) :=
  SourceSelect source_graph source_root (fst s) SHalt.
Definition SourceHalts s := exists t, SourceRuns s t /\ SourceTerminal t.

Theorem source_trace_implies_ir a b : SourceRuns a b -> IRRuns a b.
Proof.
  intro H. induction H as [s|s t u Step Runs IH]; [constructor|].
  eapply ir_next; [eapply source_step_implies_ir; exact Step|exact IH].
Qed.
Theorem source_halting_implies_tm_halting width s : fits width s -> SourceHalts s ->
  New.halts new_tm (encode width s).
Proof.
  intros F [t [R T]]. apply ir_halting_implies_tm_halting; [exact F|].
  exists t. split; [now apply source_trace_implies_ir|].
  unfold IRTerminal, SourceTerminal in *. now apply source_program_selection in T.
Qed.

Print Assumptions source_compiler_certificate.
Print Assumptions source_program_selection.
Print Assumptions source_step_implies_ir.
Print Assumptions source_halting_implies_tm_halting.
