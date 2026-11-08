(** Reduce the remaining full-iteration obligation to the opcode switch. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import ProofSearchSyntax GenericSearch RepairedSearchProof.
From Repair Require Import CompilerExecution CompilerLoopBase CompilerLoops ConstructorControl SearchPrimitivesIteration SearchPrimitivesHalt SearchMachinePrefix SearchMachineProof SourceExecution.
Import ListNotations.

Definition SourceSwitchContract :=
  forall op a b c tail next old prior rs,
    source_switch_view op a b c tail next old prior rs ->
    exists result, SourceProgramRuns (before_switch++[false],rs) (post_cursor,result) /\
      source_search_view (SearchState tail next (repaired_execute (op,a,b,c) (old,prior))) result.

Theorem source_iteration_contract_from_switch : SourceSwitchContract -> SourceIterationContract.
Proof.
  intros Switch s rs View. destruct s as [pending next [old prior]].
  destruct (instruction_decode (iteration_word pending next)) as [[[[op a] b] c] tail] eqn:Decode.
  destruct (source_iteration_to_switch_nonempty pending next old prior op a b c tail rs View Decode)
    as [r1 [mid [pad [First [Prefix [SwitchView Suffix]]]]]].
  destruct (Switch op a b c tail (iteration_next pending next) old prior r1 SwitchView) as [result [Run V]].
  assert (Distinct : (before_switch++[false],r1)<>(post_cursor,result)).
  { intro E. apply (f_equal fst) in E. unfold before_switch,post_cursor in E. vm_compute in E. discriminate. }
  destruct (source_runs_nonempty_when_distinct _ _ Run Distinct) as [mid2 [Step2 Tail]].
  exists result,mid. split; [exact First|]. split.
  - eapply source_program_runs_trans; [exact Prefix|]. eapply source_program_next; [|exact Tail].
    eapply constructor_unpad_first_step with (pad:=1). exact Step2.
  - rewrite (search_step_decoded _ _ _ _ _ _ _ _ _ Decode). exact V.
Qed.

Print Assumptions source_iteration_contract_from_switch.
