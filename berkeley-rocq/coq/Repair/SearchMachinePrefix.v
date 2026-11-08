(** The checked source program up to entry of the instruction switch. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax ConstructorArithmetic ProofSearchSyntax GenericSearch RepairedSearchProof CompilerReverse.
From Repair Require Import CompilerData CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorPush ConstructorControl ConstructorUnpair ConstructorFrame SearchPrimitivesDecode SearchPrimitivesIteration SourceExecution.
Import ListNotations.
Definition repaired_search_step := GenericSearch.search_step repaired_axiom.
Definition repaired_execute := GenericSearch.execute_instruction repaired_axiom.

Definition source_search_view (s : search_state) (rs : list nat) :=
  11<=length rs /\ nth_error rs 0=Some(pending_program s) /\ nth_error rs 1=Some(next_program s) /\
  nth_error rs 2=Some(fst (proof_stack s)) /\ nth_error rs 3=Some(snd (proof_stack s)) /\
  nth_error rs 8=Some 0 /\ nth_error rs 9=Some 0 /\ nth_error rs 10=Some 0.

Definition before_switch := repeat true 18.
Definition source_switch_view (op a b c tail next old prior : nat) (rs : list nat) :=
  11<=length rs /\ nth_error rs 0=Some tail /\ nth_error rs 1=Some next /\
  nth_error rs 2=Some 0 /\ nth_error rs 3=Some(cantor old prior) /\
  nth_error rs 4=Some op /\ nth_error rs 5=Some a /\ nth_error rs 6=Some b /\
  nth_error rs 7=Some c /\ nth_error rs 8=Some 0 /\ nth_error rs 9=Some 0 /\ nth_error rs 10=Some 0.

Local Transparent source_graph.
Lemma source_main_push_context :
  SourcePrefix source_graph source_root (decode_cursor 4++[false]) source_pushwff_root.
Proof. apply source_prefix_find_sound. vm_compute. reflexivity. Qed.
Local Opaque source_graph.
Lemma main_push_returns_to_switch : decode_cursor 4 ++ [true] = before_switch.
Proof. vm_compute. reflexivity. Qed.

Lemma search_step_decoded pending next old prior op a b c tail :
  instruction_decode (iteration_word pending next)=((op,a,b,c),tail) ->
  repaired_search_step (SearchState pending next (old,prior)) =
    SearchState tail (iteration_next pending next) (repaired_execute (op,a,b,c) (old,prior)).
Proof.
  destruct pending; cbn [iteration_word iteration_next repaired_search_step GenericSearch.search_step pending_program next_program proof_stack];
    now intros ->.
Qed.

Theorem source_iteration_to_switch_nonempty pending next old prior op a b c tail rs :
  source_search_view (SearchState pending next (old,prior)) rs ->
  instruction_decode (iteration_word pending next)=((op,a,b,c),tail) ->
  exists result mid pad, SourceProgramStep ([],rs) mid /\
    SourceProgramRuns mid (before_switch,result) /\
    source_switch_view op a b c tail (iteration_next pending next) old prior result /\
    skipn 11 result=skipn 11 rs++repeat 0 pad.
Proof.
  intros View Decode. unfold source_search_view in View. cbn [pending_program next_program proof_stack fst snd] in View.
  destruct View as [L [N [Q [T [S [X [Y Z]]]]]]].
  pose proof (instruction_encode_decode (iteration_word pending next)) as Code.
  rewrite Decode in Code. cbn [instruction_tail] in Code. symmetry in Code.
  destruct (source_iteration_prefix_nonempty pending next old prior op a b c tail rs L N Q T S X Y Code)
    as [r1 [mid [First [Prefix [L1 [N1 [Q1 [T1 [S1 [O1 [A1 [B1 [C1 [X1 [Y1 Z1]]]]]]]]]]]]]]].
  assert (Z1' : nth_error r1 10=Some 0) by (rewrite Z1; exact Z).
  destruct (source_push_nonempty (decode_cursor 4++[false]) r1 old prior
    source_main_push_context L1 T1 S1 X1) as [result [mid2 [Step2 [Push [L2 [T2 [S2 [X2 Frame]]]]]]]].
  rewrite constructor_loop_return_false, main_push_returns_to_switch in Push.
  assert (N2 : nth_error result 0=Some tail) by (rewrite Frame by lia; exact N1).
  assert (Q2 : nth_error result 1=Some(iteration_next pending next)) by (rewrite Frame by lia; exact Q1).
  assert (O2 : nth_error result 4=Some op) by (rewrite Frame by lia; exact O1).
  assert (A2 : nth_error result 5=Some a) by (rewrite Frame by lia; exact A1).
  assert (B2 : nth_error result 6=Some b) by (rewrite Frame by lia; exact B1).
  assert (C2 : nth_error result 7=Some c) by (rewrite Frame by lia; exact C1).
  assert (Y2 : nth_error result 9=Some 0) by (rewrite Frame by lia; exact Y1).
  assert (Z2 : nth_error result 10=Some 0) by (rewrite Frame by lia; exact Z1').
  assert (Run : SourceProgramRuns mid (before_switch,result)).
  { eapply source_program_runs_trans; [exact Prefix|]. eapply source_program_next; [|exact Push].
    eapply constructor_unpad_first_step with (pad:=1). exact Step2. }
  assert (Whole : SourceProgramRuns ([],rs) (before_switch,result)) by (eapply source_program_next; eassumption).
  destruct (source_runs_zero_suffix _ _ Whole L) as [pad [Suffix _]]. cbn [snd] in Suffix.
  exists result,mid,pad. repeat split; try assumption.
Qed.

Print Assumptions search_step_decoded.
Print Assumptions source_iteration_to_switch_nonempty.
