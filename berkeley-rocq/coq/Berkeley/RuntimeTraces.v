(** An intermediate machine with explicit PC words and register operations.
    This is not yet the structured source-language semantics or its compiler. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeRegisters
  RuntimeControl RuntimeCalls RuntimeProgram RuntimeSimulation RuntimeJumps.
Import ListNotations.

Definition ir_state := (list bool * list nat)%type.
Definition encode width (s : ir_state) := normal width (fst s) (snd s).
Definition fits width (s : ir_state) := length (fst s) <= width.

Inductive IRStep : ir_state -> ir_state -> Prop :=
| ir_increment w before v after out n :
    length before < 11 -> ReadPath 72 w (inc_entry (length before)) ->
    break_pc 0 (rev w++[false]) = Some(out,n) ->
    IRStep (w,before++v::after) (return_word out,before++S v::after)
| ir_decrement_zero w before after out n :
    length before < 11 -> ReadPath 72 w (dec_entry (length before)) ->
    break_pc 1 (rev w++[false]) = Some(out,n) ->
    IRStep (w,before++0::after) (return_word out,before++0::after)
| ir_decrement_positive w before v after out n :
    length before < 11 -> ReadPath 72 w (dec_entry (length before)) ->
    break_pc 0 (rev w++[false]) = Some(out,n) ->
    IRStep (w,before++S v::after) (return_word out,before++v::(after++[0]))
| ir_continue w q k out n rs :
    ReadPath 72 w q -> lookup new_table q true = Some(false,L,continue_state k) ->
    k<=3 -> continue_pc k (rev w) = Some(out,n) ->
    IRStep (w++[true],rs) (rev out,rs)
| ir_break w q k out n rs :
    ReadPath 72 w q -> lookup new_table q true = Some(false,L,break_state k) ->
    k<=2 -> break_pc k (rev w++[false]) = Some(out,n) ->
    IRStep (w++[true],rs) (return_word out,rs).

Theorem ir_step_simulation width a b : fits width a -> IRStep a b ->
  Runs (encode width a) (encode width b) /\ fits width b.
Proof.
  intros HW H. destruct H; unfold encode, fits in *; cbn [fst snd] in *; split.
  - eapply increment_simulation; eassumption.
  - exact (proj1 (returned_capacity _ _ _ _ _ HW H1)).
  - eapply decrement_zero_simulation; eassumption.
  - exact (proj1 (returned_capacity _ _ _ _ _ HW H1)).
  - eapply decrement_positive_simulation; eassumption.
  - exact (proj1 (returned_capacity _ _ _ _ _ HW H1)).
  - eapply continue_jump_simulation; eassumption.
  - pose proof (continue_pc_bounds _ _ _ _ H2) as [_ HL].
    rewrite rev_length in *. rewrite app_length in HW. simpl in HW. lia.
  - eapply break_jump_simulation; eassumption.
  - pose proof (return_word_bound _ _ _ _ H2) as [_ HL].
    rewrite app_length in HW. simpl in HW. lia.
Qed.

Inductive IRRuns : ir_state -> ir_state -> Prop :=
| ir_refl s : IRRuns s s
| ir_next s t u : IRStep s t -> IRRuns t u -> IRRuns s u.

Theorem ir_trace_simulation width a b : IRRuns a b -> fits width a ->
  Runs (encode width a) (encode width b) /\ fits width b.
Proof.
  intro H. induction H; intro HW.
  - split; [apply runs_refl|exact HW].
  - destruct (ir_step_simulation _ _ _ HW H) as [R HT].
    destruct (IHIRRuns HT) as [S HU]. split; [eapply runs_trans; eassumption|exact HU].
Qed.
Theorem ir_trace_preserves_tm_halting width a b : IRRuns a b -> fits width a ->
  (New.halts new_tm (encode width a) <-> New.halts new_tm (encode width b)).
Proof.
  intros H HW. apply runs_preserve_halting. exact (proj1 (ir_trace_simulation _ _ _ H HW)).
Qed.

Definition IRTerminal (s : ir_state) := ReadPath 72 (fst s) 1385.
Definition IRHalts s := exists t, IRRuns s t /\ IRTerminal t.
Lemma terminal_halts width s : IRTerminal s -> New.halts new_tm (encode width s).
Proof.
  destruct s as [w rs]. intro H. unfold encode, normal; cbn [fst snd].
  pose proof (root_read w 1385
    (copies (S(S(width-length w))) false (Cons true (Cons false (regs rs blank)))) H) as R.
  apply (proj2 (runs_preserve_halting _ _ R)). apply New.halted_halts.
  unfold New.halted, CR. cbn [fst snd].
  unfold new_tm,st. rewrite val_mk by (unfold new_count; lia).
  unfold lookup. vm_compute. reflexivity.
Qed.

(** Forward direction only. Coverage of successive PC words and the
    blank bootstrap are still required for a whole-program equivalence. *)
Theorem ir_halting_implies_tm_halting width s : fits width s -> IRHalts s ->
  New.halts new_tm (encode width s).
Proof.
  intros HW [t [R H]]. apply (proj2 (ir_trace_preserves_tm_halting _ _ _ R HW)).
  apply terminal_halts,H.
Qed.

Print Assumptions ir_step_simulation.
Print Assumptions ir_trace_simulation.
Print Assumptions ir_trace_preserves_tm_halting.
Print Assumptions ir_halting_implies_tm_halting.
