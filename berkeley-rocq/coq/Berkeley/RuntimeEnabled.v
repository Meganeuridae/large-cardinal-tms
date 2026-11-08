(** Every well-formed intermediate configuration can either halt or execute
    a normalized instruction. This turns checked PC coverage into progress. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeRegisters
  RuntimeControl RuntimeCalls RuntimeProgram RuntimeSimulation RuntimeJumps
  RuntimeJumpBounds RuntimeTraces RuntimePC RuntimeMacro.
Import ListNotations.

Lemma terminal_classify q : terminal q=true ->
  q=1385 \/ (exists i, i<11 /\ q=inc_entry i) \/
            (exists i, i<11 /\ q=dec_entry i).
Proof.
  unfold terminal. intro H. apply existsb_exists in H as [t [InT E]].
  apply Nat.eqb_eq in E. subst t.
  change (In q (List.map inc_entry (seq 0 11) ++ List.map dec_entry (seq 0 11) ++ [1385])) in InT.
  repeat rewrite in_app_iff in InT.
  destruct InT as [I|[I|I]].
  - apply in_map_iff in I as [i [E I]]. right; left. exists i.
    apply in_seq in I. split; [lia|symmetry; exact E].
  - apply in_map_iff in I as [i [E I]]. right; right. exists i.
    apply in_seq in I. split; [lia|symmetry; exact E].
  - simpl in I. destruct I as [E|[]]. left. symmetry; exact E.
Qed.

Lemma register_ir_enabled w rs i : i<11 -> 11<=length rs ->
  (ReadPath 72 w (inc_entry i) \/ ReadPath 72 w (dec_entry i)) ->
  exists b, IRStep (w,rs) b.
Proof.
  intros Hi Hr P.
  assert (SomeIndex : nth_error rs i <> None) by (apply nth_error_Some; lia).
  destruct (nth_error rs i) as [v|] eqn:E; [|contradiction].
  destruct (nth_error_split rs i E) as [before [after [Er L]]].
  subst rs i. destruct P as [P|P].
  - destruct (register_return_exists w (length before) 0 Hi ltac:(lia) (or_introl P))
      as [out [n F]].
    exists (return_word out,before++S v::after). econstructor; eassumption.
  - destruct v as [|v].
    + destruct (register_return_exists w (length before) 1 Hi ltac:(lia) (or_intror P))
        as [out [n F]].
      exists (return_word out,before++0::after). econstructor; eassumption.
    + destruct (register_return_exists w (length before) 0 Hi ltac:(lia) (or_intror P))
        as [out [n F]].
      exists (return_word out,before++v::(after++[0])). econstructor; eassumption.
Qed.

Lemma terminal_read_enabled w q rs : ReadPath 72 w q -> terminal q=true ->
  11<=length rs -> IRTerminal (w,rs) \/ exists b, IRStep (w,rs) b.
Proof.
  intros P T R. destruct (terminal_classify q T) as [E|[[i [I E]]|[i [I E]]]]; subst q.
  - left. exact P.
  - right. apply (register_ir_enabled w rs i); [exact I|exact R|left; exact P].
  - right. apply (register_ir_enabled w rs i); [exact I|exact R|right; exact P].
Qed.

Lemma jump_ir_enabled w q target rs : ReadPath 72 w q -> node q=true ->
  lookup new_table q true = Some(false,L,target) ->
  exists b, IRStep (w++[true],rs) b.
Proof.
  intros P N E. destruct (jump_guard_sound _ _ _ _ N E) as [_ [_ [C|C]]];
    destruct C as [k [K [T B]]]; subst target.
  - pose proof (root_path_rank true _ _ P) as HP.
    change (bit_rank true q <= ones w) in HP.
    assert (O : ones (rev w) = ones w).
    { pose proof (ones_zeros (rev w)). pose proof (ones_zeros w).
      rewrite zeros_rev,length_rev in H. lia. }
    destruct (continue_pc_total k (rev w) ltac:(rewrite O; lia)) as [out [n F]].
    exists (rev out,rs). econstructor; eassumption.
  - pose proof (root_path_rank false _ _ P) as HP.
    change (bit_rank false q <= zeros w) in HP.
    destruct (break_pc_total k (rev w++[false])
      ltac:(rewrite zeros_app,zeros_rev; simpl; lia)) as [out [n F]].
    exists (return_word out,rs). econstructor; eassumption.
Qed.

Theorem macro_enabled s : WellFormed s -> MacroTerminal s \/ exists t, MacroStep s t.
Proof.
  destruct s as [w rs]. intros [G R]. cbn [fst snd] in *.
  destruct G as [w q P|w q target P N E].
  - destruct (root_zero_completion w q P) as [n [q' [P' [T L]]]].
    destruct (terminal_read_enabled (w++repeat false n) q' rs P' T R) as [H|[b H]].
    + left. exists n. exact H.
    + right. exists b. apply (macro_step w n rs b); [eapply good_read; exact P'|exact H].
  - right. destruct (jump_ir_enabled w q target rs P N E) as [b H].
    exists b. apply ir_is_macro; [eapply good_jump; eassumption|exact H].
Qed.
Print Assumptions terminal_classify.
Print Assumptions macro_enabled.
