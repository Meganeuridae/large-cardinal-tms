(** Checked source paths and execution through the main axiom switch. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import RuntimeControl RuntimeCalls RuntimeJumps RuntimeTraces CompilerSyntax CompilerRegisters ConstructorPC CompilerReverse.
From Repair Require Import CompilerData CompilerInstance CompilerReverse CompilerContexts CompilerExecution CompilerLoopBase ConstructorGraph ConstructorControl SourceExecution.
Import ListNotations.

Fixpoint source_find_leaf program q bits : option source_atom :=
  match bits with
  | [] => None
  | b::rest =>
      match nth_error program q with
      | None => None
      | Some p => match select_branch p b with
        | SNode next => source_find_leaf program next rest
        | a => match rest with [] => Some a | _ => None end
        end
      end
  end.

Lemma source_find_leaf_sound program q bits leaf : source_find_leaf program q bits = Some leaf ->
  SourceSelect program q bits leaf.
Proof.
  revert q leaf. induction bits as [|b bits IH]; intros q leaf E; [discriminate|].
  cbn [source_find_leaf] in E. destruct (nth_error program q) as [p|] eqn:P; [|discriminate].
  destruct (select_branch p b) as [next|r|r| |k|k] eqn:A.
  - eapply select_node with (pair:=p) (j:=next); [exact P|exact A|now apply IH].
  - destruct bits; [inversion E; subst; eapply select_leaf; [exact P|exact A|reflexivity]|discriminate].
  - destruct bits; [inversion E; subst; eapply select_leaf; [exact P|exact A|reflexivity]|discriminate].
  - destruct bits; [inversion E; subst; eapply select_leaf; [exact P|exact A|reflexivity]|discriminate].
  - destruct bits; [inversion E; subst; eapply select_leaf; [exact P|exact A|reflexivity]|discriminate].
  - destruct bits; [inversion E; subst; eapply select_leaf; [exact P|exact A|reflexivity]|discriminate].
Qed.

Definition leaf_matches bits expected :=
  match source_find_leaf source_graph source_root bits with
  | Some a => if source_atom_eq_dec a expected then true else false
  | None => false
  end.
Lemma leaf_matches_sound bits expected : leaf_matches bits expected = true ->
  SourceSelect source_graph source_root bits expected.
Proof.
  unfold leaf_matches. destruct (source_find_leaf source_graph source_root bits) as [a|] eqn:E;
    [|discriminate]. destruct (source_atom_eq_dec a expected) as [->|]; [|discriminate].
  intros _. now apply source_find_leaf_sound.
Qed.

Definition main_switch_pc := repeat true 18 ++ [false].
Definition switch_pc j := main_switch_pc ++ repeat true j.
Definition regular_skip_check j :=
  andb (leaf_matches (switch_pc j ++ [false;false;false]) (SDec 4))
       (leaf_matches (switch_pc j ++ [false;false;true]) (SBreak 1)).
Definition regular_axiom_check j :=
  leaf_matches (switch_pc j ++ [false;true;false]) (SInc 4).
Definition final_axiom_check :=
  andb (leaf_matches (switch_pc 27 ++ [false;false]) (SDec 4))
       (leaf_matches (switch_pc 27 ++ [true;false]) (SInc 4)).

Lemma dispatch_paths_certificate :
  andb (forallb regular_skip_check (seq 0 27))
    (andb (forallb regular_axiom_check (seq 3 24)) final_axiom_check) = true.
Proof. vm_compute. reflexivity. Qed.

Local Opaque source_graph.
Theorem regular_skip_paths j : j < 27 ->
  SourceSelect source_graph source_root (switch_pc j ++ [false;false;false]) (SDec 4) /\
  SourceSelect source_graph source_root (switch_pc j ++ [false;false;true]) (SBreak 1).
Proof.
  intro H. pose proof dispatch_paths_certificate as C. apply andb_true_iff in C as [C _].
  rewrite forallb_forall in C. specialize (C j ltac:(apply in_seq; lia)).
  unfold regular_skip_check in C. apply andb_true_iff in C as [D B].
  split; now apply leaf_matches_sound.
Qed.
Theorem regular_axiom_inc_path j : 3 <= j -> j < 27 ->
  SourceSelect source_graph source_root (switch_pc j ++ [false;true;false]) (SInc 4).
Proof.
  intros A B. pose proof dispatch_paths_certificate as C.
  apply andb_true_iff in C as [_ C]. apply andb_true_iff in C as [C _].
  rewrite forallb_forall in C. specialize (C j ltac:(apply in_seq; lia)).
  now apply leaf_matches_sound.
Qed.
Theorem final_axiom_paths :
  SourceSelect source_graph source_root (switch_pc 27 ++ [false;false]) (SDec 4) /\
  SourceSelect source_graph source_root (switch_pc 27 ++ [true;false]) (SInc 4).
Proof.
  pose proof dispatch_paths_certificate as C. apply andb_true_iff in C as [_ C].
  apply andb_true_iff in C as [_ C]. unfold final_axiom_check in C.
  apply andb_true_iff in C as [D I]. split; now apply leaf_matches_sound.
Qed.

Lemma switch_pc_succ j : switch_pc (S j) = switch_pc j ++ [true].
Proof.
  unfold switch_pc. replace (S j) with (j+1) by lia. rewrite repeat_app.
  cbn [repeat]. now rewrite <- app_assoc.
Qed.

Lemma skip_dec_return ctx :
  break_pc 0 (rev(ctx++[false;false;false])++[false]) =
    Some(true::rev(ctx++[false;false])++[false],0) /\
  return_word (true::rev(ctx++[false;false])++[false]) = ctx++[false;false;true].
Proof.
  pose proof (constructor_child_return (ctx++[false;false]) 0) as [E W].
  cbn [repeat app] in E,W. rewrite <- app_assoc in E,W. cbn [app] in E,W. auto.
Qed.
Lemma skip_break_return ctx :
  break_pc 1 (rev(ctx++[false;false])++[false]) = Some(true::rev ctx++[false],1) /\
  return_word (true::rev ctx++[false]) = ctx++[true].
Proof.
  split; [rewrite rev_app_distr; reflexivity|apply constructor_return_word].
Qed.

Theorem switch_skip_positive j rs v : j < 27 -> 11 <= length rs ->
  nth_error rs 4 = Some(S v) ->
  SourceProgramRuns (switch_pc j,rs) (switch_pc (S j),set_register 4 v rs ++ [0]).
Proof.
  intros Bound Len V. destruct (regular_skip_paths j Bound) as [D B].
  destruct (skip_dec_return (switch_pc j)) as [Dret Dword].
  destruct (skip_break_return (switch_pc j)) as [Bret Bword].
  rewrite switch_pc_succ.
  eapply source_program_next with
    (t:=(switch_pc j++[false;false;true],set_register 4 v rs ++ [0])).
  - rewrite <- Dword.
    eapply constructor_step_dec_positive with (pad:=3) (i:=4) (value:=v)
      (out:=true::rev(switch_pc j++[false;false])++[false]) (count:=0).
    + cbn [repeat]. exact D.
    + lia.
    + exact V.
    + cbn [repeat]. exact Dret.
  - eapply source_program_next with
      (t:=(switch_pc j++[true],set_register 4 v rs ++ [0])); [|constructor].
    eapply source_program_step with (n:=0). rewrite app_nil_r.
    rewrite <- Bword. replace (switch_pc j++[false;false;true]) with
      ((switch_pc j++[false;false])++[true]) by now rewrite <- app_assoc.
    eapply source_break with (k:=1) (out:=true::rev(switch_pc j)++[false]) (n:=1).
    + now rewrite <- app_assoc.
    + exact Bret.
Qed.

Theorem switch_countdown j n rs : j+n <= 27 -> 11 <= length rs ->
  nth_error rs 4 = Some n ->
  SourceProgramRuns (switch_pc j,rs)
    (switch_pc (j+n),set_register 4 0 rs ++ repeat 0 n).
Proof.
  revert j rs. induction n as [|n IH]; intros j rs Bound Len V.
  - rewrite Nat.add_0_r. cbn [repeat]. rewrite app_nil_r, (set_register_noop _ _ _ V).
    constructor.
  - set (r1 := set_register 4 n rs ++ [0]).
    pose proof (switch_skip_positive j rs n ltac:(lia) Len V) as Cycle.
    change (SourceProgramRuns (switch_pc j,rs) (switch_pc (S j),r1)) in Cycle.
    assert (Len1 : 11 <= length r1).
    { unfold r1. rewrite app_length, set_register_length. simpl. lia. }
    assert (V1 : nth_error r1 4 = Some n).
    { unfold r1. rewrite nth_error_app1 by (rewrite set_register_length; lia).
      apply nth_error_set_same. lia. }
    pose proof (IH (S j) r1 ltac:(lia) Len1 V1) as Tail.
    replace (S j+n) with (j+S n) in Tail by lia.
    assert (Final : set_register 4 0 r1 ++ repeat 0 n =
      set_register 4 0 rs ++ repeat 0 (S n)).
    { unfold r1. rewrite set_register_append by (rewrite set_register_length; lia).
      rewrite set_register_twice. cbn [repeat]. now rewrite <- app_assoc. }
    rewrite Final in Tail. eapply source_program_runs_trans; eassumption.
Qed.

Lemma regular_case_zero_return ctx :
  break_pc 1 (rev(ctx++[false;false;false])++[false]) =
    Some(true::false::rev ctx++[false],1) /\
  return_word (true::false::rev ctx++[false]) = ctx++[false;true].
Proof.
  split.
  - rewrite rev_app_distr. reflexivity.
  - unfold return_word.
    change (rev (removelast ((true::false::rev ctx)++[false])) = ctx++[false;true]).
    rewrite removelast_last. cbn [rev]. rewrite rev_involutive.
    now rewrite <- app_assoc.
Qed.
Lemma regular_case_inc_return ctx :
  break_pc 0 (rev(ctx++[false;true;false])++[false]) =
    Some(true::rev(ctx++[false;true])++[false],0) /\
  return_word (true::rev(ctx++[false;true])++[false]) = ctx++[false;true;true].
Proof.
  pose proof (constructor_child_return (ctx++[false;true]) 0) as [E W].
  cbn [repeat app] in E,W. rewrite <- app_assoc in E,W. cbn [app] in E,W. auto.
Qed.
Lemma final_case_zero_return ctx :
  break_pc 1 (rev(ctx++[false;false])++[false]) = Some(true::rev ctx++[false],1) /\
  return_word (true::rev ctx++[false]) = ctx++[true].
Proof. apply skip_break_return. Qed.
Lemma final_case_inc_return ctx :
  break_pc 0 (rev(ctx++[true;false])++[false]) =
    Some(true::rev(ctx++[true])++[false],0) /\
  return_word (true::rev(ctx++[true])++[false]) = ctx++[true;true].
Proof.
  pose proof (constructor_child_return (ctx++[true]) 0) as [E W].
  cbn [repeat app] in E,W. rewrite <- app_assoc in E,W. cbn [app] in E,W. auto.
Qed.

Theorem regular_axiom_entry j rs : 3 <= j -> j < 27 -> nth_error rs 4 = Some 0 ->
  SourceProgramRuns (switch_pc j,rs)
    (switch_pc j++[false;true;true], set_register 4 1 rs).
Proof.
  intros Lo Hi V. destruct (regular_skip_paths j Hi) as [D _].
  pose proof (regular_axiom_inc_path j Lo Hi) as I.
  destruct (regular_case_zero_return (switch_pc j)) as [Dret Dword].
  destruct (regular_case_inc_return (switch_pc j)) as [Iret Iword].
  eapply source_program_next with (t:=(switch_pc j++[false;true],rs)).
  - rewrite <- Dword. eapply constructor_step_dec_zero with (pad:=3) (i:=4)
      (out:=true::false::rev(switch_pc j)++[false]) (count:=1).
    + cbn [repeat]. exact D.
    + lia.
    + exact V.
    + cbn [repeat]. exact Dret.
  - eapply source_program_next with
      (t:=(switch_pc j++[false;true;true],set_register 4 1 rs)); [|constructor].
    rewrite <- Iword. eapply constructor_step_inc with (pad:=1) (i:=4) (value:=0)
      (out:=true::rev(switch_pc j++[false;true])++[false]) (count:=0).
    + cbn [repeat]. rewrite <- app_assoc. exact I.
    + lia.
    + exact V.
    + cbn [repeat]. rewrite <- app_assoc. exact Iret.
Qed.

Theorem final_axiom_entry rs : nth_error rs 4 = Some 0 ->
  SourceProgramRuns (switch_pc 27,rs)
    (switch_pc 27++[true;true], set_register 4 1 rs).
Proof.
  intro V. destruct final_axiom_paths as [D I].
  destruct (final_case_zero_return (switch_pc 27)) as [Dret Dword].
  destruct (final_case_inc_return (switch_pc 27)) as [Iret Iword].
  eapply source_program_next with (t:=(switch_pc 27++[true],rs)).
  - rewrite <- Dword. eapply constructor_step_dec_zero with (pad:=2) (i:=4)
      (out:=true::rev(switch_pc 27)++[false]) (count:=1).
    + cbn [repeat]. exact D.
    + lia.
    + exact V.
    + cbn [repeat]. exact Dret.
  - eapply source_program_next with
      (t:=(switch_pc 27++[true;true],set_register 4 1 rs)); [|constructor].
    rewrite <- Iword. eapply constructor_step_inc with (pad:=1) (i:=4) (value:=0)
      (out:=true::rev(switch_pc 27++[true])++[false]) (count:=0).
    + cbn [repeat]. rewrite <- app_assoc. exact I.
    + lia.
    + exact V.
    + cbn [repeat]. rewrite <- app_assoc. exact Iret.
Qed.

Definition axiom_parent_pc i :=
  if i <? 24 then switch_pc (3+i) ++ [false;true;true]
  else switch_pc 27 ++ [true;true].

Lemma axiom_context_after_parent i : i < 24 ->
  axiom_dispatch_context i = axiom_parent_pc i ++ [false].
Proof.
  intro H. unfold axiom_dispatch_context, axiom_parent_pc, switch_pc, main_switch_pc.
  destruct (i <? 24) eqn:B.
  - replace (i+3) with (3+i) by lia.
    repeat rewrite <- app_assoc. reflexivity.
  - apply Nat.ltb_ge in B. lia.
Qed.

Theorem switch_axiom_dispatch i rs : i < 24 -> 11 <= length rs ->
  nth_error rs 4 = Some (3+i) ->
  SourceProgramRuns (main_switch_pc,rs)
    (axiom_parent_pc i, set_register 4 1 rs ++ repeat 0 (3+i)).
Proof.
  intros Hi Len V. set (r0 := set_register 4 0 rs ++ repeat 0 (3+i)).
  pose proof (switch_countdown 0 (3+i) rs ltac:(lia) Len V) as Count.
  unfold switch_pc at 1 in Count. cbn [repeat] in Count. rewrite app_nil_r in Count.
  cbn [Nat.add_0_l] in Count.
  change (SourceProgramRuns (main_switch_pc,rs) (switch_pc (3+i),r0)) in Count.
  assert (V0 : nth_error r0 4 = Some 0).
  { unfold r0. rewrite nth_error_app1 by (rewrite set_register_length; lia).
    apply nth_error_set_same. lia. }
  assert (Final : set_register 4 1 r0 = set_register 4 1 rs ++ repeat 0 (3+i)).
  { unfold r0. rewrite set_register_append by (rewrite set_register_length; lia).
    now rewrite set_register_twice. }
  unfold axiom_parent_pc. destruct (i <? 24) eqn:B.
  - apply Nat.ltb_lt in B. pose proof (regular_axiom_entry (3+i) r0 ltac:(lia) ltac:(lia) V0) as Entry.
    rewrite Final in Entry. eapply source_program_runs_trans; eassumption.
  - apply Nat.ltb_ge in B. lia.
Qed.

Print Assumptions dispatch_paths_certificate.
Print Assumptions regular_skip_paths.
Print Assumptions regular_axiom_inc_path.
Print Assumptions final_axiom_paths.
Print Assumptions switch_skip_positive.
Print Assumptions switch_countdown.
Print Assumptions regular_axiom_entry.
Print Assumptions final_axiom_entry.
Print Assumptions axiom_context_after_parent.
Print Assumptions switch_axiom_dispatch.
