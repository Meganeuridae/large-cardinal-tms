(** Source-pair contexts and their statically checked axiom-dispatch paths. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
From Berkeley Require Import CompilerSyntax CompilerData CompilerReverse.
Import ListNotations.

Theorem source_select_in_context program start prefix subtree suffix leaf :
  SourcePrefix program start prefix subtree ->
  SourceSelect program subtree suffix leaf ->
  SourceSelect program start (prefix ++ suffix) leaf.
Proof.
  intros P S. induction P as [i|i pair b j bits last Pair Branch P IH].
  - exact S.
  - simpl. eapply select_node with (pair:=pair) (j:=j); [exact Pair|exact Branch|].
    apply IH. exact S.
Qed.

Fixpoint source_prefix_find (program : list source_pair) start bits : option nat :=
  match bits with
  | [] => Some start
  | b::tail =>
      match nth_error program start with
      | Some p => match select_branch p b with
                     | SNode next => source_prefix_find program next tail
                     | _ => None
                     end
      | None => None
      end
  end.
Theorem source_prefix_find_sound program start bits subtree :
  source_prefix_find program start bits = Some subtree ->
  SourcePrefix program start bits subtree.
Proof.
  revert start. induction bits as [|b bits IH]; intros start E.
  - cbn [source_prefix_find] in E. inversion E; subst. constructor.
  - cbn [source_prefix_find] in E.
    destruct (nth_error program start) as [pair|] eqn:P; [|discriminate].
    destruct (select_branch pair b) as [next| | | | |] eqn:B; try discriminate.
    eapply source_prefix_cons; [exact P|exact B|]. now apply IH.
Qed.

(** The first 18 right choices reach main's dispatch instruction; the next
    left choice enters the switch.  Cases 3..25 use the ordinary branch
    shape.  The last case (opcode 26, Berkeley) is the final right spine
    and is represented without an extra pair wrapping the last branch. *)
Definition axiom_dispatch_context i :=
  repeat true 18 ++ [false] ++
    if i <? 23 then repeat true (i+3) ++ [false;true;true;false]
    else repeat true 28 ++ [false].

Definition context_check i :=
  match source_prefix_find source_graph source_root (axiom_dispatch_context i),
        nth_error source_residual_roots i with
  | Some found, Some expected => Nat.eqb found expected
  | _,_ => false
  end.
Lemma axiom_dispatch_contexts_certificate :
  forallb context_check (seq 0 (length source_residual_roots)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem axiom_dispatch_context_is_source_prefix i root :
  nth_error source_residual_roots i = Some root ->
  SourcePrefix source_graph source_root (axiom_dispatch_context i) root.
Proof.
  intro R. pose proof axiom_dispatch_contexts_certificate as C.
  rewrite forallb_forall in C.
  assert (I : In i (seq 0 (length source_residual_roots))).
  { apply in_seq. assert (H : i < length source_residual_roots).
    { apply nth_error_Some. rewrite R. discriminate. } lia. }
  specialize (C i I). unfold context_check in C. rewrite R in C.
  destruct (source_prefix_find source_graph source_root (axiom_dispatch_context i))
    as [found|] eqn:F; [|discriminate].
  apply Nat.eqb_eq in C. subst found. now apply source_prefix_find_sound.
Qed.

Theorem axiom_dispatch_selects_residual_leaf i root suffix leaf :
  nth_error source_residual_roots i = Some root ->
  SourceSelect source_graph root suffix leaf ->
  SourceSelect source_graph source_root (axiom_dispatch_context i ++ suffix) leaf.
Proof.
  intros R S. eapply source_select_in_context with (subtree:=root).
  - apply axiom_dispatch_context_is_source_prefix. exact R.
  - exact S.
Qed.

Print Assumptions source_select_in_context.
Print Assumptions source_prefix_find_sound.
Print Assumptions axiom_dispatch_context_is_source_prefix.
Print Assumptions axiom_dispatch_selects_residual_leaf.
