(** Independent instruction trees for the source constructor routines,
    checked against the extracted builder DAG.  The tree uses relative
    continue labels as in the builder; it is not an operational semantics. *)
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
From Berkeley Require Import CompilerSyntax.
From Repair Require Import CompilerData ConstructorData.
Import ListNotations.

Inductive constructor_tree :=
| CTInc (reg : nat)
| CTDec (reg : nat)
| CTHalt
| CTBreak (depth : nat)
| CTContinue (depth : nat)
| CTSeq (left right : constructor_tree).

Fixpoint constructor_tree_eqb a b :=
  match a,b with
  | CTInc x, CTInc y | CTDec x, CTDec y | CTBreak x, CTBreak y
  | CTContinue x, CTContinue y => Nat.eqb x y
  | CTHalt, CTHalt => true
  | CTSeq a1 a2, CTSeq b1 b2 => constructor_tree_eqb a1 b1 && constructor_tree_eqb a2 b2
  | _,_ => false
  end.
Lemma constructor_tree_eqb_sound a b : constructor_tree_eqb a b = true -> a=b.
Proof.
  revert b. induction a as [x|x| |x|x|a1 IH1 a2 IH2]; intros b H;
    destruct b; cbn in H; try discriminate; try reflexivity;
    try (apply Nat.eqb_eq in H; now subst).
  apply andb_true_iff in H as [H1 H2]. apply IH1 in H1. apply IH2 in H2. now subst.
Qed.
Definition maybe_tree_eqb a b :=
  match a,b with
  | Some x,Some y => constructor_tree_eqb x y
  | None,None => true
  | _,_ => false
  end.
Lemma maybe_tree_eqb_sound a b : maybe_tree_eqb a b = true -> a=b.
Proof.
  destruct a,b; cbn; try discriminate; try reflexivity.
  intro H. apply constructor_tree_eqb_sound in H. now subst.
Qed.

(** Every row of this untrusted, small lookup table is checked against the
    literal source DAG; it only makes normalization of certificates cheap. *)
Definition source_atom_eq_dec (a b : source_atom) : {a=b}+{a<>b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition source_pair_eq_dec (a b : source_pair) : {a=b}+{a<>b}.
Proof. decide equality; apply source_atom_eq_dec. Defined.

Fixpoint constructor_lookup i (nodes : list (nat * source_pair)) :=
  match nodes with
  | [] => None
  | (j,p)::rest => if Nat.eqb i j then Some p else constructor_lookup i rest
  end.
Definition check_constructor_node entry :=
  let '(i,p) := entry in
  match nth_error source_graph i with
  | Some q => if source_pair_eq_dec q p then true else false
  | None => false
  end.
Lemma constructor_nodes_certificate : forallb check_constructor_node constructor_nodes = true.
Proof. vm_compute. reflexivity. Qed.

Lemma constructor_lookup_in i p nodes : constructor_lookup i nodes = Some p -> In (i,p) nodes.
Proof.
  induction nodes as [|[j q] nodes IH]; cbn; [discriminate|].
  destruct (Nat.eqb i j) eqn:E.
  - intro H. apply Nat.eqb_eq in E. inversion H; subst. now left.
  - intro H. right. now apply IH.
Qed.
Lemma constructor_lookup_sound i p : constructor_lookup i constructor_nodes = Some p ->
  nth_error source_graph i = Some p.
Proof.
  intro H. pose proof (constructor_lookup_in _ _ _ H) as I.
  pose proof (proj1 (forallb_forall check_constructor_node constructor_nodes)
                constructor_nodes_certificate (i,p) I) as C.
  unfold check_constructor_node in C.
  destruct (nth_error source_graph i) as [q|] eqn:E; [|discriminate].
  destruct (source_pair_eq_dec q p) as [F|F]; [now subst|discriminate].
Qed.

(** A finite unfolding fails on a missing node or insufficient fuel. *)
Fixpoint unfold_with (lookup : nat -> option source_pair) (fuel : nat) (a : source_atom)
    : option constructor_tree :=
  match fuel with
  | 0 => None
  | S rest =>
      match a with
      | SInc r => Some (CTInc r)
      | SDec r => Some (CTDec r)
      | SHalt => Some CTHalt
      | SBreak k => Some (CTBreak k)
      | SContinue k => Some (CTContinue k)
      | SNode i =>
          match lookup i with
          | None => None
          | Some (l,r) =>
              match unfold_with lookup rest l, unfold_with lookup rest r with
              | Some x, Some y => Some (CTSeq x y)
              | _,_ => None
              end
          end
      end
  end.
Definition unfold_root i := unfold_with (nth_error source_graph) 64 (SNode i).
Definition unfold_small i := unfold_with (fun n => constructor_lookup n constructor_nodes) 64 (SNode i).

Lemma unfold_small_sound fuel a t :
  unfold_with (fun n => constructor_lookup n constructor_nodes) fuel a = Some t ->
  unfold_with (nth_error source_graph) fuel a = Some t.
Proof.
  revert a t. induction fuel as [|fuel IH]; intros a t H; [discriminate|].
  destruct a as [i|r|r| |k|k]; cbn [unfold_with] in *; try assumption.
  destruct (constructor_lookup i constructor_nodes) as [[l r]|] eqn:E; [|discriminate].
  rewrite (constructor_lookup_sound _ _ E).
  destruct (unfold_with (fun n => constructor_lookup n constructor_nodes) fuel l) as [x|] eqn:L;
    [|discriminate].
  destruct (unfold_with (fun n => constructor_lookup n constructor_nodes) fuel r) as [y|] eqn:R;
    [|discriminate].
  inversion H; subst. rewrite (IH _ _ L), (IH _ _ R). reflexivity.
Qed.

(** Register indices are the builder's allocation order:
    topwff=2, wffstack=3, param1..3=5..7, scratch1=8, scratch2=9. *)
Definition tree_while1 input output :=
  CTSeq (CTDec input) (CTSeq (CTInc output) (CTContinue 2)).
Definition tree_while2 input output1 output2 :=
  CTSeq (CTDec input) (CTSeq (CTSeq (CTInc output1) (CTInc output2)) (CTContinue 2)).

(** These are the two outer loops in TMBuilder.pair and unpair, written
    from their source structure rather than by naming a graph subtree. *)
Definition tree_pair input1 input2 output :=
  CTSeq (tree_while2 input1 input2 output)
    (CTSeq (CTDec input2)
      (CTSeq (CTSeq (CTInc output) (tree_while1 input2 input1)) (CTContinue 3))).
Definition tree_unpair input output1 output2 :=
  CTSeq (CTDec input)
    (CTSeq (CTInc output1)
      (CTSeq (CTSeq (CTDec output2) (CTContinue 3))
             (CTSeq (tree_while1 output1 output2) (CTContinue 4)))).

Definition tree_push := CTSeq (tree_pair 2 3 8) (tree_while1 8 3).
Definition tree_cons :=
  CTSeq (tree_unpair 3 8 9)
    (CTSeq (tree_while1 9 3)
      (CTSeq (tree_pair 8 2 9) (tree_while1 9 2))).
Definition tree_param p :=
  CTSeq tree_push (CTSeq (tree_while2 p 2 8) (tree_while1 8 p)).

(** The inherited v_1..v_4 splice the v_0 body and append increments.
    The separate build.py variable routine instead nests variable(n-1). *)
Fixpoint tree_increments (n : nat) : constructor_tree :=
  match n with 0 => CTInc 2 | S k => CTSeq (CTInc 2) (tree_increments k) end.
Definition tree_v tag :=
  CTSeq (tree_pair 2 3 8)
    (match tag with
     | 0 => tree_while1 8 3
     | S n => CTSeq (tree_while1 8 3) (tree_increments n)
     end).
Fixpoint tree_variable n :=
  match n with 0 => tree_push | S k => CTSeq (tree_variable k) (CTInc 2) end.
Definition tree_binary tag := CTSeq tree_cons (CTSeq (tree_v tag) tree_cons).
Definition tree_not := CTSeq (tree_v 3) tree_cons.

Definition expected_token_tree tok :=
  match tok with
  | 0 => Some (tree_binary 0)
  | 1 => Some (tree_binary 1)
  | 2 => Some tree_not
  | 3 => Some (tree_binary 2)
  | 4 => Some (tree_binary 4)
  | 9 => Some (tree_param 5)
  | 10 => Some (tree_param 6)
  | 11 => Some (tree_param 7)
  | _ => if (16 <=? tok) && (tok <=? 26)
         then Some (tree_variable (tok-16)) else None
  end.

Definition token_tree_check entry :=
  let '(tok,root) := entry in
  maybe_tree_eqb (unfold_small root) (expected_token_tree tok).
Lemma token_tree_check_small_sound tok root : token_tree_check (tok,root) = true ->
  unfold_small root = expected_token_tree tok.
Proof. unfold token_tree_check. apply maybe_tree_eqb_sound. Qed.
Lemma unfold_small_root_sound root t : unfold_small root = Some t -> unfold_root root = Some t.
Proof. unfold unfold_small, unfold_root. apply unfold_small_sound. Qed.
Lemma token_tree_certificate : forallb token_tree_check source_token_roots = true.
Proof. vm_compute. reflexivity. Qed.

Definition token_tree_supported (entry : nat * nat) :=
  match expected_token_tree (fst entry) with Some _ => true | None => false end.
Lemma token_tree_support_certificate : forallb token_tree_supported source_token_roots = true.
Proof. vm_compute. reflexivity. Qed.

Lemma small_routine_trees :
  unfold_small source_pushwff_root = Some tree_push /\
  unfold_small source_cons_root = Some tree_cons /\
  unfold_small source_par1_root = Some (tree_param 5) /\
  unfold_small source_par2_root = Some (tree_param 6) /\
  unfold_small source_par3_root = Some (tree_param 7).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma small_internal_trees :
  unfold_small 8 = Some (tree_pair 2 3 8) /\
  unfold_small 39 = Some (tree_pair 8 2 9) /\
  unfold_small 29 = Some (tree_unpair 3 8 9) /\
  unfold_small 2 = Some (tree_while2 2 3 8) /\
  unfold_small 4 = Some (tree_while1 3 2) /\
  unfold_small 33 = Some (tree_while2 8 2 9) /\
  unfold_small 35 = Some (tree_while1 2 8) /\
  unfold_small 24 = Some (tree_while1 8 9).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Avoid repeatedly normalizing the large concrete source DAG while the
    general soundness lemmas below are checked. *)
Opaque source_graph constructor_nodes source_token_roots expected_token_tree
  token_tree_check unfold_small unfold_root.

Theorem source_token_has_expected_tree tok root t : In (tok,root) source_token_roots ->
  expected_token_tree tok = Some t -> unfold_root root = Some t.
Proof.
  intros H T. pose proof (proj1 (forallb_forall token_tree_check source_token_roots)
                       token_tree_certificate (tok,root) H) as C.
  apply token_tree_check_small_sound in C. rewrite T in C.
  now apply unfold_small_root_sound.
Qed.

Theorem source_routine_trees :
  unfold_root source_pushwff_root = Some tree_push /\
  unfold_root source_cons_root = Some tree_cons /\
  unfold_root source_par1_root = Some (tree_param 5) /\
  unfold_root source_par2_root = Some (tree_param 6) /\
  unfold_root source_par3_root = Some (tree_param 7).
Proof.
  destruct small_routine_trees as [A [B [C [D E]]]].
  repeat split; eapply unfold_small_root_sound; eassumption.
Qed.

Theorem source_internal_trees :
  unfold_root 8 = Some (tree_pair 2 3 8) /\
  unfold_root 39 = Some (tree_pair 8 2 9) /\
  unfold_root 29 = Some (tree_unpair 3 8 9) /\
  unfold_root 2 = Some (tree_while2 2 3 8) /\
  unfold_root 4 = Some (tree_while1 3 2) /\
  unfold_root 33 = Some (tree_while2 8 2 9) /\
  unfold_root 35 = Some (tree_while1 2 8) /\
  unfold_root 24 = Some (tree_while1 8 9).
Proof.
  destruct small_internal_trees as [A [B [C [D [E [F [G H]]]]]]].
  repeat split; eapply unfold_small_root_sound; eassumption.
Qed.

Print Assumptions source_token_has_expected_tree.
Print Assumptions source_routine_trees.
Print Assumptions source_internal_trees.
