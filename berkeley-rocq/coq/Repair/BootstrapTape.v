(** Two-cell compressed tapes. Counts are binary positives, while the denoted
    tapes and all runs are BusyCoq's ordinary infinite streams. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia NArith PArith.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine RuntimeTape RuntimeControl.
Import ListNotations.

Definition boot_pair := (bool * bool)%type.
Definition boot_swap (p : boot_pair) : boot_pair := (snd p,fst p).
Definition boot_zero : boot_pair := (false,false).
Definition boot_block := (boot_pair * positive)%type.
Definition boot_stack := list boot_block.

Fixpoint pair_copies n (p : boot_pair) (r : side) : side :=
  match n with
  | 0 => r
  | S n => Cons (fst p) (Cons (snd p) (pair_copies n p r))
  end.
Fixpoint pair_stack (swapped : bool) (s : boot_stack) : side :=
  match s with
  | [] => blank
  | (p,n)::s => pair_copies (Pos.to_nat n) (if swapped then boot_swap p else p)
                             (pair_stack swapped s)
  end.
Definition pair_eqb (p q : boot_pair) : bool :=
  andb (Bool.eqb (fst p) (fst q)) (Bool.eqb (snd p) (snd q)).
Lemma pair_eqb_spec p q : pair_eqb p q = true <-> p = q.
Proof.
  destruct p as [a b], q as [c d]. unfold pair_eqb; simpl.
  rewrite andb_true_iff, !Bool.eqb_true_iff. split; intros H.
  - destruct H as [-> ->]. reflexivity.
  - inversion H; auto.
Qed.

Lemma pair_copies_add n m p r :
  pair_copies (n+m) p r = pair_copies n p (pair_copies m p r).
Proof. induction n; simpl; [reflexivity|now rewrite IHn]. Qed.
Lemma pair_copies_snoc n p r :
  pair_copies n p (Cons (fst p) (Cons (snd p) r)) =
  Cons (fst p) (Cons (snd p) (pair_copies n p r)).
Proof. induction n; simpl; [reflexivity|now rewrite IHn]. Qed.
Lemma pair_copies_blank n : pair_copies n boot_zero blank = blank.
Proof.
  induction n; [reflexivity|]. simpl. rewrite IHn.
  rewrite <- const_unfold. rewrite <- const_unfold. reflexivity.
Qed.

Definition pair_push (p : boot_pair) (n : positive) (s : boot_stack) : boot_stack :=
  match s with
  | [] => if pair_eqb p boot_zero then [] else [(p,n)]
  | (q,m)::s => if pair_eqb p q then (p,Pos.add n m)::s else (p,n)::(q,m)::s
  end.
Definition pair_pop (s : boot_stack) : boot_pair * boot_stack :=
  match s with
  | [] => (boot_zero,[])
  | (p,xH)::s => (p,s)
  | (p,n)::s => (p,(p,Pos.pred n)::s)
  end.

Lemma pair_push_correct flip p n s :
  pair_stack flip (pair_push p n s) =
  pair_copies (Pos.to_nat n) (if flip then boot_swap p else p) (pair_stack flip s).
Proof.
  destruct s as [|[q m] s]; simpl [pair_push pair_stack].
  - destruct (pair_eqb p boot_zero) eqn:E.
    + apply pair_eqb_spec in E; subst p. destruct flip; symmetry; apply pair_copies_blank.
    + reflexivity.
  - destruct (pair_eqb p q) eqn:E; [apply pair_eqb_spec in E; subst q|]; simpl [pair_stack].
    + rewrite Pos2Nat.inj_add, pair_copies_add. reflexivity.
    + reflexivity.
Qed.

Lemma positive_pred_nat n : n <> xH -> S (Pos.to_nat (Pos.pred n)) = Pos.to_nat n.
Proof.
  intro H. rewrite Pos2Nat.inj_pred_max. pose proof (Pos2Nat.is_pos n).
  assert (Pos.to_nat n <> 1).
  { intro E. apply H. apply Pos2Nat.inj. cbn. exact E. }
  lia.
Qed.
Lemma pair_pop_correct flip s :
  let '(p,s') := pair_pop s in
  pair_stack flip s = Cons (fst (if flip then boot_swap p else p))
    (Cons (snd (if flip then boot_swap p else p)) (pair_stack flip s')).
Proof.
  destruct s as [|[p n] s].
  - destruct flip; simpl [pair_pop pair_stack boot_swap boot_zero];
      rewrite <- const_unfold; rewrite <- const_unfold; reflexivity.
  - destruct n as [n|n|]; simpl [pair_pop pair_stack].
    + reflexivity.
    + pose proof (positive_pred_nat (xO n) ltac:(discriminate)) as H.
      cbn [Pos.to_nat] in H. rewrite <- H. reflexivity.
    + reflexivity.
Qed.

Lemma scan_pair_R q q1 a b wa wb n l r :
  edge q a wa R q1 -> edge q1 b wb R q ->
  Runs (CR q l (pair_copies n (a,b) r))
       (CR q (pair_copies n (wb,wa) l) r).
Proof.
  intros E1 E2. revert l. induction n; intro l; simpl; [apply runs_refl|].
  eapply runs_trans; [apply step_RR; exact E1|].
  eapply runs_trans; [apply step_RR; exact E2|].
  specialize (IHn (Cons wb (Cons wa l))).
  pose proof (pair_copies_snoc n (wb,wa) l) as H. cbn in H.
  exact (eq_ind _ (fun l0 => Runs (CR q (Cons wb (Cons wa l))
             (pair_copies n (a,b) r)) (CR q l0 r)) IHn _ H).
Qed.
Lemma scan_pair_L q q1 a b wa wb n l r :
  edge q a wa L q1 -> edge q1 b wb L q ->
  Runs (CL q (pair_copies n (a,b) l) r)
       (CL q l (pair_copies n (wb,wa) r)).
Proof.
  intros E1 E2. revert r. induction n; intro r; simpl; [apply runs_refl|].
  eapply runs_trans; [apply step_LL; exact E1|].
  eapply runs_trans; [apply step_LL; exact E2|].
  specialize (IHn (Cons wb (Cons wa r))).
  pose proof (pair_copies_snoc n (wb,wa) r) as H. cbn in H.
  exact (eq_ind _ (fun r0 => Runs (CL q (pair_copies n (a,b) l)
             (Cons wb (Cons wa r))) (CL q l r0)) IHn _ H).
Qed.

Print Assumptions pair_push_correct.
Print Assumptions pair_pop_correct.
Print Assumptions scan_pair_R.
Print Assumptions scan_pair_L.
