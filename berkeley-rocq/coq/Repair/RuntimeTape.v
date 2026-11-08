(** Tape algebra and symbolic steps for the literal 1,399-state machine. *)
From Stdlib Require Import Lists.List Streams.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine.
From Repair Require Import Data Machine.
Import ListNotations.

Definition st := bounded_mk new_count.
Definition side := Stream bool.
Definition cfg := (NewCtx.Q * (side * bool * side))%type.
Definition CR q (l r : side) : cfg := (st q, (l, hd r, tl r)).
Definition CL q (l r : side) : cfg := (st q, (tl l, hd l, r)).
Definition Runs := New.evstep new_tm.
Definition edge q a w d q' := new_tm (st q,a) = Some (w,d,st q').

Lemma runs_refl c : Runs c c. Proof. constructor. Qed.
Lemma runs_trans a b c : Runs a b -> Runs b c -> Runs a c.
Proof. apply New.evstep_trans. Qed.
Lemma step_RR q q' a w l r : edge q a w R q' ->
  Runs (CR q l (Cons a r)) (CR q' (Cons w l) r).
Proof. intro H. apply New.evstep_one, New.step_right. exact H. Qed.
Lemma step_RL q q' a w l r : edge q a w L q' ->
  Runs (CR q l (Cons a r)) (CL q' l (Cons w r)).
Proof. intro H. apply New.evstep_one, New.step_left. exact H. Qed.
Lemma step_LL q q' a w l r : edge q a w L q' ->
  Runs (CL q (Cons a l) r) (CL q' l (Cons w r)).
Proof. intro H. apply New.evstep_one, New.step_left. exact H. Qed.
Lemma step_LR q q' a w l r : edge q a w R q' ->
  Runs (CL q (Cons a l) r) (CR q' (Cons w l) r).
Proof. intro H. apply New.evstep_one, New.step_right. exact H. Qed.

Fixpoint copies n (b : bool) (r : side) :=
  match n with 0 => r | S n => Cons b (copies n b r) end.
Lemma copies_snoc n b r : copies n b (Cons b r) = Cons b (copies n b r).
Proof. induction n; simpl; [reflexivity|now rewrite IHn]. Qed.
Lemma copies_add n m b r : copies (n+m) b r = copies n b (copies m b r).
Proof. induction n; simpl; [reflexivity|now rewrite IHn]. Qed.
Lemma scan_R q a w n l r : edge q a w R q ->
  Runs (CR q l (copies n a r)) (CR q (copies n w l) r).
Proof.
  intro H. revert l. induction n; intro l; simpl.
  - apply runs_refl.
  - eapply runs_trans; [apply step_RR; exact H|].
    rewrite <- copies_snoc. apply IHn.
Qed.
Lemma scan_L q a w n l r : edge q a w L q ->
  Runs (CL q (copies n a l) r) (CL q l (copies n w r)).
Proof.
  intro H. revert r. induction n; intro r; simpl.
  - apply runs_refl.
  - eapply runs_trans; [apply step_LL; exact H|].
    rewrite <- copies_snoc. apply IHn.
Qed.

(** Value n is represented by n+1 ones and a separating zero. *)
Definition reg n r := copies (S n) true (Cons false r).
Fixpoint regs (ns : list nat) r :=
  match ns with [] => r | n::ns => reg n (regs ns r) end.
Definition back_reg n l := Cons false (copies (S n) true l).
Fixpoint back (ns : list nat) l :=
  match ns with [] => l | n::ns => back ns (back_reg n l) end.
Lemma regs_append xs ys r : regs (xs++ys) r = regs xs (regs ys r).
Proof. induction xs; simpl; [reflexivity|now rewrite IHxs]. Qed.
Lemma back_append xs ys l : back (xs++ys) l = back ys (back xs l).
Proof. revert l. induction xs; intro l; simpl; [reflexivity|apply IHxs]. Qed.

Ltac rr q' w :=
  lazymatch goal with
  | |- Runs (CR ?q ?l (Cons ?a ?r)) ?c =>
    eapply (runs_trans _ (CR q' (Cons w l) r));
      [apply step_RR; reflexivity|]
  end.
Ltac rl q' w :=
  lazymatch goal with
  | |- Runs (CR ?q ?l (Cons ?a ?r)) ?c =>
    eapply (runs_trans _ (CL q' l (Cons w r)));
      [apply step_RL; reflexivity|]
  end.
Ltac ll q' w :=
  lazymatch goal with
  | |- Runs (CL ?q (Cons ?a ?l) ?r) ?c =>
    eapply (runs_trans _ (CL q' l (Cons w r)));
      [apply step_LL; reflexivity|]
  end.
Ltac lr q' w :=
  lazymatch goal with
  | |- Runs (CL ?q (Cons ?a ?l) ?r) ?c =>
    eapply (runs_trans _ (CR q' (Cons w l) r));
      [apply step_LR; reflexivity|]
  end.
