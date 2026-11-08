From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia Eqdep_dec.
From BusyCoq Require Import TM.
From Berkeley Require Import StateMap.
Import ListNotations.

(** Boolean-bounded naturals, also used in K230's BusyCoq interface. *)
Definition bounded (k : nat) := {n : nat | Nat.leb n k = true}.
Definition val {k} (x : bounded k) := proj1_sig x.
Definition bounded_mk (k n : nat) : bounded k :=
  match Nat.leb n k as b return Nat.leb n k = b -> bounded k with
  | true => fun H => exist _ n H
  | false => fun _ => exist _ k (Nat.leb_refl k)
  end eq_refl.
Lemma bounded_eq k (x y : bounded k) : val x = val y -> x = y.
Proof.
  destruct x as [x Hx], y as [y Hy]; simpl. intros ->.
  f_equal. apply UIP_dec, bool_dec.
Qed.
Lemma val_bound k (x : bounded k) : val x <= k.
Proof. destruct x as [n H]. apply Nat.leb_le, H. Qed.
Lemma val_mk k n : n <= k -> val (bounded_mk k n) = n.
Proof.
  intro H. unfold bounded_mk.
  generalize (@eq_refl bool (Nat.leb n k)).
  generalize (Nat.leb n k) at 2 3. intros b E. destruct b; [reflexivity|].
  apply Nat.leb_nle in E. lia.
Qed.
Definition bounded_dec {k} (x y : bounded k) : {x=y}+{x<>y}.
Proof.
  destruct (Nat.eq_dec (val x) (val y)) as [E|E].
  - left. apply bounded_eq, E.
  - right. intro H. apply E. now rewrite H.
Defined.

Module Type Size.
  Parameter top : nat.
  Parameter positive : 1 <= top.
End Size.
Module Binary (S : Size) <: BinaryCtx.
  Definition Q := bounded S.top.
  Definition Sym := bool.
  Definition q0 : Q := bounded_mk S.top 0.
  Definition q1 : Q := bounded_mk S.top 1.
  Definition s0 := false.
  Definition s1 := true.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof.
    intro E. apply (f_equal val) in E. unfold q0, q1 in E.
    rewrite !val_mk in E by (pose proof S.positive; lia). discriminate.
  Qed.
  Lemma s0_neq_s1 : s0 <> s1. Proof. discriminate. Qed.
  Definition eqb_q := @bounded_dec S.top.
  Definition eqb_sym := bool_dec.
  Definition all_qs := map (bounded_mk S.top) (seq 0 (S S.top)).
  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    intro a. assert (E : bounded_mk S.top (val a) = a).
    { apply bounded_eq, val_mk, val_bound. }
    rewrite <- E. apply in_map, in_seq. pose proof (val_bound _ a). lia.
  Qed.
  Definition all_syms := [false;true].
  Lemma all_syms_spec : forall a, In a all_syms.
  Proof. intros []; simpl; auto. Qed.
End Binary.

Definition transition := (bool * dir * nat)%type.
Definition row := (transition * transition)%type.
Definition lookup (table : list row) (q : nat) (b : bool) :=
  match nth_error table q with
  | None => None
  | Some (t0,t1) => Some (if b then t1 else t0)
  end.
Definition map_target (f : nat -> nat) (t : transition) :=
  let '(w,d,q) := t in (w,d,f q).
Definition transition_eqb (a b : transition) :=
  let '(wa,da,qa) := a in let '(wb,db,qb) := b in
  andb (andb (Bool.eqb wa wb)
    (match da,db with L,L | R,R => true | _,_ => false end)) (Nat.eqb qa qb).
Definition option_eqb (a b : option transition) :=
  match a,b with
  | None,None => true
  | Some x, Some y => transition_eqb x y
  | _,_ => false
  end.
Lemma option_eqb_sound a b : option_eqb a b = true -> a = b.
Proof.
  destruct a as [[[wa da] qa]|], b as [[[wb db] qb]|]; simpl; try congruence.
  intro H. apply andb_true_iff in H as [H E]. apply andb_true_iff in H as [W D].
  apply Nat.eqb_eq in E. apply (proj1 (Bool.eqb_true_iff wa wb)) in W.
  destruct da,db; simpl in D; congruence.
Qed.
