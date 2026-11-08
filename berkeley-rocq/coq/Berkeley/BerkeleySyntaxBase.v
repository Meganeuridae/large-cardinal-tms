(** A hygienic, compositional first-order syntax builder.  The state supplies
    globally fresh named variables; the output is the existing primitive
    equality/membership/negation/implication/universal formula type. *)
From Stdlib Require Import Lists.List Arith.Arith.
From Berkeley Require Import Syntax.
Import ListNotations.

Definition builder := nat -> (formula * nat)%type.
Definition b_eq x y : builder := fun next => (Atom false (V x) (V y),next).
Definition b_mem x y : builder := fun next => (Atom true (V x) (V y),next).
Definition b_not (p : builder) : builder := fun next =>
  let '(a,next') := p next in (Neg a,next').
Definition b_binary (op : formula -> formula -> formula) (p q : builder) : builder := fun next =>
  let '(a,next') := p next in let '(b,next'') := q next' in (op a b,next'').
Definition b_imp := b_binary Imp.
Definition b_and := b_binary (fun p q => Neg(Imp p (Neg q))).
Definition b_or := b_binary (fun p q => Imp (Neg p) q).
Definition b_iff := b_binary (fun p q => Neg(Imp (Imp p q) (Neg(Imp q p)))).
Definition b_all (body : nat -> builder) : builder := fun next =>
  let '(p,next') := body next (S next) in (All (V next) p,next').
Definition b_ex (body : nat -> builder) : builder := b_not (b_all (fun v => b_not (body v))).
Definition b_ain a (body : nat -> builder) := b_all (fun v => b_imp (b_mem v a) (body v)).
Definition b_ein a (body : nat -> builder) := b_ex (fun v => b_and (b_mem v a) (body v)).
Definition b_and3 a b c := b_and (b_and a b) c.
Definition b_and4 a b c d := b_and (b_and3 a b c) d.
Definition b_and5 a b c d e := b_and (b_and4 a b c d) e.
Definition b_or3 a b c := b_or (b_or a b) c.

Definition b_empty a := b_all (fun x => b_not (b_mem x a)).
Definition b_subset a b := b_ain a (fun x => b_mem x b).
Definition b_singleton a x := b_all (fun z => b_iff (b_mem z a) (b_eq z x)).
Definition b_doubleton a x y := b_all (fun z => b_iff (b_mem z a) (b_or (b_eq z x) (b_eq z y))).
Definition b_pair p x y :=
  b_ex (fun u => b_ex (fun v => b_and3 (b_singleton u x) (b_doubleton v x y) (b_doubleton p u v))).
Definition b_rel r x y := b_ex (fun p => b_and (b_pair p x y) (b_mem p r)).
Definition b_node2 p tag x y := b_ex (fun q => b_and (b_pair q x y) (b_pair p tag q)).

Definition b_transitive a := b_ain a (fun x => b_ain x (fun y => b_mem y a)).
Definition b_ordinal a := b_and (b_transitive a)
  (b_ain a (fun x => b_ain a (fun y => b_or3 (b_mem x y) (b_eq x y) (b_mem y x)))).

(** Exact graph of a total, single-valued function a -> b. *)
Definition b_function f a b := b_and
  (b_ain f (fun p => b_ein a (fun x => b_ein b (fun y => b_pair p x y))))
  (b_ain a (fun x => b_ein b (fun y => b_and (b_rel f x y)
    (b_ain b (fun z => b_imp (b_rel f x z) (b_eq z y)))))).

Definition b_bijection f a b := b_and3 (b_function f a b)
  (b_ain b (fun y => b_ein a (fun x => b_rel f x y)))
  (b_ain a (fun x => b_ain a (fun z => b_ain b (fun y =>
    b_imp (b_and (b_rel f x y) (b_rel f z y)) (b_eq x z))))).

Definition b_cardinal d := b_and (b_ordinal d)
  (b_ain d (fun a => b_not (b_ex (fun f => b_bijection f a d)))).
Definition b_successor y x := b_all (fun z =>
  b_iff (b_mem z y) (b_or (b_mem z x) (b_eq z x))).
Definition b_inductive a := b_and
  (b_ein a (fun e => b_empty e))
  (b_ain a (fun x => b_ein a (fun y => b_successor y x))).
Definition b_omega w := b_and (b_inductive w)
  (b_all (fun a => b_imp (b_inductive a) (b_subset w a))).
