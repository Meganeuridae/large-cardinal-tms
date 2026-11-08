(** The register-level arithmetic of the ZF2 constructor subroutines.

    This file runs the countdown algorithms for pair/unpair from
    ConstructorArithmetic, including scratch-register handling.  It does
    not claim that the compiled decision DAG executes these programs. *)
From Stdlib Require Import Arith.Arith Lia.
From Berkeley Require Import ConstructorArithmetic.

Record constructor_registers := CR {
  top : nat;
  stack : nat;
  scratch1 : nat;
  scratch2 : nat
}.

(** [pushwff]: pair scratch1 topwff wffstack; move scratch1 to
    wffstack. The source pair routine starts with the existing scratch1. *)
Definition source_push (r : constructor_registers) : option constructor_registers :=
  match pair_routine (S (top r + stack r)) (top r) (stack r) (scratch1 r) with
  | None => None
  | Some (t,s,x) =>
      let '(x',s') := transfer1 x s in Some (CR t s' x' (scratch2 r))
  end.

Theorem source_push_correct t s x y :
  source_push (CR t s x y) = Some (CR 0 (x + cantor t s) 0 y).
Proof.
  unfold source_push. cbn [top stack scratch1 scratch2].
  rewrite pair_routine_correct by lia. rewrite transfer1_correct. reflexivity.
Qed.

(** [cons]: unpair scratch1 scratch2 wffstack; move scratch2 back to
    wffstack; pair scratch2 scratch1 topwff; move scratch2 to topwff. *)
Definition source_cons (r : constructor_registers) : option constructor_registers :=
  let '(s,x,y) := unpair_routine (stack r) (scratch1 r) (scratch2 r) in
  let '(y',s') := transfer1 y s in
  match pair_routine (S (x + top r)) x (top r) y' with
  | None => None
  | Some (x',t,y'') =>
      let '(y''',t') := transfer1 y'' t in Some (CR t' s' x' y''')
  end.

Theorem source_cons_correct t a rest :
  source_cons (CR t (cantor a rest) 0 0) = Some (CR (cantor a t) rest 0 0).
Proof.
  unfold source_cons. cbn [top stack scratch1 scratch2].
  rewrite unpair_routine_correct, transfer1_correct.
  rewrite pair_routine_correct by lia. rewrite transfer1_correct. reflexivity.
Qed.

(** Every natural stack register has a Cantor decomposition, including 0;
    the source cons routine therefore has a result on every numeric stack. *)
Theorem source_cons_total t s :
  source_cons (CR t s 0 0) =
    let '(a,rest) := uncantor s in Some (CR (cantor a t) rest 0 0).
Proof.
  pose proof (cantor_uncantor s) as H.
  destruct (uncantor s) as [a rest]. simpl in H. subst s.
  apply source_cons_correct.
Qed.

Definition increment_top n (r : constructor_registers) :=
  CR (top r+n) (stack r) (scratch1 r) (scratch2 r).

(** The parameter routine pushes first, transfers the parameter into the
    top and scratch1, then restores it from scratch1.  The returned second
    component records the parameter register, to expose its preservation. *)
Definition source_param (p : nat) (r : constructor_registers)
    : option (constructor_registers * nat) :=
  match source_push r with
  | None => None
  | Some r' =>
      let '(p',t,x) := transfer2 p (top r') (scratch1 r') in
      let '(x',p'') := transfer1 x p' in
      Some (CR t (stack r') x' (scratch2 r'),p'')
  end.

Theorem source_param_correct p t s y :
  source_param p (CR t s 0 y) = Some (CR p (cantor t s) 0 y,p).
Proof.
  unfold source_param. rewrite source_push_correct. cbn [Nat.add_0_l].
  rewrite transfer2_correct. simpl. rewrite transfer1_correct. reflexivity.
Qed.

Print Assumptions source_push_correct.
Print Assumptions source_cons_correct.
Print Assumptions source_cons_total.
Print Assumptions source_param_correct.
