From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

Inductive variable := V (n : nat) | P (n : nat).
Inductive formula :=
| Atom (membership : bool) (x y : variable)
| Neg (p : formula)
| Imp (p q : formula)
| All (x : variable) (p : formula)
| Hole (n : nat).

Definition var_token x := match x with V n => 16+n | P n => 8+n end.
Fixpoint emit (f : formula) : list nat :=
  match f with
  | Atom b x y => [var_token x; var_token y; if b then 1 else 0]
  | Neg p => emit p ++ [2]
  | Imp p q => emit p ++ emit q ++ [3]
  | All x p => [var_token x] ++ emit p ++ [4]
  | Hole n => [8+n]
  end.
Inductive symbol := Terminal (n : nat) | Reference (n : nat).
Definition expand_symbol (env : list (list nat)) (s : symbol) :=
  match s with Terminal n => [n] | Reference n => nth n env [] end.
Definition expand_word env s := flat_map (expand_symbol env) s.
Fixpoint definitions (rules : list (symbol * symbol)) (env : list (list nat)) :=
  match rules with
  | [] => env
  | (a,b)::rs => definitions rs (env ++ [expand_symbol env a ++ expand_symbol env b])
  end.

Definition var_eqb a b :=
  match a,b with V n,V m | P n,P m => Nat.eqb n m | _,_ => false end.
Fixpoint index x (env : list variable) :=
  match env with
  | [] => None
  | y::ys => if var_eqb x y then Some 0 else option_map S (index x ys)
  end.
Inductive db_variable := Bound (n : nat) | Free (x : variable).
Definition db_name x env := match index x env with Some n => Bound n | None => Free x end.
Inductive db_formula :=
| DBAtom (membership : bool) (x y : db_variable)
| DBNeg (p : db_formula)
| DBImp (p q : db_formula)
| DBAll (p : db_formula)
| DBHole (n : nat).
Fixpoint canonical f env :=
  match f with
  | Atom b x y => DBAtom b (db_name x env) (db_name y env)
  | Neg p => DBNeg (canonical p env)
  | Imp p q => DBImp (canonical p env) (canonical q env)
  | All x p => DBAll (canonical p (x::env))
  | Hole n => DBHole n
  end.
