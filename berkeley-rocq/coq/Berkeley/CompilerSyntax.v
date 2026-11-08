(** Binary source DAG after the builder's sequence-to-cons transformation.
    A node names a pair, not a machine state.  Numeric references preserve
    shared subroutines without expanding the DAG exponentially. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.

Inductive source_atom :=
| SNode (index : nat)
| SInc (register : nat)
| SDec (register : nat)
| SHalt
| SBreak (level : nat)
| SContinue (level : nat).

Definition source_pair := (source_atom * source_atom)%type.
Definition select_branch (pair : source_pair) (b : bool) : source_atom :=
  if b then snd pair else fst pair.

Definition is_leaf (a : source_atom) : bool :=
  match a with SNode _ => false | _ => true end.

(** Select from the source by descending the pair tree.  The bits consumed
    are exactly the source PC word; no TM transition appears in this rule. *)
Inductive SourceSelect (program : list source_pair) : nat -> list bool -> source_atom -> Prop :=
| select_leaf i pair b leaf :
    nth_error program i = Some pair -> select_branch pair b = leaf ->
    is_leaf leaf = true -> SourceSelect program i [b] leaf
| select_node i pair b j bits leaf :
    nth_error program i = Some pair -> select_branch pair b = SNode j ->
    SourceSelect program j bits leaf -> SourceSelect program i (b::bits) leaf.
