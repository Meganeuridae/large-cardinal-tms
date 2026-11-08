(** Recovering both arguments of a Kuratowski pair from its relational code. *)
From Berkeley Require Import BerkeleySyntaxPairs.

Lemma relational_pair_intersection {D} (R:D->D->Prop) p x y : RelPair R p x y -> forall z,
  (forall t, R t p -> R z t) <-> z=x.
Proof.
  intros [u [v [U [V P]]]] z. split.
  - intro H. apply (proj1 (U z)),H,(proj2 (P u)). now left.
  - intros E t T. apply (proj1 (P t)) in T. destruct T as [T|T]; subst t.
    + apply (proj2 (U z)). exact E.
    + apply (proj2 (V z)). now left.
Qed.
Lemma relational_pair_union {D} (R:D->D->Prop) p x y : RelPair R p x y -> forall z,
  (exists t, R t p /\ R z t) <-> z=x \/ z=y.
Proof.
  intros [u [v [U [V P]]]] z. split.
  - intros [t [T Z]]. apply (proj1 (P t)) in T. destruct T as [T|T]; subst t.
    + left. now apply (proj1 (U z)).
    + now apply (proj1 (V z)).
  - intro Z. exists v. split; [apply (proj2 (P v)); now right|now apply (proj2 (V z))].
Qed.
Theorem relational_pair_components {D} (R:D->D->Prop) p x y u v :
  RelPair R p x y -> RelPair R p u v -> x=u /\ y=v.
Proof.
  intros A B. assert (X : x=u).
  { apply (proj1 (relational_pair_intersection R p u v B x)).
    apply (proj2 (relational_pair_intersection R p x y A x)). reflexivity. }
  subst u. split; [reflexivity|].
  assert (Y : y=x \/ y=v).
  { apply (proj1 (relational_pair_union R p x v B y)).
    apply (proj2 (relational_pair_union R p x y A y)). now right. }
  destruct Y as [Y|Y]; [|exact Y]. subst y.
  assert (V : v=x \/ v=x).
  { apply (proj1 (relational_pair_union R p x x A v)).
    apply (proj2 (relational_pair_union R p x v B v)). now right. }
  destruct V; congruence.
Qed.

Print Assumptions relational_pair_components.
