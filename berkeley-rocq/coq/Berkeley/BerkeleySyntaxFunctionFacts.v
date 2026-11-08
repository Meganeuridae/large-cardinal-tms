(** Range and uniqueness consequences of literal function-graph definitions. *)
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxPairInject BerkeleySyntaxFunction.

Lemma relational_function_graph_range {D} (R:D->D->Prop) f a b x y :
  RelFunction R f a b -> RelGraph R f x y -> R x a /\ R y b.
Proof.
  intros [Graph Total] [p [Pair In]]. destruct (Graph p In) as [u [v [U [V Other]]]].
  destruct (relational_pair_components R p x y u v Pair Other) as [X Y]. subst. auto.
Qed.
Lemma relational_function_graph_unique {D} (R:D->D->Prop) f a b x y z :
  RelFunction R f a b -> RelGraph R f x y -> RelGraph R f x z -> y=z.
Proof.
  intros Function A B.
  pose proof (relational_function_graph_range R f a b x y Function A) as [X Y].
  pose proof (relational_function_graph_range R f a b x z Function B) as [_ Z].
  destruct Function as [_ Total]. destruct (Total x X) as [v [V [At Unique]]].
  transitivity v; [now apply Unique|symmetry; now apply Unique].
Qed.

Print Assumptions relational_function_graph_range.
Print Assumptions relational_function_graph_unique.
