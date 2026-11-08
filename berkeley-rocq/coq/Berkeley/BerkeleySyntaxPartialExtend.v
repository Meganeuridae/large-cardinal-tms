(** A generic one-node extension rule for downward-closed partial evaluations. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import BerkeleySyntaxPairs BerkeleySyntaxSets BerkeleySyntaxFormulaSet BerkeleySyntaxEnvironment
  BerkeleySyntaxPartialTruth BerkeleySyntaxPartialUnion.
Import ListNotations.

Definition RelAllowedChildren {D} (R:D->D->Prop) p g f tn ti ta :=
  (forall q, R q f -> RelPair R p tn q -> R q g) /\
  (forall q r, R q f -> R r f -> RelNode2 R p ti q r -> R q g /\ R r g) /\
  (forall x q, R q f -> RelNode2 R p ta x q -> R q g).
Definition RelTruthAt {D} (R:D->D->Prop) h p e f w m te tm tn ti ta := forall s, R s e ->
  (forall u v x y, R u w -> R v w -> R x m -> R y m -> RelGraph R s u x -> RelGraph R s v y ->
    RelNode2 R p te u v -> (RelGraph R h p s <-> x=y)) /\
  (forall u v x y, R u w -> R v w -> R x m -> R y m -> RelGraph R s u x -> RelGraph R s v y ->
    RelNode2 R p tm u v -> (RelGraph R h p s <-> R x y)) /\
  (forall q, R q f -> RelPair R p tn q -> (RelGraph R h p s <-> ~RelGraph R h q s)) /\
  (forall q r, R q f -> R r f -> RelNode2 R p ti q r ->
    (RelGraph R h p s <-> (RelGraph R h q s -> RelGraph R h r s))) /\
  (forall u q, R u w -> R q f -> RelNode2 R p ta u q ->
    (RelGraph R h p s <-> forall t, R t e -> RelUpdate R s t u w m -> RelGraph R h q t)).

Theorem partial_evaluation_extend {D} (R:D->D->Prop) h g h' g' p e f w m te tm tn ti ta :
  RelPartialEvaluation R h g e f w m te tm tn ti ta -> R p f ->
  RelAllowedChildren R p g f tn ti ta ->
  (forall q, R q g' <-> R q g \/ q=p) ->
  (forall q s, R q g -> (RelGraph R h' q s <-> RelGraph R h q s)) ->
  RelTruthAt R h' p e f w m te tm tn ti ta -> RelTruthGraphBound R h' g' e ->
  RelPartialEvaluation R h' g' e f w m te tm tn ti ta.
Proof.
  intros [Sub [[NDown [IDown ADown]] [Truth Bound]]] Pf [NAllowed [IAllowed AAllowed]] G Old New NewBound.
  unfold RelPartialEvaluation. split.
  - intros q Q. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq]; [now apply Sub|now subst].
  - split.
    + unfold RelPartialDownward. split.
      * intros q r Q Rf Pair. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq]; apply (proj2 (G r)); left.
        -- exact (NDown q r Q Rf Pair).
        -- subst q. exact (NAllowed r Rf Pair).
      * split.
        -- intros q r t Q Rf Tf Node. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq].
           ++ destruct (IDown q r t Q Rf Tf Node) as [A B]. split; apply (proj2 (G _)); now left.
           ++ subst q. destruct (IAllowed r t Rf Tf Node) as [A B]. split; apply (proj2 (G _)); now left.
        -- intros q x r Q Rf Node. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq]; apply (proj2 (G r)); left.
           ++ exact (ADown q x r Q Rf Node).
           ++ subst q. exact (AAllowed x r Rf Node).
    + split; [|exact NewBound]. intros s S. specialize (Truth s S). specialize (New s S).
      destruct Truth as [E [M [N [I A]]]]. destruct New as [E' [M' [N' [I' A']]]]. split.
      * intros x y a b q Q X Y A0 B Ga Gb Node. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq].
        -- rewrite (Old q s Q). exact (E x y a b q Q X Y A0 B Ga Gb Node).
        -- subst q. exact (E' x y a b X Y A0 B Ga Gb Node).
      * split.
        -- intros x y a b q Q X Y A0 B Ga Gb Node. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq].
           ++ rewrite (Old q s Q). exact (M x y a b q Q X Y A0 B Ga Gb Node).
           ++ subst q. exact (M' x y a b X Y A0 B Ga Gb Node).
        -- split.
           ++ intros r q Q Rf Pair. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq].
              ** pose proof (NDown q r Q Rf Pair) as Rg. rewrite (Old q s Q),(Old r s Rg).
                 exact (N r q Q Rf Pair).
              ** subst q. exact (N' r Rf Pair).
           ++ split.
              ** intros r t q Q Rf Tf Node. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq].
                 --- destruct (IDown q r t Q Rf Tf Node) as [Rg Tg]. rewrite (Old q s Q),(Old r s Rg),(Old t s Tg).
                     exact (I r t q Q Rf Tf Node).
                 --- subst q. exact (I' r t Rf Tf Node).
              ** intros x r q Q X Rf Node. apply (proj1 (G q)) in Q. destruct Q as [Q|Eq].
                 --- pose proof (ADown q x r Q Rf Node) as Rg. rewrite (Old q s Q),(A x r q Q X Rf Node).
                     split; intros Cond t T Up; [apply (proj2 (Old r t Rg))|apply (proj1 (Old r t Rg))]; now apply Cond.
                 --- subst q. exact (A' x r X Rf Node).
Qed.

Print Assumptions partial_evaluation_extend.
