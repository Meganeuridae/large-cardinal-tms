(** Standard finite numerals represented relationally inside an internal omega.
    This never assumes that its other members are externally standard. *)
From Stdlib Require Import Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxRepresentations
  BerkeleySyntaxZFBase BerkeleySyntaxZFFoundation.

Fixpoint RelNumeral {D} (R:D->D->Prop) n a : Prop :=
  match n with
  | 0 => RelEmpty R a
  | S k => exists prev, RelNumeral R k prev /\ RelSuccessor R a prev
  end.

Section Numerals.
Context {D:Type} (R:D->D->Prop).
Variable Ext : RelExtensional R.

Lemma numeral_unique n a b : RelNumeral R n a -> RelNumeral R n b -> a=b.
Proof.
  revert a b. induction n as [|n IH]; intros a b A B; cbn [RelNumeral] in A,B.
  - apply Ext. intro z. specialize (A z). specialize (B z). tauto.
  - destruct A as [x [A S]]. destruct B as [y [B T]].
    assert (x=y) by (apply IH; assumption). subst y. apply Ext. intro z. rewrite (S z),(T z). reflexivity.
Qed.

Theorem standard_numeral_exists w : RelInductive R w -> forall n, exists a, R a w /\ RelNumeral R n a.
Proof.
  intros [Zero Succ] n. induction n as [|n IH].
  - destruct Zero as [a [A E]]. now exists a.
  - destruct IH as [a [A N]]. destruct (Succ a A) as [b [B S]]. exists b. split; [exact B|].
    cbn [RelNumeral]. now exists a.
Qed.

Theorem standard_numeral_in_omega w n a : RelInductive R w -> RelNumeral R n a -> R a w.
Proof.
  intros Ind N. destruct (standard_numeral_exists w Ind n) as [b [B NB]].
  assert (a=b) by (apply (numeral_unique n); assumption). now subst.
Qed.

Lemma numeral_less_member n m a b : n<m -> RelNumeral R n a -> RelNumeral R m b -> R a b.
Proof.
  revert n a b. induction m as [|m IH]; intros n a b Less A B; [lia|].
  cbn [RelNumeral] in B. destruct B as [prev [N Succ]]. apply (proj2 (Succ a)).
  destruct (Nat.eq_dec n m) as [Eq|Ne].
  - subst n. right. now apply (numeral_unique m).
  - left. eapply IH; eauto. lia.
Qed.

Theorem numeral_indices_unique : (forall a, ~R a a) -> forall n m a,
  RelNumeral R n a -> RelNumeral R m a -> n=m.
Proof.
  intros Irref n m a A B. destruct (Nat.lt_trichotomy n m) as [Less|[Eq|Less]]; [|exact Eq|].
  - exfalso. apply (Irref a). eapply numeral_less_member; eassumption.
  - exfalso. apply (Irref a). eapply numeral_less_member; eassumption.
Qed.

Theorem numeral_distinct : (forall a, ~R a a) -> forall n m a b,
  n<>m -> RelNumeral R n a -> RelNumeral R m b -> a<>b.
Proof.
  intros Irref n m a b Ne A B Eq. subst b. apply Ne. now apply (numeral_indices_unique Irref n m a).
Qed.
End Numerals.

Theorem zf_standard_numeral_indices_distinct {D} (R:D->D->Prop) (EM:forall P:Prop, P \/ ~P) (Model:satisfies_zf_prefix R) n m a b :
  n<>m -> RelNumeral R n a -> RelNumeral R m b -> a<>b.
Proof.
  apply numeral_distinct; [apply (zf_prefix_extensional R EM Model)|apply (zf_prefix_membership_irreflexive R EM Model)].
Qed.

Print Assumptions standard_numeral_exists.
Print Assumptions standard_numeral_in_omega.
Print Assumptions zf_standard_numeral_indices_distinct.
