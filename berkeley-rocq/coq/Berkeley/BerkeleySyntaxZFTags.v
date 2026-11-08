(** The five literal constructor tags are obtained by four successor steps
    from an empty set; all witnesses are constructed inside the ZF model. *)
From Stdlib Require Import Lists.List.
From Berkeley Require Import BerkeleySyntaxSets BerkeleySyntaxOmega BerkeleySyntaxSentence BerkeleySyntaxZFBase
  BerkeleySyntaxZFPaths BerkeleySyntaxZFUnion.
Import ListNotations.

Section Tags.
Context {D:Type} (R:D->D->Prop).
Variable EM : forall P:Prop, P \/ ~P.
Variable Model : satisfies_zf_prefix R.

Theorem zf_prefix_successor_exists a : exists b, RelSuccessor R b a.
Proof.
  destruct (zf_prefix_singleton_exists R EM Model a) as [one One].
  destruct (zf_prefix_binary_union_exists R EM Model a one) as [b B]. exists b. intro z.
  rewrite (B z),(One z). reflexivity.
Qed.
Theorem zf_prefix_tag_chain_exists w : RelOmega R w -> exists te tm tn ti ta, RelTags R w te tm tn ti ta.
Proof.
  intro Omega. destruct (zf_prefix_empty_exists R EM Model w) as [te Zero].
  destruct (zf_prefix_successor_exists te) as [tm S1]. destruct (zf_prefix_successor_exists tm) as [tn S2].
  destruct (zf_prefix_successor_exists tn) as [ti S3]. destruct (zf_prefix_successor_exists ti) as [ta S4].
  exists te,tm,tn,ti,ta. unfold RelTags. exact (conj Omega (conj Zero (conj S1 (conj S2 (conj S3 S4))))).
Qed.
End Tags.

Print Assumptions zf_prefix_successor_exists.
Print Assumptions zf_prefix_tag_chain_exists.
