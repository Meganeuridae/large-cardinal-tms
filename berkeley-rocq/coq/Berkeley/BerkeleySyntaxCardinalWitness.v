(** Interpretation of the outer cardinal and transitive-set quantifiers. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntax BerkeleySyntaxInterpretation
  BerkeleySyntaxSets BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxBijection BerkeleySyntaxCardinal
  BerkeleySyntaxFormulaSet BerkeleySyntaxLocal FormulaSemantics.
Import ListNotations.

Definition cardinal_scope_builder d f w te tm tn ti ta :=
  b_all (fun m => b_imp (b_and (b_transitive m) (b_mem d m))
    (b_berkeley_local d m f w te tm tn ti ta)).
Definition RelCardinalScope {D} (R:D->D->Prop) d f w te tm tn ti ta :=
  forall m, RelTransitive R m -> R d m -> RelBerkeleyLocal R d m f w te tm tn ti ta.
Definition RelBerkeleyCardinal {D} (R:D->D->Prop) f w te tm tn ti ta :=
  exists d, RelCardinal R d /\ R w d /\ RelCardinalScope R d f w te tm tn ti ta.

Lemma b_good_bijection f a b : b_good (b_bijection f a b).
Proof.
  unfold b_bijection,b_and3. apply b_good_and.
  - apply b_good_and; [apply b_good_function|apply b_good_bijection_surj].
  - apply b_good_ain. intro x. apply b_good_ain. intro z. apply b_good_ain. intro y.
    unfold b_imp. apply b_good_binary; [apply b_good_and; apply b_good_rel|apply b_good_eq].
Qed.
Lemma b_good_cardinal d : b_good (b_cardinal d).
Proof.
  unfold b_cardinal. apply b_good_and; [apply b_good_ordinal|].
  apply b_good_ain. intro a. apply b_good_not,b_good_ex. intro f. apply b_good_bijection.
Qed.
Lemma b_good_cardinal_scope d f w te tm tn ti ta : b_good (cardinal_scope_builder d f w te tm tn ti ta).
Proof.
  unfold cardinal_scope_builder. apply b_good_all. intro m. unfold b_imp.
  apply b_good_binary; [apply b_good_and; [apply b_good_transitive|apply b_good_mem]|apply b_good_local].
Qed.
Lemma b_good_berkeley_cardinal f w te tm tn ti ta : b_good (b_berkeley_cardinal f w te tm tn ti ta).
Proof.
  unfold b_berkeley_cardinal. apply b_good_ex. intro d. unfold b_and3.
  change (b_good (b_and (b_and (b_cardinal d) (b_mem w d)) (cardinal_scope_builder d f w te tm tn ti ta))).
  apply b_good_and; [apply b_good_and; [apply b_good_cardinal|apply b_good_mem]|apply b_good_cardinal_scope].
Qed.

Section CardinalWitnessSemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma cardinal_scope_builder_holds rho d f w te tm tn ti ta n :
  d<n -> f<n -> w<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (cardinal_scope_builder d f w te tm tn ti ta) n <->
   RelCardinalScope R (rho d) (rho f) (rho w) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros D0 F W Te Tm Tn Ti Ta. unfold cardinal_scope_builder,RelCardinalScope. rewrite b_holds_all. split; intros H m; specialize (H m).
  - rewrite b_holds_imp,(b_holds_and EM),transitive_builder_holds,b_holds_mem in H by lia.
    assert (K : S n <= b_next (b_and (b_transitive n) (b_mem d n)) (S n))
      by (apply b_good_and; [apply b_good_transitive|apply b_good_mem]).
    rewrite (local_builder_holds EM) in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. tauto.
  - rewrite b_holds_imp,(b_holds_and EM),transitive_builder_holds,b_holds_mem by lia.
    assert (K : S n <= b_next (b_and (b_transitive n) (b_mem d n)) (S n))
      by (apply b_good_and; [apply b_good_transitive|apply b_good_mem]).
    rewrite (local_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. tauto.
Qed.

Theorem berkeley_cardinal_builder_holds rho f w te tm tn ti ta n :
  f<n -> w<n -> te<n -> tm<n -> tn<n -> ti<n -> ta<n ->
  (b_holds R rho (b_berkeley_cardinal f w te tm tn ti ta) n <->
   RelBerkeleyCardinal R (rho f) (rho w) (rho te) (rho tm) (rho tn) (rho ti) (rho ta)).
Proof.
  intros F W Te Tm Tn Ti Ta. unfold b_berkeley_cardinal,RelBerkeleyCardinal. rewrite (b_holds_ex EM). split.
  - intros [d H]. change (b_holds R (update_variable rho n d)
      (b_and (b_and (b_cardinal n) (b_mem w n)) (cardinal_scope_builder n f w te tm tn ti ta)) (S n)) in H.
    rewrite !(b_holds_and EM) in H.
    assert (K1 : S n <= b_next (b_cardinal n) (S n)) by apply b_good_cardinal.
    assert (K2 : S n <= b_next (b_and (b_cardinal n) (b_mem w n)) (S n))
      by (apply b_good_and; [apply b_good_cardinal|apply b_good_mem]).
    rewrite (cardinal_builder_holds EM),b_holds_mem,cardinal_scope_builder_holds in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exists d. tauto.
  - intros [d H]. exists d. change (b_holds R (update_variable rho n d)
      (b_and (b_and (b_cardinal n) (b_mem w n)) (cardinal_scope_builder n f w te tm tn ti ta)) (S n)).
    rewrite !(b_holds_and EM).
    assert (K1 : S n <= b_next (b_cardinal n) (S n)) by apply b_good_cardinal.
    assert (K2 : S n <= b_next (b_and (b_cardinal n) (b_mem w n)) (S n))
      by (apply b_good_and; [apply b_good_cardinal|apply b_good_mem]).
    rewrite (cardinal_builder_holds EM),b_holds_mem,cardinal_scope_builder_holds by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. tauto.
Qed.
End CardinalWitnessSemantics.

Print Assumptions cardinal_scope_builder_holds.
Print Assumptions berkeley_cardinal_builder_holds.
