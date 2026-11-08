(** Semantic interpretation of environments, coordinate updates, and images. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxBijection FormulaSemantics.
Import ListNotations.

Definition RelEnvironments {D} (R:D->D->Prop) e w m :=
  forall s, R s e <-> RelFunction R s w m.
Definition RelEnvAgreement {D} (R:D->D->Prop) s t v m :=
  forall x, R x m -> (RelGraph R s v x <-> RelGraph R t v x).
Definition RelUpdate {D} (R:D->D->Prop) s t u w m :=
  forall v, R v w -> v=u \/ RelEnvAgreement R s t v m.
Definition env_agreement_builder s t v m :=
  b_ain m (fun x => b_iff (b_rel s v x) (b_rel t v x)).

Section Environments.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Theorem environments_builder_holds rho e w m n : e<n -> w<n -> m<n ->
  (b_holds R rho (b_environments e w m) n <-> RelEnvironments R (rho e) (rho w) (rho m)).
Proof.
  intros E W M. unfold b_environments,RelEnvironments. rewrite b_holds_all. split; intros H s; specialize (H s).
  - apply (proj1 (b_holds_iff EM _ _ _ _ _)) in H.
    rewrite b_holds_mem in H. replace (b_next (b_mem n e) (S n)) with (S n) in H by reflexivity.
    rewrite (function_builder_holds EM) in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - apply (proj2 (b_holds_iff EM _ _ _ _ _)).
    rewrite b_holds_mem. replace (b_next (b_mem n e) (S n)) with (S n) by reflexivity.
    rewrite (function_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.

Theorem env_agreement_builder_holds rho s t v m n : s<n -> t<n -> v<n -> m<n ->
  (b_holds R rho (env_agreement_builder s t v m) n <->
   RelEnvAgreement R (rho s) (rho t) (rho v) (rho m)).
Proof.
  intros Hs T V M. unfold env_agreement_builder,RelEnvAgreement. rewrite b_holds_ain by exact M.
  split; intros H x X; specialize (H x X).
  - apply (proj1 (b_holds_iff EM _ _ _ _ _)) in H.
    assert (K : S n <= b_next (b_rel s v n) (S n)) by apply b_good_rel.
    rewrite !(relation_builder_holds EM) in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - apply (proj2 (b_holds_iff EM _ _ _ _ _)).
    assert (K : S n <= b_next (b_rel s v n) (S n)) by apply b_good_rel.
    rewrite !(relation_builder_holds EM) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.

Theorem update_builder_holds rho s t u w m n : s<n -> t<n -> u<n -> w<n -> m<n ->
  (b_holds R rho (b_update s t u w m) n <->
   RelUpdate R (rho s) (rho t) (rho u) (rho w) (rho m)).
Proof.
  intros Hs T U W M. unfold b_update,RelUpdate. rewrite b_holds_ain by exact W. split; intros H v V; specialize (H v V).
  - rewrite (b_holds_or EM),b_holds_eq in H. cbn [b_next b_eq] in H.
    change (update_variable rho n v n = update_variable rho n v u \/
      b_holds R (update_variable rho n v) (env_agreement_builder s t n m) (S n)) in H.
    rewrite (env_agreement_builder_holds) in H by lia.
    rewrite update_variable_eq in H. repeat rewrite update_variable_neq in H by lia. exact H.
  - rewrite (b_holds_or EM),b_holds_eq. cbn [b_next b_eq].
    change (update_variable rho n v n = update_variable rho n v u \/
      b_holds R (update_variable rho n v) (env_agreement_builder s t n m) (S n)).
    rewrite (env_agreement_builder_holds) by lia.
    rewrite update_variable_eq. repeat rewrite update_variable_neq by lia. exact H.
Qed.
End Environments.

Print Assumptions environments_builder_holds.
Print Assumptions env_agreement_builder_holds.
Print Assumptions update_builder_holds.
