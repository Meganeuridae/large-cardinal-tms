(** Relational semantics of environment images and elementary embeddings. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import BerkeleySyntaxBase BerkeleySyntaxSatisfaction BerkeleySyntaxInterpretation
  BerkeleySyntaxPairs BerkeleySyntaxFunction BerkeleySyntaxBijection FormulaSemantics.
Import ListNotations.

Definition RelImageEnvironment {D} (R:D->D->Prop) j s t w m :=
  forall u x y, R u w -> R x m -> R y m -> RelGraph R s u x -> RelGraph R j x y -> RelGraph R t u y.
Definition RelElementaryClause {D} (R:D->D->Prop) j m e f w sat :=
  forall p s t, R p f -> R s e -> R t e -> RelImageEnvironment R j s t w m ->
    (RelGraph R sat p s <-> RelGraph R sat p t).
Definition RelElementary {D} (R:D->D->Prop) j m e f w sat :=
  RelFunction R j m m /\ RelElementaryClause R j m e f w sat.

Definition image_core_builder j s t u x y :=
  b_imp (b_and (b_rel s u x) (b_rel j x y)) (b_rel t u y).
Definition elementary_core_builder j m w sat p s t :=
  b_imp (b_image_environment j s t w m) (b_iff (b_rel sat p s) (b_rel sat p t)).
Definition elementary_clause_builder j m e f w sat :=
  b_ain f (fun p => b_ain e (fun s => b_ain e (fun t => elementary_core_builder j m w sat p s t))).

Lemma b_good_image_environment j s t w m : b_good (b_image_environment j s t w m).
Proof.
  unfold b_image_environment. apply b_good_ain. intro u. apply b_good_ain. intro x. apply b_good_ain. intro y.
  unfold b_imp,b_and. apply b_good_binary; [apply b_good_binary; apply b_good_rel|apply b_good_rel].
Qed.

Section ElementarySemantics.
Variable EM : forall P:Prop, P \/ ~P.
Variable D : Type.
Variable R : D->D->Prop.

Lemma image_core_holds rho j s t u x y n : j<n -> s<n -> t<n -> u<n -> x<n -> y<n ->
  (b_holds R rho (image_core_builder j s t u x y) n <->
    (RelGraph R (rho s) (rho u) (rho x) /\ RelGraph R (rho j) (rho x) (rho y) ->
     RelGraph R (rho t) (rho u) (rho y))).
Proof.
  intros J S0 T U X Y. unfold image_core_builder. rewrite b_holds_imp,(b_holds_and EM).
  assert (K1 : n <= b_next (b_rel s u x) n) by apply b_good_rel.
  assert (K2 : n <= b_next (b_and (b_rel s u x) (b_rel j x y)) n).
  { unfold b_and. apply b_good_binary; apply b_good_rel. }
  rewrite !(relation_builder_holds EM) by lia. reflexivity.
Qed.

Theorem image_environment_builder_holds rho j s t w m n : j<n -> s<n -> t<n -> w<n -> m<n ->
  (b_holds R rho (b_image_environment j s t w m) n <->
   RelImageEnvironment R (rho j) (rho s) (rho t) (rho w) (rho m)).
Proof.
  intros J S0 T W M. unfold b_image_environment,RelImageEnvironment. rewrite b_holds_ain by exact W. split.
  - intros H u x y U X Y A B. specialize (H u U). rewrite b_holds_ain in H by lia.
    specialize (H x). rewrite update_variable_neq in H by lia. specialize (H X).
    rewrite b_holds_ain in H by lia. specialize (H y).
    repeat rewrite update_variable_neq in H by lia. specialize (H Y).
    change (b_holds R (update_variable (update_variable (update_variable rho n u) (S n) x) (S(S n)) y)
      (image_core_builder j s t n (S n) (S(S n))) (S(S(S n)))) in H.
    rewrite image_core_holds in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n u) (S n) x) (S(S n)) y) in H.
    assert (Sj : sigma j=rho j) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ss : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (St : sigma t=rho t) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Su : sigma n=u) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sx : sigma (S n)=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S(S n))=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sj,Ss,St,Su,Sx,Sy in H. now apply H.
  - intros H u U. rewrite b_holds_ain by lia. intros x X. rewrite update_variable_neq in X by lia.
    rewrite b_holds_ain by lia. intros y Y. repeat rewrite update_variable_neq in Y by lia.
    change (b_holds R (update_variable (update_variable (update_variable rho n u) (S n) x) (S(S n)) y)
      (image_core_builder j s t n (S n) (S(S n))) (S(S(S n)))).
    rewrite image_core_holds by lia.
    set (sigma := update_variable (update_variable (update_variable rho n u) (S n) x) (S(S n)) y).
    change ((RelGraph R (sigma s) (sigma n) (sigma (S n)) /\
             RelGraph R (sigma j) (sigma (S n)) (sigma (S(S n)))) ->
             RelGraph R (sigma t) (sigma n) (sigma (S(S n)))).
    assert (Sj : sigma j=rho j) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ss : sigma s=rho s) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (St : sigma t=rho t) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Su : sigma n=u) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sx : sigma (S n)=x) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Sy : sigma (S(S n))=y) by (unfold sigma; apply update_variable_eq).
    rewrite Sj,Ss,St,Su,Sx,Sy. intros [A B]. now apply H with (x:=x).
Qed.

Lemma elementary_core_holds rho j m w sat p s t n :
  j<n -> m<n -> w<n -> sat<n -> p<n -> s<n -> t<n ->
  (b_holds R rho (elementary_core_builder j m w sat p s t) n <->
    (RelImageEnvironment R (rho j) (rho s) (rho t) (rho w) (rho m) ->
     (RelGraph R (rho sat) (rho p) (rho s) <-> RelGraph R (rho sat) (rho p) (rho t)))).
Proof.
  intros J M W Sa P S0 T. unfold elementary_core_builder.
  rewrite b_holds_imp,(b_holds_iff EM).
  assert (K1 : n <= b_next (b_image_environment j s t w m) n) by apply b_good_image_environment.
  assert (K2 : b_next (b_image_environment j s t w m) n <=
      b_next (b_rel sat p s) (b_next (b_image_environment j s t w m) n)) by apply b_good_rel.
  rewrite image_environment_builder_holds by lia.
  rewrite !(relation_builder_holds EM) by lia. reflexivity.
Qed.

Theorem elementary_clause_builder_holds rho j m e f w sat n :
  j<n -> m<n -> e<n -> f<n -> w<n -> sat<n ->
  (b_holds R rho (elementary_clause_builder j m e f w sat) n <->
   RelElementaryClause R (rho j) (rho m) (rho e) (rho f) (rho w) (rho sat)).
Proof.
  intros J M E F W Sa. unfold elementary_clause_builder,RelElementaryClause. rewrite b_holds_ain by exact F. split.
  - intros H p s t P S0 T Image. specialize (H p P). rewrite b_holds_ain in H by lia.
    specialize (H s). rewrite update_variable_neq in H by lia. specialize (H S0).
    rewrite b_holds_ain in H by lia. specialize (H t).
    repeat rewrite update_variable_neq in H by lia. specialize (H T).
    rewrite elementary_core_holds in H by lia.
    set (sigma := update_variable (update_variable (update_variable rho n p) (S n) s) (S(S n)) t) in H.
    assert (Sj : sigma j=rho j) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ssat : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sp : sigma n=p) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Ss : sigma (S n)=s) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (St : sigma (S(S n))=t) by (unfold sigma; apply update_variable_eq).
    rewrite Sj,Sm,Sw,Ssat,Sp,Ss,St in H. now apply H.
  - intros H p P. rewrite b_holds_ain by lia. intros s S0. rewrite update_variable_neq in S0 by lia.
    rewrite b_holds_ain by lia. intros t T. repeat rewrite update_variable_neq in T by lia.
    rewrite elementary_core_holds by lia.
    set (sigma := update_variable (update_variable (update_variable rho n p) (S n) s) (S(S n)) t).
    change (RelImageEnvironment R (sigma j) (sigma (S n)) (sigma (S(S n))) (sigma w) (sigma m) ->
      (RelGraph R (sigma sat) (sigma n) (sigma (S n)) <-> RelGraph R (sigma sat) (sigma n) (sigma (S(S n))))).
    assert (Sj : sigma j=rho j) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sm : sigma m=rho m) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sw : sigma w=rho w) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Ssat : sigma sat=rho sat) by (unfold sigma; repeat rewrite update_variable_neq by lia; reflexivity).
    assert (Sp : sigma n=p) by (unfold sigma; repeat rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (Ss : sigma (S n)=s) by (unfold sigma; rewrite update_variable_neq by lia; apply update_variable_eq).
    assert (St : sigma (S(S n))=t) by (unfold sigma; apply update_variable_eq).
    rewrite Sj,Sm,Sw,Ssat,Sp,Ss,St. now apply H.
Qed.

Theorem elementary_builder_holds rho j m e f w sat n :
  j<n -> m<n -> e<n -> f<n -> w<n -> sat<n ->
  (b_holds R rho (b_elementary j m e f w sat) n <->
   RelElementary R (rho j) (rho m) (rho e) (rho f) (rho w) (rho sat)).
Proof.
  intros J M E F W Sa. unfold b_elementary,RelElementary.
  change (b_holds R rho (b_and (b_function j m m) (elementary_clause_builder j m e f w sat)) n <->
    RelFunction R (rho j) (rho m) (rho m) /\
    RelElementaryClause R (rho j) (rho m) (rho e) (rho f) (rho w) (rho sat)).
  rewrite (b_holds_and EM),(function_builder_holds EM) by lia.
  assert (K : n <= b_next (b_function j m m) n) by apply b_good_function.
  rewrite elementary_clause_builder_holds by lia. reflexivity.
Qed.
End ElementarySemantics.

Print Assumptions image_environment_builder_holds.
Print Assumptions elementary_builder_holds.
