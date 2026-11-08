(** Simultaneous semantics of bounded fresh quantifier blocks. Bounds are old
    variable names; the captured environment is represented by push_environment. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import FormulaSemantics BerkeleySyntaxBase BerkeleySyntaxInterpretation BerkeleySyntaxScope.
Import ListNotations.


Lemma b_holds_all2 {D} (R:D->D->Prop) rho body n :
  (b_holds R rho (b_all (fun x => b_all (fun y => body x y))) n <->
   forall x y, b_holds R (push_environment rho n [x;y]) (body n (S n)) (S(S n))).
Proof.
  rewrite b_holds_all. split.
  - intros H x y. specialize (H x). rewrite b_holds_all in H. exact (H y).
  - intros H x. rewrite b_holds_all. intro y. exact (H x y).
Qed.
Lemma b_holds_ain_all_ain3 {D} (R:D->D->Prop) rho a c body n : a<n -> c<n ->
  (b_holds R rho (b_ain a (fun x => b_all (fun y => b_ain c (fun z => body x y z)))) n <->
   forall x y z, R x (rho a) -> R z (rho c) ->
     b_holds R (push_environment rho n [x;y;z]) (body n (S n) (S(S n))) (S(S(S n)))).
Proof.
  intros A C. rewrite b_holds_ain by exact A. split.
  - intros H x y z X Z. specialize (H x X). rewrite b_holds_all in H. specialize (H y).
    rewrite b_holds_ain in H by lia. specialize (H z). repeat rewrite update_variable_neq in H by lia. exact (H Z).
  - intros H x X. rewrite b_holds_all. intro y. rewrite b_holds_ain by lia. intros z Z.
    repeat rewrite update_variable_neq in Z by lia. exact (H x y z X Z).
Qed.

Lemma b_holds_ain2 {D} (R:D->D->Prop) rho a b body n : a<n -> b<n ->
  (b_holds R rho (b_ain a (fun x => b_ain b (fun y => body x y))) n <->
   forall x y, R x (rho a) -> R y (rho b) ->
     b_holds R (push_environment rho n [x;y]) (body n (S n)) (S(S n))).
Proof.
  intros A B. rewrite b_holds_ain by exact A. split.
  - intros H x y X Y. specialize (H x X). rewrite b_holds_ain in H by lia.
    specialize (H y). rewrite update_variable_neq in H by lia. exact (H Y).
  - intros H x X. rewrite b_holds_ain by lia. intros y Y. rewrite update_variable_neq in Y by lia.
    exact (H x y X Y).
Qed.

Lemma b_holds_ain3 {D} (R:D->D->Prop) rho a b c body n : a<n -> b<n -> c<n ->
  (b_holds R rho (b_ain a (fun x => b_ain b (fun y => b_ain c (fun z => body x y z)))) n <->
   forall x y z, R x (rho a) -> R y (rho b) -> R z (rho c) ->
     b_holds R (push_environment rho n [x;y;z]) (body n (S n) (S(S n))) (S(S(S n)))).
Proof.
  intros A B C. rewrite b_holds_ain by exact A. split.
  - intros H x y z X Y Z. specialize (H x X). rewrite b_holds_ain in H by lia.
    specialize (H y). rewrite update_variable_neq in H by lia. specialize (H Y).
    rewrite b_holds_ain in H by lia. specialize (H z). repeat rewrite update_variable_neq in H by lia. exact (H Z).
  - intros H x X. rewrite b_holds_ain by lia. intros y Y. rewrite update_variable_neq in Y by lia.
    rewrite b_holds_ain by lia. intros z Z. repeat rewrite update_variable_neq in Z by lia. exact (H x y z X Y Z).
Qed.

Lemma b_holds_ain5 {D} (R:D->D->Prop) rho a b c d e body n : a<n -> b<n -> c<n -> d<n -> e<n ->
  (b_holds R rho (b_ain a (fun v => b_ain b (fun w => b_ain c (fun x => b_ain d (fun y => b_ain e (fun z => body v w x y z)))))) n <->
   forall v w x y z, R v (rho a) -> R w (rho b) -> R x (rho c) -> R y (rho d) -> R z (rho e) ->
     b_holds R (push_environment rho n [v;w;x;y;z])
       (body n (S n) (S (S n)) (S (S (S n))) (S (S (S (S n)))))
       (S (S (S (S (S n)))))).
Proof.
  intros A B C D0 E. rewrite b_holds_ain by exact A. split.
  - intros H v w x y z V W X Y Z. specialize (H v V). rewrite b_holds_ain in H by lia.
    specialize (H w). rewrite update_variable_neq in H by lia. specialize (H W).
    rewrite b_holds_ain in H by lia. specialize (H x). repeat rewrite update_variable_neq in H by lia. specialize (H X).
    rewrite b_holds_ain in H by lia. specialize (H y). repeat rewrite update_variable_neq in H by lia. specialize (H Y).
    rewrite b_holds_ain in H by lia. specialize (H z). repeat rewrite update_variable_neq in H by lia. exact (H Z).
  - intros H v V. rewrite b_holds_ain by lia. intros w W. rewrite update_variable_neq in W by lia.
    rewrite b_holds_ain by lia. intros x X. repeat rewrite update_variable_neq in X by lia.
    rewrite b_holds_ain by lia. intros y Y. repeat rewrite update_variable_neq in Y by lia.
    rewrite b_holds_ain by lia. intros z Z. repeat rewrite update_variable_neq in Z by lia. exact (H v w x y z V W X Y Z).
Qed.



Lemma push_environment_two {D} (rho:nat->D) n a b :
  (forall i, i<n -> push_environment rho n [a;b] i = rho i) /\
  push_environment rho n [a;b] n=a /\ push_environment rho n [a;b] (S n)=b.
Proof.
  split; [intros; now apply push_environment_old|]. split.
  - pose proof (@push_environment_at D rho n [a;b] 0 a eq_refl) as H. now rewrite Nat.add_0_r in H.
  - replace (S n) with (n+1) by lia. eapply push_environment_at. reflexivity.
Qed.
Lemma push_environment_three {D} (rho:nat->D) n a b c :
  (forall i, i<n -> push_environment rho n [a;b;c] i = rho i) /\
  push_environment rho n [a;b;c] n=a /\ push_environment rho n [a;b;c] (S n)=b /\
  push_environment rho n [a;b;c] (S(S n))=c.
Proof.
  split; [intros; now apply push_environment_old|]. split.
  - pose proof (@push_environment_at D rho n [a;b;c] 0 a eq_refl) as H. now rewrite Nat.add_0_r in H.
  - split; [replace (S n) with (n+1) by lia; eapply push_environment_at; reflexivity|].
    replace (S(S n)) with (n+2) by lia. eapply push_environment_at. reflexivity.
Qed.

Lemma push_environment_five {D} (rho:nat->D) n a b c d e :
  (forall i, i<n -> push_environment rho n [a;b;c;d;e] i = rho i) /\
  push_environment rho n [a;b;c;d;e] n=a /\
  push_environment rho n [a;b;c;d;e] (S n)=b /\
  push_environment rho n [a;b;c;d;e] (S(S n))=c /\
  push_environment rho n [a;b;c;d;e] (S(S(S n)))=d /\
  push_environment rho n [a;b;c;d;e] (S(S(S(S n))))=e.
Proof.
  split; [intros; now apply push_environment_old|]. split.
  - pose proof (@push_environment_at D rho n [a;b;c;d;e] 0 a eq_refl) as H. now rewrite Nat.add_0_r in H.
  - split; [replace (S n) with (n+1) by lia; eapply push_environment_at; reflexivity|].
    split; [replace (S(S n)) with (n+2) by lia; eapply push_environment_at; reflexivity|].
    split; [replace (S(S(S n))) with (n+3) by lia; eapply push_environment_at; reflexivity|].
    replace (S(S(S(S n)))) with (n+4) by lia. eapply push_environment_at. reflexivity.
Qed.

Print Assumptions push_environment_two.
Print Assumptions push_environment_three.
Print Assumptions push_environment_five.
Print Assumptions b_holds_all2.
Print Assumptions b_holds_ain_all_ain3.
Print Assumptions b_holds_ain2.
Print Assumptions b_holds_ain3.
Print Assumptions b_holds_ain5.
