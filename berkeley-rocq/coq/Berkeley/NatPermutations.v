(** Explicit finite permutations taking 0,1,2,3 to any four distinct names. *)
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.
Definition swap_nat a b n := if Nat.eqb n a then b else if Nat.eqb n b then a else n.
Lemma swap_left a b : swap_nat a b a=b.
Proof. unfold swap_nat. now rewrite Nat.eqb_refl. Qed.
Lemma swap_right a b : swap_nat a b b=a.
Proof.
  destruct (Nat.eq_dec a b) as [E|E]; [subst;apply swap_left|].
  unfold swap_nat. assert ((b=?a)=false) by (apply Nat.eqb_neq;congruence). now rewrite H,Nat.eqb_refl.
Qed.
Lemma swap_other a b n : n<>a -> n<>b -> swap_nat a b n=n.
Proof. intros A B. unfold swap_nat. apply Nat.eqb_neq in A,B. now rewrite A,B. Qed.
Lemma swap_involution a b n : swap_nat a b (swap_nat a b n)=n.
Proof.
  destruct (Nat.eq_dec n a) as [E|E]; [subst;now rewrite swap_left,swap_right|].
  destruct (Nat.eq_dec n b) as [F|F]; [subst;now rewrite swap_right,swap_left|].
  rewrite (swap_other a b n E F). now apply swap_other.
Qed.
Lemma swap_injective a b x y : swap_nat a b x=swap_nat a b y -> x=y.
Proof. intro E. apply (f_equal (swap_nat a b)) in E. now rewrite !swap_involution in E. Qed.
Definition update_perm (pi:nat->nat) a v n := swap_nat (pi a) v (pi n).
Lemma update_perm_injective pi a v : (forall x y, pi x=pi y -> x=y) ->
  forall x y, update_perm pi a v x=update_perm pi a v y -> x=y.
Proof. intros I x y E. apply I. apply (swap_injective (pi a) v). exact E. Qed.
Lemma update_perm_here pi a v : update_perm pi a v a=v.
Proof. apply swap_left. Qed.
Lemma update_perm_preserves pi a v j : (forall x y, pi x=pi y -> x=y) -> j<>a -> pi j<>v ->
  update_perm pi a v j=pi j.
Proof.
  intros I J V. unfold update_perm. apply swap_other; [intro E;apply J,I,E|exact V].
Qed.
Definition perm1 x := update_perm (fun n=>n) 0 x.
Definition perm2 x y := update_perm (perm1 x) 1 y.
Definition perm3 x y z := update_perm (perm2 x y) 2 z.
Definition perm4 x y z w := update_perm (perm3 x y z) 3 w.
Definition invperm4 x y z w n :=
  swap_nat 0 x (swap_nat (perm1 x 1) y (swap_nat (perm2 x y 2) z (swap_nat (perm3 x y z 3) w n))).
Lemma perm1_inj x : forall a b, perm1 x a=perm1 x b -> a=b.
Proof. apply update_perm_injective. auto. Qed.
Lemma perm2_inj x y : forall a b, perm2 x y a=perm2 x y b -> a=b.
Proof. apply update_perm_injective,perm1_inj. Qed.
Lemma perm3_inj x y z : forall a b, perm3 x y z a=perm3 x y z b -> a=b.
Proof. apply update_perm_injective,perm2_inj. Qed.
Lemma perm4_left_inverse x y z w n : invperm4 x y z w (perm4 x y z w n)=n.
Proof. unfold invperm4,perm4,perm3,perm2,perm1,update_perm. now rewrite !swap_involution. Qed.
Lemma perm4_right_inverse x y z w n : perm4 x y z w (invperm4 x y z w n)=n.
Proof. unfold invperm4,perm4,perm3,perm2,perm1,update_perm. now rewrite !swap_involution. Qed.
Theorem perm4_values x y z w :
  x<>y -> x<>z -> x<>w -> y<>z -> y<>w -> z<>w ->
  perm4 x y z w 0=x /\ perm4 x y z w 1=y /\ perm4 x y z w 2=z /\ perm4 x y z w 3=w.
Proof.
  intros XY XZ XW YZ YW ZW.
  assert (A0 : perm1 x 0=x) by apply update_perm_here.
  assert (B1 : perm2 x y 1=y) by apply update_perm_here.
  assert (B0 : perm2 x y 0=x).
  { unfold perm2. rewrite update_perm_preserves; [exact A0|apply perm1_inj|lia|rewrite A0;congruence]. }
  assert (C2 : perm3 x y z 2=z) by apply update_perm_here.
  assert (C0 : perm3 x y z 0=x).
  { unfold perm3. rewrite update_perm_preserves; [exact B0|apply perm2_inj|lia|rewrite B0;congruence]. }
  assert (C1 : perm3 x y z 1=y).
  { unfold perm3. rewrite update_perm_preserves; [exact B1|apply perm2_inj|lia|rewrite B1;congruence]. }
  split; [|split; [|split]].
  - unfold perm4. rewrite update_perm_preserves; [exact C0|apply perm3_inj|lia|rewrite C0;congruence].
  - unfold perm4. rewrite update_perm_preserves; [exact C1|apply perm3_inj|lia|rewrite C1;congruence].
  - unfold perm4. rewrite update_perm_preserves; [exact C2|apply perm3_inj|lia|rewrite C2;congruence].
  - apply update_perm_here.
Qed.
Print Assumptions perm4_left_inverse.
Print Assumptions perm4_right_inverse.
Print Assumptions perm4_values.
