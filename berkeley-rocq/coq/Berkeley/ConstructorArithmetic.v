(** Arithmetic used by the literal ZF2 constructor routines.

    The pairing routine in vendor/wade/TMBuilder.py is a loop, not a
    primitive provided by the target machine.  We model its two inner
    transfer loops and its outer loop here; source-control-flow compilation
    is a separate obligation. *)
From Stdlib Require Import Arith.Arith Lia.

Fixpoint triangle (n : nat) : nat :=
  match n with 0 => 0 | S k => triangle k + S k end.

Definition cantor (a b : nat) := triangle (a+b) + a.

Lemma triangle_twice n : 2 * triangle n = n * (n+1).
Proof. induction n; cbn [triangle]; nia. Qed.

Theorem cantor_closed_form a b :
  cantor a b = (a+b) * (a+b+1) / 2 + a.
Proof.
  unfold cantor. rewrite <- triangle_twice.
  rewrite (Nat.mul_comm 2 (triangle (a+b))), Nat.div_mul by lia. reflexivity.
Qed.

(** One countdown loop which increments both destination registers. *)
Fixpoint transfer2 (n x y : nat) : nat * nat * nat :=
  match n with
  | 0 => (0,x,y)
  | S k => transfer2 k (S x) (S y)
  end.

Lemma transfer2_correct n x y : transfer2 n x y = (0,x+n,y+n).
Proof.
  revert x y. induction n as [|n IH]; intros x y; simpl.
  - now rewrite !Nat.add_0_r.
  - rewrite IH. f_equal; [f_equal|]; lia.
Qed.

(** The corresponding one-destination countdown loop. *)
Fixpoint transfer1 (n x : nat) : nat * nat :=
  match n with
  | 0 => (0,x)
  | S k => transfer1 k (S x)
  end.

Lemma transfer1_correct n x : transfer1 n x = (0,x+n).
Proof.
  revert x. induction n as [|n IH]; intro x; simpl.
  - now rewrite Nat.add_0_r.
  - rewrite IH. f_equal; lia.
Qed.

(** A fuel-bounded, literal arithmetic account of TMBuilder.pair.
    [out] need not initially be zero; both inputs are cleared. *)
Fixpoint pair_routine (fuel a b out : nat) : option (nat * nat * nat) :=
  match fuel with
  | 0 => None
  | S rest =>
      let '(a',b',out') := transfer2 a b out in
      match b' with
      | 0 => Some (a',0,out')
      | S b'' =>
          let '(b''',a'') := transfer1 b'' a' in
          pair_routine rest a'' b''' (S out')
      end
  end.

Theorem pair_routine_correct fuel a b out : a+b < fuel ->
  pair_routine fuel a b out = Some (0,0,out + cantor a b).
Proof.
  revert a b out. induction fuel as [|fuel IH]; intros a b out H; [lia|].
  cbn [pair_routine]. rewrite transfer2_correct.
  destruct (b+a) as [|k] eqn:E.
  - assert (a=0 /\ b=0) by lia. destruct H0; subst.
    reflexivity.
  - rewrite transfer1_correct. simpl.
    rewrite IH by lia. unfold cantor. replace (a+b) with (S k) by lia.
    replace (k+0) with k by lia. simpl. f_equal. f_equal. lia.
Qed.

(** One iteration of TMBuilder.unpair after its input decrement.  The
    output pair progresses along Cantor's diagonals. *)
Definition unpair_advance (xy : nat * nat) : nat * nat :=
  let '(x,y) := xy in
  match y with
  | 0 => (0,S x)
  | S z => (S x,z)
  end.

Fixpoint unpair_iterations (n : nat) (xy : nat * nat) : nat * nat :=
  match n with 0 => xy | S k => unpair_iterations k (unpair_advance xy) end.

Definition uncantor n := unpair_iterations n (0,0).

(** This is the unpair loop with its input counter written explicitly.
    It performs one decrement of the input, increments out1, then either
    decrements out2 or drains out1 into out2. *)
Fixpoint unpair_routine (input out1 out2 : nat) : nat * nat * nat :=
  match input with
  | 0 => (0,out1,out2)
  | S k =>
      match out2 with
      | S y => unpair_routine k (S out1) y
      | 0 => let '(x,y) := transfer1 (S out1) 0 in unpair_routine k x y
      end
  end.

Theorem unpair_routine_iterations n x y :
  unpair_routine n x y =
    let '(a,b) := unpair_iterations n (x,y) in (0,a,b).
Proof.
  revert x y. induction n as [|n IH]; intros x y; [reflexivity|].
  cbn [unpair_routine unpair_iterations unpair_advance].
  destruct y as [|y]; [rewrite transfer1_correct; simpl|]; apply IH.
Qed.

Lemma unpair_iterations_add m n xy :
  unpair_iterations (m+n) xy = unpair_iterations n (unpair_iterations m xy).
Proof.
  revert xy. induction m as [|m IH]; intro xy; simpl; [reflexivity|apply IH].
Qed.

Lemma unpair_iterations_diagonal n x y : n <= y ->
  unpair_iterations n (x,y) = (x+n,y-n).
Proof.
  revert x y. induction n as [|n IH]; intros x y H; simpl.
  - now rewrite !Nat.add_0_r, Nat.sub_0_r.
  - destruct y as [|y]; [lia|]. cbn [unpair_advance].
    rewrite IH by lia. f_equal; lia.
Qed.

Lemma unpair_triangle d : uncantor (triangle d) = (0,d).
Proof.
  induction d as [|d IH]; [reflexivity|].
  unfold uncantor in *. cbn [triangle]. rewrite unpair_iterations_add, IH.
  replace (S d) with (d+1) by lia. rewrite unpair_iterations_add.
  rewrite unpair_iterations_diagonal by lia. simpl. rewrite Nat.sub_diag. f_equal. lia.
Qed.

Theorem uncantor_cantor a b : uncantor (cantor a b) = (a,b).
Proof.
  unfold cantor, uncantor. rewrite unpair_iterations_add.
  change (unpair_iterations (triangle (a+b)) (0,0)) with (uncantor (triangle (a+b))).
  rewrite unpair_triangle, unpair_iterations_diagonal by lia. f_equal; lia.
Qed.

Corollary unpair_routine_correct a b :
  unpair_routine (cantor a b) 0 0 = (0,a,b).
Proof.
  rewrite unpair_routine_iterations. change (unpair_iterations (cantor a b) (0,0)) with (uncantor (cantor a b)).
  now rewrite uncantor_cantor.
Qed.

Lemma cantor_advance x y :
  let '(a,b) := unpair_advance (x,y) in cantor a b = S (cantor x y).
Proof.
  destruct y as [|y]; cbn [unpair_advance]; unfold cantor.
  - cbn. rewrite !Nat.add_0_r. lia.
  - replace (S x+y) with (x+S y) by lia. lia.
Qed.

Lemma unpair_iterations_value n x y :
  let '(a,b) := unpair_iterations n (x,y) in cantor a b = cantor x y + n.
Proof.
  revert x y. induction n as [|n IH]; intros x y.
  - cbn [unpair_iterations]. lia.
  - cbn [unpair_iterations]. destruct (unpair_advance (x,y)) as [a b] eqn:E.
    specialize (IH a b). destruct (unpair_iterations n (a,b)) as [u v].
    pose proof (cantor_advance x y) as H.
    rewrite E in H. lia.
Qed.

Theorem cantor_uncantor n : let '(a,b) := uncantor n in cantor a b = n.
Proof.
  unfold uncantor. pose proof (unpair_iterations_value n 0 0) as H.
  cbn [cantor triangle] in H. exact H.
Qed.

Print Assumptions transfer2_correct.
Print Assumptions cantor_closed_form.
Print Assumptions transfer1_correct.
Print Assumptions pair_routine_correct.
Print Assumptions unpair_routine_iterations.
Print Assumptions uncantor_cantor.
Print Assumptions unpair_routine_correct.
Print Assumptions cantor_uncantor.
