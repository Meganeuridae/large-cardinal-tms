(** A small, replayable block machine. The pair compression is an execution
    accelerator only; [boot_macro_sound] relates every block to actual steps
    of [Machine.new_tm]. *)
From Stdlib Require Import Lists.List Streams.Streams Bool.Bool Arith.Arith Lia NArith PArith.
From BusyCoq Require Import TM.
From Berkeley Require Import FiniteMachine Data Machine RuntimeTape RuntimeControl BootstrapTape.
Import ListNotations.

Record boot_cfg := BootCfg {
  boot_q : nat;
  boot_focus : boot_pair;
  boot_half : bool;                 (* false: left bit; true: right bit *)
  boot_left : boot_stack;
  boot_right : boot_stack
}.
Definition boot_encode (c : boot_cfg) : cfg :=
  let '(a,b) := boot_focus c in
  if boot_half c then
    CR (boot_q c) (Cons a (pair_stack true (boot_left c)))
      (Cons b (pair_stack false (boot_right c)))
  else
    CR (boot_q c) (pair_stack true (boot_left c))
      (Cons a (Cons b (pair_stack false (boot_right c)))).
Definition boot_bit (c : boot_cfg) :=
  if boot_half c then snd (boot_focus c) else fst (boot_focus c).

Definition boot_primitive w d q' (c : boot_cfg) : boot_cfg :=
  let '(a,b) := boot_focus c in
  match boot_half c, d with
  | false,R => BootCfg q' (w,b) true (boot_left c) (boot_right c)
  | true,L => BootCfg q' (a,w) false (boot_left c) (boot_right c)
  | true,R => let '(p,r) := pair_pop (boot_right c) in
              BootCfg q' p false (pair_push (a,w) xH (boot_left c)) r
  | false,L => let '(p,l) := pair_pop (boot_left c) in
               BootCfg q' p true l (pair_push (w,b) xH (boot_right c))
  end.

Lemma boot_primitive_sound c w d q' :
  edge (boot_q c) (boot_bit c) w d q' ->
  Runs (boot_encode c) (boot_encode (boot_primitive w d q' c)).
Proof.
  destruct c as [q [a b] h l r]; destruct h, d; cbv beta iota zeta delta [boot_bit boot_primitive boot_encode boot_q boot_half boot_focus boot_left boot_right fst snd] in *.
  - intro E.
    change (Runs (CR q (Cons a (pair_stack true l)) (Cons b (pair_stack false r)))
      (CL q' (Cons a (pair_stack true l)) (Cons w (pair_stack false r)))).
    apply step_RL. exact E.
  - intro E. destruct (pair_pop r) as [[x y] r'] eqn:P.
    pose proof (pair_pop_correct false r) as H. rewrite P in H. cbn in H.
    rewrite pair_push_correct. cbn [pair_copies boot_swap].
    change (Runs (CR q (Cons a (pair_stack true l)) (Cons b (pair_stack false r)))
      (CR q' (Cons w (Cons a (pair_stack true l))) (Cons x (Cons y (pair_stack false r'))))).
    rewrite <- H. apply step_RR. exact E.
  - intro E. destruct (pair_pop l) as [[x y] l'] eqn:P.
    pose proof (pair_pop_correct true l) as H. rewrite P in H. cbn in H.
    rewrite pair_push_correct. cbn [pair_copies boot_swap].
    change (Runs (CR q (pair_stack true l) (Cons a (Cons b (pair_stack false r))))
      (CL q' (Cons y (Cons x (pair_stack true l'))) (Cons w (Cons b (pair_stack false r))))).
    rewrite <- H. apply step_RL. exact E.
  - intro E. apply step_RR. exact E.
Qed.

Lemma boot_scan_right q q1 a b wa wb n l r :
  edge q a wa R q1 -> edge q1 b wb R q ->
  let '(p,r') := pair_pop r in
  Runs (boot_encode (BootCfg q (a,b) false l (((a,b),n)::r)))
       (boot_encode (BootCfg q p false (pair_push (wa,wb) (Pos.succ n) l) r')).
Proof.
  intros E1 E2. destruct (pair_pop r) as [[x y] r'] eqn:P.
  pose proof (pair_pop_correct false r) as H. rewrite P in H. cbn in H.
  cbv beta iota zeta delta [boot_encode boot_q boot_half boot_focus boot_left boot_right fst snd].
  rewrite pair_push_correct.
  rewrite Pos2Nat.inj_succ. cbn [boot_swap]. rewrite <- H.
  change (Runs (CR q (pair_stack true l)
    (pair_copies (S (Pos.to_nat n)) (a,b) (pair_stack false r)))
    (CR q (pair_copies (S (Pos.to_nat n)) (wb,wa) (pair_stack true l))
      (pair_stack false r))).
  eapply scan_pair_R; eassumption.
Qed.

Lemma boot_scan_left q q1 a b wa wb n l r :
  edge q b wb L q1 -> edge q1 a wa L q ->
  let '(p,l') := pair_pop l in
  Runs (boot_encode (BootCfg q (a,b) true (((a,b),n)::l) r))
       (boot_encode (BootCfg q p true l' (pair_push (wa,wb) (Pos.succ n) r))).
Proof.
  intros E1 E2. destruct (pair_pop l) as [[x y] l'] eqn:P.
  pose proof (pair_pop_correct true l) as H. rewrite P in H. cbn in H.
  cbv beta iota zeta delta [boot_encode boot_q boot_half boot_focus boot_left boot_right fst snd].
  rewrite pair_push_correct.
  rewrite Pos2Nat.inj_succ. cbn [boot_swap].
  change (Runs (CL q (pair_copies (S (Pos.to_nat n)) (b,a) (pair_stack true l))
                 (pair_stack false r))
    (CL q (Cons y (Cons x (pair_stack true l')))
      (pair_copies (S (Pos.to_nat n)) (wa,wb) (pair_stack false r)))).
  rewrite <- H. eapply scan_pair_L; eassumption.
Qed.

Print Assumptions boot_primitive_sound.
Print Assumptions boot_scan_right.
Print Assumptions boot_scan_left.

(** Try to consume the current pair and a matching adjacent run at once.
    A shortcut is taken only if both literal transitions point in the same
    direction and return to the starting state. *)
Definition boot_try (c : boot_cfg) (w : bool) (d : dir) (q1 : nat) : option boot_cfg :=
  let '(a,b) := boot_focus c in
  match boot_half c, d with
  | false,R =>
      match boot_right c with
      | (p,n)::rest =>
          if pair_eqb (a,b) p then
            match lookup new_table q1 b with
            | Some (wb,R,q2) =>
                if Nat.eqb q2 (boot_q c) then
                  let '(p',r') := pair_pop rest in
                  Some (BootCfg (boot_q c) p' false
                           (pair_push (w,wb) (Pos.succ n) (boot_left c)) r')
                else None
            | _ => None
            end
          else None
      | [] => None
      end
  | true,L =>
      match boot_left c with
      | (p,n)::rest =>
          if pair_eqb (a,b) p then
            match lookup new_table q1 a with
            | Some (wa,L,q2) =>
                if Nat.eqb q2 (boot_q c) then
                  let '(p',l') := pair_pop rest in
                  Some (BootCfg (boot_q c) p' true l'
                           (pair_push (wa,w) (Pos.succ n) (boot_right c)))
                else None
            | _ => None
            end
          else None
      | [] => None
      end
  | _,_ => None
  end.
Definition boot_macro (c : boot_cfg) : option boot_cfg :=
  match lookup new_table (boot_q c) (boot_bit c) with
  | None => None
  | Some (w,d,q1) =>
      match boot_try c w d q1 with
      | Some c' => Some c'
      | None => Some (boot_primitive w d q1 c)
      end
  end.

Lemma bootstrap_lookup_bound q b w d n :
  lookup new_table q b = Some (w,d,n) -> n <= new_count.
Proof.
  unfold lookup. destruct (nth_error new_table q) as [row|] eqn:E; try discriminate.
  destruct row as [[[w0 d0] n0] [[w1 d1] n1]].
  pose proof new_targets as H. rewrite forallb_forall in H.
  apply nth_error_In in E. specialize (H _ E). simpl in H.
  apply andb_true_iff in H as [H0 H1].
  destruct b; intro K; inversion K; subst; apply Nat.leb_le; assumption.
Qed.
Lemma bootstrap_lookup_edge q b w d q' :
  q <= new_count -> lookup new_table q b = Some (w,d,q') -> edge q b w d q'.
Proof.
  intros Hq E. unfold edge, new_tm, st. rewrite val_mk by exact Hq.
  rewrite E. reflexivity.
Qed.

Lemma boot_try_sound c w d q1 c' :
  q1 <= new_count -> edge (boot_q c) (boot_bit c) w d q1 ->
  boot_try c w d q1 = Some c' ->
  boot_q c' = boot_q c /\ Runs (boot_encode c) (boot_encode c').
Proof.
  destruct c as [q [a b] half l r]; destruct half, d;
    cbv beta iota zeta delta [boot_try boot_q boot_half boot_focus boot_left boot_right
      boot_bit fst snd] in *; try discriminate.
  - intros B E. destruct l as [|[p n] rest]; [discriminate|].
    destruct (pair_eqb (a,b) p) eqn:Ep; [|discriminate].
    apply pair_eqb_spec in Ep. subst p.
    destruct (lookup new_table q1 a) as [[[wa dir] q2]|] eqn:T; [|discriminate].
    destruct dir; [|discriminate].
    destruct (Nat.eqb q2 q) eqn:Eq; [|discriminate].
    apply Nat.eqb_eq in Eq. subst q2.
    destruct (pair_pop rest) as [p l'] eqn:P. intro C. inversion C; subst c'.
    split; [reflexivity|].
    pose proof (boot_scan_left q q1 a b wa w n rest r E
      (bootstrap_lookup_edge q1 a wa L q B T)) as H.
    rewrite P in H. exact H.
  - intros B E. destruct r as [|[p n] rest]; [discriminate|].
    destruct (pair_eqb (a,b) p) eqn:Ep; [|discriminate].
    apply pair_eqb_spec in Ep. subst p.
    destruct (lookup new_table q1 b) as [[[wb dir] q2]|] eqn:T; [|discriminate].
    destruct dir; [discriminate|].
    destruct (Nat.eqb q2 q) eqn:Eq; [|discriminate].
    apply Nat.eqb_eq in Eq. subst q2.
    destruct (pair_pop rest) as [p r'] eqn:P. intro C. inversion C; subst c'.
    split; [reflexivity|].
    pose proof (boot_scan_right q q1 a b w wb n l rest E
      (bootstrap_lookup_edge q1 b wb R q B T)) as H.
    rewrite P in H. exact H.
Qed.

Lemma boot_primitive_q c w d q1 : boot_q (boot_primitive w d q1 c) = q1.
Proof.
  destruct c as [q [a b] h l r]; destruct h,d;
    cbv beta iota zeta delta [boot_primitive boot_q boot_half boot_focus boot_left boot_right fst snd];
    repeat match goal with |- context [pair_pop ?s] => destruct (pair_pop s) as [? ?] end;
    reflexivity.
Qed.

Theorem boot_macro_sound c c' :
  boot_q c <= new_count -> boot_macro c = Some c' ->
  boot_q c' <= new_count /\ Runs (boot_encode c) (boot_encode c').
Proof.
  intros Q H. unfold boot_macro in H.
  destruct (lookup new_table (boot_q c) (boot_bit c)) as [[[w d] q1]|] eqn:T;
    [|discriminate].
  pose proof (bootstrap_lookup_bound _ _ _ _ _ T) as B.
  pose proof (bootstrap_lookup_edge _ _ _ _ _ Q T) as E.
  destruct (boot_try c w d q1) as [c1|] eqn:F.
  - inversion H; subst c1. destruct (boot_try_sound c w d q1 c' B E F) as [K R].
    split; [rewrite K; exact Q|exact R].
  - inversion H; subst c'. split; [rewrite boot_primitive_q; exact B|].
    apply boot_primitive_sound. exact E.
Qed.
Print Assumptions boot_macro_sound.
