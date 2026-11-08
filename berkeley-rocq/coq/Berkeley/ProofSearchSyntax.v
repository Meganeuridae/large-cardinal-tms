(** Numeric proof instructions and the explicit axiom presentation searched
    by the candidate.  No claim equating this calculus with standard ZF or
    the Berkeley assertion is built into these definitions. *)
From Stdlib Require Import Lists.List Arith.Arith Lia.
From Berkeley Require Import Syntax SyntaxData ConstructorArithmetic ConstructorStreams.
Import ListNotations.

Definition code_eq x y := cantor (cantor x y) 0.
Definition code_mem x y := cantor (cantor x y) 1.
Definition code_neg p := cantor p 3.
Definition code_imp p q := cantor (cantor p q) 2.
Definition code_all x p := cantor (cantor x p) 4.

Definition instruction := (nat * nat * nat * nat)%type.
Definition instruction_params a b c n :=
  match n with 1 => a | 2 => b | 3 => c | _ => 0 end.
Definition instantiated_axiom i a b c :=
  option_map (formula_code (instruction_params a b c)) (nth_error candidate_axioms i).

Inductive NumericProvable : nat -> Prop :=
| numeric_reflexivity : NumericProvable 0
| numeric_axiom i a b c f : instantiated_axiom i a b c = Some f -> NumericProvable f
| numeric_mp p q : NumericProvable (code_imp p q) -> NumericProvable p -> NumericProvable q
| numeric_gen x p : NumericProvable p -> NumericProvable (code_all x p).
Definition NumericInconsistent := NumericProvable 1.

Definition instruction_tail (i : instruction) tail :=
  let '(op,a,b,c) := i in cantor op (cantor a (cantor b (cantor c tail))).
Definition instruction_decode n : instruction * nat :=
  let '(op,n1) := uncantor n in
  let '(a,n2) := uncantor n1 in
  let '(b,n3) := uncantor n2 in
  let '(c,tail) := uncantor n3 in ((op,a,b,c),tail).
Fixpoint program_code (p : list instruction) :=
  match p with [] => 0 | i::rest => S (instruction_tail i (program_code rest)) end.

Lemma instruction_decode_encode i tail :
  instruction_decode (instruction_tail i tail) = (i,tail).
Proof. destruct i as [[[op a] b] c]. unfold instruction_decode,instruction_tail.
  now rewrite !uncantor_cantor. Qed.
Lemma instruction_encode_decode n :
  let '(i,tail) := instruction_decode n in instruction_tail i tail = n.
Proof.
  unfold instruction_decode. pose proof (cantor_uncantor n) as H0.
  destruct (uncantor n) as [op n1]. pose proof (cantor_uncantor n1) as H1.
  destruct (uncantor n1) as [a n2]. pose proof (cantor_uncantor n2) as H2.
  destruct (uncantor n2) as [b n3]. pose proof (cantor_uncantor n3) as H3.
  destruct (uncantor n3) as [c tail]. cbn [instruction_tail].
  now rewrite H3,H2,H1,H0.
Qed.
Lemma triangle_ge n : n <= triangle n.
Proof. induction n; cbn [triangle]; lia. Qed.
Lemma cantor_ge_left a b : a <= cantor a b.
Proof. unfold cantor. lia. Qed.
Lemma cantor_ge_right a b : b <= cantor a b.
Proof. unfold cantor. pose proof (triangle_ge (a+b)). lia. Qed.
Lemma instruction_tail_ge i tail : tail <= instruction_tail i tail.
Proof. destruct i as [[[op a] b] c]. cbn [instruction_tail].
  eapply Nat.le_trans; [apply cantor_ge_right|].
  eapply Nat.le_trans; [apply cantor_ge_right|].
  eapply Nat.le_trans; apply cantor_ge_right.
Qed.
Lemma decoded_tail_le n i tail : instruction_decode n = (i,tail) -> tail <= n.
Proof. intro E. pose proof (instruction_encode_decode n) as H.
  rewrite E in H. rewrite <- H. apply instruction_tail_ge. Qed.
Lemma program_code_nonempty i p : 0 < program_code (i::p).
Proof. cbn [program_code]. lia. Qed.
Lemma program_code_tail_lt i p : program_code p < program_code (i::p).
Proof. cbn [program_code]. pose proof (instruction_tail_ge i (program_code p)). lia. Qed.

Print Assumptions instruction_decode_encode.
Print Assumptions instruction_encode_decode.
Print Assumptions decoded_tail_le.
Print Assumptions program_code_tail_lt.
