From Stdlib Require Import Lists.List.
From Berkeley Require Import Syntax LogicCertificates.
Import ListNotations.
Definition megill_certificates : list CertificateStep := [
  cert_axiom 1;
  cert_axiom 7;
  cert_detach 0 1 [0] [0; 1; 2; 3] [(Hole 0); (Atom false (P 1) (P 2)); (Atom false (P 1) (P 3)); (Atom false (P 2) (P 3))] [(Hole 0)];
  cert_axiom 2;
  cert_axiom 0;
  cert_detach 4 3 [0] [0] [(Hole 0); (Imp (Imp (Neg (Hole 2)) (Neg (Hole 3))) (Imp (Hole 3) (Hole 2))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 5 [0] [0] [(Hole 0); (Hole 1); (Imp (Neg (Hole 2)) (Neg (Hole 3))); (Imp (Hole 3) (Hole 2))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 6 4 [0] [0] [(Hole 0); (Neg (Hole 1)); (Hole 2); (Hole 1)] [(Hole 0); (Neg (Hole 1)); (Neg (Hole 2))];
  cert_detach 0 7 [0] [0] [(Hole 0); (Neg (Hole 1)); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_axiom 9;
  cert_axiom 3;
  cert_detach 0 0 [0] [0] [(Hole 0); (Imp (Hole 1) (Imp (Hole 2) (Hole 3))); (Imp (Hole 1) (Hole 2)); (Imp (Hole 1) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 0 4 [0] [0] [(Hole 0); (Hole 1); (Hole 2); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 11 12 [0] [0] [(Hole 0); (Hole 1); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Imp (Hole 1) (Hole 2))];
  cert_axiom 8;
  cert_detach 13 14 [0] [0; 1; 2; 2] [(Hole 0); (Neg (All (P 1) (Atom false (P 1) (P 2)))); (Imp (Atom false (P 2) (P 2)) (All (P 1) (Atom false (P 2) (P 2))))] [(Hole 0)];
  cert_axiom 4;
  cert_detach 4 15 [0] [0; 1; 2] [(Hole 0); (Imp (Neg (All (P 1) (Atom false (P 1) (P 2)))) (Imp (Atom false (P 2) (P 2)) (All (P 1) (Atom false (P 2) (P 2))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 17 [0] [0; 1; 2] [(Hole 0); (Hole 1); (Neg (All (P 1) (Atom false (P 1) (P 2)))); (Imp (Atom false (P 2) (P 2)) (All (P 1) (Atom false (P 2) (P 2))))] [(Hole 0); (Hole 1)];
  cert_detach 18 16 [0; 2; 3] [0; 1] [(Hole 0); (All (P 1) (Neg (All (P 2) (Atom false (P 2) (P 3)))))] [(Hole 0); (Hole 1); (Neg (All (P 2) (Atom false (P 2) (P 3))))];
  cert_gen 19 4;
  cert_detach 10 20 [0; 1] [0; 1; 2; 3; 1] [(Hole 0); (Hole 1); (Neg (All (P 2) (Atom false (P 2) (P 3)))); (Imp (Atom false (P 3) (P 3)) (All (P 2) (Atom false (P 3) (P 3))))] [(Hole 0)];
  cert_axiom 6;
  cert_detach 4 21 [0] [0; 1; 2; 3] [(Hole 0); (Imp (All (P 1) (Neg (All (P 2) (Atom false (P 2) (P 3))))) (All (P 1) (Imp (Atom false (P 3) (P 3)) (All (P 2) (Atom false (P 3) (P 3)))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 23 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (All (P 1) (Neg (All (P 2) (Atom false (P 2) (P 3))))); (All (P 1) (Imp (Atom false (P 3) (P 3)) (All (P 2) (Atom false (P 3) (P 3)))))] [(Hole 0); (Hole 1)];
  cert_detach 24 22 [0; 1; 1; 2] [0; 1] [(Hole 0); (Neg (Atom false (P 1) (P 2)))] [(Hole 0); (Hole 1); (Atom false (P 1) (P 2))];
  cert_detach 4 9 [0] [0; 1; 2] [(Hole 0); (Imp (All (P 1) (Imp (Atom false (P 1) (P 2)) (All (P 1) (Hole 2)))) (Hole 2)); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2); (Hole 2)];
  cert_detach 0 26 [0] [0; 1; 2] [(Hole 0); (Hole 1); (All (P 1) (Imp (Atom false (P 1) (P 2)) (All (P 1) (Hole 2)))); (Hole 2)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 27 25 [0; 1; 1] [0; 1; 1] [(Hole 0); (Neg (Atom false (P 1) (P 1))); (Atom false (P 1) (P 1))] [(Hole 0)];
  cert_detach 8 28 [0] [0; 1] [(Hole 0); (Atom false (P 1) (P 1)); (Hole 1)] [(Hole 0)];
  cert_detach 3 29 [0] [0; 1] [(Hole 0); (Atom false (P 1) (P 1)); (Hole 1)] [(Hole 0); (Neg (Hole 1))];
  cert_detach 2 30 [0; 1; 2; 1] [0; 1] [(Hole 0)] [(Hole 0); (Atom false (P 1) (P 2))];
  cert_detach 4 1 [0] [0; 1; 2; 3] [(Hole 0); (Imp (Atom false (P 1) (P 2)) (Imp (Atom false (P 1) (P 3)) (Atom false (P 2) (P 3)))); (Hole 1)] [(Hole 0)];
  cert_detach 0 32 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (Atom false (P 1) (P 2)); (Imp (Atom false (P 1) (P 3)) (Atom false (P 2) (P 3)))] [(Hole 0); (Hole 1)];
  cert_detach 33 31 [0; 2; 1; 3] [0; 1; 2] [(Hole 0); (Atom false (P 1) (P 2))] [(Hole 0)];
  cert_detach 0 34 [0] [0; 1; 2; 3] [(Hole 0); (Atom false (P 1) (P 2)); (Atom false (P 2) (P 3)); (Atom false (P 1) (P 3))] [(Hole 0)];
  cert_detach 4 35 [0] [0; 1; 2; 3] [(Hole 0); (Imp (Imp (Atom false (P 1) (P 2)) (Atom false (P 2) (P 3))) (Imp (Atom false (P 1) (P 2)) (Atom false (P 1) (P 3)))); (Hole 1)] [(Hole 0)];
  cert_detach 0 36 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (Imp (Atom false (P 1) (P 2)) (Atom false (P 2) (P 3))); (Imp (Atom false (P 1) (P 2)) (Atom false (P 1) (P 3)))] [(Hole 0); (Hole 1)];
  cert_detach 37 4 [0; 3; 1; 2] [0] [(Hole 0); (Atom false (P 1) (P 2))] [(Hole 0); (Atom false (P 1) (P 2)); (Atom false (P 3) (P 1))];
  cert_detach 6 7 [0] [0] [(Hole 0); (Neg (Neg (Hole 1))); (Hole 1); (Hole 2)] [(Hole 0); (Neg (Hole 1)); (Neg (Hole 2))];
  cert_detach 0 39 [0] [0] [(Hole 0); (Neg (Neg (Hole 1))); (Hole 2); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 40 4 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Neg (Neg (Hole 1))))] [(Hole 0); (Neg (Neg (Hole 1))); (Hole 2)];
  cert_detach 3 41 [0] [0] [(Hole 0); (Neg (Neg (Hole 1))); (Hole 1)] [(Hole 0); (Neg (Hole 1))];
  cert_detach 4 22 [0] [0; 1] [(Hole 0); (Imp (Neg (Hole 2)) (All (P 1) (Neg (All (P 1) (Hole 2))))); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 0 43 [0] [0; 1] [(Hole 0); (Hole 1); (Neg (Hole 2)); (All (P 1) (Neg (All (P 1) (Hole 2))))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 44 42 [0; 1] [0] [(Hole 0); (Hole 1); (Neg (Hole 1))] [(Hole 0); (Hole 1)];
  cert_gen 45 2;
  cert_detach 9 46 [0; 1; 2] [0; 1; 1] [(Hole 0); (Hole 1); (Hole 2); (Neg (All (P 1) (Neg (Atom false (P 1) (P 2)))))] [(Hole 0); (Atom false (P 1) (P 2))];
  cert_axiom 5;
  cert_detach 4 0 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Imp (Hole 3) (Hole 4))) (Imp (Imp (Hole 2) (Hole 3)) (Imp (Hole 2) (Hole 4)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 49 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Hole 3) (Hole 4))); (Imp (Imp (Hole 2) (Hole 3)) (Imp (Hole 2) (Hole 4)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 50 4 [0] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Hole 3); (Hole 1); (Hole 2)] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Hole 3)];
  cert_detach 0 51 [0] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Imp (Hole 3) (Hole 1)); (Imp (Hole 3) (Hole 2))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_axiom 10;
  cert_detach 0 53 [0] [0; 1; 2] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2))); (All (P 1) (Hole 1)); (All (P 2) (Hole 1))] [(Hole 0); (Hole 1); (Hole 2); (Hole 1)];
  cert_gen 16 2;
  cert_detach 10 55 [0; 1] [0; 1; 1] [(Hole 0); (Hole 1); (Hole 1); (Hole 1)] [(Hole 0); (Hole 1); (Hole 1)];
  cert_detach 54 56 [0; 1; 2] [0; 1] [(Hole 0); (Atom false (P 1) (P 2))] [(Hole 0); (Atom false (P 1) (P 2))];
  cert_detach 4 57 [0] [0; 1; 2] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (All (P 2) (Atom false (P 1) (P 2)))); (Hole 1)] [(Hole 0)];
  cert_detach 52 58 [0] [0; 2; 1] [(Hole 0); (All (P 1) (Atom false (P 2) (P 1))); (Hole 1); (All (P 2) (Atom false (P 2) (P 1)))] [(Hole 0); (Imp (All (P 1) (Atom false (P 2) (P 1))) (Hole 1))];
  cert_detach 4 59 [0] [0; 1; 2] [(Hole 0); (Imp (Imp (All (P 1) (Atom false (P 2) (P 1))) (Hole 2)) (Imp (All (P 2) (Atom false (P 2) (P 1))) (Hole 2))); (Hole 1)] [(Hole 0); (Hole 2)];
  cert_detach 0 60 [0] [0; 1; 2] [(Hole 0); (Hole 1); (Imp (All (P 1) (Atom false (P 2) (P 1))) (Hole 2)); (Imp (All (P 2) (Atom false (P 2) (P 1))) (Hole 2))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 61 53 [0; 1; 3] [0; 1; 2] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2))); (All (P 2) (Atom false (P 3) (P 1)))] [(Hole 0); (Hole 1); (Hole 2); (Atom false (P 3) (P 1))];
  cert_detach 4 31 [0] [0; 1; 2] [(Hole 0); (Imp (Atom false (P 1) (P 2)) (Atom false (P 2) (P 1))); (Hole 1)] [(Hole 0)];
  cert_detach 0 63 [0] [0; 1; 2] [(Hole 0); (Hole 1); (Atom false (P 1) (P 2)); (Atom false (P 2) (P 1))] [(Hole 0); (Hole 1)];
  cert_detach 64 16 [0; 2; 3] [0; 1] [(Hole 0); (All (P 1) (Atom false (P 2) (P 3)))] [(Hole 0); (Hole 1); (Atom false (P 2) (P 3))];
  cert_gen 65 4;
  cert_detach 10 66 [0; 1] [0; 1; 2; 3; 1] [(Hole 0); (Hole 1); (Atom false (P 2) (P 3)); (Atom false (P 3) (P 2))] [(Hole 0)];
  cert_detach 4 67 [0] [0; 1; 2; 3] [(Hole 0); (Imp (All (P 1) (Atom false (P 2) (P 3))) (All (P 1) (Atom false (P 3) (P 2)))); (Hole 1)] [(Hole 0)];
  cert_detach 0 68 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 2) (P 3))); (All (P 1) (Atom false (P 3) (P 2)))] [(Hole 0); (Hole 1)];
  cert_detach 69 57 [0; 2; 1; 2] [0; 1; 2] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2)))] [(Hole 0)];
  cert_detach 4 62 [0] [0; 1; 2; 3] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (Imp (All (P 3) (Atom false (P 3) (P 1))) (All (P 2) (Atom false (P 3) (P 1))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 71 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 1) (P 2))); (Imp (All (P 3) (Atom false (P 3) (P 1))) (All (P 2) (Atom false (P 3) (P 1))))] [(Hole 0); (Hole 1)];
  cert_detach 72 70 [0; 2; 1; 3] [0; 1; 2] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2)))] [(Hole 0)];
  cert_detach 4 53 [0] [0; 1; 2] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (Imp (All (P 1) (Hole 2)) (All (P 2) (Hole 2)))); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2); (Hole 2)];
  cert_detach 0 74 [0] [0; 1; 2] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 1) (P 2))); (Imp (All (P 1) (Hole 2)) (All (P 2) (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 75 70 [0; 2; 1] [0; 1; 2] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2))); (Hole 1)] [(Hole 0)];
  cert_detach 4 4 [0] [0] [(Hole 0); (Imp (Hole 2) (Imp (Hole 3) (Hole 2))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 77 [0] [0] [(Hole 0); (Hole 1); (Hole 2); (Imp (Hole 3) (Hole 2))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 78 76 [0] [0; 1; 2] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2))); (Imp (All (P 2) (Hole 2)) (All (P 1) (Hole 2))); (Hole 1)] [(Hole 0); (Hole 2)];
  cert_detach 4 16 [0] [0; 1] [(Hole 0); (Imp (All (P 1) (Hole 2)) (Hole 2)); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 52 80 [0] [0; 1] [(Hole 0); (Hole 1); (Hole 2); (All (P 1) (Hole 1))] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Hole 1)];
  cert_detach 4 81 [0] [0; 1] [(Hole 0); (Imp (Imp (Hole 2) (Hole 3)) (Imp (All (P 1) (Hole 2)) (Hole 3))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 82 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (Hole 2) (Hole 3)); (Imp (All (P 1) (Hole 2)) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 83 [0] [0; 1] [(Hole 0); (Imp (Imp (Hole 2) (Imp (Hole 3) (Hole 4))) (Imp (Hole 2) (Imp (All (P 1) (Hole 3)) (Hole 4)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 84 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Hole 3) (Hole 4))); (Imp (Hole 2) (Imp (All (P 1) (Hole 3)) (Hole 4)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 85 14 [0; 4] [0; 1; 2; 3] [(Hole 0); (Neg (All (P 1) (Atom false (P 1) (P 2)))); (Neg (All (P 1) (Atom false (P 1) (P 3)))); (Atom false (P 2) (P 3)); (All (P 1) (Atom false (P 2) (P 3)))] [(Hole 0)];
  cert_detach 4 42 [0] [0] [(Hole 0); (Imp (Hole 2) (Neg (Neg (Hole 2)))); (Hole 1)] [(Hole 0); (Hole 2)];
  cert_detach 0 87 [0] [0] [(Hole 0); (Hole 1); (Hole 2); (Neg (Neg (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 88 86 [0] [0; 1; 2; 3; 4] [(Hole 0); (Neg (All (P 1) (Atom false (P 1) (P 2)))); (Imp (Neg (All (P 1) (Atom false (P 1) (P 3)))) (Imp (All (P 4) (Atom false (P 2) (P 3))) (All (P 1) (Atom false (P 2) (P 3)))))] [(Hole 0)];
  cert_detach 3 89 [0] [0; 1; 4; 2; 3] [(Hole 0); (All (P 1) (Atom false (P 1) (P 4))); (Neg (Imp (Neg (All (P 1) (Atom false (P 1) (P 2)))) (Imp (All (P 3) (Atom false (P 4) (P 2))) (All (P 1) (Atom false (P 4) (P 2))))))] [(Hole 0)];
  cert_detach 4 79 [0] [0; 1; 2] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (Imp (Hole 2) (Imp (All (P 2) (Hole 3)) (All (P 1) (Hole 3))))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 91 [0] [0; 1; 2] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 1) (P 2))); (Imp (Hole 2) (Imp (All (P 2) (Hole 3)) (All (P 1) (Hole 3))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 92 90 [0; 1; 4] [0; 1; 2; 3; 4] [(Hole 0); (Neg (Imp (Neg (All (P 1) (Atom false (P 1) (P 2)))) (Imp (All (P 3) (Atom false (P 4) (P 2))) (All (P 1) (Atom false (P 4) (P 2)))))); (Hole 1); (Hole 2)] [(Hole 0)];
  cert_detach 8 93 [0] [0; 1; 2; 3; 3] [(Hole 0); (Imp (Neg (All (P 1) (Atom false (P 1) (P 2)))) (Imp (All (P 3) (Atom false (P 3) (P 2))) (All (P 1) (Atom false (P 3) (P 2))))); (Hole 1)] [(Hole 0); (Neg (All (P 1) (Atom false (P 1) (P 2)))); (Atom false (P 3) (P 2))];
  cert_detach 3 94 [0] [0; 1; 2; 3] [(Hole 0); (Imp (Neg (All (P 1) (Atom false (P 1) (P 2)))) (Imp (All (P 3) (Atom false (P 3) (P 2))) (All (P 1) (Atom false (P 3) (P 2))))); (Hole 1)] [(Hole 0); (Neg (Hole 1))];
  cert_detach 95 4 [0; 1; 2; 3] [0] [(Hole 0); (Imp (Hole 1) (Imp (Hole 2) (Hole 1)))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 88 96 [0] [0; 1; 2; 3] [(Hole 0); (Neg (All (P 1) (Atom false (P 1) (P 2)))); (Imp (All (P 3) (Atom false (P 3) (P 2))) (All (P 1) (Atom false (P 3) (P 2))))] [(Hole 0)];
  cert_detach 3 97 [0] [0; 3; 2; 1] [(Hole 0); (All (P 3) (Atom false (P 3) (P 2))); (Neg (Imp (All (P 1) (Atom false (P 1) (P 2))) (All (P 3) (Atom false (P 1) (P 2)))))] [(Hole 0)];
  cert_detach 4 73 [0] [0; 1; 2; 3] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (Imp (All (P 3) (Atom false (P 3) (P 2))) (All (P 1) (Atom false (P 3) (P 2))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 99 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 1) (P 2))); (Imp (All (P 3) (Atom false (P 3) (P 2))) (All (P 1) (Atom false (P 3) (P 2))))] [(Hole 0); (Hole 1)];
  cert_detach 100 98 [0; 3; 2; 4] [0; 1; 2; 3] [(Hole 0); (Neg (Imp (All (P 1) (Atom false (P 1) (P 2))) (All (P 3) (Atom false (P 1) (P 2)))))] [(Hole 0)];
  cert_detach 8 101 [0] [0; 1; 2; 3; 1] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (All (P 3) (Atom false (P 1) (P 2)))); (Hole 1)] [(Hole 0)];
  cert_detach 3 102 [0] [0; 1; 2; 3] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (All (P 3) (Atom false (P 1) (P 2)))); (Hole 1)] [(Hole 0); (Neg (Hole 1))];
  cert_detach 103 4 [0; 1; 2; 3] [0] [(Hole 0); (Imp (Hole 1) (Imp (Hole 2) (Hole 1)))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_gen 104 4;
  cert_detach 10 105 [0; 1] [0; 1; 2; 3; 1] [(Hole 0); (Hole 1); (Atom false (P 1) (P 2)); (All (P 3) (Atom false (P 1) (P 2)))] [(Hole 0)];
  cert_detach 4 48 [0] [0; 1; 2] [(Hole 0); (Imp (All (P 1) (All (P 2) (Hole 2))) (All (P 2) (All (P 1) (Hole 2)))); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2); (Hole 2)];
  cert_detach 0 107 [0] [0; 1; 2] [(Hole 0); (Hole 1); (All (P 1) (All (P 2) (Hole 2))); (All (P 2) (All (P 1) (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 108 106 [0; 1; 3] [0; 1; 2; 3] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2))); (Atom false (P 1) (P 2))] [(Hole 0)];
  cert_detach 4 109 [0] [0; 1; 2; 3] [(Hole 0); (Imp (All (P 1) (Atom false (P 1) (P 2))) (All (P 3) (All (P 1) (Atom false (P 1) (P 2))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 110 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 1) (P 2))); (All (P 3) (All (P 1) (Atom false (P 1) (P 2))))] [(Hole 0); (Hole 1)];
  cert_detach 111 41 [0; 1; 2; 3] [0] [(Hole 0); (Neg (Neg (All (P 1) (Atom false (P 1) (P 2)))))] [(Hole 0); (All (P 1) (Atom false (P 1) (P 2)))];
  cert_detach 88 112 [0] [0; 1; 2; 3] [(Hole 0); (Neg (Neg (All (P 1) (Atom false (P 1) (P 2))))); (All (P 3) (All (P 1) (Atom false (P 1) (P 2))))] [(Hole 0)];
  cert_detach 3 113 [0] [0; 2; 3; 1] [(Hole 0); (Neg (All (P 2) (Atom false (P 2) (P 3)))); (Neg (All (P 1) (All (P 2) (Atom false (P 2) (P 3)))))] [(Hole 0)];
  cert_detach 4 114 [0] [0; 1; 2; 3] [(Hole 0); (Imp (Neg (All (P 1) (All (P 2) (Atom false (P 2) (P 3))))) (Neg (All (P 2) (Atom false (P 2) (P 3))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 115 [0] [0; 1; 2; 3] [(Hole 0); (Hole 1); (Neg (All (P 1) (All (P 2) (Atom false (P 2) (P 3))))); (Neg (All (P 2) (Atom false (P 2) (P 3))))] [(Hole 0); (Hole 1)];
  cert_detach 116 16 [0; 2; 3; 4] [0; 1] [(Hole 0); (All (P 1) (Neg (All (P 2) (All (P 3) (Atom false (P 3) (P 4))))))] [(Hole 0); (Hole 1); (Neg (All (P 2) (All (P 3) (Atom false (P 3) (P 4)))))];
  cert_gen 117 5;
  cert_detach 10 118 [0; 1] [0; 1; 2; 3; 4; 1] [(Hole 0); (Hole 1); (Neg (All (P 2) (All (P 3) (Atom false (P 3) (P 4))))); (Neg (All (P 3) (Atom false (P 3) (P 4))))] [(Hole 0)];
  cert_detach 4 119 [0] [0; 1; 2; 3; 4] [(Hole 0); (Imp (All (P 1) (Neg (All (P 2) (All (P 3) (Atom false (P 3) (P 4)))))) (All (P 1) (Neg (All (P 3) (Atom false (P 3) (P 4)))))); (Hole 1)] [(Hole 0)];
  cert_detach 0 120 [0] [0; 1; 2; 3; 4] [(Hole 0); (Hole 1); (All (P 1) (Neg (All (P 2) (All (P 3) (Atom false (P 3) (P 4)))))); (All (P 1) (Neg (All (P 3) (Atom false (P 3) (P 4)))))] [(Hole 0); (Hole 1)];
  cert_detach 121 22 [0; 3; 3; 1; 2] [0; 3] [(Hole 0); (Neg (All (P 1) (Atom false (P 1) (P 2))))] [(Hole 0); (Hole 1); (All (P 1) (Atom false (P 1) (P 2)))];
  cert_detach 11 77 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Hole 1)); (Hole 3)] [(Hole 0); (Imp (Hole 1) (Imp (Imp (Hole 2) (Hole 1)) (Hole 3))); (Hole 1); (Hole 2)];
  cert_detach 78 0 [0] [0] [(Hole 0); (Imp (Hole 1) (Imp (Hole 2) (Hole 3))); (Imp (Imp (Hole 1) (Hole 2)) (Imp (Hole 1) (Hole 3))); (Hole 4)] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 123 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Imp (Imp (Hole 3) (Hole 2)) (Hole 4))) (Imp (Hole 2) (Hole 4))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 125 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Imp (Hole 3) (Hole 2)) (Hole 4))); (Imp (Hole 2) (Hole 4))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 126 124 [0] [0] [(Hole 0); (Imp (Hole 1) (Imp (Hole 2) (Hole 3))); (Hole 2); (Hole 1); (Imp (Hole 1) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 2)];
  cert_detach 6 88 [0] [0] [(Hole 0); (Imp (Neg (Hole 1)) (Hole 2)); (Hole 1); (Neg (Hole 2))] [(Hole 0); (Neg (Hole 1)); (Hole 2)];
  cert_detach 4 128 [0] [0] [(Hole 0); (Imp (Imp (Neg (Hole 2)) (Hole 3)) (Imp (Neg (Hole 3)) (Hole 2))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 52 129 [0] [0] [(Hole 0); (Imp (Neg (Hole 1)) (Hole 2)); (Hole 3); (Imp (Neg (Hole 2)) (Hole 1))] [(Hole 0); (Imp (Imp (Neg (Hole 1)) (Hole 2)) (Hole 3)); (Hole 2); (Hole 1)];
  cert_detach 6 8 [0] [0] [(Hole 0); (Imp (Neg (Hole 1)) (Hole 1)); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Neg (Hole 2))];
  cert_detach 0 131 [0] [0] [(Hole 0); (Imp (Neg (Hole 1)) (Hole 1)); (Hole 2); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 132 4 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Neg (Hole 1)) (Hole 1)))] [(Hole 0); (Imp (Neg (Hole 1)) (Hole 1)); (Hole 2)];
  cert_detach 4 133 [0] [0] [(Hole 0); (Imp (Imp (Neg (Hole 2)) (Hole 2)) (Hole 2)); (Hole 1)] [(Hole 0); (Hole 2)];
  cert_detach 0 134 [0] [0] [(Hole 0); (Hole 1); (Imp (Neg (Hole 2)) (Hole 2)); (Hole 2)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 4 135 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Imp (Neg (Hole 3)) (Hole 3))) (Imp (Hole 2) (Hole 3))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 136 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Neg (Hole 3)) (Hole 3))); (Imp (Hole 2) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 137 51 [0] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Imp (Neg (Hole 2)) (Hole 1)); (Hole 2)] [(Hole 0); (Hole 1); (Hole 2); (Neg (Hole 2))];
  cert_detach 4 130 [0] [0] [(Hole 0); (Imp (Imp (Imp (Neg (Hole 2)) (Hole 3)) (Hole 4)) (Imp (Imp (Neg (Hole 3)) (Hole 2)) (Hole 4))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 139 [0] [0] [(Hole 0); (Hole 1); (Imp (Imp (Neg (Hole 2)) (Hole 3)) (Hole 4)); (Imp (Imp (Neg (Hole 3)) (Hole 2)) (Hole 4))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 140 138 [0] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Hole 2); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 4 141 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Hole 3)) (Imp (Imp (Neg (Hole 2)) (Hole 3)) (Hole 3))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 142 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Hole 3)); (Imp (Imp (Neg (Hole 2)) (Hole 3)) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 78 16 [0] [0; 1] [(Hole 0); (All (P 1) (Hole 1)); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Hole 1)];
  cert_gen 144 2;
  cert_detach 10 145 [0; 1] [0; 1; 1] [(Hole 0); (Hole 1); (Hole 1); (Imp (Hole 2) (Hole 1))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 4 146 [0] [0; 1] [(Hole 0); (Imp (All (P 1) (Hole 2)) (All (P 1) (Imp (Hole 3) (Hole 2)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 147 [0] [0; 1] [(Hole 0); (Hole 1); (All (P 1) (Hole 2)); (All (P 1) (Imp (Hole 3) (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 51 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Hole 3)) (Imp (Imp (Hole 4) (Hole 2)) (Imp (Hole 4) (Hole 3)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 149 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Hole 3)); (Imp (Imp (Hole 4) (Hole 2)) (Imp (Hole 4) (Hole 3)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 150 148 [0] [0; 1] [(Hole 0); (Imp (Hole 1) (All (P 1) (Hole 2))); (Hole 1); (All (P 1) (Imp (Hole 4) (Hole 2))); (Hole 3)] [(Hole 0); (Hole 1); (Hole 2); (Hole 4)];
  cert_detach 4 143 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Imp (Hole 3) (Hole 4))) (Imp (Hole 2) (Imp (Imp (Neg (Hole 3)) (Hole 4)) (Hole 4)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 152 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Hole 3) (Hole 4))); (Imp (Hole 2) (Imp (Imp (Neg (Hole 3)) (Hole 4)) (Hole 4)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 153 151 [0] [0; 1] [(Hole 0); (Imp (Hole 1) (All (P 1) (Hole 2))); (Imp (Hole 3) (Hole 1)); (Hole 3); (All (P 1) (Imp (Hole 4) (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 4 127 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Imp (Hole 3) (Hole 4))) (Imp (Hole 3) (Imp (Hole 2) (Hole 4)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 155 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Imp (Hole 3) (Hole 4))); (Imp (Hole 3) (Imp (Hole 2) (Hole 4)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 156 154 [0] [0; 1] [(Hole 0); (Imp (Hole 1) (All (P 1) (Hole 2))); (Imp (Hole 3) (Hole 1)); (Imp (Neg (Hole 3)) (All (P 1) (Imp (Hole 4) (Hole 2)))); (All (P 1) (Imp (Hole 4) (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 157 [0] [0; 1] [(Hole 0); (Imp (Hole 1) (All (P 1) (Hole 2))); (Imp (Neg (Hole 3)) (All (P 1) (Imp (Hole 4) (Hole 2)))); (Imp (Imp (Hole 3) (Hole 1)) (All (P 1) (Imp (Hole 4) (Hole 2))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 4 158 [0] [0; 1] [(Hole 0); (Imp (Imp (Imp (Hole 2) (All (P 1) (Hole 3))) (Imp (Neg (Hole 4)) (All (P 1) (Imp (Hole 5) (Hole 3))))) (Imp (Imp (Hole 2) (All (P 1) (Hole 3))) (Imp (Imp (Hole 4) (Hole 2)) (All (P 1) (Imp (Hole 5) (Hole 3)))))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4); (Hole 5)];
  cert_detach 0 159 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (Imp (Hole 2) (All (P 1) (Hole 3))) (Imp (Neg (Hole 4)) (All (P 1) (Imp (Hole 5) (Hole 3))))); (Imp (Imp (Hole 2) (All (P 1) (Hole 3))) (Imp (Imp (Hole 4) (Hole 2)) (All (P 1) (Imp (Hole 5) (Hole 3)))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4); (Hole 5)];
  cert_detach 160 4 [0; 1] [0] [(Hole 0); (Imp (Neg (Hole 1)) (All (P 1) (Imp (Hole 2) (Hole 3)))); (Hole 4); (Hole 3); (Hole 1); (Hole 2)] [(Hole 0); (Imp (Neg (Hole 1)) (All (P 1) (Imp (Hole 2) (Hole 3)))); (Imp (Hole 4) (All (P 1) (Hole 3)))];
  cert_detach 150 7 [0] [0] [(Hole 0); (Neg (Hole 1)); (Hole 1); (Hole 3); (Hole 2)] [(Hole 0); (Hole 1); (Hole 3)];
  cert_detach 83 162 [0; 1] [0] [(Hole 0); (Neg (Hole 1)); (Imp (Hole 2) (Hole 1)); (Imp (Hole 2) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 163 [0] [0; 1] [(Hole 0); (Imp (Neg (Hole 2)) (Imp (All (P 1) (Imp (Hole 3) (Hole 2))) (Imp (Hole 3) (Hole 4)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 164 [0] [0; 1] [(Hole 0); (Hole 1); (Neg (Hole 2)); (Imp (All (P 1) (Imp (Hole 3) (Hole 2))) (Imp (Hole 3) (Hole 4)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 165 16 [0; 2] [0; 1] [(Hole 0); (All (P 1) (Neg (Hole 1))); (Hole 1); (Hole 2); (Hole 3)] [(Hole 0); (Hole 1); (Neg (Hole 1))];
  cert_gen 166 3;
  cert_detach 10 167 [0; 1] [0; 1; 2; 1] [(Hole 0); (Hole 1); (Neg (Hole 1)); (Imp (All (P 2) (Imp (Hole 2) (Hole 1))) (Imp (Hole 2) (Hole 3)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 10 [0] [0; 1] [(Hole 0); (Imp (All (P 1) (Imp (All (P 1) (Hole 2)) (Hole 3))) (Imp (All (P 1) (Hole 2)) (All (P 1) (Hole 3)))); (Hole 1)] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 0 169 [0] [0; 1] [(Hole 0); (Hole 1); (All (P 1) (Imp (All (P 1) (Hole 2)) (Hole 3))); (Imp (All (P 1) (Hole 2)) (All (P 1) (Hole 3)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 170 168 [0; 1] [0; 1; 1] [(Hole 0); (All (P 1) (Neg (Hole 1))); (Imp (Hole 2) (Hole 1)); (Imp (Hole 2) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 171 [0] [0; 1] [(Hole 0); (Imp (All (P 1) (Neg (Hole 2))) (Imp (All (P 1) (Imp (Hole 3) (Hole 2))) (All (P 1) (Imp (Hole 3) (Hole 4))))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 172 [0] [0; 1] [(Hole 0); (Hole 1); (All (P 1) (Neg (Hole 2))); (Imp (All (P 1) (Imp (Hole 3) (Hole 2))) (All (P 1) (Imp (Hole 3) (Hole 4))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 173 22 [0; 1] [0; 1] [(Hole 0); (Neg (Hole 1)); (All (P 1) (Hole 1)); (Hole 2); (Hole 3)] [(Hole 0); (Hole 1); (Hole 1)];
  cert_detach 0 174 [0] [0; 1] [(Hole 0); (Neg (Hole 1)); (All (P 1) (Imp (Hole 2) (All (P 1) (Hole 1)))); (All (P 1) (Imp (Hole 2) (Hole 3)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 4 175 [0] [0; 1] [(Hole 0); (Imp (Imp (Neg (Hole 2)) (All (P 1) (Imp (Hole 3) (All (P 1) (Hole 2))))) (Imp (Neg (Hole 2)) (All (P 1) (Imp (Hole 3) (Hole 4))))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 0 176 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (Neg (Hole 2)) (All (P 1) (Imp (Hole 3) (All (P 1) (Hole 2))))); (Imp (Neg (Hole 2)) (All (P 1) (Imp (Hole 3) (Hole 4))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4)];
  cert_detach 177 4 [0; 1] [0] [(Hole 0); (All (P 1) (Imp (Hole 1) (All (P 1) (Hole 2)))); (Hole 2); (Hole 1); (Hole 3)] [(Hole 0); (All (P 1) (Imp (Hole 1) (All (P 1) (Hole 2)))); (Neg (Hole 2))];
  cert_detach 4 161 [0] [0; 1] [(Hole 0); (Imp (Imp (Neg (Hole 2)) (All (P 1) (Imp (Hole 3) (Hole 4)))) (Imp (Imp (Hole 5) (All (P 1) (Hole 4))) (Imp (Imp (Hole 2) (Hole 5)) (All (P 1) (Imp (Hole 3) (Hole 4)))))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3); (Hole 4); (Hole 5)];
  cert_detach 0 179 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (Neg (Hole 2)) (All (P 1) (Imp (Hole 3) (Hole 4)))); (Imp (Imp (Hole 5) (All (P 1) (Hole 4))) (Imp (Imp (Hole 2) (Hole 5)) (All (P 1) (Imp (Hole 3) (Hole 4)))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3); (Hole 4); (Hole 5)];
  cert_detach 180 178 [0; 1] [0; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (All (P 1) (Hole 2)))); (Hole 2); (Hole 1); (Hole 4); (Hole 3)] [(Hole 0); (Hole 1); (Hole 2); (Hole 4)];
  cert_detach 52 43 [0] [0; 1] [(Hole 0); (All (P 1) (Neg (All (P 1) (Hole 1)))); (Hole 2); (Neg (Hole 1))] [(Hole 0); (Imp (All (P 1) (Neg (All (P 1) (Hole 1)))) (Hole 2)); (Hole 1)];
  cert_detach 11 40 [0] [0] [(Hole 0); (Neg (Neg (Hole 1))); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Imp (Hole 1) (Hole 2))];
  cert_detach 4 183 [0] [0] [(Hole 0); (Imp (Imp (Neg (Neg (Hole 2))) (Imp (Hole 2) (Hole 3))) (Imp (Neg (Neg (Hole 2))) (Hole 3))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 184 [0] [0] [(Hole 0); (Hole 1); (Imp (Neg (Neg (Hole 2))) (Imp (Hole 2) (Hole 3))); (Imp (Neg (Neg (Hole 2))) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 185 4 [0] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Hole 1); (Hole 2)] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Neg (Neg (Hole 1)))];
  cert_detach 6 186 [0] [0] [(Hole 0); (Imp (Hole 1) (Neg (Hole 2))); (Neg (Hole 1)); (Hole 2)] [(Hole 0); (Hole 1); (Neg (Hole 2))];
  cert_detach 4 187 [0] [0] [(Hole 0); (Imp (Imp (Hole 2) (Neg (Hole 3))) (Imp (Hole 3) (Neg (Hole 2)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 188 [0] [0] [(Hole 0); (Hole 1); (Imp (Hole 2) (Neg (Hole 3))); (Imp (Hole 3) (Neg (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 189 88 [0] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Hole 1); (Neg (Hole 2))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 83 190 [0; 1] [0] [(Hole 0); (Imp (Hole 1) (Hole 2)); (Neg (Hole 2)); (Neg (Hole 1))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 4 191 [0] [0; 1] [(Hole 0); (Imp (Imp (Hole 2) (Hole 3)) (Imp (All (P 1) (Neg (Hole 3))) (Neg (Hole 2)))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 192 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (Hole 2) (Hole 3)); (Imp (All (P 1) (Neg (Hole 3))) (Neg (Hole 2)))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 193 16 [0; 2] [0; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (Hole 2))); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Imp (Hole 1) (Hole 2))];
  cert_gen 194 3;
  cert_detach 10 195 [0; 1] [0; 1; 2; 1] [(Hole 0); (Hole 1); (Imp (Hole 1) (Hole 2)); (Imp (All (P 2) (Neg (Hole 2))) (Neg (Hole 1)))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 170 196 [0; 1] [0; 1; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (Hole 2))); (Neg (Hole 2)); (Neg (Hole 1))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 4 182 [0] [0; 1] [(Hole 0); (Imp (Imp (All (P 1) (Neg (All (P 1) (Hole 2)))) (Hole 3)) (Imp (Neg (Hole 2)) (Hole 3))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 198 [0] [0; 1] [(Hole 0); (Hole 1); (Imp (All (P 1) (Neg (All (P 1) (Hole 2)))) (Hole 3)); (Imp (Neg (Hole 2)) (Hole 3))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 199 197 [0; 1] [0; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (All (P 1) (Hole 2)))); (Hole 2); (All (P 1) (Neg (Hole 1)))] [(Hole 0); (Hole 1); (All (P 1) (Hole 2))];
  cert_detach 83 16 [0; 2] [0; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (Hole 2))); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Imp (Hole 1) (Hole 2))];
  cert_gen 201 3;
  cert_detach 10 202 [0; 1] [0; 1; 2; 1] [(Hole 0); (Hole 1); (Imp (Hole 1) (Hole 2)); (Imp (All (P 2) (Hole 1)) (Hole 2))] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 170 203 [0; 1] [0; 1; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (Hole 2))); (Hole 1); (Hole 2)] [(Hole 0); (Hole 1); (Hole 2)];
  cert_detach 4 108 [0] [0; 1; 2] [(Hole 0); (Imp (Imp (Hole 2) (All (P 1) (All (P 2) (Hole 3)))) (Imp (Hole 2) (All (P 2) (All (P 1) (Hole 3))))); (Hole 1)] [(Hole 0); (Hole 2); (Hole 3)];
  cert_detach 0 205 [0] [0; 1; 2] [(Hole 0); (Hole 1); (Imp (Hole 2) (All (P 1) (All (P 2) (Hole 3)))); (Imp (Hole 2) (All (P 2) (All (P 1) (Hole 3))))] [(Hole 0); (Hole 1); (Hole 2); (Hole 3)];
  cert_detach 206 204 [0; 1; 2] [0; 1] [(Hole 0); (All (P 1) (Imp (Hole 1) (All (P 2) (Hole 2)))); (All (P 1) (Hole 1)); (Hole 2)] [(Hole 0); (Hole 1); (All (P 2) (Hole 2))]
].
Definition L17_schema := (Imp (Atom false (P 1) (P 2)) (Imp (Atom false (P 3) (P 1)) (Atom false (P 3) (P 2)))).
Theorem L17_certificate : SchemaProvable L17_schema.
Proof. eapply certificate_sound with (steps := megill_certificates) (result := ltac:(let x := eval vm_compute in (certificate_build [] megill_certificates) in lazymatch x with Some ?l => exact l end)) (i:=38); vm_compute; reflexivity. Qed.
Print Assumptions L17_certificate.
Definition L18_schema := (Neg (All (P 1) (Neg (Atom false (P 1) (P 2))))).
Theorem L18_certificate : SchemaProvable L18_schema.
Proof. eapply certificate_sound with (steps := megill_certificates) (result := ltac:(let x := eval vm_compute in (certificate_build [] megill_certificates) in lazymatch x with Some ?l => exact l end)) (i:=47); vm_compute; reflexivity. Qed.
Print Assumptions L18_certificate.
Definition L19_schema := (Imp (Neg (All (P 1) (Atom false (P 1) (P 2)))) (All (P 3) (Neg (All (P 1) (Atom false (P 1) (P 2)))))).
Theorem L19_certificate : SchemaProvable L19_schema.
Proof. eapply certificate_sound with (steps := megill_certificates) (result := ltac:(let x := eval vm_compute in (certificate_build [] megill_certificates) in lazymatch x with Some ?l => exact l end)) (i:=122); vm_compute; reflexivity. Qed.
Print Assumptions L19_certificate.
Definition L20_schema := (Imp (All (P 1) (Imp (Hole 1) (All (P 1) (Hole 2)))) (Imp (Imp (Hole 3) (All (P 1) (Hole 4))) (Imp (Imp (Hole 2) (Hole 3)) (All (P 1) (Imp (Hole 1) (Hole 4)))))).
Theorem L20_certificate : SchemaProvable L20_schema.
Proof. eapply certificate_sound with (steps := megill_certificates) (result := ltac:(let x := eval vm_compute in (certificate_build [] megill_certificates) in lazymatch x with Some ?l => exact l end)) (i:=181); vm_compute; reflexivity. Qed.
Print Assumptions L20_certificate.
Definition L21_schema := (Imp (All (P 1) (Imp (Hole 1) (All (P 1) (Hole 2)))) (Imp (Neg (Hole 2)) (All (P 1) (Neg (Hole 1))))).
Theorem L21_certificate : SchemaProvable L21_schema.
Proof. eapply certificate_sound with (steps := megill_certificates) (result := ltac:(let x := eval vm_compute in (certificate_build [] megill_certificates) in lazymatch x with Some ?l => exact l end)) (i:=200); vm_compute; reflexivity. Qed.
Print Assumptions L21_certificate.
Definition L22_schema := (Imp (All (P 1) (Imp (Hole 1) (All (P 2) (Hole 2)))) (Imp (All (P 1) (Hole 1)) (All (P 2) (All (P 1) (Hole 2))))).
Theorem L22_certificate : SchemaProvable L22_schema.
Proof. eapply certificate_sound with (steps := megill_certificates) (result := ltac:(let x := eval vm_compute in (certificate_build [] megill_certificates) in lazymatch x with Some ?l => exact l end)) (i:=207); vm_compute; reflexivity. Qed.
Print Assumptions L22_certificate.
