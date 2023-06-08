Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.
From Clerical.Preliminaries Require Import Preliminaries.
(*
  This file develops mathemtical theory that is used in the verification of Clerical programs.



  - sin : R -> R is the sin function
  - sin_n := fun n => (-1) ^ n / INR (fact (2 * n + 1)) : nat -> R
      is the coefficient of the taylor expansion:
      sin x = infinite_sum n => infty. (sin_n n) * x^n 
      
 *)

(* partial sum term *)
Fixpoint sin_q n x : R
  := match n with
     | O => x
     | S m => - x * x * (sin_q m x) / (INR (2 * m + 3)%nat) / (INR (2 * m + 2)%nat)
     end.

Fixpoint sin_A n x : R
  := match n with
     | O => x
     | S m => sin_q (S m) x + sin_A m x 
     end.

Lemma Rtheorem : forall n x,
    Rabs (sin x - sin_A n x) < Rabs (sin_q (S n) x).
Proof.
Admitted.

Lemma Rconverge : forall x,
    forall n, exists m, forall k, (m <= k)%nat -> Rabs (sin_q (S k) x) < pow2 (- n).
Admitted.

