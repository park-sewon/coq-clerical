Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra Lia List.
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


Lemma PI_in_34 : 3 < PI < 4.
Proof.
Admitted.


Lemma PI_unique_in_34 :
  forall s, 3<s<4 -> sin s = 0 -> s = PI.
Admitted.

Lemma PI_simple_in_34 :
  forall s, 3<s<4 -> (sin s < 0 -> PI < s) /\ (0 < sin s ->  s < PI).
Admitted.

Definition is_rational x : Prop :=
  exists p q, q <> 0%Z /\ x = IZR p / IZR q. 
Lemma PI_irrational :
  is_rational PI -> False.
Admitted.


Lemma Z_is_rational : forall z, is_rational (IZR z).
Proof.
  intros.
  exists z.
  exists 1%Z.
  unfold Rdiv.
  replace (/1) with 1 by auto with real.
  split; auto with real; try lia.
Defined.

Lemma rationals_add_rational : forall x y, is_rational x -> is_rational y-> is_rational (x + y).
Proof.
  intros x y [p1 [q1 [z1 e1]]] [p2 [q2 [z2 e2]]].
  exists (p1 * q2 + p2 * q1)%Z.
  exists (q1 * q2)%Z.
  rewrite e1.
  rewrite e2.
  split; auto.
  lia.
  field_simplify.
  repeat rewrite <- mult_IZR.
  repeat rewrite <- plus_IZR.
  replace (q1 * p2)%Z with (p2 * q1)%Z by ring.
  reflexivity.
  apply not_0_IZR.
  lia.
  split; apply not_0_IZR; lia.
Defined.

Lemma rationals_mult_rational : forall x y, is_rational x -> is_rational y-> is_rational (x * y).
Proof.
  intros x y [p1 [q1 [z1 e1]]] [p2 [q2 [z2 e2]]].
  exists (p1 * p2)%Z.
  exists (q1 * q2)%Z.
  rewrite e1.
  rewrite e2.
  split; auto.
  lia.
  field_simplify.
  repeat rewrite <- mult_IZR.
  repeat rewrite <- plus_IZR.
  replace (q1 * p2)%Z with (p2 * q1)%Z by ring.
  reflexivity.
  apply not_0_IZR.
  lia.
  split; apply not_0_IZR; lia.
Defined.


Lemma rational_recip_rational : forall x, x <> 0 -> is_rational x ->
                                          is_rational (/x).
Proof.
  intros x h [p [q [z e]]].
  exists q.
  exists p.
  assert (p <> 0)%Z.
  intro.
  rewrite H in e.
  contradict h.
  lra.
  split; auto.
  rewrite e.
  field_simplify.
  reflexivity.
  apply not_0_IZR.
  auto.
  split; apply not_0_IZR; lia.
Defined.

  
Lemma ratoinals_midpoint_is_rational :
  forall x y, is_rational x -> is_rational y -> is_rational ((x + y) / 2).
Proof.
  intros.
  apply rationals_mult_rational.
  apply rationals_add_rational; auto.
  apply rational_recip_rational.
  auto.
  apply Z_is_rational.
Defined.

Lemma midpoint_in_interval :
  forall x y, x < y -> x < (x + y)/2 < y.
Proof.
  intros.
  lra.
Defined.

Lemma dist_between_points_in_interval : forall a b c d,
    a < b -> a < c < b -> a < d < b ->
    Rabs (c - d) < b - a.
Proof.
  intros.
  destruct (Rtotal_order c d).
  assert (c - d <= 0) by lra.
  rewrite (Rabs_left1 _ H3).
  lra.
  assert (c - d >= 0) by lra.
  rewrite (Rabs_right _ H3).
  lra.
Defined.


