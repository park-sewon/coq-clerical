Require Import Reals.
Open Scope R.
Require Import Lia Lra.
From Clerical.Preliminaries Require Import BaseAxioms.

Definition Rltb'' : R -> R -> bool.
Proof.
  intros x y.
  destruct (total_order_T x y).
  destruct s.
  exact (true)%R.
  exact (false).
  exact (false).
Defined.

Definition pow2 : Z -> R := fun x => (powerRZ 2) x.

Lemma archimed_pow2' : forall n, (0 < n)%nat -> pow2 (- Z.of_nat n) < 1 / INR n. 
Proof.
  intros.
  induction n.
  contradict H; lia.
  destruct n.
  simpl.
  lra.
  destruct n.
  simpl.
  lra.
  replace (- Z.of_nat (S (S (S n))))%Z with (- Z.of_nat (S (S n)) - 1)%Z.
  replace (1 / INR (S (S (S n)))) with (1 / (INR (S (S n)) + 1)).
  assert (0 < S (S n))%nat by lia.
  apply IHn in H0.
  replace (pow2 (- Z.of_nat (S (S n)) - 1)) with
    (pow2 (- Z.of_nat (S (S n))) /2 ).
  assert (pow2 (- Z.of_nat (S (S n)))/2 < 1 / INR (S (S n)) /2).
  lra.
  assert (1 / INR (S (S n)) / 2 < 1 / (INR (S (S n)) + 1)).
  assert (forall x,2 <= x -> x + 1 < 2 * x).
  intros.
  lra.
  pose proof (H2 (INR (S (S n)))).
  assert (2 <= INR (S (S n))).
  replace 2 with (INR (S (S O))).
  apply le_INR.
  lia.
  auto.
  apply H3 in H4.
  assert (0 < INR (S (S n)) + 1).
  lra.
  assert (0<  2 * INR (S (S n))).
  lra.
  apply (Rmult_lt_compat_l _ _ _ (Rinv_0_lt_compat _ H5)) in H4.
  apply (Rmult_lt_compat_l _ _ _ (Rinv_0_lt_compat _ H6)) in H4.
  rewrite Rinv_l in H4.
  replace (/ (2 * INR (S (S n))) * (/ (INR (S (S n)) + 1) * (2 * INR (S (S n)))))
    with (/ (2 * INR (S (S n)))  * (2 * INR (S (S n))) * (/ (INR (S (S n)) + 1))) in H4 by ring.    
  rewrite Rinv_l in H4.
  unfold Rdiv.
  unfold Rdiv in H4.
  rewrite Rinv_mult in H4.
  replace (/ 2 * / INR (S (S n)) * 1) with (1 * / INR (S (S n)) * / 2) in H4 by ring.
  auto.
  lra.
  lra.
  lra.
  unfold Rdiv.
  assert (pow2 (- 1)%Z = / 2).
  simpl.
  lra.
  rewrite <- H1.
  unfold pow2.
  rewrite <- powerRZ_add.
  apply lp.
  lia.
  lra.
  simpl.
  auto.
  simpl.
  lia.
Defined.

Lemma archimed_pow2 :forall x : R, 0 < x -> exists k, pow2 k < x.
Proof.
  intros.
  pose proof (archimed_cor1 _ H).
  destruct H0.
  exists (- Z.of_nat x0)%Z.
  destruct H0.
  pose proof (archimed_pow2' x0 H1).
  lra.
Defined.



Lemma Rltb''_prop : forall x y, Rltb'' x y = true <-> (x < y)%R.
Proof.
  intros.
  unfold Rltb''.
  destruct (total_order_T x y).
  destruct s.
  split; auto.
  split.
  intro.
  contradict H; discriminate.
  intro.
  rewrite e in H.
  contradict (Rlt_irrefl _ H).
  split; intro.
  contradict H; discriminate.
  contradict (Rlt_asym _ _ r H).
Defined.


Lemma Rabs_plus_Rabs_Rabs : forall x, (0 < x -> Rabs (x + (Rabs x)) = 2 * x) /\
                                        (x <= 0 -> Rabs (x + (Rabs x)) = 0).
Proof.
  intros.
  split.
  intro.
  rewrite (Rabs_right _ (Rgt_ge _ _ H)).
  pose proof (Rplus_lt_compat _ _ _ _ H H).
  rewrite Rplus_0_l in H0.
  rewrite (Rabs_right _ (Rgt_ge _ _ H0)).
  ring.
  intro.
  rewrite (Rabs_left1 _ H).
  rewrite Rplus_opp_r.
  apply Rabs_R0.
Defined.

Lemma Rabs_minus_Rabs_Rabs : forall x, (0 < x -> Rabs (x - (Rabs x)) = 0) /\
                                        (x <= 0 -> Rabs (x - (Rabs x)) = - 2 * x).
Proof.
  intros.
  split.
  intro.
  rewrite (Rabs_right _ (Rgt_ge _ _ H)).
  unfold Rminus.
  rewrite Rplus_opp_r.
  apply Rabs_R0.
  
  intro.
  rewrite (Rabs_left1 _ H).
  replace (x - - x) with (2 * x) by ring.
  assert (2 *x <= 0) by lra.
  rewrite (Rabs_left1 _  H0).
  ring.
Defined.

Lemma pow2_positive : forall x, 0 < pow2 x.
Proof.
  intro.
  assert (0 < 2).
  auto with real.
  pose proof (powerRZ_le _ x H).
  destruct H0.
  exact H0.
  assert (2 <> 0).
  auto with real.
  pose proof (powerRZ_NOR 2 x H1).
  contradict H2; auto.
Defined.

Lemma pow2_add : forall x y, pow2 (x + y) = pow2 x * pow2 y.
Proof.
  intros.
  assert (2 <> 0).
  auto with real.
  apply (powerRZ_add 2 x y H).
Defined.

  
Lemma pow2_add_one : forall x,  pow2 (x + 1) = pow2 x + pow2 x.
Proof.
  intro.
  rewrite pow2_add.
  simpl.
  ring.
Defined.

Lemma overlap_splitting : forall x y z, x < z -> x < y \/ y < z.
Proof.
  intros.
  destruct (Rlt_or_le x y).
  left; auto.
  right.
  apply (Rle_lt_trans _ _ _ H0 H).
Defined.

Lemma overlap_splitting_symmetric : forall x z, 0 < x -> - x < z  \/ z < x.
Proof.
  intros.
  apply overlap_splitting.
  lra.
Defined.


Lemma pow2_increasing' : forall a n, pow2 a <= pow2 (a + Z.of_nat n).
Proof.
  intros.
  induction n.
  simpl.
  replace (a + 0)%Z with a by ring.
  right; auto.
  replace (a + Z.of_nat (S n))%Z with
    ((a + Z.of_nat n) + 1)%Z by lia.
  rewrite pow2_add_one.
  pose proof (pow2_positive (a + Z.of_nat n)).
  lra.
Defined.

Lemma pow2_increasing'' : forall a n, (0 < n)%nat -> pow2 a < pow2 (a + Z.of_nat n).
Proof.
  intros.
  induction n.
  contradict H; lia.
  destruct n.
  rewrite pow2_add_one.
  pose proof (pow2_positive a).
  lra.
  assert (0 < S n)%nat by lia.
  apply IHn in H0.
  clear IHn.
  replace (a + Z.of_nat (S (S n)))%Z with
    ((a + Z.of_nat (S n)) + 1)%Z by lia.
  rewrite pow2_add_one.
  pose proof (pow2_positive (a + Z.of_nat (S n))).
  lra.
Defined.

Lemma pow2_increasing : forall a b, (a < b)%Z -> pow2 a < pow2 b.
Proof.
  intros.
  assert (0 < Z.to_nat (b - a))%nat by lia.
  assert (b = a + (Z.of_nat (Z.to_nat (b - a))))%Z by lia.
  rewrite H1.
  apply pow2_increasing''; auto.
Defined.

Lemma pow2_monotone : forall a b, (a <= b)%Z -> pow2 a <= pow2 b.
Proof.
  intros.
  assert (b = a + (Z.of_nat (Z.to_nat (b - a))))%Z by lia.
  rewrite H0.
  apply pow2_increasing'; auto.
Defined.


  
Lemma Rltb''_prop_false : forall x y,
    Rltb'' x y = false <-> y <= x.
Proof.
  intros.
  unfold Rltb''.
  destruct (total_order_T x y).
  destruct s.
  split.
  intro.
  contradict H; discriminate.
  intro.
  contradict (Rle_not_lt _ _ H r).
  split; intro; auto.
  right; auto.
  split; intro; auto.
  left; auto.
Defined.

Lemma pow2_minus_one : forall x,
    pow2 x / 2 = pow2 (x - 1).
Proof.
  intro.
  unfold Zminus.
  rewrite pow2_add.
  simpl.
  replace (2 * 1) with 2 by ring.
  unfold Rdiv; ring.
Defined.
  
