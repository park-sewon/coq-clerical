Require Import ZArith.
Require Import Reals.
Open Scope R_scope.
Require Import Lra Lia.


From Clerical Require Import Preliminaries.

Require Import PowerdomainInfinite.
Require Import PowerdomainMonad.
Require Import PowerdomainProperties.
Require Import PowerdomainCompleteness.
Require Import PowerdomainOrderProperties.
Require Import PowerdomainFixedpoints.



Definition Rrecip' : R -> flat R.
Proof.
  intro x.
  destruct (total_order_T x 0).
  destruct s.
  exact (total (/x))%R.
  exact (bot R).
  exact (total (/x))%R.
Defined.


Definition Rltb' : R -> R -> flat bool.
Proof.
  intros x y.
  destruct (total_order_T x y).
  destruct s.
  exact (total true)%R.
  exact (bot bool).
  exact (total false)%R.
Defined.

Definition Rrecip : R -> pdom R := fun x => flat_to_pdom (Rrecip' x).

Definition Rltb : R -> R -> pdom bool := fun x y => flat_to_pdom (Rltb' x y).

Definition Rlim_def (f : Z -> pdom R) : flat R -> Prop :=
  (fun y : flat R =>
     exists y' : R, y = total y' /\                            
                      forall x : Z,
                        ~ pdom_is_empty (f x) /\ 
                          forall z : flat R,
                            proj1_sig (f x) z ->
                            exists z' : R, z = total z' /\ Rabs (z' - y') < powerRZ 2 (- x))%R.


Lemma Rlim_def_unique f : forall x y, Rlim_def f x -> Rlim_def f y -> x = y.
Proof.
  intros x y H H0.
  destruct H as [x' [tx hx]].
  destruct H0 as [y' [ty hy]].
  rewrite tx, ty; apply lp.
  clear tx ty.

  destruct (lem (x' = y')); auto.
  destruct (Rdichotomy _ _ H).
  (* when x' < y' *)
  clear H.
  assert (0 < y' - x') by lra.
  pose proof (archimed_pow2 _ H).
  destruct H1 as [k o].

  pose proof (hx (- k + 1)%Z) as [xk hxk].
  pose proof (hy (- k + 1)%Z) as [yk hyk].
  apply pdom_neg_empty_exists in xk as [xk mx].
  (* apply pdom_neg_empty_exists in yk as [yk my]. *)
  pose proof (hxk _ mx) as [zx [p1 p2]].
  (* pose proof (hyk _ my) as [zy [q1 q2]]. *)
  pose proof (hyk _ mx) as [zy [q1 q2]].
  rewrite p1 in q1.
  apply total_is_injective in q1.
  induction q1.
  pose proof (Rplus_lt_compat _ _ _ _ p2 q2).
  rewrite <- Rabs_Ropp in H1 at 1.
  pose proof (Rle_lt_trans _ _ _ (Rabs_triang _ _) H1).
  replace (- (zx - x') + (zx - y')) with (x' - y') in H2 by ring.
  replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1))) with (pow2 k) in H2.
  rewrite Rabs_left in H2.
  replace ( - (x' - y')) with (y' - x') in H2 by ring.
  contradict (Rlt_asym _ _ H2 o).
  lra.
  replace (- (- k + 1))%Z with (k + - 1)%Z by ring.
  rewrite powerRZ_add.
  simpl.
  unfold pow2.
  lra.
  lra.

  (* when y' < x' *)
  clear H.
  assert (0 < x' - y') by lra.
  pose proof (archimed_pow2 _ H).
  destruct H1 as [k o].

  pose proof (hx (- k + 1)%Z) as [xk hxk].
  pose proof (hy (- k + 1)%Z) as [yk hyk].
  apply pdom_neg_empty_exists in xk as [xk mx].
  (* apply pdom_neg_empty_exists in yk as [yk my]. *)
  pose proof (hxk _ mx) as [zx [p1 p2]].
  (* pose proof (hyk _ my) as [zy [q1 q2]]. *)
  pose proof (hyk _ mx) as [zy [q1 q2]].
  rewrite p1 in q1.
  apply total_is_injective in q1.
  induction q1.
  pose proof (Rplus_lt_compat _ _ _ _ p2 q2).
  rewrite <- Rabs_Ropp in H1 at 1.
  pose proof (Rle_lt_trans _ _ _ (Rabs_triang _ _) H1).
  replace (- (zx - x') + (zx - y')) with (x' - y') in H2 by ring.
  replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1))) with (pow2 k) in H2.
  rewrite Rabs_right in H2.
  contradict (Rlt_asym _ _ H2 o).
  lra.
  replace (- (- k + 1))%Z with (k + - 1)%Z by ring.
  rewrite powerRZ_add.
  simpl.
  unfold pow2.
  lra.
  lra.
Defined.

Lemma Rlim_def_never_bot : forall f, ~ (Rlim_def f (bot R)).
Proof.
  intro.
  intro.
  destruct H.
  destruct H.
  contradict (flat_bot_neq_total _ H).
Defined.

Definition Rlim : (Z -> pdom R) -> pdom R.
Proof.
  intro f.
  exists (Rlim_def f).
  intro H.
  apply pset_infinite_subset_infinite in H.
  contradict H.
  apply hprop_ninfinite.
  intros.
  destruct x, y.
  apply sig_eq.
  simpl.
  apply (Rlim_def_unique f); auto.
Defined.

