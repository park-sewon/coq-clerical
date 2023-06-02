From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals.

(* computing the absolute value of variable k *)
Definition exp_abs k :=  
  Lim
    (CASE
       VAR (S k) ;<; EXP ( :-: (VAR 0) :-: (INT 1))
       ==> ;-; VAR (S k)
       OR
       ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k) 
       ==> VAR (S k)
       END)
.

Lemma exp_abs_wty :
  forall Γ k, Γ |- VAR k : REAL ->
                         Γ |- exp_abs k : REAL. 
  intros.
  auto_typing.
Defined.

Require Import Reals.
Open Scope R.
Require Import Lra.


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
  Check Rabs_left.
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


Lemma exp_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    Γ |--
      [{fun _ => True}]
      exp_abs k 
      [{y : REAL | fun x => y = Rabs (ro_access Γ k REAL w x) }].
Proof.
  intros.
  apply (pp_ro_lim_tot_util_known_limit (fun x =>  Rabs (ro_access Γ k REAL w x)));
    try (intros h1 h2 [_ h3]; auto; fail).
  apply (pp_ro_rw_tot_back).
  apply (pp_rw_case_tot
           (Γ := (INTEGER :: Γ))
           (θ1 := ( fun b x => b = true -> (ro_access _ _ _ w (snd (snd_app x))) <
                                      pow2 (- ((fst (snd_app x))) - 1)%Z))
           (θ2 := ( fun b x => b = true -> - (ro_access _ _ _ w (snd (snd_app x))) <
                                      pow2 (- ((fst (snd_app x))) - 1)%Z))
           
           (ϕ1 := ( fun x =>  (ro_access _ _ _ w (snd (snd_app x))) <
                         pow2 (- ((fst (snd_app x))) - 1)%Z))
           (ϕ2 := ( fun x =>  - pow2 (- ((fst (snd_app x))) - 1)%Z < (ro_access _ _ _ w (snd (snd_app x)))))
        ); simpl.
  
  proves_simple_arithmetical.
  intro e.
  rewrite e in val.
  apply eq_sym in val.
  apply (proj1 (Rltb''_prop _ _)) in val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S, ro_access_Var_0 in val.
  rewrite (ro_access_typing_irrl _ _ _ w (has_type_ro_Var_S_inv Γ k INTEGER REAL h)).
  exact val.

  proves_simple_arithmetical.
  intro e.
  rewrite e in val.
  apply eq_sym in val.
  apply (proj1 (Rltb''_prop _ _)) in val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S, ro_access_Var_0 in val.
  rewrite (ro_access_typing_irrl _ _ _ w (has_type_ro_Var_S_inv Γ k INTEGER REAL h0)).
  lra.

  proves_simple_arithmetical.
  unfold ro_to_rw_pre in pre.
  pose proof (pre eq_refl).
  rewrite val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S.
  simpl in H.
  rewrite <- Rabs_Ropp.
  rewrite (ro_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h0) w).
  replace ((- (0 - ro_access Γ k REAL w s - Rabs (ro_access Γ k REAL w s)))) with
    (ro_access Γ k REAL w s + Rabs (ro_access Γ k REAL w s)) by ring.
  pose proof (Rabs_plus_Rabs_Rabs (ro_access _ _ _ w s)) as [p q].
  destruct (Rle_or_lt (ro_access _ _ _ w s) 0).
  rewrite (q H0).
  apply pow2_positive.
  rewrite (p H0).
  pose proof (Rplus_lt_compat _ _ _ _ H H).
  replace (ro_access Γ k REAL w s + ro_access Γ k REAL w s) with
    (2 * ro_access Γ k REAL w s) in H1 by ring.
  rewrite <- pow2_add_one in H1.
  replace (- z - 1 + 1)%Z with (-z)%Z in H1 by ring. 
  exact H1.

  proves_simple_arithmetical.
  unfold ro_to_rw_pre in pre.
  pose proof (pre eq_refl).
  rewrite val.
  destruct x.
  simpl.
  rewrite ro_access_Var_S.
  simpl in H.
  rewrite (ro_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL tmp1) w).
  pose proof (Rabs_minus_Rabs_Rabs (ro_access _ _ _ w s)) as [p q].
  destruct (Rle_or_lt (ro_access _ _ _ w s) 0).
  rewrite (q H0).
  pose proof (Rplus_lt_compat _ _ _ _ H H).
  rewrite <- pow2_add_one in H1.
  replace (- z - 1 + 1)%Z with (-z)%Z in H1 by ring. 
  replace (- ro_access Γ k REAL w s +  - ro_access Γ k REAL w s) with
    (- 2 * ro_access Γ k REAL w s) in H1 by ring.
  exact H1.
  rewrite (p H0).
  apply pow2_positive.

  proves_simple_arithmetical.
  repeat split; auto.
  destruct x.  
  rewrite ro_access_Var_S, ro_access_Var_0.
  simpl in pre.
  rewrite (ro_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h) w).
  auto with real.

  rewrite val.
  apply (proj2 (Rltb''_prop _ _)).
  destruct x.
  rewrite ro_access_Var_S, ro_access_Var_0.
  simpl in pre.
  rewrite (ro_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h) w).
  exact pre.
  
  proves_simple_arithmetical.
  repeat split; auto.
  destruct x.  
  rewrite ro_access_Var_S, ro_access_Var_0.
  simpl in pre.
  rewrite (ro_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h0) w).
  unfold Rminus.
  rewrite Rplus_0_l.
  auto with real.

  rewrite val.
  apply (proj2 (Rltb''_prop _ _)).
  destruct x.
  rewrite ro_access_Var_S, ro_access_Var_0.
  simpl in pre.
  rewrite (ro_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h0) w).
  unfold Rminus.
  rewrite Rplus_0_l.
  auto with real.

  intros.
  destruct x.
  simpl.
  apply or_comm, overlap_splitting_symmetric, pow2_positive.
Defined.  
  
