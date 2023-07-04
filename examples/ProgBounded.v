From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.

From Examples Require Import ProgAbs.

(* computing the absolute value of variable k *)
Definition clerical_bounded k δ :=  
  CASE
    clerical_abs k  ;<; (VAR δ) ==> TRUE
  | (VAR δ) ;*; EXP (INT -1) ;<; clerical_abs k ==> FALSE
  END.

Lemma clerical_bounded_correct :
  forall Γ k δ (wk : Γ |- VAR k : REAL) (wδ : Γ |- VAR δ : REAL),
    [x : Γ] |-
      {{0 < var_access Γ δ REAL wδ x}}
      clerical_bounded k δ 
      {{y : BOOL | (y = true -> Rabs (var_access Γ k REAL wk x) < (var_access Γ δ REAL wδ x))
                   /\
                   (y = false -> (var_access Γ δ REAL wδ x) / 2 < Rabs (var_access Γ k REAL wk x)) }}ᵗ.    
Proof.
  intros.
  apply (pp_ro_rw_tot_back).
  apply (pp_rw_case_tot
           (θ1 := (fun '(x, b) => b = true ->
                              Rabs (var_access _ _ _ wk (fst_app x)) <
                                (var_access _ _ _ wδ (fst_app x))))
           (θ2 := (fun '(x, b) => b = true ->
                              (var_access _ _ _ wδ (fst_app x)) / 2 < 
                                Rabs (var_access _ _ _ wk (fst_app x))))           
           (ϕ1 := (fun x => 
                      Rabs (var_access _ _ _ wk (fst_app x)) <
                        (var_access _ _ _ wδ (fst_app x))))
           (ϕ2 := (fun x => 
                     (var_access _ _ _ wδ (fst_app x)) / 2 < 
                       Rabs (var_access _ _ _ wk (fst_app x))))); simpl.
  {
    apply (pp_ro_real_comp_lt_prt
             (fun '(x, y) => y = Rabs (var_access _ _ _ wk x))
             (fun '(x, y) => y = (var_access _ _ _ wδ x))).
    {
      apply (pp_ro_imply_prt
               (ψ := patf)
               (pp_ro_tot_prt
                  (clerical_abs_correct _ _ wk))).
      intros h1 h2; auto.
      intros [h1 h2] h3; auto.
    }

    proves_simple_arithmetical.
    rewrite val.
    apply (var_access_typing_irrl _ _ _ tmp1 wδ).

    intros.
    apply (proj1 (Rltb''_prop _ _)) in H2.
    reduce_tedious.
    rewrite <- H0.
    rewrite <- H.
    exact H2.
  }

  {   
    apply (pp_ro_real_comp_lt_prt
             (fun '(x, y) => y = (var_access _ _ _ wδ x) / 2 )
             (fun '(x, y) => y = Rabs (var_access _ _ _ wk x))).
    proves_simple_arithmetical.
    rewrite val.
    rewrite Rmult_1_r.
    rewrite (var_access_typing_irrl _ _ _ h wδ).
    reflexivity.

    {
      apply (pp_ro_imply_prt (ψ := patf)
               (pp_ro_tot_prt
                  (clerical_abs_correct _ _ wk))).
      intros h1 h2; auto.
      intros [h1 h2] h3; auto.
    }

    intros.    
    apply (proj1 (Rltb''_prop _ _)) in H2.
    reduce_tedious.
    rewrite <- H0.
    rewrite <- H.
    exact H2.
  }

  {
    proves_simple_arithmetical. 
    split; intro h.
    pose proof (pre (eq_refl _)).
    exact H.
    rewrite val in h; contradict h; discriminate.
  }

  {
    proves_simple_arithmetical. 
    split; intro h.
    rewrite val in h; contradict h; discriminate.
    pose proof (pre (eq_refl _)).
    exact H.    
  }

  {
    apply (pp_ro_real_comp_lt_tot
             (fun '(x, y) => y = Rabs (var_access _ _ _ wk x) /\ Rabs (var_access _ _ _ wk x) < (var_access _ _ _ wδ x))
             (fun '(x, y) => y = (var_access _ _ _ wδ x))).
    {
      apply (pp_ro_imply_tot (ψ := patf)
               (pp_ro_tot_pose_readonly (ψ := patf)
                  (fun x => Rabs (var_access _ _ _ wk x) < (var_access _ _ _ wδ x)) 
                  (clerical_abs_correct _ _ wk))).
      intros h1 h2; split; auto.
      intros [h1 h2] h3; auto.
    }

    proves_simple_arithmetical.
    rewrite val.
    apply (var_access_typing_irrl _ _ _ tmp1 wδ).
    intros.
    destruct H.
    rewrite <- H in H1; rewrite <- H0 in H1.
    split.
    lra.
    apply Rltb''_prop.
    exact H1.
  }

  {
    apply (pp_ro_real_comp_lt_tot
             (fun '(x, y) => y = (var_access _ _ _ wδ x)/2 /\ (var_access _ _ _ wδ x)/2 <Rabs (var_access _ _ _ wk x))
             (fun '(x, y) => y = Rabs (var_access _ _ _ wk x))).
    {
      proves_simple_arithmetical.
      split; auto.
      rewrite val.
      rewrite Rmult_1_r.
      rewrite (var_access_typing_irrl _ _ _ h wδ).
      reflexivity.
    }
    
    apply (pp_ro_imply_tot (ψ := patf)
             (pp_ro_tot_pose_readonly (ψ := patf)
                (fun x => (var_access _ _ _ wδ x)/2 <Rabs (var_access _ _ _ wk x)) 
                (clerical_abs_correct _ _ wk))).
    intros h1 h2; split; auto.
    intros [h1 h2] h3; auto.
    destruct h3.
    exact H.

    intros.
    destruct H.
    rewrite <- H in H1; rewrite <- H0 in H1.
    split.
    lra.
    apply Rltb''_prop.
    exact H1.
  }

  {
    intros.
    simpl in H.
    apply or_comm.
    apply overlap_splitting.
    lra.
  }

Defined.
