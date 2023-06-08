From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.

From Examples Require Import ProgAbs.

(* computing the absolute value of variable k *)
Definition clerical_bounded k δ :=  
  CASE
    clerical_abs k  ;<; (VAR δ)  
    ==> TRUE
    OR
    (VAR δ) ;*; EXP (INT -1) ;<; clerical_abs k
    (* ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k)  *)
    ==> FALSE
  END.

Lemma clerical_bounded_correct :
  forall Γ k δ (wk : Γ |- VAR k : REAL) (wδ : Γ |- VAR δ : REAL),
    Γ |--
      [{fun x => 0 < (ro_access Γ δ REAL wδ x)}]
      clerical_bounded k δ 
      [{y : BOOL | fun x =>
                     (y = true -> Rabs (ro_access Γ k REAL wk x) < (ro_access Γ δ REAL wδ x)) /\
                       (y = false -> (ro_access Γ δ REAL wδ x) / 2 < Rabs (ro_access Γ k REAL wk x))    
        }].
Proof.
  intros.
  apply (pp_ro_rw_tot_back).
  apply (pp_rw_case_tot
           (θ1 := (fun b x => b = true ->
                              Rabs (ro_access _ _ _ wk (snd_app x)) <
                                (ro_access _ _ _ wδ (snd_app x))))
           (θ2 := (fun b x => b = true ->
                              (ro_access _ _ _ wδ (snd_app x)) / 2 < 
                                Rabs (ro_access _ _ _ wk (snd_app x))))           
           (ϕ1 := (fun x => 
                      Rabs (ro_access _ _ _ wk (snd_app x)) <
                        (ro_access _ _ _ wδ (snd_app x))))
           (ϕ2 := (fun x => 
                     (ro_access _ _ _ wδ (snd_app x)) / 2 < 
                       Rabs (ro_access _ _ _ wk (snd_app x))))); simpl.
  {
    apply (pp_ro_real_comp_lt_prt
             (fun y x => y = Rabs (ro_access _ _ _ wk x))
             (fun y x => y = (ro_access _ _ _ wδ x))).
    {
      apply (pp_ro_imply_prt
               (pp_ro_tot_prt
                  (clerical_abs_correct _ _ wk))).
      intros h1 h2; auto.
      intros h1 h2 h3; auto.
    }

    proves_simple_arithmetical.
    rewrite val.
    apply (ro_access_typing_irrl _ _ _ tmp1 wδ).

    intros.
    apply (proj1 (Rltb''_prop _ _)) in H2.
    unfold snd_app; simpl .
    rewrite <- H0.
    rewrite <- H.
    exact H2.
  }

  {   
    apply (pp_ro_real_comp_lt_prt
             (fun y x => y = (ro_access _ _ _ wδ x) / 2 )
             (fun y x => y = Rabs (ro_access _ _ _ wk x))).
    proves_simple_arithmetical.
    rewrite val.
    rewrite Rmult_1_r.
    rewrite (ro_access_typing_irrl _ _ _ h wδ).
    reflexivity.

    {
      apply (pp_ro_imply_prt
               (pp_ro_tot_prt
                  (clerical_abs_correct _ _ wk))).
      intros h1 h2; auto.
      intros h1 h2 h3; auto.
    }

    intros.    
    apply (proj1 (Rltb''_prop _ _)) in H2.
    unfold snd_app; simpl .
    rewrite <- H0.
    rewrite <- H.
    exact H2.
  }

  {
    proves_simple_arithmetical. 
    unfold ro_to_rw_pre in pre.
    split; intro h.
    pose proof (pre (eq_refl _)).
    unfold snd_app in H; simpl in H.
    unfold snd_app; simpl.
    exact H.
    rewrite val in h; contradict h; discriminate.
  }

  {
    proves_simple_arithmetical. 
    split; intro h.
    rewrite val in h; contradict h; discriminate.
    unfold ro_to_rw_pre in pre.
    pose proof (pre (eq_refl _)).
    unfold snd_app in H; simpl in H.
    unfold snd_app; simpl.
    exact H.    
  }

  {
    apply (pp_ro_real_comp_lt_tot
             (fun y x => y = Rabs (ro_access _ _ _ wk x) /\ Rabs (ro_access _ _ _ wk x) < (ro_access _ _ _ wδ x))
             (fun y x => y = (ro_access _ _ _ wδ x))).
    {
      apply (pp_ro_imply_tot
               (pp_ro_tot_pose_readonly
                  (fun x => Rabs (ro_access _ _ _ wk x) < (ro_access _ _ _ wδ x)) 
                  (clerical_abs_correct _ _ wk))).
      intros h1 h2; split; auto.
      intros h1 h2 h3; auto.
    }

    proves_simple_arithmetical.
    rewrite val.
    apply (ro_access_typing_irrl _ _ _ tmp1 wδ).
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
             (fun y x => y = (ro_access _ _ _ wδ x)/2 /\ (ro_access _ _ _ wδ x)/2 <Rabs (ro_access _ _ _ wk x))
             (fun y x => y = Rabs (ro_access _ _ _ wk x))).
    {
      proves_simple_arithmetical.
      split; auto.
      rewrite val.
      rewrite Rmult_1_r.
      rewrite (ro_access_typing_irrl _ _ _ h wδ).
      reflexivity.
    }
    
    apply (pp_ro_imply_tot
             (pp_ro_tot_pose_readonly
                (fun x => (ro_access _ _ _ wδ x)/2 <Rabs (ro_access _ _ _ wk x)) 
                (clerical_abs_correct _ _ wk))).
    intros h1 h2; split; auto.
    intros h1 h2 h3; auto.
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
    unfold rw_to_ro_pre in H.
    simpl in H.
    unfold snd_app; simpl.
    apply or_comm.
    apply overlap_splitting.
    lra.
  }

Defined.
