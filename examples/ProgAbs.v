From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals Lra List.
Open Scope R.

(* computing the absolute value of variable k *)
Definition clerical_abs k :=  
  Lim
    (CASE
       VAR (S k) ;<; EXP ( :-: (VAR 0) :-: (INT 1)) ==> ;-; VAR (S k)
     | ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k)  ==> VAR (S k)
     END)
.

Lemma clerical_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    [x : Γ] |- {{True}} clerical_abs k {{y : REAL | y = Rabs (var_access Γ k REAL w x) }}ᵗ.
Proof.
  intros.
  apply (ro_lim_tot_util_known_limit (fun x =>  Rabs (var_access Γ k REAL w x)) (ψ := patf));
    try (intros [h1 h2] [_ h3]; auto; fail).
  apply (ro_rw_tot_back (ψ := patf)).
  apply (rw_case2_tot
           (Γ := Γ ::: INTEGER)
           (θ1 := (fun '(x, b) => b = true -> (var_access _ _ _ w (fst (fst_app x))) <
                                      pow2 (- ((snd (fst_app x))) - 1)%Z))
           (θ2 := (fun '(x, b) => b = true -> - (var_access _ _ _ w (fst (fst_app x))) <
                                      pow2 (- ((snd (fst_app x))) - 1)%Z))
           
           (ϕ1 := (fun x =>  (var_access _ _ _ w (fst (fst_app x))) <
                         pow2 (- ((snd (fst_app x))) - 1)%Z))
           (ϕ2 := (fun x =>  - pow2 (- ((snd (fst_app x))) - 1)%Z < (var_access _ _ _ w (fst (fst_app x)))))
           (ψ := pattf) (ϕ := patf)
        ); simpl.

  {
    (* prove the first guard's condition θ1 *)
    prove_arith.
    intro e.
    rewrite e in val.
    apply eq_sym in val.
    apply (proj1 (Rltb''_prop _ _)) in val.
    destruct y.
    simpl.
    reduce_var_access val.
    rewrite (var_access_typing_irrl _ _ _ w (has_type_ro_Var_S_inverse h)).
    exact val.
  }
  
  {
    (* prove the second guard's condition θ1 *)  
    prove_arith.
    intro e.
    rewrite e in val.
    apply eq_sym in val.
    apply (proj1 (Rltb''_prop _ _)) in val.
    destruct y.
    simpl.
    reduce_var_access val.
    rewrite (var_access_typing_irrl _ _ _ w (has_type_ro_Var_S_inverse h0)).
    lra.
  }

  {
    (* prove the first branch *)
    apply (rw_ro_tot_back (Γ := Γ ::: INTEGER) (Δ := nil) (τ := REAL) (ϕ := patf) (ψ := pattf)).
    prove_arith.
    destruct y.  
    pose proof (pre eq_refl).
    rewrite val.
    reduce_var_access.
    simpl in H.
    rewrite <- Rabs_Ropp.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inverse h0) w).
    replace ((- (0 - var_access Γ k REAL w s - Rabs (var_access Γ k REAL w s)))) with
      (var_access Γ k REAL w s + Rabs (var_access Γ k REAL w s)) by ring.
    pose proof (Rabs_plus_Rabs_Rabs (var_access _ _ _ w s)) as [p q].
    destruct (Rle_or_lt (var_access _ _ _ w s) 0).
    rewrite (q H0).
    apply pow2_positive.
    rewrite (p H0).
    pose proof (Rplus_lt_compat _ _ _ _ H H).
    replace (var_access Γ k REAL w s + var_access Γ k REAL w s) with
      (2 * var_access Γ k REAL w s) in H1 by ring.
    rewrite <- pow2_add_one in H1.
    replace (- z - 1 + 1)%Z with (-z)%Z in H1 by ring. 
    exact H1.
  }
  
  {
    (* prove the second branch *)
    apply (rw_ro_tot_back (Γ := Γ ::: INTEGER) (Δ := nil) (τ := REAL) (ϕ := patf) (ψ := pattf)).
    prove_arith.
    destruct y.
    pose proof (pre eq_refl).
    rewrite val.
    reduce_var_access.
    simpl in H.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inverse tmp1) w).
    pose proof (Rabs_minus_Rabs_Rabs (var_access _ _ _ w s)) as [p q].
    destruct (Rle_or_lt (var_access _ _ _ w s) 0).
    rewrite (q H0).
    pose proof (Rplus_lt_compat _ _ _ _ H H).
    rewrite <- pow2_add_one in H1.
    replace (- z - 1 + 1)%Z with (-z)%Z in H1 by ring. 
    replace (- var_access Γ k REAL w s +  - var_access Γ k REAL w s) with
      (- 2 * var_access Γ k REAL w s) in H1 by ring.
    exact H1.
    rewrite (p H0).
    apply pow2_positive.
  }

  {
    (* prove the first guard's termination and holding condition ϕ1 *)
    prove_arith.
    repeat split; auto.
    destruct x.  
    rewrite var_access_Var_S, var_access_Var_0.
    simpl in pre.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h) w).
    auto with real.

    rewrite val.
    apply (proj2 (Rltb''_prop _ _)).
    destruct y.
    rewrite var_access_Var_S, var_access_Var_0.
    simpl in pre.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h) w).
    exact pre.
  }

  {
    (* prove the second guard's termination and holding condition ϕ2 *)

    prove_arith.
    repeat split; auto.
    destruct x.  
    rewrite var_access_Var_S, var_access_Var_0.
    simpl in pre.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h0) w).
    unfold Rminus.
    rewrite Rplus_0_l.
    auto with real.

    rewrite val.
    apply (proj2 (Rltb''_prop _ _)).
    destruct y.
    rewrite var_access_Var_S, var_access_Var_0.
    simpl in pre.
    rewrite (var_access_typing_irrl _ _ _ (has_type_ro_Var_S_inv Γ k INTEGER REAL h0) w).
    unfold Rminus.
    rewrite Rplus_0_l.
    auto with real.
  }

  {
    (* prove that there is at least one guard that holds ϕ => ϕ1 \/ ϕ2 *)
    intros.
    destruct x.
    simpl.
    apply or_comm, overlap_splitting_symmetric, pow2_positive.
  }
Defined.  
  
