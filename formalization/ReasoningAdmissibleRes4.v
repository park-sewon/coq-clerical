Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals.
Require Import ZArith.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.
Require Import Clerical.ReasoningSoundness.
Require Import Clerical.ReasoningAdmissibleRes0.
Require Import Clerical.ReasoningAdmissibleRes1.
Require Import Clerical.ReasoningAdmissibleRes2.
Require Import Clerical.ReasoningAdmissibleRes3.


Fixpoint r_admissible_ro_conj_prt Γ e τ (w : Γ |- e : τ) ϕ ψ1 ψ2 {struct e} : w |~ {{ϕ}} e {{ψ1}} -> w |~ {{ϕ}} e {{ψ2}} ->  w |~ {{ϕ}} e {{ψ1 /\\\ ψ2}}
with r_admissible_ro_conj_tot Γ e τ (w : Γ |- e : τ) ϕ ψ1 ψ2 {struct e} : w |~ [{ϕ}] e [{ψ1}] -> w |~ [{ϕ}] e [{ψ2}] ->  w |~ [{ϕ}] e [{ψ1 /\\\ ψ2}]
with r_admissible_rw_conj_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ1 ψ2 {struct e} : w ||~ {{ϕ}} e {{ψ1}} -> w ||~ {{ϕ}} e {{ψ2}} ->  w ||~ {{ϕ}} e {{ψ1 /\\\ ψ2}}
with r_admissible_rw_conj_tot Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ1 ψ2 {struct e} : w ||~ [{ϕ}] e [{ψ1}] -> w ||~ [{ϕ}] e [{ψ2}] ->  w ||~ [{ϕ}] e [{ψ1 /\\\ ψ2}].
Proof.
  +
    intros t1 t2.
    dependent destruction e. 

    pose proof (r_ro_var_prt _ _ _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_var_prt_inv t1).
    pose proof (r_ro_var_prt_inv t2).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.
    
    destruct b.
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True Γ) w).
    pose proof (r_ro_true_prt _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_true_prt_inv t1).
    pose proof (r_ro_true_prt_inv t2).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False Γ) w).
    pose proof (r_ro_false_prt _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_false_prt_inv t1).
    pose proof (r_ro_false_prt_inv t2).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int Γ _) w).
    pose proof (r_ro_int_prt _ _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_int_prt_inv t1).
    pose proof (r_ro_int_prt_inv t2).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.

    destruct b.
    induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_op_plus_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_op_plus_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_op_minus_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_op_minus_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_op_mult_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_op_mult_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_comp_lt_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_comp_lt_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_comp_eq_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_comp_eq_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.
    
    induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_op_plus_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_op_plus_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.
    
    induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_op_minus_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_op_minus_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_lt_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_lt_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.
    
    induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_op_mult_prt_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_op_mult_prt_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    destruct u.
    induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
    pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w'. 
    pose proof (r_ro_recip_prt_inv w' t1) as [θ1 [p1 p2]]. 
    pose proof (r_ro_recip_prt_inv w' t2) as [θ2 [q1 q2]]. 
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
    apply (r_ro_recip_prt _ _  w' _ _ _ _  X).
    intros y γ h.
    split.
    apply p2.
    destruct h.
    split.
    destruct H.
    auto.
    auto.
    apply q2.
    destruct h.
    split.
    destruct H.
    auto.
    auto.
    
    induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
    pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w'. 
    pose proof (r_ro_coerce_prt_inv w' t1) as p. 
    pose proof (r_ro_coerce_prt_inv w' t2) as q. 
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p q).
    apply (r_ro_coerce_prt _ _ _ _ _ _  X).
    
    induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
    pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w'. 
    pose proof (r_ro_exp_prt_inv w' t1) as p. 
    pose proof (r_ro_exp_prt_inv w' t2) as q. 
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p q).
    apply (r_ro_exp_prt _ _ _ _ _ _  X).
    
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip Γ) w).
    pose proof (r_ro_skip_prt _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_skip_prt_inv t1).
    pose proof (r_ro_skip_prt_inv t2).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.

    dependent destruction w.
    pose proof (has_type_rw_Seq_inverse _ _ _ _ _ h) as [r1 r2].
    
    apply (r_ro_sequence_prt_inv r1 r2) in t1 as [θ1 [p1 p2]].
    apply (r_ro_sequence_prt_inv r1 r2) in t2 as [θ2 [q1 q2]].
    pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ p1 q1).
    assert (r2 ||~ {{(θ1 /\\\ θ2) tt}} e2 {{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ1 y (fst x; snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    assert (r2 ||~ {{(θ1 /\\\ θ2) tt}} e2 {{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ2 y (fst x; snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X0 X1).
    
    pose proof (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ h X X2).
    pose proof (r_rw_ro_prt _ _ _ _ _ _ (has_type_ro_rw Γ (e1;; e2) τ h) X3).
    exact X4.
    
    dependent destruction w.
    pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ h) as [[r1 r2] r3].

    apply (r_ro_cond_prt_inv r1 r2 r3) in t1 as [θ1 [[p1 p2] p3]].
    apply (r_ro_cond_prt_inv r1 r2 r3) in t2 as [θ2 [[q1 q2] q3]].
    pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
    assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ1 y (fst x; snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ2 y (fst x; snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X0 X1).
    assert (r3 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) false)}} e3 {{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ1 y (fst x; snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    assert (r3 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) false)}} e3 {{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ2 y (fst x; snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X3 X4).
    assert (r1 |~ {{rw_to_ro_pre (fun x => ϕ (snd x))}} e1 {{y | (θ1 /\\\ θ2) y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    pose proof (r_rw_cond_prt Γ nil e1 e2 e3 τ r1 r2 r3 h _ _ _ X6 X2 X5).
    pose proof (r_rw_ro_prt _ _ _ _ _ _ (  has_type_ro_rw Γ (IF e1 THEN e2 ELSE e3 END) τ h) X7).
    exact X8.

    {
      dependent destruction w.
      pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ _ h) as [[[w1 w2] w3] w4].
      Check r_rw_case_prt_inv.
      pose proof (@r_ro_case_prt_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t1) as
        [θ11 [θ12 [[[p1 p2] p3] p4]]].
      pose proof (@r_ro_case_prt_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t2) as
        [θ21 [θ22 [[[q1 q2] q3] q4]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p2 q2).
      assert (w3 ||~ {{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}} e2 {{y | @ro_to_rw_pre Γ nil (ψ1 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w3 ||~ {{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}} e2 {{y | @ro_to_rw_pre Γ nil (ψ2 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q3);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ {{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}} e4 {{y | @ro_to_rw_pre Γ nil (ψ1 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ {{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}} e4 {{y | @ro_to_rw_pre Γ nil (ψ2 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q4);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X1 X2).
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X3 X4).

      pose proof (r_rw_case_prt).
      pose proof (r_rw_case_prt _ _ _ _ _ _ _ w1 w2 w3 w4 h (fun x => ϕ (snd x)) _ _ _ X X0 X5 X6).
      
      exact (r_rw_ro_prt _ _ _ _ _ _ (has_type_ro_rw Γ _ τ h) X8).

    }

    {
      dependent destruction w.
      
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ h) as wty_l.
      apply (r_ro_case_list_prt_inv wty_l) in t1 as [θ1 f1].
      apply (r_ro_case_list_prt_inv wty_l) in t2 as [θ2 f2].
      assert (h ||~ {{fun x => ϕ (snd x)}} CaseList l {{fun y x => (ψ1 /\\\ ψ2) y (snd x)}}).
      apply (r_rw_case_list_prt _ _ _ _ wty_l h (ForallT_map2 (fun _ x y => x /\\\ y) θ1 θ2)).
      clear h.
      induction l.
      
      dependent destruction θ1.
      dependent destruction wty_l.      
      apply ForallT2_nil.
      
      inversion f1.
      clear H0 H1.
      induction (projT2_eq H); clear H.
      induction (projT2_eq H3); clear H3.
      inversion f2.
      clear H0 H1.
      induction (projT2_eq H);
        clear H.
      induction (projT2_eq H3);
        clear H3.
      induction (projT2_eq H4); clear H4.
      simpl.
      unfold solution_left.
      easy_rewrite_uip.
      apply ForallT2_cons.
      apply IHl.
      apply X.
      apply X1.
      destruct X0, X2.
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ r r1).
      split.
      apply X0.
      apply r_admissible_rw_conj_prt.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.

      exact (r_rw_ro_prt _ _ _ _ _ _ (has_type_ro_rw Γ (CaseList l) τ h) X).

      
    }


    {
      (* while *)
      dependent destruction w.
      assert (h ||~ {{fun x => ϕ (snd x)}} While e1 e2 {{fun y x => (ψ1 /\\\ ψ2) y (snd x)}}).
      
      induction (eq_sym (has_type_rw_While_infer h)).
      pose proof (has_type_rw_While_inverse h) as [r1 r2].
      apply (r_ro_while_prt_inv r1 r2) in t1 as [I1 [θ1 [[[p1 p2] p3] p4]]].
      apply (r_ro_while_prt_inv r1 r2) in t2 as [I2 [θ2 [[[q1 q2] q3] q4]]].
      assert (r1 |~ {{rw_to_ro_pre (I1 /\\ I2)}} e1 {{y | θ1 y}}) as x1.
      {
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      assert (r1 |~ {{rw_to_ro_pre (I1 /\\ I2)}} e1 {{y | θ2 y}}) as x2.
      {
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a q3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _  x1 x2) as trip_e.
      clear x1 x2 p3 q3.

      assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{_ | I1}}) as x1.
      {
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{_ | I2}}) as x2.
      {
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _  x1 x2) as trip_c.
      clear x1 x2 p4 q4.
      pose proof (r_rw_while_prt _ _ _ _ _ _ h _ _ trip_e trip_c) as H.

      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a H);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply p1.
      simpl.
      exact h2.
      apply q1.
      exact h2.
      destruct h2.
      destruct s.
      destruct h1.
      simpl.
      intros.
      split.
      pose proof (p2 (tt, s0)).
      simpl in H1.
      apply H1; clear H1.
      destruct H0.
      destruct H0, H1.
      split; auto.
      pose proof (q2 (tt, s0)).
      simpl in H1.
      apply H1; clear H1.
      destruct H0.
      destruct H0, H1.
      split; auto.
      
      exact (r_rw_ro_prt _ _ _ _ _ _ (has_type_ro_rw Γ _ τ h) X).

      
    }

    {
      dependent destruction w.
      assert (h ||~ {{fun x => ϕ (snd x)}} (NEWVAR e1 IN e2) {{y | fun x => (ψ1 /\\\ ψ2) y (snd x)}}).
      pose proof (has_type_rw_Newvar_inverse h) as [σ [we wc]].
      pose proof (r_ro_new_var_prt_inv we wc t1) as [θ1 [p1 p2]].
      pose proof (r_ro_new_var_prt_inv we wc t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _  p1 q1) as trip_e.
      simpl in p2, q2.
      assert (wc ||~ {{(fun x : sem_datatype σ * unit * sem_ro_ctx Γ => (θ1 /\\\ θ2) (fst (fst x)) (snd x))}} e2 {{y
       | (fun x : sem_datatype σ * unit * sem_ro_ctx Γ => ψ1 y (snd x))}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (wc ||~ {{(fun x : sem_datatype σ * unit * sem_ro_ctx Γ => (θ1 /\\\ θ2) (fst (fst x)) (snd x))}} e2 {{y
       | (fun x : sem_datatype σ * unit * sem_ro_ctx Γ => ψ2 y (snd x))}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _  X X0) as trip_c.
      pose proof (r_rw_new_var_prt Γ nil e1 e2 τ σ we wc (fun x => ϕ (snd x)) (fun y x => (ψ1 /\\\ ψ2) y (snd x)) (θ1 /\\\ θ2) h trip_e trip_c).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      
      apply (r_rw_ro_prt _ _ _ _ _ _ (has_type_ro_rw Γ _ τ h) X).

    }

    {
      dependent destruction w.
      induction (eq_sym (has_type_rw_Assign_infer h)).
      contradict (has_type_rw_Assign_absurd _ _ _ h).
    }

    {

      induction (eq_sym (has_type_ro_Lim_infer _ _ _ w)).
      pose proof (has_type_ro_Lim_inverse _ _ w).
      pose proof (r_ro_lim_prt_inv H t1) as [θ1 [p1 p2]].
      pose proof (r_ro_lim_prt_inv H t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      apply (r_ro_lim_prt _ _ H _ _ w _ trip_e).
      intros.
      simpl.
      pose proof (p2 _ H0) as [y1 [i1 i2]].
      pose proof (q2 _ H0) as [y2 [j1 j2]].
      assert (y1 = y2).
      {
        Require Import Lra.
        destruct (lem (y1 = y2)); auto.
        assert (y1 - y2 <> 0)%R as H2 by lra.
        apply Rabs_pos_lt in H2.
        pose proof (archimed_pow2 _ H2) as [k o].

        apply r_proves_ro_tot_proves_ro_tot in p1, q1.
        pose proof (proves_ro_tot_pick_from_two_post p1 q1 (-k +1, γ)%Z H0) as [z [o1 o2]]. 
        apply i2 in o1.
        apply j2 in o2.
        pose proof (Rplus_lt_compat _ _ _ _ o1 o2).
        rewrite <- Rabs_Ropp in H3 at 1.
        pose proof (Rabs_triang (- (z - y1)) (z - y2))%R.
        replace (- (z - y1) + (z - y2))%R with (y1 - y2)%R in H4 by ring.
        pose proof (Rle_lt_trans _ _ _ H4 H3).
        replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1)))%R with
          (powerRZ 2 (- (- k + 1)) * powerRZ 2 1)%R in H5.

        assert (2 <> 0)%R by lra.
        rewrite <- (powerRZ_add _ _ _ H6) in H5.
        replace (- (- k + 1) + 1)%Z with k in H5 by ring.
        pose proof (Rlt_trans _ _ _ o H5).
        contradict (Rlt_irrefl _ H7).

        simpl.
        ring.
      }

      induction H1.
      exists y1.
      repeat split; auto.
      intros x z [a b].
      exact (i2  x z a).
    }   
  +
    intros t1 t2.
    dependent destruction e. 

    pose proof (r_ro_var_tot _ _ _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_var_tot_inv t1).
    pose proof (r_ro_var_tot_inv t2).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.
    
    destruct b.
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True Γ) w).
    pose proof (r_ro_true_tot _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_true_tot_inv t1).
    pose proof (r_ro_true_tot_inv t2).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False Γ) w).
    pose proof (r_ro_false_tot _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_false_tot_inv t1).
    pose proof (r_ro_false_tot_inv t2).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int Γ _) w).
    pose proof (r_ro_int_tot _ _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_int_tot_inv t1).
    pose proof (r_ro_int_tot_inv t2).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.

    destruct b.
    induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_op_plus_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_op_plus_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_op_minus_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_op_minus_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_op_mult_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_op_mult_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_comp_lt_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_comp_lt_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_int_comp_eq_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_int_comp_eq_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.
    
    induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_op_plus_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_op_plus_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.
    
    induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_op_minus_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_op_minus_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_lt_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_lt_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.
    apply (m13 _ _ _ H H0).
    split.
    apply (m13 _ _ _ H H0).
    apply (m23 _ _ _ H1 H2).
    
    induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w1 w2]. 
    pose proof (r_ro_real_op_mult_tot_inv w1 w2 t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
    pose proof (r_ro_real_op_mult_tot_inv w1 w2 t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
    apply (r_ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    split.    
    apply m13; auto.
    apply m23; auto.

    destruct u.
    induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
    pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w'. 
    pose proof (r_ro_recip_tot_inv w' t1) as [θ1 [p1 p2]]. 
    pose proof (r_ro_recip_tot_inv w' t2) as [θ2 [q1 q2]]. 
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p1 q1).
    apply (r_ro_recip_tot _ _  w' _ _ _ _  X).
    intros y γ h.
    destruct h.
    split.
    apply (p2 _ _ H).
    split.
    apply p2.
    exact H.
    apply q2.
    exact H0.
    
    induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
    pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w'. 
    pose proof (r_ro_coerce_tot_inv w' t1) as p. 
    pose proof (r_ro_coerce_tot_inv w' t2) as q. 
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p q).
    apply (r_ro_coerce_tot _ _ _ _ _ _  X).
    
    induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
    pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w'. 
    pose proof (r_ro_exp_tot_inv w' t1) as p. 
    pose proof (r_ro_exp_tot_inv w' t2) as q. 
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p q).
    apply (r_ro_exp_tot _ _ _ _ _ _  X).
    
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip Γ) w).
    pose proof (r_ro_skip_tot _ w (ψ1 /\\\ ψ2)).
    pose proof (r_ro_skip_tot_inv t1).
    pose proof (r_ro_skip_tot_inv t2).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    split.
    apply H; auto.
    apply H0; auto.

    dependent destruction w.
    pose proof (has_type_rw_Seq_inverse _ _ _ _ _ h) as [r1 r2].
    
    apply (r_ro_sequence_tot_inv r1 r2) in t1 as [θ1 [p1 p2]].
    apply (r_ro_sequence_tot_inv r1 r2) in t2 as [θ2 [q1 q2]].
    pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ p1 q1).
    assert (r2 ||~ [{(θ1 /\\\ θ2) tt}] e2 [{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ1 y (fst x; snd x))}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    assert (r2 ||~ [{(θ1 /\\\ θ2) tt}] e2 [{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ2 y (fst x; snd x))}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X0 X1).
    
    pose proof (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ h X X2).
    pose proof (r_rw_ro_tot _ _ _ _ _ _ (has_type_ro_rw Γ (e1;; e2) τ h) X3).
    exact X4.
    
    dependent destruction w.
    pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ h) as [[r1 r2] r3].

    apply (r_ro_cond_tot_inv r1 r2 r3) in t1 as [θ1 [[p1 p2] p3]].
    apply (r_ro_cond_tot_inv r1 r2 r3) in t2 as [θ2 [[q1 q2] q3]].
    pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p1 q1).
    assert (r2 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) true)}] e2 [{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ1 y (fst x; snd x))}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    assert (r2 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) true)}] e2 [{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ2 y (fst x; snd x))}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X0 X1).
    assert (r3 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) false)}] e3 [{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ1 y (fst x; snd x))}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    assert (r3 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) false)}] e3 [{y | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ2 y (fst x; snd x))}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; auto.
    pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X3 X4).
    assert (r1 |~ [{rw_to_ro_pre (fun x => ϕ (snd x))}] e1 [{y | (θ1 /\\\ θ2) y}]).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    pose proof (r_rw_cond_tot Γ nil e1 e2 e3 τ r1 r2 r3 h _ _ _ X6 X2 X5).
    pose proof (r_rw_ro_tot _ _ _ _ _ _ (  has_type_ro_rw Γ (IF e1 THEN e2 ELSE e3 END) τ h) X7).
    exact X8.
    
    {
      dependent destruction w.
      pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ _ h) as [[[w1 w2] w3] w4].
      pose proof (@r_ro_case_tot_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t1) as
        [θ11 [θ12 [ϕ11 [ϕ12 [[[[[[p1 p2] p3] p4] p5] p6] p7]]]]].
      pose proof (@r_ro_case_tot_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t2) as
        [θ21 [θ22 [ϕ21 [ϕ22 [[[[[[q1 q2] q3] q4] q5] q6] q7]]]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p2 q2).
      assert (w3 ||~ [{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}] e2 [{y | @ro_to_rw_pre Γ nil (ψ1 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w3 ||~ [{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}] e2 [{y | @ro_to_rw_pre Γ nil (ψ2 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q3);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ [{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}] e4 [{y | @ro_to_rw_pre Γ nil (ψ1 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ [{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}] e4 [{y | @ro_to_rw_pre Γ nil (ψ2 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q4);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X1 X2).
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X3 X4).

      pose proof (r_rw_case_tot).
      pose proof (r_rw_case_tot _ _ _ _ _ _ _ w1 w2 w3 w4 h (fun x => ϕ (snd x)) _ _ _ ϕ11 ϕ12 X X0 X5 X6 p5 p6 p7).
      
      exact (r_rw_ro_tot _ _ _ _ _ _ (has_type_ro_rw Γ _ τ h) X8).
    }
    
    {
      dependent destruction w.
      
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ h) as wty_l.
      apply (r_ro_case_list_tot_inv wty_l) in t1 as [θ1 [ϕi1 f1]].
      apply (r_ro_case_list_tot_inv wty_l) in t2 as [θ2 [ϕi2 f2]].
      assert (h ||~ [{fun x => ϕ (snd x)}] CaseList l [{fun y x => (ψ1 /\\\ ψ2) y (snd x)}]).
      Check r_rw_case_list_tot.
      apply (r_rw_case_list_tot _ _ _ _ wty_l h
                                (ForallT_map2 (fun _ x y => x /\\\ y) θ1 θ2)
                                ϕi1
            (* (ForallT_map2 (fun _ x y => x /\\ y) ϕi1 ϕi2) *)
            ).
      clear h.
      destruct f1.
      destruct f2.
      clear f0 f2.

      induction l.

      
      dependent destruction θ1.
      dependent destruction ϕi1.
      dependent destruction wty_l.      
      apply ForallT3_nil.

      inversion f.
      unwind H H3 H4.
      use_eq_l H3.
      use_eq_l H.
      use_eq_l H4.
      inversion f1.
      unwind H H5 H6 H7.
      use_eq_l H.
      use_eq_l H5.
      use_eq_l H6.
      use_eq_l H7.

      (* dependent destruction θ2. *)
      (* dependent destruction ϕi2. *)
      simpl.
      unfold solution_left.
      easy_rewrite_uip.
      apply ForallT3_cons.
      apply (IHl _ _ _ X _ t5 X1).

      destruct X0 as [[m1 m2] m3].
      destruct X2 as [[n1 n2] n3].
      repeat split.
      apply r_admissible_ro_conj_prt.
      exact m1.
      exact n1.
      apply r_admissible_rw_conj_tot.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a n2);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

      intros.
      apply f1.
      exact H.

      
      exact (r_rw_ro_tot _ _ _ _ _ _ (has_type_ro_rw Γ (CaseList l) τ h) X).
      
    }


    {
      (* while *)
      dependent destruction w.
      assert (h ||~ [{fun x => ϕ (snd x)}] While e1 e2 [{fun y x => (ψ1 /\\\ ψ2) y (snd x)}]).
      
      induction (eq_sym (has_type_rw_While_infer h)).
      pose proof (has_type_rw_While_inverse h) as [r1 r2].
      rewrite <- app_nil_r in r2.
      apply (r_ro_while_tot_inv r1 r2) in t1 as [I1 [θ1 [V1 [[[[p1 p2] p3] p4] p5]]]].
      apply (r_ro_while_tot_inv r1 r2) in t2 as [I2 [θ2 [V2 [[[[q1 q2] q3] q4] q5]]]].
      assert (r1 |~ [{rw_to_ro_pre (I1 /\\ I2)}] e1 [{y | θ1 y}]) as x1.
      {
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      assert (r1 |~ [{rw_to_ro_pre (I1 /\\ I2)}] e1 [{y | θ2 y}]) as x2.
      {
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a q3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  x1 x2) as trip_e.
      clear x1 x2 p3 q3.
      pose proof (r_rw_while_tot _ _ _ _ r1 r2 h (I1 /\\ I2) (θ1 /\\\ θ2) V1 trip_e).
      assert (r2
      ||~ [{(fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) =>
             ro_to_rw_pre ((θ1 /\\\ θ2) true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ'))}] e2
      [{_
       | (fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => (I1 /\\ I2) (fst δγδ', fst_app (snd δγδ')) /\ V1 δγδ')}]).
      clear X.
      
      assert (r2 ||~ [{fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) =>
         ro_to_rw_pre ((θ1 /\\\ θ2) true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] e2 [{_ | fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => (I1 ) (fst δγδ', fst_app (snd δγδ')) /\ V1 δγδ'}]) as x1.
      {
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; split; auto.
        destruct H; auto.
      }
      assert (r2 ||~ [{fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) =>
         ro_to_rw_pre ((θ1 /\\\ θ2) true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] e2 [{_ | fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => (I2 ) (fst δγδ', fst_app (snd δγδ'))}]) as x2.
      {
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; split; auto.
        destruct H; auto.
        intros.
        destruct H.
        exact H.
      }

      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _  x1 x2) as trip_c.
      clear x1 x2 p4 q4.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a trip_c);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      destruct H as [[t1 t2] t3].
      repeat split; auto.
      apply X in X0.
      
        

      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      
      apply p1.
      simpl.
      exact h2.
      apply q1.
      exact h2.
      destruct h2.
      destruct s.
      destruct h1.
      simpl.
      intros.
      split.
      pose proof (p2 (tt, s0)).
      simpl in H0.
      apply H0; clear H0.
      destruct H.
      destruct H0, H.
      split; auto.
      pose proof (q2 (tt, s0)).
      simpl in H0.
      apply H0; clear H0.
      destruct H.
      destruct H, H0.
      split; auto.
      intros.
      destruct H.
      apply p5.
      exact H.
      
      exact (r_rw_ro_tot _ _ _ _ _ _ (has_type_ro_rw Γ _ τ h) X).

      
    }

    {
      dependent destruction w.
      assert (h ||~ [{fun x => ϕ (snd x)}] (NEWVAR e1 IN e2) [{y | fun x => (ψ1 /\\\ ψ2) y (snd x)}]).
      pose proof (has_type_rw_Newvar_inverse h) as [σ [we wc]].
      pose proof (r_ro_new_var_tot_inv we wc t1) as [θ1 [p1 p2]].
      pose proof (r_ro_new_var_tot_inv we wc t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      simpl in p2, q2.
      assert (wc ||~ [{(fun x : sem_datatype σ * unit * sem_ro_ctx Γ => (θ1 /\\\ θ2) (fst (fst x)) (snd x))}] e2 [{y
       | (fun x : sem_datatype σ * unit * sem_ro_ctx Γ => ψ1 y (snd x))}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (wc ||~ [{(fun x : sem_datatype σ * unit * sem_ro_ctx Γ => (θ1 /\\\ θ2) (fst (fst x)) (snd x))}] e2 [{y
       | (fun x : sem_datatype σ * unit * sem_ro_ctx Γ => ψ2 y (snd x))}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _  X X0) as trip_c.
      pose proof (r_rw_new_var_tot Γ nil e1 e2 τ σ we wc (fun x => ϕ (snd x)) (fun y x => (ψ1 /\\\ ψ2) y (snd x)) (θ1 /\\\ θ2) h trip_e trip_c).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      
      apply (r_rw_ro_tot _ _ _ _ _ _ (has_type_ro_rw Γ _ τ h) X).

    }

    {
      dependent destruction w.
      induction (eq_sym (has_type_rw_Assign_infer h)).
      contradict (has_type_rw_Assign_absurd _ _ _ h).
    }

    {

      induction (eq_sym (has_type_ro_Lim_infer _ _ _ w)).
      pose proof (has_type_ro_Lim_inverse _ _ w).
      pose proof (r_ro_lim_tot_inv H t1) as [θ1 [p1 p2]].
      pose proof (r_ro_lim_tot_inv H t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      apply (r_ro_lim_tot _ _ H _ _ w _ trip_e).
      intros.
      simpl.
      pose proof (p2 _ H0) as [y1 [i1 i2]].
      pose proof (q2 _ H0) as [y2 [j1 j2]].
      assert (y1 = y2).
      {
        Require Import Lra.
        destruct (lem (y1 = y2)); auto.
        assert (y1 - y2 <> 0)%R as H2 by lra.
        apply Rabs_pos_lt in H2.
        pose proof (archimed_pow2 _ H2) as [k o].

        apply r_proves_ro_tot_proves_ro_tot in p1, q1.
        pose proof (proves_ro_tot_pick_from_two_post p1 q1 (-k +1, γ)%Z H0) as [z [o1 o2]]. 
        apply i2 in o1.
        apply j2 in o2.
        pose proof (Rplus_lt_compat _ _ _ _ o1 o2).
        rewrite <- Rabs_Ropp in H3 at 1.
        Search (Rabs (- _))%R.
        pose proof (Rabs_triang (- (z - y1)) (z - y2))%R.
        replace (- (z - y1) + (z - y2))%R with (y1 - y2)%R in H4 by ring.
        pose proof (Rle_lt_trans _ _ _ H4 H3).
        replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1)))%R with
          (powerRZ 2 (- (- k + 1)) * powerRZ 2 1)%R in H5.

        assert (2 <> 0)%R by lra.
        rewrite <- (powerRZ_add _ _ _ H6) in H5.
        replace (- (- k + 1) + 1)%Z with k in H5 by ring.
        pose proof (Rlt_trans _ _ _ o H5).
        contradict (Rlt_irrefl _ H7).

        simpl.
        ring.
      }

      induction H1.
      exists y1.
      repeat split; auto.
      intros x z [a b].
      exact (i2  x z a).
    }   
    
  +
    intros t1 t2.
    dependent destruction e. 
    {
      dependent destruction w.
      pose proof (r_ro_var_prt _ _ _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_var_prt_inv _ _ _ _ h _ _ _ t1).
      pose proof (r_rw_var_prt_inv _ _ _ _ h _ _ _ t2).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ (has_type_rw_ro Γ Δ (VAR n) τ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H.
      rewrite tedious_equiv_0.
      exact h2.
      apply H0.
      rewrite tedious_equiv_0.
      exact h2.
      rewrite tedious_equiv_0.
      intro x; exact x.
    }

    destruct b.
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True _) h).
      pose proof (r_ro_true_prt _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_true_prt_inv _ _ h _ _ _ t1).
      pose proof (r_rw_true_prt_inv _ _ h _ _ _ t2).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro Γ Δ TRUE BOOL h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H; rewrite tedious_equiv_0; auto.
      apply H0; rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False _) h).
      pose proof (r_ro_false_prt _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_false_prt_inv _ _ h _ _ _ t1).
      pose proof (r_rw_false_prt_inv _ _ h _ _ _ t2).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro Γ Δ FALSE BOOL h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H; rewrite tedious_equiv_0; auto.
      apply H0; rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int _ _) h).
      pose proof (r_ro_int_prt _ _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_int_prt_inv _ _ _ h _ _ _ t1).
      pose proof (r_rw_int_prt_inv _ _ _ h _ _ _ t2).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H; rewrite tedious_equiv_0; auto.
      apply H0; rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    
    destruct b.
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 :+: e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZplus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_op_plus_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_op_plus_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    } 
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 :-: e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZminus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_op_minus_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_op_minus_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 :*: e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZmult_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_op_mult_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_op_mult_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 :<: e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZlt_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_comp_lt_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_comp_lt_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 :=: e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZeq_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_comp_eq_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_comp_eq_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 ;+; e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRplus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_op_plus_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_op_plus_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 ;-; e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRminus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_op_minus_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_op_minus_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 ;<; e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRlt_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_lt_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_lt_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ {{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}}
                (e1 ;*; e2)
                {{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}}).
      induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRmult_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_op_mult_prt_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_op_mult_prt_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
                                    
    destruct u.
    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ h)).
      pose proof (has_type_ro_OpRrecip_inverse _ _ h) as w'. 
      pose proof (@r_rw_recip_prt_inv _ _ _ _ w' _ _ t1) as [θ1 [p1 p2]]. 
      pose proof (@r_rw_recip_prt_inv _ _ _ _ w' _ _ t2) as [θ2 [q1 q2]]. 
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
      pose proof (r_ro_recip_prt _ _  w' _ _ h
                  (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))
                  X).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X0.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
      intros y x hh.
      destruct hh.
      destruct H.
      split.
      apply p2.
      split; auto.
      apply q2.
      split; auto.
    }
    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ h)).
      pose proof (has_type_ro_OpZRcoerce_inverse _ _ h) as w'. 
      pose proof (@r_rw_coerce_prt_inv _ _ _ _ w' _ _ t1) as p.  
      pose proof (@r_rw_coerce_prt_inv _ _ _ _ w' _ _ t2) as q.  
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p q).
      pose proof r_ro_coerce_prt.
      pose proof (r_ro_coerce_prt _ _  w' _
                    (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))
                  h
                  X).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X1.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ h)).
      pose proof (has_type_ro_OpZRexp_inverse _ _ h) as w'. 
      pose proof (@r_rw_exp_prt_inv _ _ _ _ w' _ _ t1) as p.  
      pose proof (@r_rw_exp_prt_inv _ _ _ _ w' _ _ t2) as q.  
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p q).
      pose proof r_ro_exp_prt.
      pose proof (r_ro_exp_prt _ _  w' _
                    (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))
                  h
                  X).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X1.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip _) h).
      pose proof (r_ro_skip_prt _ h (fun y  x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_skip_prt_inv _ _ h _ _ _ t1).
      pose proof (r_rw_skip_prt_inv _ _ h _ _ _ t2).
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _  a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H.
      rewrite tedious_equiv_0; auto.
      apply H0.
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }

    {
      pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w) as [r1 r2].
      
      apply (r_rw_sequence_prt_inv r1 r2) in t1 as [θ1 [p1 p2]].
      apply (r_rw_sequence_prt_inv r1 r2) in t2 as [θ2 [q1 q2]].
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ p1 q1).
      assert (r2 ||~ {{(θ1 /\\\ θ2) tt}} e2 {{y | (fun x  => ψ1 y x)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (r2 ||~ {{(θ1 /\\\ θ2) tt}} e2 {{y | (fun x => ψ2 y x )}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X0 X1).
      apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ w X X2).
    }

    {
      pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w) as [[r1 r2] r3].
      apply (r_rw_cond_prt_inv r1 r2 r3) in t1 as [θ1 [[p1 p2] p3]].
      apply (r_rw_cond_prt_inv r1 r2 r3) in t2 as [θ2 [[q1 q2] q3]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
      assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{y | ψ1 y }}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{y | ψ2 y }}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X0 X1).
      assert (r3 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) false)}} e3 {{y |  ψ1 y }}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (r3 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) false)}} e3 {{y |  ψ2 y }}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X3 X4).
      assert (r1 |~ {{rw_to_ro_pre (fun x => ϕ x)}} e1 {{y | (θ1 /\\\ θ2) y}}).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre in h2.
      unfold fst_app, snd_app;
        destruct (tedious_sem_app Δ Γ h1); exact h2.
      apply (r_rw_cond_prt Γ _ e1 e2 e3 τ r1 r2 r3 w _ _ _ X6 X2 X5).
    }

    {
      pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ _ w) as [[[w1 w2] w3] w4].
      pose proof (@r_rw_case_prt_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t1) as
        [θ11 [θ12 [[[p1 p2] p3] p4]]].
      pose proof (@r_rw_case_prt_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t2) as
        [θ21 [θ22 [[[q1 q2] q3] q4]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p2 q2).
      assert (w3 ||~ {{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}} e2 {{y | (ψ1 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w3 ||~ {{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}} e2 {{y | (ψ2 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q3);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ {{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}} e4 {{y | (ψ1 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ {{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}} e4 {{y | (ψ2 y)}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q4);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X1 X2).
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _ X3 X4).

      pose proof (r_rw_case_prt).
      exact (r_rw_case_prt _ _ _ _ _ _ _ w1 w2 w3 w4 w (fun x => ϕ ( x)) _ _ _ X X0 X5 X6).
     
    }
    {     
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ w) as wty_l.
      apply (r_rw_case_list_prt_inv wty_l) in t1 as [θ1 f1].
      apply (r_rw_case_list_prt_inv wty_l) in t2 as [θ2 f2].
      assert (w ||~ {{fun x => ϕ x}} CaseList l {{fun y x => (ψ1 /\\\ ψ2) y (x)}}).
      apply (r_rw_case_list_prt _ _ _ _ wty_l w (ForallT_map2 (fun _ x y => x /\\\ y) θ1 θ2)).
      clear w.
      induction l.
      
      dependent destruction θ1.
      dependent destruction wty_l.      
      apply ForallT2_nil.
      
      inversion f1.
      clear H0 H1.
      induction (projT2_eq H); clear H.
      induction (projT2_eq H3); clear H3.
      inversion f2.
      clear H0 H1.
      induction (projT2_eq H);
        clear H.
      induction (projT2_eq H3);
        clear H3.
      induction (projT2_eq H4); clear H4.
      simpl.
      unfold solution_left.
      easy_rewrite_uip.
      apply ForallT2_cons.
      apply IHl.
      apply X.
      apply X1.
      destruct X0, X2.
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ r r1).
      split.
      apply X0.
      apply r_admissible_rw_conj_prt.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      exact X.      
    }


    {
      (* while *)
      induction (eq_sym (has_type_rw_While_infer w)).
      pose proof (has_type_rw_While_inverse w) as [r1 r2].
      apply (r_rw_while_prt_inv r1 r2) in t1 as [I1 [θ1 [[[p1 p2] p3] p4]]].
      apply (r_rw_while_prt_inv r1 r2) in t2 as [I2 [θ2 [[[q1 q2] q3] q4]]].
      assert (r1 |~ {{rw_to_ro_pre (I1 /\\ I2)}} e1 {{y | θ1 y}}) as x1.
      {
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      assert (r1 |~ {{rw_to_ro_pre (I1 /\\ I2)}} e1 {{y | θ2 y}}) as x2.
      {
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a q3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _  x1 x2) as trip_e.
      clear x1 x2 p3 q3.

      assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{_ | I1}}) as x1.
      {
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      assert (r2 ||~ {{ro_to_rw_pre ((θ1 /\\\ θ2) true)}} e2 {{_ | I2}}) as x2.
      {
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _  x1 x2) as trip_c.
      clear x1 x2 p4 q4.
      pose proof (r_rw_while_prt _ _ _ _ _ _ w _ _ trip_e trip_c) as H.

      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a H);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply p1.
      simpl.
      exact h2.
      apply q1.
      exact h2.
      destruct h2.
      destruct h1.
      simpl.
      intros.
      split.
      pose proof (p2 (s, s0)).
      simpl in H1.
      apply H1; clear H1.
      destruct H0.
      destruct H0, H1.
      split; auto.
      pose proof (q2 (s, s0)).
      simpl in H1.
      apply H1; clear H1.
      destruct H0.
      destruct H0, H1.
      split; auto.
    }

    {
      pose proof (has_type_rw_Newvar_inverse w) as [σ [we wc]].
      pose proof (r_rw_new_var_prt_inv we wc t1) as [θ1 [p1 p2]].
      pose proof (r_rw_new_var_prt_inv we wc t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _  p1 q1) as trip_e.
      simpl in p2, q2.
      assert (wc ||~ {{(fun x => (θ1 /\\\ θ2) (fst (fst x)) (snd (fst x); snd x))}} e2 {{y
       | (fun x  => ψ1 y (snd (fst x), snd x))}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (wc ||~ {{(fun x => (θ1 /\\\ θ2) (fst (fst x)) (snd (fst x); snd x)) }} e2 {{y
       | (fun x => ψ2 y (snd (fst x), snd x))}}).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a q2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_prt _ _ _ _ _ _ _ _  X X0) as trip_c.
      pose proof (r_rw_new_var_prt Γ _ e1 e2 τ σ we wc _ (fun y x => (ψ1 /\\\ ψ2) y x) (θ1 /\\\ θ2) w trip_e trip_c).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
    }

    {
      induction (eq_sym (has_type_rw_Assign_infer w)).
      pose proof (has_type_rw_Assign_inverse w) as [σ [we wc]].
      pose proof (r_rw_assign_prt_inv wc t1) as [θ1 [p1 p2]].
      pose proof (r_rw_assign_prt_inv wc t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _  p1 q1) as trip_e.
      pose proof (r_rw_assign_prt).
      apply (r_rw_assign_prt _ _ _ _ _ _ _ _
                                  (ψ1 /\\\ ψ2)
                    w trip_e).
      intros.
      destruct H; split.
      apply p2.
      exact H.
      apply q2.
      exact H0.
    }

    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_Lim_infer _ _ _ h)).
      pose proof (has_type_ro_Lim_inverse _ _ h).
      pose proof (r_rw_lim_prt_inv H t1) as [θ1 [p1 p2]].
      pose proof (r_rw_lim_prt_inv H t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      pose proof (r_ro_lim_prt _ _ H (fun x => ϕ (tedious_sem_app _ _ x)) _ h
                               (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))
                    trip_e).
      assert ((forall γ : sem_ro_ctx (Δ ++ Γ),
       (fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ x)) γ ->
       exists y : R,
         (fun (y0 : R) (x : sem_ro_ctx (Δ ++ Γ)) => (ψ1 /\\\ ψ2) y0 (tedious_sem_app Δ Γ x)) y γ /\
         (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
          ((fun y0 : sem_datatype REAL => θ1 y0) /\\\ (fun y0 : sem_datatype REAL => θ2 y0)) z (x, γ) -> (Rabs (z - y) < powerRZ 2 (- x))%R))).
      intros.
      pose proof (p2 _ H0) as [y1 [i1 i2]].
      pose proof (q2 _ H0) as [y2 [j1 j2]].
      assert (y1 = y2).
      {
        Require Import Lra.
        destruct (lem (y1 = y2)); auto.
        assert (y1 - y2 <> 0)%R as H2 by lra.
        apply Rabs_pos_lt in H2.
        pose proof (archimed_pow2 _ H2) as [k o].

        apply r_proves_ro_tot_proves_ro_tot in p1, q1.
        pose proof (proves_ro_tot_pick_from_two_post p1 q1 (-k +1, γ)%Z H0) as [z [o1 o2]]. 
        apply i2 in o1.
        apply j2 in o2.
        pose proof (Rplus_lt_compat _ _ _ _ o1 o2).
        rewrite <- Rabs_Ropp in H3 at 1.
        pose proof (Rabs_triang (- (z - y1)) (z - y2))%R.
        replace (- (z - y1) + (z - y2))%R with (y1 - y2)%R in H4 by ring.
        pose proof (Rle_lt_trans _ _ _ H4 H3).
        replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1)))%R with
          (powerRZ 2 (- (- k + 1)) * powerRZ 2 1)%R in H5.

        assert (2 <> 0)%R by lra.
        rewrite <- (powerRZ_add _ _ _ H6) in H5.
        replace (- (- k + 1) + 1)%Z with k in H5 by ring.
        pose proof (Rlt_trans _ _ _ o H5).
        contradict (Rlt_irrefl _ H7).

        simpl.
        ring.
      }

      induction H1.
      exists y1.
      repeat split; auto.
      intros x z [a b].
      exact (i2  x z a).

      apply X in H0.
      apply (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in H0.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _  a H0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0.
      exact h2.
      rewrite tedious_equiv_0.
      auto.      
    }   
  +

    intros t1 t2.
    dependent destruction e. 
    {
      dependent destruction w.
      pose proof (r_ro_var_tot _ _ _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_var_tot_inv _ _ _ _ h _ _ _ t1).
      pose proof (r_rw_var_tot_inv _ _ _ _ h _ _ _ t2).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ (has_type_rw_ro Γ Δ (VAR n) τ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H.
      rewrite tedious_equiv_0.
      exact h2.
      apply H0.
      rewrite tedious_equiv_0.
      exact h2.
      rewrite tedious_equiv_0.
      intro x; exact x.
    }

    destruct b.
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True _) h).
      pose proof (r_ro_true_tot _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_true_tot_inv _ _ h _ _ _ t1).
      pose proof (r_rw_true_tot_inv _ _ h _ _ _ t2).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro Γ Δ TRUE BOOL h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H; rewrite tedious_equiv_0; auto.
      apply H0; rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False _) h).
      pose proof (r_ro_false_tot _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_false_tot_inv _ _ h _ _ _ t1).
      pose proof (r_rw_false_tot_inv _ _ h _ _ _ t2).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro Γ Δ FALSE BOOL h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H; rewrite tedious_equiv_0; auto.
      apply H0; rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int _ _) h).
      pose proof (r_ro_int_tot _ _ h (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_int_tot_inv _ _ _ h _ _ _ t1).
      pose proof (r_rw_int_tot_inv _ _ _ h _ _ _ t2).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H; rewrite tedious_equiv_0; auto.
      apply H0; rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    
    destruct b.
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 :+: e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZplus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_op_plus_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_op_plus_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    } 
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 :-: e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZminus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_op_minus_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_op_minus_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 :*: e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZmult_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_op_mult_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_op_mult_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 :<: e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZlt_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_comp_lt_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_comp_lt_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 :=: e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpZeq_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_int_comp_eq_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_int_comp_eq_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 ;+; e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRplus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_op_plus_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_op_plus_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 ;-; e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRminus_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_op_minus_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_op_minus_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 ;<; e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRlt_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_lt_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_lt_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.
      apply (m13 _ _ _ H H0).
      split.
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      assert (h |~ [{(fun γ => ϕ (tedious_sem_app Δ Γ γ))}]
                (e1 ;*; e2)
                [{y | (fun x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))}]).
      induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ h)).
      pose proof (has_type_ro_OpRmult_inverse _ _ _ h) as [w1 w2]. 
      pose proof (@r_rw_real_op_mult_tot_inv _ _ _ _ _ w1 w2 _ _ t1) as [ψ11 [ψ12 [[m11 m12] m13]]].
      pose proof (@r_rw_real_op_mult_tot_inv _ _ _ _ _ w1 w2 _ _ t2) as [ψ21 [ψ22 [[m21 m22] m23]]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m11 m21).
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ m12 m22).
      apply (r_ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
      intros.
      destruct H, H0.
      split.    
      apply m13; auto.
      apply m23; auto.

      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
                                    
    destruct u.
    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ h)).
      pose proof (has_type_ro_OpRrecip_inverse _ _ h) as w'. 
      pose proof (@r_rw_recip_tot_inv _ _ _ _ w' _ _ t1) as [θ1 [p1 p2]]. 
      pose proof (@r_rw_recip_tot_inv _ _ _ _ w' _ _ t2) as [θ2 [q1 q2]]. 
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p1 q1).
      pose proof (r_ro_recip_tot _ _  w' _ _ h
                  (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))
                  X).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X0.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
      intros y x hh.
      destruct hh.
      split.
      apply (p2 _ _ H).
      split.
      apply p2.
      exact H.
      apply q2.
      exact H0.
    }
    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ h)).
      pose proof (has_type_ro_OpZRcoerce_inverse _ _ h) as w'. 
      pose proof (@r_rw_coerce_tot_inv _ _ _ _ w' _ _ t1) as p.  
      pose proof (@r_rw_coerce_tot_inv _ _ _ _ w' _ _ t2) as q.  
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p q).
      pose proof r_ro_coerce_tot.
      pose proof (r_ro_coerce_tot _ _  w' _
                    (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))
                  h
                  X).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X1.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ h)).
      pose proof (has_type_ro_OpZRexp_inverse _ _ h) as w'. 
      pose proof (@r_rw_exp_tot_inv _ _ _ _ w' _ _ t1) as p.  
      pose proof (@r_rw_exp_tot_inv _ _ _ _ w' _ _ t2) as q.  
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p q).
      pose proof r_ro_exp_tot.
      pose proof (r_ro_exp_tot _ _  w' _
                    (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app Δ Γ x))
                  h
                  X).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X1.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }
    {
      dependent destruction w.
      induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip _) h).
      pose proof (r_ro_skip_tot _ h (fun y  x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))).
      pose proof (r_rw_skip_tot_inv _ _ h _ _ _ t1).
      pose proof (r_rw_skip_tot_inv _ _ h _ _ _ t2).
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in X.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _  a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      apply H.
      rewrite tedious_equiv_0; auto.
      apply H0.
      rewrite tedious_equiv_0; auto.
      rewrite tedious_equiv_0; auto.
    }

    {
      pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w) as [r1 r2].
      
      apply (r_rw_sequence_tot_inv r1 r2) in t1 as [θ1 [p1 p2]].
      apply (r_rw_sequence_tot_inv r1 r2) in t2 as [θ2 [q1 q2]].
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ p1 q1).
      assert (r2 ||~ [{(θ1 /\\\ θ2) tt}] e2 [{y | (fun x  => ψ1 y x)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (r2 ||~ [{(θ1 /\\\ θ2) tt}] e2 [{y | (fun x => ψ2 y x )}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X0 X1).
      apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ w X X2).
    }

    {
      pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w) as [[r1 r2] r3].
      apply (r_rw_cond_tot_inv r1 r2 r3) in t1 as [θ1 [[p1 p2] p3]].
      apply (r_rw_cond_tot_inv r1 r2 r3) in t2 as [θ2 [[q1 q2] q3]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _ p1 q1).
      assert (r2 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) true)}] e2 [{y | ψ1 y }]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (r2 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) true)}] e2 [{y | ψ2 y }]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X0 X1).
      assert (r3 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) false)}] e3 [{y |  ψ1 y }]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (r3 ||~ [{ro_to_rw_pre ((θ1 /\\\ θ2) false)}] e3 [{y |  ψ2 y }]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X3 X4).
      assert (r1 |~ [{rw_to_ro_pre (fun x => ϕ x)}] e1 [{y | (θ1 /\\\ θ2) y}]).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre in h2.
      unfold fst_app, snd_app;
        destruct (tedious_sem_app Δ Γ h1); exact h2.
      apply (r_rw_cond_tot Γ _ e1 e2 e3 τ r1 r2 r3 w _ _ _ X6 X2 X5).
    }

    {
      pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ _ w) as [[[w1 w2] w3] w4].
      pose proof (@r_rw_case_tot_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t1) as
        [θ11 [θ12 [ϕ11 [ϕ12 [[[[[[p1 p2] p3] p4] p5] p6] p7]]]]].
      pose proof (@r_rw_case_tot_inv _ _ _ _ _ _ _ _ w1 w2 w3 w4 _ _ t2) as
        [θ21 [θ22 [ϕ21 [ϕ22 [[[[[[q1 q2] q3] q4] q5] q6] q7]]]]].
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p1 q1).
      pose proof (r_admissible_ro_conj_prt _ _ _ _ _ _ _ p2 q2).
      assert (w3 ||~ [{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}] e2 [{y |  (ψ1 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w3 ||~ [{ro_to_rw_pre ((θ11 /\\\ θ21)  true)}] e2 [{y |  (ψ2 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q3);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ [{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}] e4 [{y | (ψ1 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 [ch2 h3]; auto); try (intros h1 h2 h3; auto).
      assert (w4 ||~ [{ro_to_rw_pre ((θ12 /\\\ θ22)  true)}] e4 [{y |  (ψ2 y)}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q4);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X1 X2).
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _ X3 X4).

      pose proof (r_rw_case_tot).
      exact (r_rw_case_tot _ _ _ _ _ _ _ w1 w2 w3 w4 w (fun x => ϕ ( x)) _ _ _ ϕ11 ϕ12 X X0 X5 X6 p5 p6 p7).
      
    }

    {     
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ w) as wty_l.
      apply (r_rw_case_list_tot_inv wty_l) in t1 as [θ1 [ϕi1 [f1 f2]]].
      apply (r_rw_case_list_tot_inv wty_l) in t2 as [θ2 [ϕi2 [g1 g2]]].
      apply (r_rw_case_list_tot _ _ _ _ wty_l w
                                (ForallT_map2 (fun _ x y => x /\\\ y) θ1 θ2)
                                ϕi1
            (* (ForallT_map2 (fun _ x y => x /\\ y) ϕi1 ϕi2) *)
            ).
      clear w f2 g2.
      induction l.
      dependent destruction θ1.
      dependent destruction ϕi1.
      dependent destruction wty_l.      
      apply ForallT3_nil.

      inversion f1.
      unwind H H3 H4.
      use_eq_l H3.
      use_eq_l H.
      use_eq_l H4.
      inversion g1.
      unwind H H5 H6 H7.
      use_eq_l H.
      use_eq_l H5.
      use_eq_l H6.
      use_eq_l H7.

      (* dependent destruction θ2. *)
      (* dependent destruction ϕi2. *)
      simpl.
      unfold solution_left.
      easy_rewrite_uip.
      apply ForallT3_cons.
      apply (IHl _ _ _ X _ t5 X1).

      destruct X0 as [[m1 m2] m3].
      destruct X2 as [[n1 n2] n3].
      repeat split.
      apply r_admissible_ro_conj_prt.
      exact m1.
      exact n1.
      apply r_admissible_rw_conj_tot.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a n2);
        try (intros h1 [h2 h3]; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

      intros.
      apply f2.
      exact H.
    }


    {
      (* while *)
      induction (eq_sym (has_type_rw_While_infer w)).
      pose proof (has_type_rw_While_inverse w) as [r1 r2].
      apply (fun a => has_type_rw_add_auxiliary _ _ _ _ a Δ) in r2. 
      apply (r_rw_while_tot_inv r1 r2) in t1 as [I1 [θ1 [V1 [[[[p1 p2] p3] p4] p5]]]].
      apply (r_rw_while_tot_inv r1 r2) in t2 as [I2 [θ2 [V2 [[[[q1 q2] q3] q4] q5]]]].
      assert (r1 |~ [{rw_to_ro_pre (I1 /\\ I2)}] e1 [{y | θ1 y}]) as x1.
      {
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      assert (r1 |~ [{rw_to_ro_pre (I1 /\\ I2)}] e1 [{y | θ2 y}]) as x2.
      {
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a q3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; auto.
      }

      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  x1 x2) as trip_e.
      clear x1 x2 p3 q3.
      pose proof (r_rw_while_tot _ _ _ _ r1 r2 w (I1 /\\ I2) (θ1 /\\\ θ2) V1 trip_e).
      assert (r2
      ||~ [{(fun δγδ' =>
               ro_to_rw_pre ((θ1 /\\\ θ2) true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ'))}] e2
      [{_
       | (fun δγδ' => (I1 /\\ I2) (fst δγδ', fst_app (snd δγδ')) /\ V1 δγδ')}]).
      clear X.
      
      assert (r2 ||~ [{fun δγδ' =>
         ro_to_rw_pre ((θ1 /\\\ θ2) true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] e2 [{_ | fun δγδ'  => (I1 ) (fst δγδ', fst_app (snd δγδ')) /\ V1 δγδ'}]) as x1.
      {
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; split; auto.
        destruct H; auto.
      }
      assert (r2 ||~ [{fun δγδ'  =>
         ro_to_rw_pre ((θ1 /\\\ θ2) true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] e2 [{_ | fun δγδ'  => (I2 ) (fst δγδ', fst_app (snd δγδ'))}]) as x2.
      {
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h2; split; auto.
        destruct H; auto.
        intros.
        destruct H.
        exact H.
      }

      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _  x1 x2) as trip_c.
      clear x1 x2 p4 q4.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a trip_c);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      destruct H as [[t1 t2] t3].
      repeat split; auto.
      apply X in X0.
      
        

      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      split.
      
      apply p1.
      simpl.
      exact h2.
      apply q1.
      exact h2.
      destruct h2.
      destruct h1.
      simpl.
      intros.
      split.
      pose proof (p2 (s, s0)).
      simpl in H0.
      apply H0; clear H0.
      destruct H.
      destruct H0, H.
      split; auto.
      pose proof (q2 (s, s0)).
      simpl in H0.
      apply H0; clear H0.
      destruct H.
      destruct H, H0.
      split; auto.
      intros.
      destruct H.
      apply p5.
      exact H.
    }

    {
      pose proof (has_type_rw_Newvar_inverse w) as [σ [we wc]].
      pose proof (r_rw_new_var_tot_inv we wc t1) as [θ1 [p1 p2]].
      pose proof (r_rw_new_var_tot_inv we wc t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      simpl in p2, q2.
      assert (wc ||~ [{(fun x => (θ1 /\\\ θ2) (fst (fst x)) (snd (fst x); snd x))}] e2 [{y
       | (fun x  => ψ1 y (snd (fst x), snd x))}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      assert (wc ||~ [{(fun x => (θ1 /\\\ θ2) (fst (fst x)) (snd (fst x); snd x)) }] e2 [{y
       | (fun x => ψ2 y (snd (fst x), snd x))}]).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a q2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2; auto.
      pose proof (r_admissible_rw_conj_tot _ _ _ _ _ _ _ _  X X0) as trip_c.
      pose proof (r_rw_new_var_tot Γ _ e1 e2 τ σ we wc _ (fun y x => (ψ1 /\\\ ψ2) y x) (θ1 /\\\ θ2) w trip_e trip_c).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
    }

    {
      induction (eq_sym (has_type_rw_Assign_infer w)).
      pose proof (has_type_rw_Assign_inverse w) as [σ [we wc]].
      pose proof (r_rw_assign_tot_inv wc t1) as [θ1 [p1 p2]].
      pose proof (r_rw_assign_tot_inv wc t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      pose proof (r_rw_assign_tot).
      apply (r_rw_assign_tot _ _ _ _ _ _ _ _
                                  (ψ1 /\\\ ψ2)
                    w trip_e).
      intros.
      destruct H; split.
      apply p2.
      exact H.
      apply q2.
      exact H0.
    }

    {
      dependent destruction w.
      induction (eq_sym (has_type_ro_Lim_infer _ _ _ h)).
      pose proof (has_type_ro_Lim_inverse _ _ h).
      pose proof (r_rw_lim_tot_inv H t1) as [θ1 [p1 p2]].
      pose proof (r_rw_lim_tot_inv H t2) as [θ2 [q1 q2]].
      pose proof (r_admissible_ro_conj_tot _ _ _ _ _ _ _  p1 q1) as trip_e.
      pose proof (r_ro_lim_tot _ _ H (fun x => ϕ (tedious_sem_app _ _ x)) _ h
                               (fun y x => (ψ1 /\\\ ψ2) y (tedious_sem_app _ _ x))
                    trip_e).
      assert ((forall γ : sem_ro_ctx (Δ ++ Γ),
       (fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ x)) γ ->
       exists y : R,
         (fun (y0 : R) (x : sem_ro_ctx (Δ ++ Γ)) => (ψ1 /\\\ ψ2) y0 (tedious_sem_app Δ Γ x)) y γ /\
         (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
          ((fun y0 : sem_datatype REAL => θ1 y0) /\\\ (fun y0 : sem_datatype REAL => θ2 y0)) z (x, γ) -> (Rabs (z - y) < powerRZ 2 (- x))%R))).
      intros.
      pose proof (p2 _ H0) as [y1 [i1 i2]].
      pose proof (q2 _ H0) as [y2 [j1 j2]].
      assert (y1 = y2).
      {
        Require Import Lra.
        destruct (lem (y1 = y2)); auto.
        assert (y1 - y2 <> 0)%R as H2 by lra.
        apply Rabs_pos_lt in H2.
        pose proof (archimed_pow2 _ H2) as [k o].

        apply r_proves_ro_tot_proves_ro_tot in p1, q1.
        pose proof (proves_ro_tot_pick_from_two_post p1 q1 (-k +1, γ)%Z H0) as [z [o1 o2]]. 
        apply i2 in o1.
        apply j2 in o2.
        pose proof (Rplus_lt_compat _ _ _ _ o1 o2).
        rewrite <- Rabs_Ropp in H3 at 1.
        pose proof (Rabs_triang (- (z - y1)) (z - y2))%R.
        replace (- (z - y1) + (z - y2))%R with (y1 - y2)%R in H4 by ring.
        pose proof (Rle_lt_trans _ _ _ H4 H3).
        replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1)))%R with
          (powerRZ 2 (- (- k + 1)) * powerRZ 2 1)%R in H5.

        assert (2 <> 0)%R by lra.
        rewrite <- (powerRZ_add _ _ _ H6) in H5.
        replace (- (- k + 1) + 1)%Z with k in H5 by ring.
        pose proof (Rlt_trans _ _ _ o H5).
        contradict (Rlt_irrefl _ H7).

        simpl.
        ring.
      }

      induction H1.
      exists y1.
      repeat split; auto.
      intros x z [a b].
      exact (i2  x z a).

      apply X in H0.
      apply (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_ro _ _ _ _ h )) in H0.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _  a H0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_0.
      exact h2.
      rewrite tedious_equiv_0.
      auto.      
    }   
Defined.

