From Clerical Require Import Preliminaries.Preliminaries.
From Clerical Require Import Powerdomain.Powerdomain.
From Clerical Require Import Syntax Typing TypingProperties Semantics ReasoningTyPaired ReasoningUtils.
Require Import Coq.Program.Equality.
Require Import ZArith Reals.

Inductive simple_arithmetical : forall e, Type :=
  SA_Var : forall k, simple_arithmetical (VAR k)
| SA_int_op_plus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :+: e2)
| SA_int_op_minus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :-: e2)
| SA_int_op_mult : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :*: e2)
| SA_int_comp_lt : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :<: e2)
| SA_int_comp_eq : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 :=: e2)
| SA_real_op_plus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;+; e2)
| SA_real_op_minus : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;-; e2)
| SA_real_op_mult : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;*; e2)
| SA_real_comp_lt : forall e1 e2, simple_arithmetical e1 -> simple_arithmetical e2 -> simple_arithmetical (e1 ;<; e2)
| SA_real_recip : forall e, simple_arithmetical e -> simple_arithmetical (;/; e)

| SA_coerce : forall e, simple_arithmetical e -> simple_arithmetical (RE e)
| SA_exp : forall e, simple_arithmetical e -> simple_arithmetical (EXP e)
| SA_int : forall k, simple_arithmetical (INT k)
| SA_true : simple_arithmetical TRUE
| SA_false : simple_arithmetical FALSE
.

Fixpoint simple_arithmetical_value_prt e (p : simple_arithmetical e) Γ τ (w : Γ |- e :τ) : sem_ctx Γ -> sem_datatype τ.
Proof.
  dependent destruction p.
  exact (var_access _ _ _ w).

  induction (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) + (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) - (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) * (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) <? (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) =? (simple_arithmetical_value_prt _ p2 _ _ w2 x))%Z.

  induction (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) + (simple_arithmetical_value_prt _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) - (simple_arithmetical_value_prt _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => (simple_arithmetical_value_prt _ p1 _ _ w1 x) * (simple_arithmetical_value_prt _ p2 _ _ w2 x))%R.

  induction (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
  pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w1 w2].  
  exact (fun x => Rltb'' (simple_arithmetical_value_prt _ p1 _ _ w1 x) (simple_arithmetical_value_prt _ p2 _ _ w2 x)).

  induction (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
  pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w1.  
  exact (fun x => / (simple_arithmetical_value_prt _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w1.  
  exact (fun x => IZR (simple_arithmetical_value_prt _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w1.  
  exact (fun x => pow2 (simple_arithmetical_value_prt _ p _ _ w1 x))%R.

  induction (eq_sym (has_type_ro_Int_infer _ _ _ w)).
  exact (fun x => k).

  induction (eq_sym (has_type_ro_True_infer  _ _ w)).
  exact (fun x => true).

  induction (eq_sym (has_type_ro_False_infer _ _  w)).
  exact (fun x => false).  
Defined.

Fixpoint simple_arithmetical_prt Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical e) :
  [x : Γ] |- {{True}} e {{y : τ | y = simple_arithmetical_value_prt e p Γ τ w x}}ᵖ.
Proof.
  dependent destruction p; simpl.
  {
    apply (pp_ro_var_prt_back w).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZplus_inverse _ _ _ w)). intros w1 w2 e.    
    apply (
        pp_ro_int_op_plus_prt
          (fun x y => y = ( (simple_arithmetical_value_prt _ p1 _ _ w1) x))
          (fun x y => y = ( (simple_arithmetical_value_prt _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_prt _ _ _ w1 p1).
    apply (pp_ro_imply_prt X);
      try intros x1 x2; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_prt _ _ _ w2 p2).
    apply (pp_ro_imply_prt X);
      try intros x1 x2; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    rewrite e.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZminus_inverse _ _ _ w)); intros w1 w2 e.    
    apply (pp_ro_int_op_minus_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZmult_inverse _ _ _ w)); intros w1 w2 e.    
    apply (pp_ro_int_op_mult_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZlt_inverse _ _ _ w)); intros w1 w2 e.    
    apply (pp_ro_int_comp_lt_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpZeq_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (pp_ro_int_comp_eq_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ INTEGER w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ INTEGER w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRplus_inverse _ _ _ w)); intros w1 w2 e.    
    apply (pp_ro_real_op_plus_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRminus_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (pp_ro_real_op_minus_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRmult_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (pp_ro_real_op_mult_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    case_eq ( (has_type_ro_OpRlt_inverse _ _ _ w)) ; intros w1 w2 e.    
    apply (pp_ro_real_comp_lt_prt
             (fun x y => y = simple_arithmetical_value_prt e1 p1 Γ REAL w1 x)
             (fun x y => y = simple_arithmetical_value_prt e2 p2 Γ REAL w2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    simpl.
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)).
    injection e; intros eq1 eq2; induction eq1, eq2.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpRrecip_infer Γ e τ w)).
    pose ((has_type_ro_OpRrecip_inverse _ _ w)) as w1.    
    apply (pp_ro_recip_prt_back).
    pose proof (simple_arithmetical_prt _ _ _ w1 p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }

  
  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer Γ e τ w)).
    pose ((has_type_ro_OpZRcoerce_inverse _ _ w)) as w1.    
    apply (pp_ro_coerce_prt).
    pose proof (simple_arithmetical_prt _ _ _ w1 p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }
  
  {
    destruct (eq_sym (has_type_ro_OpZRexp_infer Γ e τ w)).
    pose ((has_type_ro_OpZRexp_inverse _ _ w)) as w1.    
    apply (pp_ro_exp_prt).
    pose proof (simple_arithmetical_prt _ _ _ w1 p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    simpl.
    apply lp.
    reflexivity.
  }

  
  {
    destruct (eq_sym (has_type_ro_Int_infer Γ k τ w)).
    simpl.
    apply (pp_ro_int_prt_back).
    intros x1 x2; auto.
  }

  {
    destruct (eq_sym (has_type_ro_True_infer Γ τ w)).
    simpl.
    apply (pp_ro_true_prt_back).
    intros x1 x2; auto.
  }

  {
    destruct (eq_sym (has_type_ro_False_infer Γ τ w)).
    simpl.
    apply (pp_ro_false_prt_back).
    intros x1 x2; auto.
  }  
  
Defined.


Fixpoint simple_arithmetical_value_tot e (p : simple_arithmetical e) Γ τ (w : Γ |- e : τ)  :
  (sem_ctx Γ -> Prop) * (sem_ctx Γ -> sem_datatype τ).
Proof.
  dependent destruction p.
  exact (fun _ => True, var_access _ _ _ w).

  destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZplus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x + snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x - snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x * snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x <? snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x =? snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%Z.

  destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x + snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%R.

  destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x - snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%R.

  destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x,  
         fun x => snd (simple_arithmetical_value_tot _ p1 _ _ w1) x * snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))%R.

  destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
  destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [w1 w2].    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p1 _ _ w1) x /\ fst (simple_arithmetical_value_tot  _ p2 _ _ w2) x /\
                  (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) <> (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x)
         ,  
         fun x => Rltb'' (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x)))%R.

  destruct (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
  pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w1.    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p _ _ w1) x /\
                  (snd (simple_arithmetical_value_tot _ p _ _ w1) x <> 0%R)
         ,
         fun x => / snd (simple_arithmetical_value_tot _ p _ _ w1) x))%R.

  destruct (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w1.    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p _ _ w1) x
         ,
         fun x => IZR (snd (simple_arithmetical_value_tot _ p _ _ w1) x)))%R.

  destruct (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
  pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w1.    
  exact (
      (fun x => fst (simple_arithmetical_value_tot _ p _ _ w1) x
         ,
         fun x => pow2 (snd (simple_arithmetical_value_tot _ p _ _ w1) x)))%R.

  destruct (eq_sym (has_type_ro_Int_infer _ _ _ w)).
  exact (
      (fun x => True,
         fun x => k))%Z.
  
  destruct (eq_sym (has_type_ro_True_infer _ _ w)).
  exact (
      (fun x => True,
         fun x => true))%Z.

  destruct (eq_sym (has_type_ro_False_infer _ _ w)).
  exact (
      (fun x => True,
         fun x => false))%Z.

Defined.

Fixpoint simple_arithmetical_tot e (p : simple_arithmetical e) Γ τ (w : Γ |- e : τ) :
  [x : Γ] |- {{fst (simple_arithmetical_value_tot _ p _ _ w) x}} e {{y : τ | y = snd (simple_arithmetical_value_tot _ p _ _ w) x}}ᵗ.
Proof.
  dependent destruction p; simpl.
  {
    apply (pp_ro_var_tot_back w).
    intros x _.
    reflexivity.
  }

  {
    destruct (eq_sym (has_type_ro_OpZplus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZplus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_op_plus_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZminus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZminus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_op_minus_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZmult_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZmult_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_op_mult_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZlt_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZlt_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_comp_lt_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpZeq_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpZeq_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_int_comp_eq_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRplus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRplus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_op_plus_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRminus_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRminus_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_op_minus_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRmult_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRmult_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_op_mult_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).
    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    simpl.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_OpRlt_infer _ _ _ _ w)).
    destruct ( (has_type_ro_OpRlt_inverse _ _ _ w)) as [w1 w2].    
    apply (
        pp_ro_real_comp_lt_tot
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) /\  y <> (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
          (fun x y => y = (snd (simple_arithmetical_value_tot _ p2 _ _ w2) x))
      ).

    pose proof (simple_arithmetical_tot _ p1 _ _ w1).
    apply (pp_ro_tot_pose_readonly
             (fun x =>
                (snd (simple_arithmetical_value_tot _ p1 _ _ w1) x) <>
                  (snd (simple_arithmetical_value_tot _ p2 _ _  w2) x))) in X.
             
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    split.
    exact x2.
    destruct x3.
    exact H0.
    split.
    destruct x3.
    exact H.
    destruct x3.
    rewrite H; exact H0.

    
    pose proof (simple_arithmetical_tot _ p2 _ _ w2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    destruct h1.
    split; auto.
    rewrite <- h2 in H0.
    exact H0.    
    rewrite H, h2; auto.
  }
  {
    destruct (eq_sym (has_type_ro_OpRrecip_infer _ _ _ w)).
    pose ( (has_type_ro_OpRrecip_inverse _ _ w)) as w1.    
    
    apply (pp_ro_recip_tot_back).
    pose proof (simple_arithmetical_tot _ p _ _ w1).
    apply (pp_ro_tot_pose_readonly
             (fun x => 
                (snd (simple_arithmetical_value_tot _ p _ _ w1) x) <> 0%R)) in X.
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro.
    intros.
    split.
    destruct H.
    auto.
    destruct H.
    auto.
    destruct x3.
    split.
    rewrite H; auto.
    rewrite H; auto.
  }

  {
    destruct (eq_sym (has_type_ro_OpZRcoerce_infer _ _ _ w)).
    pose ( (has_type_ro_OpZRcoerce_inverse _ _ w)) as w1.    
    
    apply (pp_ro_coerce_tot).
    pose proof (simple_arithmetical_tot _ p _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro.
    intros.
    simpl in H.
    exact H.
    simpl.
    rewrite x3; auto.
  }
  
  {
    destruct (eq_sym (has_type_ro_OpZRexp_infer _ _ _ w)).
    pose ( (has_type_ro_OpZRexp_inverse _ _ w)) as w1.    
    
    apply (pp_ro_exp_tot).
    pose proof (simple_arithmetical_tot _ p _ _ w1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intro.
    intros.
    simpl in H.
    exact H.
    simpl.
    rewrite x3; auto.
  }

  {
    destruct (eq_sym (has_type_ro_Int_infer _ _ _ w)).
    apply (pp_ro_int_tot_back).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_True_infer _ _ w)).
    apply (pp_ro_true_tot_back).
    intros x _.
    reflexivity.
  }
  {
    destruct (eq_sym (has_type_ro_False_infer _ _ w)).
    apply (pp_ro_false_tot_back).
    intros x _.
    reflexivity.
  }    
Defined.


Fixpoint simple_arithmetical_dec e : simple_arithmetical e + (simple_arithmetical e -> False).
Proof.
  dependent destruction e;
    try (left; constructor; auto; fail);
    try (destruct b; left; constructor; auto; fail).

  destruct (simple_arithmetical_dec e1).
  destruct (simple_arithmetical_dec e2).
  destruct b; constructor; auto; constructor; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.
  
  destruct (simple_arithmetical_dec e).
  left; destruct u; constructor; auto.
  right.
  intro.
  dependent destruction H; apply f; auto.

  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  right; intro.
  dependent destruction H.
  (* right; intro. *)
  (* dependent destruction H. *)
Defined.


