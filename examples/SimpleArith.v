From Clerical Require Import Clerical.
Require Import Coq.Program.Equality.
Require Import ZArith Reals.

Inductive simple_arithmetical Γ : forall e τ, Γ |- e : τ -> Type :=
  SA_Var : forall k τ (w : Γ |- VAR k : τ), simple_arithmetical Γ (VAR k) τ w
| SA_int_op_plus : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 INTEGER w1 -> simple_arithmetical Γ e2 INTEGER w2 -> simple_arithmetical Γ (e1 :+: e2) INTEGER w
| SA_int_op_minus : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 INTEGER w1 -> simple_arithmetical Γ e2 INTEGER w2 -> simple_arithmetical Γ (e1 :-: e2) INTEGER w
| SA_int_op_mult : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 INTEGER w1 -> simple_arithmetical Γ e2 INTEGER w2 -> simple_arithmetical Γ (e1 :*: e2) INTEGER w
| SA_real_op_plus : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 REAL w1 -> simple_arithmetical Γ e2 REAL w2 -> simple_arithmetical Γ (e1 ;+; e2) REAL w
| SA_real_op_minus : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 REAL w1 -> simple_arithmetical Γ e2 REAL w2 -> simple_arithmetical Γ (e1 ;-; e2) REAL w
| SA_real_op_mult : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 REAL w1 -> simple_arithmetical Γ e2 REAL w2 -> simple_arithmetical Γ (e1 ;*; e2) REAL w
| SA_int_comp_lt : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 INTEGER w1 -> simple_arithmetical Γ e2 INTEGER w2 -> simple_arithmetical Γ (e1 :<: e2) BOOL w
| SA_int_comp_eq : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 INTEGER w1 -> simple_arithmetical Γ e2 INTEGER w2 -> simple_arithmetical Γ (e1 :=: e2) BOOL w
| SA_real_comp_lt : forall e1 e2 w1 w2 w, simple_arithmetical Γ e1 REAL w1 -> simple_arithmetical Γ e2 REAL w2 -> simple_arithmetical Γ (e1 ;<; e2) BOOL w
| SA_real_recip : forall e w w', simple_arithmetical Γ e REAL w -> simple_arithmetical Γ (;/; e) REAL w'
.                                                                

Fixpoint simple_arithmetical_value_prt Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical Γ e τ w) : sem_ro_ctx Γ -> sem_datatype τ.
Proof.
  dependent destruction p.
  exact (ro_access _ _ _ w).
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) + (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%Z.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) - (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%Z.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) * (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%Z.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) + (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%R.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) - (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%R.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) * (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%R.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) <? (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%Z.
  exact (fun x => (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) =? (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%Z.
  exact (fun x => Rltb'' (simple_arithmetical_value_prt Γ e1 _ w1 p1 x) (simple_arithmetical_value_prt Γ e2 _ w2 p2 x))%R.
  exact (fun x => / (simple_arithmetical_value_prt Γ e _ w p x)).
Defined.

Fixpoint simple_arithmetical_prt Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical Γ e τ w) :
  Γ |-- {{fun _ => True}} e {{y : τ | fun x => y = simple_arithmetical_value_prt Γ e τ w p x}}.
Proof.
  dependent destruction p; simpl.
  {
    apply (pp_ro_var_prt_back w).
    intros x _.
    reflexivity.
  }

  {
    apply (pp_ro_int_op_plus_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 INTEGER w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 INTEGER w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }

  {
    apply (pp_ro_int_op_minus_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 INTEGER w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 INTEGER w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_int_op_mult_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 INTEGER w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 INTEGER w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_real_op_plus_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 _ w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 _ w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_real_op_minus_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 _ w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 _ w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_real_op_mult_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 _ w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 _ w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_int_comp_lt_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 INTEGER w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 INTEGER w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_int_comp_eq_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 INTEGER w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 INTEGER w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_real_comp_lt_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 _ w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 _ w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {
    apply (pp_ro_recip_prt_back).
    pose proof (simple_arithmetical_prt _ _ _ _ p).
    apply (pp_ro_imply_prt X).
    intros x1 x2; auto.
    intros x1 x2 h.
    rewrite h.
    reflexivity.
  }
Defined.


Fixpoint simple_arithmetical_value_tot Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical Γ e τ w) :
  (sem_ro_ctx Γ -> Prop) * (sem_ro_ctx Γ -> sem_datatype τ).
Proof.
  dependent destruction p.
  exact (fun _ => True, ro_access _ _ _ w).
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x + snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%Z.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x - snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%Z.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x * snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%Z.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x + snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%R.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x - snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%R.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x * snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%R.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x <? snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%Z.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x,  
         fun x => snd (simple_arithmetical_value_tot Γ _ _ _ p1) x =? snd (simple_arithmetical_value_tot Γ _ _ _ p2) x))%Z.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p1) x /\ fst (simple_arithmetical_value_tot Γ _ _ _ p2) x
                /\ (snd (simple_arithmetical_value_tot Γ _ _ _ p1) x) <> (snd (simple_arithmetical_value_tot Γ _ _ _ p2) x),
         fun x => Rltb'' (snd (simple_arithmetical_value_tot Γ _ _ _ p1) x) (snd (simple_arithmetical_value_tot Γ _ _ _ p2) x)))%R.
  exact (
      (fun x => fst (simple_arithmetical_value_tot Γ _ _ _ p) x /\
                  snd (simple_arithmetical_value_tot Γ _ _ _ p) x <> 0%R,
         fun x => / snd (simple_arithmetical_value_tot Γ _ _ _ p) x))%R.
Defined.

Fixpoint simple_arithmetical_tot Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical Γ e τ w) :
  Γ |-- [{fst (simple_arithmetical_value_tot _ _ _ _ p)}] e [{y : τ | fun x => y = snd (simple_arithmetical_value_tot _ _ _ _ p) x}].
Proof.
  dependent destruction p; simpl.
  {
    apply (pp_ro_var_tot_back w).
    intros x _.
    reflexivity.
  }

  {
    apply (
        pp_ro_int_op_plus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_int_op_minus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_int_op_mult_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_real_op_plus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_real_op_minus_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_real_op_mult_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_int_comp_lt_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_int_comp_eq_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    reflexivity.
  }
  {
    apply (
        pp_ro_real_comp_lt_tot
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e1 _ w1 p1) x) /\ y <> (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
          (fun y x => y = (snd (simple_arithmetical_value_tot Γ e2 _ w2 p2) x))
      ).
    pose proof (simple_arithmetical_tot _ _ _ _ p1).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 x3]; auto; try intros x1 x2 x3; auto.
    pose proof (simple_arithmetical_tot _ _ _ _ p2).
    apply (pp_ro_imply_tot X);
      try intros x1 [x2 [x3 x4]]; auto; try intros x1 x2 x3; auto.
    intros x1 x2 x3 h1 h2.
    rewrite h1, h2.
    split; auto.
    reflexivity.
  }
  {
    apply (pp_ro_int_op_minus_prt
             (fun y x => y = simple_arithmetical_value_prt Γ e1 INTEGER w1 p1 x)
             (fun y x => y = simple_arithmetical_value_prt Γ e2 INTEGER w2 p2 x)
          ).
    apply simple_arithmetical_prt.
    apply simple_arithmetical_prt.
    intros.
    rewrite H, H0.
    reflexivity.
  }
  {

Fixpoint simple_arithmetical_domain Γ e τ (w : Γ |- e : τ) (p : simple_arithmetical Γ e τ w) : sem_datatype τ -> sem_ro_ctx Γ -> Prop.
Proof.
  dependent destruction p.
  exact (fun y x => y = ro_access _ _ _ w x).

