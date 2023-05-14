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
Require Import Clerical.ReasoningAdmissible1.
Require Import Clerical.ReasoningSoundness.


Lemma r_proves_ro_prt_typing_irrl {Γ} {e} {τ} {w1 : Γ |- e : τ} {ϕ} {ψ} (p : w1 |~ {{ϕ}} e {{ψ}}) (w2 : Γ |- e : τ) : w2 |~ {{ϕ}} e {{ψ}}.
Proof.
  apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.
  
Lemma r_proves_ro_tot_typing_irrl {Γ} {e} {τ} {w1 : Γ |- e : τ} {ϕ} {ψ} (p : w1 |~ [{ϕ}] e [{ψ}]) (w2 : Γ |- e : τ) : w2 |~ [{ϕ}] e [{ψ}].
Proof.
  apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.
  
Lemma r_proves_rw_prt_typing_irrl {Γ} {Δ} {e} {τ} {w1 : Γ ;;; Δ ||- e : τ} {ϕ} {ψ} (p : w1 ||~ {{ϕ}} e {{ψ}}) (w2 : Γ ;;; Δ ||- e : τ) : w2 ||~ {{ϕ}} e {{ψ}}.
Proof.
  apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma r_proves_rw_tot_typing_irrl {Γ} {Δ} {e} {τ} {w1 : Γ ;;; Δ ||- e : τ} {ϕ} {ψ} (p : w1 ||~ [{ϕ}] e [{ψ}]) (w2 : Γ ;;; Δ ||- e : τ) : w2 ||~ [{ϕ}] e [{ψ}].
Proof.
  apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined. 

Fixpoint r_admissible_ro_exfalso_prt Γ e τ (w : Γ |- e : τ) ψ {struct e}: w |~ {{fun _ => False}} e {{ψ}}
with r_admissible_ro_exfalso_tot Γ e τ (w : Γ |- e : τ) ψ {struct e}: w |~ [{fun _ => False}] e [{ψ}]
with r_admissible_rw_exfalso_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ {struct e}: w ||~ {{fun _ => False}} e {{ψ}}
with r_admissible_rw_exfalso_tot Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ {struct e}: w ||~ [{fun _ => False}] e [{ψ}].
Proof.
  +
    dependent destruction e.

    pose proof (r_ro_var_prt _ _ _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    destruct b.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True Γ) w).
    pose proof (r_ro_true_prt _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.


    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False Γ) w).
    pose proof (r_ro_false_prt _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int Γ _) w).
    pose proof (r_ro_int_prt _ _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct b;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H as w1, H0 as w2;
      pose proof (r_admissible_ro_exfalso_prt _ _ _ w1 (fun _ _ => False));
      pose proof (r_admissible_ro_exfalso_prt _ _ _ w2 (fun _ _ => False)).
    apply (r_ro_int_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_eq_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_plus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_minus_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_lt_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_mult_prt _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct u;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H.
    
    pose proof (r_admissible_ro_exfalso_prt _ _ _ H (fun _ _ => False)).
    apply (r_ro_recip_prt _ _ _ _ _ _ _ X).
    intros h1 h2 h3.
    destruct h3.
    contradict H0.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ H (fun x => ψ (IZR x))).
    apply (r_ro_coerce_prt _ _ _ _ _ _ X).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ H (fun x => ψ ((powerRZ 2 x)))).
    apply (r_ro_exp_prt _ _ _ _ _ _ X).

    
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip Γ) w).
    pose proof (r_ro_skip_prt _ w ψ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

              
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r1, r2.
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ (Typing.has_type_rw_Seq _ _ _ _ _ r1 r2 ) X X0).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X1).
    simpl in X2.
    exact X2.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r3.
    apply r_has_type_ro_has_type_ro in r1. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r3 (fun y x => ψ y (snd x))).
    simpl in X, X1, X0.
    pose proof (r_rw_cond_prt _ _ _ _ _ _ _ _ _ (has_type_rw_Cond _ _ _ _ _ _ r1 r2 r3) (fun _ => False) _ _ X X0 X1).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    simpl in X3.
    exact X3.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r4.
    apply r_has_type_ro_has_type_ro in r1, r3. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r3 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r4 (fun y x => ψ y (snd x))).
    simpl in X, X1, X0, X2.
    pose proof (r_rw_case_prt _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Case _ _ _ _ _ _ _ r1 r2 r3 r4) (fun _ => False) _ _ _ X X1 X0 X2).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X3).
    simpl in X4.
    exact X4.


    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose proof (r_rw_case_list_prt).
    pose (ForallT_map
                                      (fun _ x =>
                                         pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                                              (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
                                              f).
    pose proof (r_rw_case_list_prt Γ nil _ _ f1
                                   (has_type_rw_CaseList _ _ _ _ l1 f1) f0 (fun _ => False) (fun y x => ψ y (snd x))
               ).
    assert (ForallT2 (fun ec : exp * exp => (((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l : ((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))
            (θ : bool -> sem_ro_ctx (nil ++ Γ) -> Prop) =>
          ((fst wty_l |~ {{rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False)}} fst ec {{y | θ y}}) *
           (snd wty_l ||~ {{ro_to_rw_pre (θ true)}} snd ec {{y
                                                            | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ y (snd x))}}))%type) l f1 f0).
    clear X0 l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT2_nil.
    dependent destruction f.
    apply ForallT2_cons.
    apply IHl.

    split.
    simpl.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_prt.

    pose proof (X0 X1).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    exact X3.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r0 (fun _ _ => False)).
    pose proof r_rw_while_prt.
    pose proof (r_rw_while_prt _ _ _ _ _ _ (has_type_rw_While _ _ _ _ r r0) _ _ X X0).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    simpl in X3.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H.
    contradict H; auto.

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ r0 (fun _ _ => False)).
    pose proof r_rw_new_var_prt.
    pose proof (r_rw_new_var_prt _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ (has_type_rw_Newvar _ _ _ _ _ _ r r0) X X0).
    pose proof (r_rw_ro_prt Γ _ _ _ _ _ w X2).
    simpl in X3.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H; auto.


    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    contradict (assignable_absurd _ _ a).

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in H. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun _ _ => False)).
    pose proof r_ro_lim_prt.
    pose proof (r_ro_lim_prt _ _ _ (fun _ => False) (fun _ _ => False) w ψ X).
    assert ( (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) Γ,
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) Γ => False) γ ->
        exists y : R,
          ψ y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x)))).
    intros.
    contradict H0.
    pose proof (X1 H0).
    exact X2.

  +
    dependent destruction e.

    pose proof (r_ro_var_tot _ _ _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    destruct b.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_True Γ) w).
    pose proof (r_ro_true_tot _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.


    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_False Γ) w).
    pose proof (r_ro_false_tot _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Int Γ _) w).
    pose proof (r_ro_int_tot _ _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct b;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H as w1, H0 as w2;
      pose proof (r_admissible_ro_exfalso_tot _ _ _ w1 (fun _ _ => False));
      pose proof (r_admissible_ro_exfalso_tot _ _ _ w2 (fun _ _ => False)).
    apply (r_ro_int_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_int_comp_eq_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_plus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_minus_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_lt_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    apply (r_ro_real_op_mult_tot _ _ _ w1 w2 _ _ _ _ _ X X0).
    intros.
    contradict H1.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    destruct u;    
      dependent destruction H;
      apply r_has_type_ro_has_type_ro in H.
    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun _ _ => False)).
    apply (r_ro_recip_tot _ _ _ _ _ _ _ X).
    intros h1 h2 h3.
    destruct h3.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun x => ψ (IZR x))).
    apply (r_ro_coerce_tot _ _ _ _ _ _ X).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun x => ψ ((powerRZ 2 x)))).
    apply (r_ro_exp_tot _ _ _ _ _ _ X).

    
    induction (has_type_ro_unambiguous _ _ _ _ (has_type_ro_Skip Γ) w).
    pose proof (r_ro_skip_tot _ w ψ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.

              
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r1, r2.
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ (Typing.has_type_rw_Seq _ _ _ _ _ r1 r2 ) X X0).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X1).
    simpl in X2.
    exact X2.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r3.
    apply r_has_type_ro_has_type_ro in r1. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r3 (fun y x => ψ y (snd x))).
    simpl in X, X1, X0.
    pose proof (r_rw_cond_tot _ _ _ _ _ _ _ _ _ (has_type_rw_Cond _ _ _ _ _ _ r1 r2 r3) (fun _ => False) _ _ X X0 X1).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X2).
    simpl in X3.
    exact X3.
    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r2, r4.
    apply r_has_type_ro_has_type_ro in r1, r3. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r2 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r3 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r4 (fun y x => ψ y (snd x))).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun b _ => b = true)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r3 (fun b _ => b = true)).
    simpl in X, X1, X0, X2.
    pose proof (r_rw_case_tot _ _ _ _ _ _ _ _ _ _ _ (has_type_rw_Case _ _ _ _ _ _ _ r1 r2 r3 r4) (fun _ => False) _ _ _ (fun _ => False) (fun _ => False) X X1 X0 X2 X3 X4).
    assert ((forall x : sem_ro_ctx (nil ++ Γ),
        rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False) x ->
        (fun _ : sem_ro_ctx (nil ++ Γ) => False) x \/ (fun _ : sem_ro_ctx (nil ++ Γ) => False) x)).
    intros.
    destruct H.
    
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w (X5 H)).
    simpl in X6.
    exact X6.

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose (ForallT_by_restriction (fun _ : exp * exp =>  sem_ro_ctx (nil ++ Γ) -> Prop) l (fun _ _ => False)).
    pose proof (r_rw_case_list_tot).
    pose (ForallT_map
                                      (fun _ x =>
                                         pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                                              (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
                                              f).
    pose proof (r_rw_case_list_tot Γ nil _ _ f2
                                   (has_type_rw_CaseList _ _ _ _ l1 f2) f0 f1 (fun _ => False) (fun y x => ψ y (snd x))
               ).
    assert (ForallT3 (fun ec : exp * exp => (((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (nil ++ Γ) -> Prop)
         (fun _ : exp * exp => sem_ro_ctx (nil ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l : ((nil ++ Γ) |- fst ec : BOOL) * (Γ;;; nil ||- snd ec : τ))
            (θ : bool -> sem_ro_ctx (nil ++ Γ) -> Prop) (ϕi : sem_ro_ctx (nil ++ Γ) -> Prop) =>
          ((fst wty_l |~ {{rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False)}} fst ec {{y | θ y}}) *
           (snd wty_l ||~ [{ro_to_rw_pre (θ true)}] snd ec [{y
            | (fun x : sem_ro_ctx nil * sem_ro_ctx Γ => ψ y (snd x))}]) *
           (fst wty_l |~ [{ϕi}] fst ec [{b | (fun _ : sem_ro_ctx (nil ++ Γ) => b = true)}]))%type) l f2 f0 f1). 
    
    clear X0 l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT3_nil.
    dependent destruction f.
    apply ForallT3_cons.
    apply IHl.
    split.
    split.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_tot.
    apply r_admissible_ro_exfalso_tot.
    pose proof (X0 X1).
    assert ((forall x : sem_ro_ctx (nil ++ Γ),
        rw_to_ro_pre (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False) x ->
        ForallT_disj (fun _ : exp * exp => sem_ro_ctx (nil ++ Γ) -> Prop)
                     (fun (a : exp * exp) (ϕi : (fun _ : exp * exp => sem_ro_ctx (nil ++ Γ) -> Prop) a) => ϕi x) l f1)).
    intros.
    destruct H.
    pose proof (X2 H).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X3).
    exact X4.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot (Γ ++ nil) nil e2 _ (has_type_rw_add_auxiliary _ _ _ _ r0 nil) (fun _ _ => False)).
    assert (has_type_rw_add_auxiliary Γ nil e2 UNIT r0 nil
  ||~ [{(fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) =>
         ro_to_rw_pre (fun _ : sem_ro_ctx (nil ++ Γ) => False) (fst δγδ', fst_app (snd δγδ')) /\
         fst δγδ' = snd_app (snd δγδ'))}] e2 [{_
                                              | (fun δγδ' : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => (fun _ => False) (fst δγδ', fst_app (snd δγδ')) /\ False)}]).

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros x y.

    destruct y.
    destruct H.
    intros h1 h2 h3; auto.
    
    pose proof (r_rw_while_tot _ _ _ _ _ _ (has_type_rw_While _ _ _ _ r r0) _ _ (fun _ => False) X X1).
    assert ((forall (δ : sem_ro_ctx nil) (γ : sem_ro_ctx Γ),
        (fun _ : sem_ro_ctx nil * sem_ro_ctx Γ => False) (δ, γ) ->
        ~
        (exists f : nat -> sem_ro_ctx nil,
           f 0%nat = δ /\
             (forall n : nat, (fun _ : sem_ro_ctx nil * sem_ro_ctx (Γ ++ nil) => False) (f (S n), (γ; f n)))))).
    intros.
    destruct H.
    pose proof (X2 H).    
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X3).
    simpl in X3.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X4);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H0.
    contradict H0; auto.

    
    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_rw_has_type_rw in r0.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ r0 (fun _ _ => False)).
    pose proof r_rw_new_var_tot.
    pose proof (r_rw_new_var_tot _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ (has_type_rw_Newvar _ _ _ _ _ _ r r0) X X0).
    pose proof (r_rw_ro_tot Γ _ _ _ _ _ w X2).
    simpl in X3.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H; auto.


    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    contradict (assignable_absurd _ _ a).

    pose proof (has_type_ro_r_has_type_ro _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in H. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ H (fun _ _ => False)).
    pose proof r_ro_lim_tot.
    pose proof (r_ro_lim_tot _ _ _ (fun _ => False) (fun _ _ => False) w ψ X).
    assert ( (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) Γ,
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) Γ => False) γ ->
        exists y : R,
          ψ y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x)))).
    intros.
    contradict H0.
    pose proof (X1 H0).
    exact X2.


  +
    dependent destruction e.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_var_prt _ _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_true_prt _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_false_prt _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.


    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_int_prt _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_plus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_minus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_mult_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_lt_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 <? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_eq_prt _ _ _ _ _ _ _ _ (has_type_ro_OpZeq _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 =? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_plus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_minus_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_lt_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
                (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
                (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
                y1 <> y2 -> (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (Rltb'' y1 y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_mult_prt _ _ _ _ _ _ _ _ (has_type_ro_OpRmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct u.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun y x => False)).
    pose proof (r_ro_recip_prt _ _ _ _ _ (has_type_ro_OpRrecip _ _  r) (fun y x => ψ y (fst_app x, snd_app x)) X).
    assert (((fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) /\\\
        (fun (x : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => x <> 0)) ->>>
       (fun x : sem_datatype REAL => (fun (y : R) (x0 : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x0, snd_app x0)) (/ x))).
    intros h1 h2 [h3 _].
    destruct h3.
    pose proof (X0 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X1).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun y x => False)).
    pose proof (r_ro_coerce_prt _ _ _ _ (fun y x => False) (has_type_ro_OpZRcoerce _ _  r) X).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun y x => False)).
    pose proof (r_ro_exp_prt _ _ _ _ (fun y x => False) (has_type_ro_OpZRexp _ _  r) X).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_skip_prt _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H0 ψ). 
    apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ X X0).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H0 ψ). 
    apply (r_rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r, r0.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r0 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H0 ψ). 
    apply (r_rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1 X2).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose proof (r_rw_case_list_prt).
    pose (ForallT_map
                                      (fun _ x =>
                                         pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                                              (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
                                              f).
    apply (r_rw_case_list_prt Γ Δ _ _ f1 w f0 (fun _ => False) ψ).

    clear l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT2_nil.
    dependent destruction f.
    apply ForallT2_cons.
    apply IHl.
    split.
    simpl.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_prt.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H (fun _ _ => False)).
    pose proof r_rw_while_prt.
    pose proof (r_rw_while_prt _ _ _ _ _ _ w  _ _ X X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H0.
    contradict H0.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_prt _ _ _ _ H (fun _ _ => False)).
    pose proof r_rw_new_var_prt.
    pose proof (r_rw_new_var_prt _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ w X X0).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H0; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof r_rw_assign_prt.
    pose proof (r_rw_assign_prt _ _ _ _ _ _ (fun _ => False) (fun _ _ => False) ψ w X).
    assert ((forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ),
                (fun (_ : sem_datatype τ) (_ : sem_ro_ctx (Δ ++ Γ)) => False) x (δ; γ) -> ψ tt (update' r w δ x, γ))).
    intros.
    contradict H.
    exact (X1 H).
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r. 
    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof r_ro_lim_prt.
    pose proof (r_ro_lim_prt _ _ _ (fun _ => False) (fun _ _ => False)
                             (has_type_ro_Lim _ _ r) (fun y x => ψ y (fst_app x , snd_app x)) X).
    assert (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) (Δ ++ Γ),
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) (Δ ++ Γ) => False) γ ->
        exists y : R,
          (fun (y0 : R)
             (x : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                     match lst with
                     | nil => unit
                     | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                     end) (Δ ++ Γ)) => ψ y0 (fst_app x, snd_app x)) y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Δ ++ Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x))).
    intros.
    contradict H.
    pose proof (X1 H).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

  +
    dependent destruction e.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_var_tot _ _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_true_tot _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_false_tot _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.


    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_int_tot _ _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct b.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_plus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_minus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_op_mult_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : Z) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_lt_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 <? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_int_comp_eq_tot _ _ _ _ _ _ _ _ (has_type_ro_OpZeq _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype INTEGER) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 =? y2)%Z γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_plus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRplus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_minus_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRminus _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 - y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_lt_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRlt _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        y1 <> y2 /\ (fun (y : bool) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (Rltb'' y1 y2) γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r1, r2.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r1 (fun y x => False)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r2 (fun y x => False)). 
    pose proof (r_ro_real_op_mult_tot _ _ _ _ _ _ _ _ (has_type_ro_OpRmult _ _ _ r1 r2) (fun y x => ψ y (fst_app x, snd_app x)) X X0).
    assert ((forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx (Δ ++ Γ)),
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y1 γ ->
        (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) y2 γ ->
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 * y2)%R γ)).
    intros.
    destruct H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    destruct u.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun y x => False)).
    pose proof (r_ro_recip_tot _ _ _ _ _ (has_type_ro_OpRrecip _ _  r) (fun y x => ψ y (fst_app x, snd_app x)) X).
    assert ((fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => False) ->>>
       ((fun (x : R) (_ : sem_ro_ctx (Δ ++ Γ)) => x <> 0) /\\\
        (fun x : R => (fun (y : R) (x0 : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x0, snd_app x0)) (/ x)))).
    intros h1 h2 h3.
    destruct h3.
    pose proof (X0 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X1).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun y x => False)).
    pose proof (r_ro_coerce_tot _ _ _ _ (fun y x => False) (has_type_ro_OpZRcoerce _ _  r) X).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun y x => False)).
    pose proof (r_ro_exp_tot _ _ _ _ (fun y x => False) (has_type_ro_OpZRexp _ _  r) X).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intro h; contradict h.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_ro_skip_tot _ r (fun y x => ψ y (fst_app x, snd_app x))).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    contradict h2; auto.
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H0 ψ). 
    apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ X X0).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r.
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H0 ψ). 
    apply (r_rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1).

    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H, H0.
    apply r_has_type_ro_has_type_ro in r, r0.
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_ro_exfalso_prt _ _ _ r0 (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H ψ).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H0 ψ).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun b _ => b = true)).
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r0 (fun b _ => b = true)).
    apply (r_rw_case_tot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X X0 X1 X2 X3 X4).
    intros.
    contradict H1.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    pose (ForallT_by_restriction (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l (fun _ _ _ => False)).
    pose proof (r_rw_case_list_tot).
    pose (ForallT_map
            (fun _ x =>
               pair (r_has_type_ro_has_type_ro _ _ _ (fst x)) 
                    (r_has_type_rw_has_type_rw _ _ _ _ (snd x)))
            f).
    pose (ForallT_by_restriction (fun _ : exp * exp =>  sem_ro_ctx (Δ ++ Γ) -> Prop) l (fun _ _ => False)).
    apply (r_rw_case_list_tot Γ Δ _ _ f1 w f0 f2 (fun _ => False) ψ).
    clear l1 X w.
    dependent induction l.
    dependent destruction f.
    simpl.
    apply ForallT3_nil.
    dependent destruction f.
    apply ForallT3_cons.
    apply IHl.
    split.
    split.
    apply r_admissible_ro_exfalso_prt.
    apply r_admissible_rw_exfalso_tot.
    apply r_admissible_ro_exfalso_tot.
    intros.
    contradict H.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r.    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot (Γ ++ Δ) Δ e2 _ (has_type_rw_add_auxiliary _ _ _ _ H Δ) (fun _ _ => False)).
    assert (has_type_rw_add_auxiliary Γ Δ e2 UNIT H Δ
  ||~ [{(fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) =>
         ro_to_rw_pre (fun _ : sem_ro_ctx (Δ ++ Γ) => False) (fst δγδ', fst_app (snd δγδ')) /\
         fst δγδ' = snd_app (snd δγδ'))}] e2 [{_
                                              | (fun δγδ' : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => (fun _ => False) (fst δγδ', fst_app (snd δγδ')) /\ False)}]).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2.
    contradict H0.
    intros h1 h2 h3; auto.
    
    pose proof (r_rw_while_tot _ _ _ _ _ _ w _ _ (fun _ => False) X X1).
    assert  (forall (δ : sem_ro_ctx Δ) (γ : sem_ro_ctx Γ),
        (fun _ : sem_ro_ctx Δ * sem_ro_ctx Γ => False) (δ, γ) ->
        ~
        (exists f : nat -> sem_ro_ctx Δ,
           f 0%nat = δ /\
             (forall n : nat, (fun _ : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => False) (f (S n), (γ; f n))))).
    intros.
    contradict H0.
    pose proof (X2 H0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    destruct H1.
    contradict H1.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_rw_has_type_rw in H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof (r_admissible_rw_exfalso_tot _ _ _ _ H (fun _ _ => False)).
    pose proof r_rw_new_var_tot.
    pose proof (r_rw_new_var_tot _ _ _ _ _ _ _ _ (fun _  => False) (fun _ _ => False) _ w X X0).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    contradict H0; auto.
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    apply r_has_type_ro_has_type_ro in r. 
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof r_rw_assign_tot.
    pose proof (r_rw_assign_tot _ _ _ _ _ _ (fun _ => False) (fun _ _ => False) ψ w X).
    assert ((forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ),
                (fun (_ : sem_datatype τ) (_ : sem_ro_ctx (Δ ++ Γ)) => False) x (δ; γ) -> ψ tt (update' r w δ x, γ))).
    intros.
    contradict H.
    exact (X1 H).
    
    pose proof (has_type_rw_r_has_type_rw _ _ _ _ w) as H.
    dependent destruction H.
    dependent destruction r.
    apply r_has_type_ro_has_type_ro in r. 
    
    pose proof (r_admissible_ro_exfalso_tot _ _ _ r (fun _ _ => False)).
    pose proof r_ro_lim_tot.
    pose proof (r_ro_lim_tot _ _ _ (fun _ => False) (fun _ _ => False)
                             (has_type_ro_Lim _ _ r) (fun y x => ψ y (fst_app x , snd_app x)) X).
    assert (forall
          γ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                 match lst with
                 | nil => unit
                 | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                 end) (Δ ++ Γ),
        (fun
           _ : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                  match lst with
                  | nil => unit
                  | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                  end) (Δ ++ Γ) => False) γ ->
        exists y : R,
          (fun (y0 : R)
             (x : (fix sem_list_datatype (lst : ro_ctx) : Type :=
                     match lst with
                     | nil => unit
                     | t :: lst0 => (sem_datatype t * sem_list_datatype lst0)%type
                     end) (Δ ++ Γ)) => ψ y0 (fst_app x, snd_app x)) y γ /\
          (forall (x : sem_datatype INTEGER) (z : sem_datatype REAL),
           (fun (_ : sem_datatype REAL) (_ : sem_ro_ctx (INTEGER :: Δ ++ Γ)) => False) z (x, γ) ->
           Rabs (z - y) < powerRZ 2 (- x))).
    intros.
    contradict H.
    pose proof (X1 H).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w X2).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold fst_app, snd_app; destruct h2; rewrite tedious_equiv_1; auto.
Defined.


Fixpoint r_ro_var_prt_inv {Γ} {k} {τ} {w : Γ |- Var k : τ} {ϕ} {ψ} (p : w |~ {{ϕ}} (Var k) {{ψ}}) {struct p}:
  ϕ ->> (fun γ : sem_ro_ctx Γ => ψ (ro_access Γ k τ w γ) γ)
  with r_rw_var_prt_inv Γ k τ (w : Γ |- Var k : τ) (w' : Γ ;;; nil ||- Var k : τ) ϕ ψ (p : w' ||~ {{ϕ}} (Var k) {{ψ}}) {struct p} :  (fun γ : sem_ro_ctx Γ => ϕ (tt, γ)) ->> (fun γ : sem_ro_ctx Γ => ψ (ro_access Γ k τ w γ) (tt, γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_var_prt_inv _ _ _ _ _ _ p).
  intros γ m.
  apply a0.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_var_prt_inv _ _ _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_var_prt_inv _ _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ m.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  apply (r_ro_var_prt_inv _ _ _ _ _ _ r γ m).
Qed.  

Fixpoint r_ro_skip_prt_inv {Γ} {w : Γ |- SKIP : UNIT} {ϕ} {ψ} (p : w |~ {{ϕ}} (SKIP) {{ψ}}) {struct p}:
  ϕ ->> (ψ tt)
with r_rw_skip_prt_inv Γ (w : Γ |- SKIP : UNIT) (w' : Γ ;;; nil ||- SKIP : UNIT) ϕ ψ (p : w' ||~ {{ϕ}} (SKIP) {{ψ}}) {struct p} :
  (fun γ : sem_ro_ctx Γ => ϕ (tt, γ)) ->> (fun γ : sem_ro_ctx Γ => ψ tt (tt, γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_skip_prt_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_skip_prt_inv _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_skip_prt_inv _  w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ m.
  apply (r_ro_skip_prt_inv _ _ _ _  r γ m).
Qed.


Fixpoint r_ro_true_prt_inv {Γ} {w : Γ |- TRUE : BOOL} {ϕ} {ψ} (p : w |~ {{ϕ}} (TRUE) {{ψ}}) {struct p}:
  ϕ ->> (ψ true)
with r_rw_true_prt_inv Γ (w : Γ |- TRUE : BOOL) (w' : Γ ;;; nil ||- TRUE : BOOL) ϕ ψ (p : w' ||~ {{ϕ}} (TRUE) {{ψ}}) {struct p} :
  (fun γ : sem_ro_ctx Γ => ϕ (tt, γ)) ->> (fun γ : sem_ro_ctx Γ => ψ true (tt, γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_true_prt_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_true_prt_inv _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_true_prt_inv _  w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ m.
  apply (r_ro_true_prt_inv _ _ _ _  r γ m).
Qed.

Fixpoint r_ro_false_prt_inv {Γ} {w : Γ |- FALSE : BOOL} {ϕ} {ψ} (p : w |~ {{ϕ}} (FALSE) {{ψ}}) {struct p}:
  ϕ ->> (ψ false)
with r_rw_false_prt_inv Γ (w : Γ |- FALSE : BOOL) (w' : Γ ;;; nil ||- FALSE : BOOL) ϕ ψ (p : w' ||~ {{ϕ}} (FALSE) {{ψ}}) {struct p} :
  (fun γ : sem_ro_ctx Γ => ϕ (tt, γ)) ->> (fun γ : sem_ro_ctx Γ => ψ false (tt, γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_false_prt_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_false_prt_inv _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_false_prt_inv _  w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ m.
  apply (r_ro_false_prt_inv _ _ _ _  r γ m).
Qed.

Fixpoint r_ro_int_prt_inv {Γ} {k} {w : Γ |- (INT k) : INTEGER} {ϕ} {ψ} (p : w |~ {{ϕ}} (INT k) {{ψ}}) {struct p}:
  ϕ ->> (ψ k)
with r_rw_int_prt_inv Γ k (w : Γ |- (INT k) : INTEGER) (w' : Γ ;;; nil ||- (INT k) : INTEGER) ϕ ψ (p : w' ||~ {{ϕ}} (INT k) {{ψ}}) {struct p} :
  (fun γ : sem_ro_ctx Γ => ϕ (tt, γ)) ->> (fun γ : sem_ro_ctx Γ => ψ k (tt, γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_int_prt_inv _ _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_int_prt_inv _ _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_int_prt_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ m.
  apply (r_ro_int_prt_inv _ _ _ _ _  r γ m).
Qed.


Fixpoint r_ro_int_op_plus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :+: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :+: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%Z γ)} }%type
with r_rw_int_op_plus_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 :+: e2) : INTEGER}
  {w1 : Γ |- e1 : INTEGER}
  {w2 : Γ |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :+: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%Z (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_int_op_plus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_int_op_plus_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_int_op_plus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_int_op_plus_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_int_op_minus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :-: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :-: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%Z γ)} }%type
with r_rw_int_op_minus_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 :-: e2) : INTEGER}
  {w1 : Γ |- e1 : INTEGER}
  {w2 : Γ |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :-: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%Z (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_int_op_minus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_int_op_minus_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_int_op_minus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_int_op_minus_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_int_op_mult_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :*: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :*: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%Z γ)} }%type
with r_rw_int_op_mult_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 :*: e2) : INTEGER}
  {w1 : Γ |- e1 : INTEGER}
  {w2 : Γ |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :*: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%Z (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_int_op_mult_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_int_op_mult_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_int_op_mult_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_int_op_mult_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_int_comp_lt_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :<: e2) : BOOL}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :<: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 <? y2)%Z γ)} }%type
with r_rw_int_comp_lt_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 :<: e2) : BOOL}
  {w1 : Γ |- e1 : INTEGER}
  {w2 : Γ |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :<: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 <? y2)%Z (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_int_comp_lt_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_int_comp_lt_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_int_comp_lt_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_int_comp_lt_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_int_comp_eq_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :=: e2) : BOOL}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :=: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 =? y2)%Z γ)} }%type
with r_rw_int_comp_eq_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 :=: e2) : BOOL}
  {w1 : Γ |- e1 : INTEGER}
  {w2 : Γ |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :=: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 =? y2)%Z (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_int_comp_eq_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_int_comp_eq_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_int_comp_eq_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_int_comp_eq_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_real_op_plus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;+; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;+; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%R γ)} }%type
with r_rw_real_op_plus_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 ;+; e2) : REAL}
  {w1 : Γ |- e1 : REAL}
  {w2 : Γ |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;+; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%R (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_real_op_plus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_real_op_plus_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_real_op_plus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_real_op_plus_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.



Fixpoint r_ro_real_op_minus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;-; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;-; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%R γ)} }%type
with r_rw_real_op_minus_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 ;-; e2) : REAL}
  {w1 : Γ |- e1 : REAL}
  {w2 : Γ |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;-; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%R (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_real_op_minus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_real_op_minus_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_real_op_minus_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_real_op_minus_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_real_op_mult_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;*; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;*; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%R γ)} }%type
with r_rw_real_op_mult_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 ;*; e2) : REAL}
  {w1 : Γ |- e1 : REAL}
  {w2 : Γ |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;*; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%R (tt, γ)))%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_real_op_mult_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_real_op_mult_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_real_op_mult_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_real_op_mult_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_real_lt_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;<; e2) : BOOL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;<; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ)} }%type
with r_rw_real_lt_prt_inv {Γ} {e1 e2} {w0 : Γ;;; nil ||- (e1 ;<; e2) : BOOL}
  {w1 : Γ |- e1 : REAL}
  {w2 : Γ |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;<; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e2 {{y | ψ2 y}}) *
              (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) (tt, γ)) )%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_real_lt_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_real_lt_prt_inv _ _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_real_lt_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    exact (r_ro_real_lt_prt_inv _ _ _ _ w1 w2 _ _ r).
Qed.

Fixpoint r_ro_recip_prt_inv {Γ} {e} {w : Γ |- (;/; e) : REAL}
  (w' : Γ |- e : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (;/; e) {{ψ}}) {struct p}:
  {θ & (w' |~ {{ϕ}} e {{θ}}) *   ((θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> 0)) ->>> (fun x : sem_datatype REAL => ψ (/ x)))}%type
with r_rw_recip_prt_inv {Γ} {e} {w : Γ;;; nil ||- (;/; e) : REAL}
  {w' : Γ |- e : REAL}
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (;/; e) {{ψ}}) {struct p}:
  {θ & (w' |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e {{y | θ y}}) *
         ((θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> 0)) ->>> (fun x γ => ψ (/ x) (tt, γ)))}%type.
Proof.
    dependent induction p.
    pose proof (r_ro_recip_prt_inv _ _ _  w' _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    intros y γ.
    intro.
    apply a0.
    apply m2.
    exact H.
    apply (r_rw_recip_prt_inv _ _ _ _ _ _ r).

    exists θ.
    split.
    apply (r_proves_ro_prt_typing_irrl p).
    apply a.

  +
    dependent induction p.
    pose proof (r_rw_recip_prt_inv _ _ _  w' _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros y γ h.
    apply a0.
    apply m2.
    exact h.    
    exact (r_ro_recip_prt_inv _ _ _ w' _ _ r).
Qed.
  
Fixpoint r_ro_coerce_prt_inv {Γ} {e} {w : Γ |- (RE e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (RE e) {{ψ}}) {struct p}:
  w' |~ {{ϕ}} e {{y | ψ (IZR y)}}
with r_rw_coerce_prt_inv {Γ} {e} {w : Γ ;;; nil ||- (RE e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (RE e) {{ψ}}) {struct p}:
  w' |~ {{fun γ => ϕ (tt, γ)}} e {{y | fun γ => ψ (IZR y) (tt, γ)}}.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_coerce_prt_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_rw_coerce_prt_inv _ _ w0); auto.
    apply (r_proves_ro_prt_typing_irrl p).
  +
    dependent induction p.
    pose proof (r_rw_coerce_prt_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    exact (r_ro_coerce_prt_inv _ _ _  w' _ _ r). 
Qed.

Fixpoint r_ro_exp_prt_inv {Γ} {e} {w : Γ |- (EXP e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (EXP e) {{ψ}}) {struct p}:
  w' |~ {{ϕ}} e {{y | ψ (powerRZ 2 y)}}
with r_rw_exp_prt_inv {Γ} {e} {w : Γ ;;; nil ||- (EXP e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (EXP e) {{ψ}}) {struct p}:
  w' |~ {{fun γ => ϕ (tt, γ)}} e {{y | fun γ => ψ (powerRZ 2 y) (tt, γ)}}.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_exp_prt_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_rw_exp_prt_inv _ _ w0); auto.
    apply (r_proves_ro_prt_typing_irrl p).
  +
    dependent induction p.
    pose proof (r_rw_exp_prt_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    exact (r_ro_exp_prt_inv _ _ _  w' _ _ r). 
Qed.


Axiom magic : forall A, A.


Check r_rw_sequence_prt.
Fixpoint r_rw_sequence_prt_inv {Γ Δ} {c1 c2} {τ} {w : Γ ;;; Δ ||- (c1 ;; c2) : τ}
  (w1 : Γ ;;; Δ ||- c1 : UNIT)
  (w2 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (c1 ;; c2) {{ψ}}) {struct p}:
  {θ & (w1 ||~ {{ϕ}} c1 {{θ}}) * (w2 ||~ {{θ tt}} c2 {{ψ}})}%type
with r_ro_sequence_prt_inv {Γ Δ} {c1 c2} {τ} {w : (Δ ++ Γ) |- (c1 ;; c2) : τ}
  (w1 : Γ ;;; Δ ||- c1 : UNIT)
  (w2 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (c1 ;; c2) {{ψ}}) {struct p}:
  {θ & (w1 ||~ {{fun x => ϕ (fst x; snd x)}} c1 {{θ}}) * (w2 ||~ {{θ tt}} c2 {{fun y x => ψ y (fst x; snd x)}})}%type.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_sequence_prt_inv _ _ _ _ _ _ w1 w2 _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_sequence_prt_inv _ _ _ _ _ _ w1 w2 _ _ r) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl; auto.
    exists θ.
    split; auto.
    apply (r_proves_rw_prt_typing_irrl p1).
    apply (r_proves_rw_prt_typing_irrl p2).
  +
    dependent induction p.
    pose proof (r_ro_sequence_prt_inv _ _ _ _ _ w0 w1 w2 _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_rw_sequence_prt_inv _ _ _ _ _ w0 w1 w2 _ _ r).
    destruct h2.

    
    
    
  Check tedious_equiv_1.
  
  unfold tedious_prod_sem.
  apply m1.
  dependent destruction w0.
  
  pose proof has_type_ro_rw.

  (has_type_ro_rw _ _  w1).
  pose proof (r_ro_sequence_prt_inv _ _ _ _ w0 (has_type_ro_rw _ _ _ w1) (has_type_ro_rw w2)).
  dependent induction r.
  apply (IHr c1 c2 _ _ .
  dependent induction r.

  
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
    
    apply magic.
    apply magic.
    apply magic.
    apply magic.
    apply magic.
    apply magic.
    apply magic.
    apply magic.
  +
    apply magic.
        
  +
    apply magic.

        
  +
    apply magic.
Qed.
    
