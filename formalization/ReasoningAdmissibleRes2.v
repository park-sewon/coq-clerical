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
Require Import Clerical.ReasoningAdmissibleRes0.
Require Import Clerical.ReasoningAdmissibleRes1.
Require Import Clerical.ReasoningSoundness.

Lemma pdom_neg_is_empty_to_evidence {X} (S : pdom X) : pdom_neg_is_empty S -> exists x : flat X, x ∈ S.
Proof.
  intro n.
  unfold pdom_neg_is_empty in n.
  unfold pdom_is_empty in n.
  apply neg_forall_exists_neg in n as [x p].
  exists x.
  destruct S.
  simpl in p.
  apply dn_elim in p.
  simpl.
  exact p.
Defined.  

Lemma proves_ro_tot_pick_from_two_post {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ1 ψ2} (p : w |- [{ϕ}] e [{ψ1}]) (q : w |- [{ϕ}] e [{ψ2}]) :
  forall γ, ϕ γ -> exists y, ψ1 y γ /\ ψ2 y γ.
Proof.
  intros γ H.
  apply proves_ro_tot_sound in p.
  apply proves_ro_tot_sound in q.
  pose proof (p γ H) as [n x].
  pose proof (q γ H) as [_ y].
  apply pdom_neg_is_empty_to_evidence in n as [z h].
  pose proof (x z h) as [v hh].
  pose proof (y z h) as [vv hhh].
  exists v.
  destruct hh.
  simpl in H1.
  destruct hhh.
  simpl in H3.
  rewrite H0 in H2.
  apply total_is_injective in H2.
  induction H2.
  split; auto.
Defined.


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
           Rabs (z - y) < powerRZ 2 (- x))))%R.
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
           Rabs (z - y) < powerRZ 2 (- x)))%R).
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
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2)%R γ)).
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
        (fun (x : sem_datatype REAL) (_ : sem_ro_ctx (Δ ++ Γ)) => x <> 0%R)) ->>>
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
           Rabs (z - y) < powerRZ 2 (- x)))%R.
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
        (fun (y : R) (x : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x, snd_app x)) (y1 + y2)%R γ)).
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
        (fun x : R => (fun (y : R) (x0 : sem_ro_ctx (Δ ++ Γ)) => ψ y (fst_app x0, snd_app x0)) (/ x))))%R.
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
           Rabs (z - y) < powerRZ 2 (- x)))%R.
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
  inversion p.
  repeat apply projT2_eq in H;
    repeat apply projT2_eq in H0;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H6.
    

  pose proof (r_ro_var_prt_inv _ _ _ _ _ _ X).
  intros γ m.
  induction H6.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  apply H7, H8.
  induction H4.
  apply H5.
  exact m.

  repeat apply projT2_eq in H3;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6.
  induction H5.
  induction H3.
  intros h1 h2.
  induction H6.
  exact h2.

  repeat apply projT2_eq in H3;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6.

  induction H5.
  induction H6.
  apply (r_rw_var_prt_inv _ _ _ w w0 _ _ X).

  inversion p.
  repeat apply projT2_eq in H;
    repeat apply projT2_eq in H0;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H7.
  
  pose proof (r_rw_var_prt_inv _ _ _ w _ _ _ X).
  intros γ m.
  induction H7.
  apply H8.
  apply H9.
  apply H6.
  induction H5.
  exact m.
  
  repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6;
    repeat apply projT2_eq in H7.
  induction H7.
  intros γ m.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  induction H6.
  apply (r_ro_var_prt_inv _ _ _ _ _ _ X γ m).
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
  {θ & (w' |~ {{ϕ}} e {{θ}}) *   ((θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> 0%R)) ->>> (fun x : sem_datatype REAL => ψ (/ x)%R))}%type
with r_rw_recip_prt_inv {Γ} {e} {w : Γ;;; nil ||- (;/; e) : REAL}
  {w' : Γ |- e : REAL}
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (;/; e) {{ψ}}) {struct p}:
  {θ & (w' |~ {{(fun γ : sem_ro_ctx Γ => ϕ (tt, γ))}} e {{y | θ y}}) *
         ((θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> 0%R)) ->>> (fun x γ => ψ (/ x)%R (tt, γ)))}%type.
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

Lemma has_type_rw_move
     : forall (Γ : list datatype) (Δ1 : ro_ctx) (Δ2 : list datatype) (e : exp) (τ : datatype),
    (Δ2 ++ Γ);;; Δ1 ||- e : τ -> Γ;;; (Δ1 ++ Δ2) ||- e : τ.
Proof.
  intros.
  apply r_has_type_rw_has_type_rw.
  apply has_type_rw_r_has_type_rw in H.
  apply r_has_type_rw_move.
  exact H.
Defined
.

  
Fixpoint r_admissible_move_rw_prt Γ Δ1 Δ2 e τ (w : (Δ2 ++ Γ) ;;; Δ1 ||- e : τ) ϕ ψ (p : w ||~ {{ϕ}} e {{ψ}}) :
  (has_type_rw_move Γ Δ1 Δ2 e τ w) ||~ {{fun x => ϕ (fst_app (fst x), (snd_app (fst x); snd x))}} e {{fun y x => ψ y (fst_app (fst x), (snd_app (fst x); snd x))}}.
Proof.
Admitted.

Check r_rw_sequence_prt.
(* Lemma has_type_ro_Seq_rw  *)
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
    pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w0) as [r1 r2].
    pose proof (r_rw_sequence_prt_inv _ _ _ _ _ w0 r1 r2 _ _ r) as [θ [m1 m2]].
    exists (fun _ x => θ tt (tt, (fst x; snd x))).
    split.
    apply r_admissible_move_rw_prt in m1.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1, h2.
    simpl in s.
    unfold fst_app, snd_app; simpl.
    auto.
    apply r_admissible_move_rw_prt in m2.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Qed.

  

Fixpoint r_rw_cond_prt_inv {Γ Δ} {e c1 c2} {τ} {w : Γ ;;; Δ ||- (IF e THEN c1 ELSE c2 END) : τ}
  (w1 : (Δ ++ Γ) |- e : BOOL)
  (w2 : Γ ;;; Δ ||- c1 : τ)
  (w3 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (IF e THEN c1 ELSE c2 END) {{ψ}}) {struct p}:
  {θ & (w1 |~ {{fun x => ϕ (fst_app x, snd_app x)}} e {{θ}}) * (w2 ||~ {{ro_to_rw_pre (θ true)}} c1 {{ψ}}) * (w3 ||~ {{ro_to_rw_pre (θ false)}} c2 {{ψ}})}%type
with r_ro_cond_prt_inv {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- (IF e THEN c1 ELSE c2 END) : τ}
  (w1 : (Δ ++ Γ) |- e : BOOL)
  (w2 : Γ ;;; Δ ||- c1 : τ)
  (w3 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (IF e THEN c1 ELSE c2 END) {{ψ}}) {struct p}:
  {θ & (w1 |~ {{ϕ}} e {{θ}}) * (w2 ||~ {{ro_to_rw_pre (θ true)}} c1 {{fun y x => ψ y (fst x; snd x)}}) * (w3 ||~ {{ro_to_rw_pre (θ false)}} c2 {{fun y x => ψ y (fst x; snd x)}})}%type.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_cond_prt_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ p) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    pose proof (r_ro_cond_prt_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ r) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_2.
    exact h2.

    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl.
    auto.
    
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl.
    auto.
    
    exists θ.
    split; auto.
    split.
    assert (w4 |~ {{(fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (fst_app x, snd_app x))}} e {{y | θ y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre.
    unfold fst_app, snd_app in h2.
    destruct (tedious_sem_app Δ Γ h1); auto.
    apply (r_proves_ro_prt_typing_irrl X).
    apply (r_proves_rw_prt_typing_irrl p1).
    apply (r_proves_rw_prt_typing_irrl p2).

  +
    dependent induction p.
    pose proof (r_ro_cond_prt_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ p) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w0) as [[r1 r2] r3].
    pose proof (r_rw_cond_prt_inv _ _ _ _ _ _ w0 r1 r2 r3 _ _ r) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    assert (r1 |~ {{(fun γ : sem_ro_ctx (Δ ++ Γ) => P (tt, γ))}} e {{y | θ y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_proves_ro_prt_typing_irrl X).

    
    apply r_admissible_move_rw_prt in m2.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; simpl.
    simpl in s.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl.
    unfold snd_app.
    simpl.
    auto.

    apply r_admissible_move_rw_prt in m3.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; simpl.
    simpl in s.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl.
    unfold snd_app.
    simpl.
    auto.
Qed.


Fixpoint r_rw_case_list_prt_inv {Γ Δ} {l} {τ} {w : Γ ;;; Δ ||- (CaseList l) : τ}
  wty_l
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (CaseList l) {{ψ}}) {struct p} :
  {θ & ForallT2 (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l0 : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ)) (θ0 : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) =>
            ((fst wty_l0 |~ {{rw_to_ro_pre ϕ}} fst ec {{y | θ0 y}}) * (snd wty_l0 ||~ {{ro_to_rw_pre (θ0 true)}} snd ec {{y | ψ y}}))%type) l wty_l θ}
with r_ro_case_list_prt_inv {Γ Δ} {l} {τ} {w : (Δ ++ Γ) |- (CaseList l) : τ}
  wty_l
  {ϕ} {ψ} (p : w |~ {{ϕ}} (CaseList l) {{ψ}}) {struct p} :
  {θ : ForallT (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l &
  ForallT2 (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type)
    (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
    (fun (ec : exp * exp) (wty_l0 : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ)) (θ0 : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) =>
     ((fst wty_l0 |~ {{rw_to_ro_pre (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ (tedious_prod_sem Δ Γ γδ))}} fst ec {{y | θ0 y}}) *
      (snd wty_l0 ||~ {{ro_to_rw_pre (θ0 true)}} snd ec {{y | (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ψ y (tedious_prod_sem Δ Γ γδ))}}))%type) l wty_l
    θ}.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_case_list_prt_inv _ _ _ _ w0 wty_l _ _ p) as [θ F].
    clear IHp .
    clear w.
    clear p w0.
    exists θ.
    dependent induction F.
    apply ForallT2_nil.
    apply ForallT2_cons.
    simpl.
    apply IHF.
    clear IHF.
    simpl in F.
    destruct F.
    destruct r.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply a.
    unfold rw_to_ro_pre in h2.
    auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct r.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply a.
    unfold rw_to_ro_pre in h2.
    auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

    apply (r_ro_case_list_prt_inv _ _ _ _ w0); auto.

    exists θ.
    clear w.
    dependent induction f.
    simpl.
    dependent destruction wty_l.
    apply ForallT2_nil.
    dependent destruction wty_l.
    apply ForallT2_cons.
    apply IHf.
    destruct r.
    clear IHf wty_l.
    split.
    apply (r_proves_ro_prt_typing_irrl r).
    apply (r_proves_rw_prt_typing_irrl r0).
  +
    dependent induction p.
    pose proof (r_ro_case_list_prt_inv _ _ _ _ w0 wty_l _ _ p) as [θ f].
    exists θ.
    clear p w0 w IHp.
    induction f.
    apply ForallT2_nil.
    apply ForallT2_cons.
    apply IHf.
    clear IHf.
    destruct r.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply a.
    apply h2.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

    pose proof (has_type_rw_CaseList_inverse _ _ _ _ w0).
    pose proof (r_rw_case_list_prt_inv _ _ _ _ w0 H _ _ r) as [θ f].
    exists θ.
    clear r w w0.
    dependent induction f.
    dependent destruction wty_l.
    apply ForallT2_nil.
    dependent destruction wty_l.
    apply ForallT2_cons.
    apply IHf.
    clear IHf.
    destruct r.
    split.
    assert (fst p0 |~ {{rw_to_ro_pre (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => P (tt, tedious_prod_sem Δ Γ γδ))}} fst a {{y | q y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    simpl in h1.
    unfold rw_to_ro_pre.
    unfold rw_to_ro_pre in h2.
    simpl.
    pose proof (tedious_equiv_2 h1).
    rewrite H.
    rewrite H in h2.
    unfold fst_app, snd_app.
    unfold fst_app, snd_app in h2.
    destruct (tedious_sem_app Δ Γ h1).
    simpl.
    simpl in h2.
    rewrite tedious_equiv_1 in h2.
    exact h2.
    apply (r_proves_ro_prt_typing_irrl X).
    
    assert (snd p0 ||~ {{ro_to_rw_pre (q true)}} snd a {{y | (fun x => Q y (tt, snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    simpl in h2.
    destruct h2.
    simpl.
    destruct u.
    auto.
    apply r_admissible_move_rw_prt in X.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl in s.
    simpl.
    unfold snd_app; simpl.
    auto.
    destruct h2.
    simpl in s.
    simpl.
    unfold snd_app; simpl.
    auto.
Qed.
  
Fixpoint r_rw_while_prt_inv {Γ Δ} {e c} {w : Γ ;;; Δ ||- (WHILE e DO c END) : UNIT}
         (we : (Δ ++ Γ) |- e : BOOL)
         (wc : Γ ;;; Δ ||- c : UNIT) {ϕ} {ψ} (p : w ||~ {{ϕ}} (WHILE e DO c END) {{ψ}}) {struct p} :
  {I & {θ &
          (ϕ ->> I) * ((I /\\ ro_to_rw_pre (θ false)) ->> ψ tt) *
            (we |~ {{rw_to_ro_pre I}} e {{θ}}) *
            (wc ||~ {{ro_to_rw_pre (θ true)}} c {{fun _ => I}})} }%type
with r_ro_while_prt_inv {Γ Δ} {e c} {w0 : (Δ ++ Γ) |- (WHILE e DO c END) : UNIT}
                        (we : (Δ ++ Γ) |- e : BOOL)
                        (wc : Γ ;;; Δ ||- c : UNIT) {ϕ0} {ψ0} (p : w0 |~ {{ϕ0}} (WHILE e DO c END) {{ψ0}}) {struct p} :
  let ϕ := (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ0 (tedious_prod_sem Δ Γ γδ)) in
  let ψ := (fun (v : unit) (γδ : sem_ro_ctx Δ * sem_ro_ctx Γ) => ψ0 v (tedious_prod_sem Δ Γ γδ)) in
  {I  &
     {θ  &
        ((ϕ ->> I) * ((I /\\ ro_to_rw_pre (θ false)) ->> ψ tt) * (we |~ {{rw_to_ro_pre I}} e {{y | θ y}}) *
           (wc ||~ {{ro_to_rw_pre (θ true)}} c {{_ | I}}))%type } }.
Proof.
  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H7.    

      pose proof (r_rw_while_prt_inv _ _ _ _ _ we wc _ _ X) as [I [θ [[[m1 m2] m3] m4]]].
      exists I.
      exists θ.
      repeat split; auto.
      intros x q.
      apply m1.
      induction H5.
      apply H6.
      exact q.
      intros q [h1 h2].
      induction H7.
      apply H8.
      apply m2.
      split; auto.
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.    
      induction H6.
      induction H7.
      apply (r_ro_while_prt_inv _ _ _ _ w0 we wc _ _ X).
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.    
      exists ϕ.
      exists θ.
      repeat split; (try intros h1 h2; auto); auto.
      induction H7.
      induction H6.
      exact h2.
      induction H6.
      apply (r_proves_ro_prt_typing_irrl X).
      induction H6.
      apply (r_proves_rw_prt_typing_irrl X0).
    }

  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H6.
      pose proof (r_ro_while_prt_inv _ _ _ _ _ we wc _ _ X) as [I [θ [[[m1 m2] m3] m4]]].
      exists I.
      exists θ.
      repeat split; auto.
      induction H4.
      intros x h.
      apply m1.
      apply H5.
      exact h.

      induction H6.
      intros x h.
      apply H7.
      apply m2.
      exact h.
    }
   
    {
      repeat apply projT2_eq in H3.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      pose proof (has_type_rw_While_inverse w) as [r1 r2]. 
      pose proof (r_rw_while_prt_inv _ _ _ _ _ r1 r2 _ _ X) as [I [θ [[[m1 m2] m3] m4]]].
      exists (fun x => I (tt, tedious_prod_sem _ _ x)).
      exists (θ).
      repeat split; auto.
      intros x h.
      apply m1.
      induction H5.
      exact h.
      intros x h.
      induction H6.
      apply m2.
      exact h.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre.
      unfold rw_to_ro_pre in h2.
      simpl in h2.
      simpl.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply r_admissible_move_rw_prt in m4.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold ro_to_rw_pre, fst_app, snd_app.
      simpl.
      
      unfold ro_to_rw_pre in h2.
      destruct h1; auto.
      destruct h2; auto.      
    }
Qed.

Fixpoint r_rw_new_var_prt_inv {Γ Δ} {e c} {τ σ} {w : Γ ;;; Δ ||- (NEWVAR e IN c) : τ}
         (we : (Δ ++ Γ) |- e : σ)
         (wc : Γ ;;; (σ :: Δ) ||- c : τ) {ϕ} {ψ} (p : w ||~ {{ϕ}} (NEWVAR e IN c) {{ψ}}) {struct p} :
  {θ &
     (we |~ {{(fun x => ϕ (tedious_sem_app Δ Γ x))}} e {{y | θ y}}) *
       (wc ||~ {{(fun x => θ (fst (fst x)) (snd (fst x); snd x))}} c {{fun y x => ψ y (snd (fst x), snd x)}}) }%type
with r_ro_new_var_prt_inv {Γ Δ} {e c} {τ σ} {w0 : (Δ ++ Γ) |- (NEWVAR e IN c) : τ}
         (we : (Δ ++ Γ) |- e : σ)
         (wc : Γ ;;; (σ :: Δ) ||- c : τ) {ϕ0} {ψ0} (p : w0 |~ {{ϕ0}} (NEWVAR e IN c) {{ψ0}}) {struct p} :
  let ϕ := (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ0 (tedious_prod_sem Δ Γ γδ)) in
  let ψ := (fun (v : sem_datatype τ) (γδ : sem_ro_ctx Δ * sem_ro_ctx Γ) => ψ0 v (tedious_prod_sem Δ Γ γδ)) in
  {θ : sem_datatype σ -> sem_ro_ctx (Δ ++ Γ) -> Prop &
  ((we |~ {{(fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ x))}} e {{y | θ y}}) *
   (wc ||~ {{(fun x : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst x)) (snd (fst x); snd x))}} c {{y
    | (fun x : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => ψ y (snd (fst x), snd x))}}))%type}.
Proof.
  +
    inversion p.
    {
      repeat apply projT2_eq in H;
        repeat apply projT2_eq in H0;
        repeat apply projT2_eq in H5;
        repeat apply projT2_eq in H7.

      pose proof (r_rw_new_var_prt_inv _ _ _ _ _ _ _ we wc _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H6.
      induction H5.
      exact h2.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a t2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      induction H7.
      apply H8.
      exact H9.
    }
    
    {
      repeat apply projT2_eq in H4;
      repeat apply projT2_eq in H5;
      repeat apply projT2_eq in H6;
      repeat apply projT2_eq in H7.
      induction H6.
      induction H7.
      apply (r_ro_new_var_prt_inv _ _ _ _ _ _ w0 we wc _ _ X).
    }
    
    {
      repeat apply projT2_eq in H5;
      repeat apply projT2_eq in H6;
      repeat apply projT2_eq in H7;
      repeat apply projT2_eq in H8.
      induction (has_type_ro_unambiguous _ _ _ _ we w1).
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H7.
      exact h2.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H8.
      intro x; exact x.      
    }

    +
      inversion p.
      {
        repeat apply projT2_eq in H;
        repeat apply projT2_eq in H0;
        repeat apply projT2_eq in H4;
        repeat apply projT2_eq in H6.
        pose proof (r_ro_new_var_prt_inv _ _ _ _ _ _ _ we wc _ _ X) as [θ [t1 t2]].
        exists θ.
        split.
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply H5.
        induction H4.
        exact h2.
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a t2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        intro.
        induction H6.
        apply H7.
        exact H8.
      }

      {
        repeat apply projT2_eq in H3;
        repeat apply projT2_eq in H4;
        repeat apply projT2_eq in H5;
        repeat apply projT2_eq in H6.
        pose proof (has_type_rw_Newvar_inverse w) as [σ' [r1 r2]].
        induction (has_type_ro_unambiguous _ _ _ _ we r1).        
        pose proof (r_rw_new_var_prt_inv _ _ _ _ _ _ _ r1 r2 _ _ X) as [θ [t1 t2]].
        exists θ.
        split.
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        induction H5.
        simpl.
        rewrite tedious_equiv_3 in h2.
        exact h2.
        apply r_admissible_move_rw_prt in t2.
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a t2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h1.
        simpl.
        simpl in h2.
        destruct s.
        simpl.
        simpl in h2.
        simpl in s1.
        unfold snd_app; simpl.
        exact h2.
        destruct h2.
        destruct s.
        simpl.
        unfold snd_app; simpl.
        induction H6.
        intro x; exact x.
      }
Defined.

Lemma update'_typing_irrl {Γ Δ} {e} {k} {τ} (w1 w2 : (Δ ++ Γ) |- e : τ) (w1' w2' : Γ ;;; Δ ||- (LET k := e) : UNIT) :
  forall δ x, update' w1 w1' δ x = update' w2 w2' δ x.
Proof.
  intros.
  unfold update'.
  apply lp.
  apply assignable_unique.
Defined.
  
Fixpoint r_rw_assign_prt_inv {Γ Δ} {e} {k} {τ} {w : Γ ;;; Δ ||- (LET k := e) : UNIT}
         (we : (Δ ++ Γ) |- e : τ) {ϕ} {ψ} (p : w ||~ {{ϕ}} (LET k := e) {{ψ}}) {struct p} :
  {θ & (we |~ {{(fun x => ϕ (tedious_sem_app Δ Γ x))}} e {{θ}}) *
         (forall x γ δ, θ x (δ; γ) -> ψ tt (update' we w δ x, γ))}%type.
Proof.
  +
    dependent destruction p.
    {
      pose proof (r_rw_assign_prt_inv _ _ _ _ _ _ we _ _ p) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      rewrite (update'_typing_irrl we we w w0).
      apply a0.
      apply t2.
      exact H.
    }
    
    {
      contradict (ro_assign_absurd _ _ _ w0).
    }
    
    {
      induction (has_type_ro_unambiguous _ _ _ _ we w0).
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      intros.
      rewrite (update'_typing_irrl we w0 w w).
      apply ψ1.
      exact H.
    }
Defined.

Ltac use_eq_l id :=
  induction id; clear id.
Ltac use_eq_r id :=
  induction (eq_sym id); clear id.

Fixpoint r_ro_lim_prt_inv {Γ} {e} {w : Γ |- (Lim e) : REAL}
         (we : (INTEGER :: Γ) |- e : REAL) {ϕ} {ψ} (p : w |~ {{ϕ}} (Lim e) {{ψ}}) {struct p} :
  {θ & (we |~ [{(fun γ' : sem_ro_ctx (INTEGER :: Γ) => ϕ (snd γ'))}] e [{y | θ y}]) *
       (forall γ, ϕ γ ->
                  exists y : R,
                    ψ y γ /\
                      (forall x z , θ z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x))%R)}%type
with r_rw_lim_prt_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (Lim e) : REAL}
         (we : (INTEGER :: (Δ ++ Γ)) |- e : REAL) {ϕ} {ψ} (p : w ||~ {{ϕ}} (Lim e) {{ψ}}) {struct p} : 
  let ϕ' := fun x => ϕ (tedious_sem_app _ _ x) in
  let ψ' := fun y x => ψ y (tedious_sem_app _ _ x) in
  {θ  & ((we |~ [{(fun γ' => ϕ' (snd γ'))}] e [{y | θ y}]) *
             (forall γ,
                 ϕ' γ ->
                 exists y : R,
                   ψ' y γ /\
                     (forall x z, θ z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x))%R))}%type.
Proof.
  +
    simple inversion p;
      try (contradict H0; discriminate).
    (* try (induction (eq_sym H)); *)
    (* try (induction (eq_sym H0)); *)
    (* try (induction (eq_sym H1)); *)
    (* try (induction (eq_sym H2)); *)
    (* try (induction (eq_sym H3)).  *)
    {
      use_eq_r H1.
      use_eq_r H2.
      use_eq_r H3.
      repeat apply projT2_eq in H4.
      use_eq_l H4.
      repeat apply projT2_eq in H5.
      injection H5.
      intros.

      pose proof (r_ro_lim_prt_inv _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      apply H1.
      induction H0.
      exact h2.

      intros.
      induction H0.
      apply H1 in H3.
      pose proof (t2 γ H3) as [y [a b]].
      exists y.
      split.
      induction H.
      apply H2.
      exact a.
      exact b.    
    }

    {
      intros.
      use_eq_r H.
      use_eq_r H1.
      use_eq_r H0.    
      repeat apply projT2_eq in H2.
      use_eq_r H2.
      repeat apply projT2_eq in H3.
      injection H3; intros.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_lim_prt_inv _ nil _ _ we _ _ X).    
    }

    {
      intros.
      use_eq_r H0.
      injection H1.
      intro.
      clear H1.
      use_eq_r H0.
      repeat apply projT2_eq in H3.
      use_eq_r H3.
      repeat apply projT2_eq in H4.
      injection H4; intros.
      use_eq_r H0.
      use_eq_r H1.
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      exact H.
    }
  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H7.
      pose proof (r_rw_lim_prt_inv _ _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      apply H6.
      induction H5.
      exact h2.
      intros.
      induction H5.
      apply H6 in H9.
      pose proof (t2 _ H9) as [y [a b]].
      exists y.
      split.
      induction H7.
      apply H8.
      exact a.
      exact b.
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.
      induction H6.
      induction H7.
      pose proof (r_ro_lim_prt_inv _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      rewrite tedious_equiv_3 in h2.
      exact h2.
      intros.
      pose proof (t2 _ H3) as [y [a b]].
      exists y.
      split; auto.
      intros.
      apply b.
      rewrite tedious_equiv_3.
      exact H6.
    }      
Defined.



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
    
    apply magic.

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
    apply magic.
    
  +
    apply magic.

    
  +
    apply magic.
Qed.

