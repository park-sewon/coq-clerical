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

Open Scope detail_scope.

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

Lemma r_proves_ro_prt_ctx_rewrite : forall {Γ1 Γ2} {e} {τ} (eq : Γ1 = Γ2) {w : Γ1 |- e : τ} {ϕ} {ψ},
    w |~ {{ϕ}} e {{ψ}} -> (tr (fun Γ => Γ |- e : τ)  eq w) |~ {{fun x => ϕ (tr sem_ro_ctx (eq_sym eq) x)}} e {{fun y x => ψ y (tr sem_ro_ctx (eq_sym eq) x)}}.
Proof.
  intros.
  destruct eq.
  simpl.
  exact X.
Defined.

Lemma r_proves_ro_tot_ctx_rewrite : forall {Γ1 Γ2} {e} {τ} (eq : Γ1 = Γ2) {w : Γ1 |- e : τ} {ϕ} {ψ},
    w |~ [{ϕ}] e [{ψ}] -> (tr (fun Γ => Γ |- e : τ)  eq w) |~ [{fun x => ϕ (tr sem_ro_ctx (eq_sym eq) x)}] e [{fun y x => ψ y (tr sem_ro_ctx (eq_sym eq) x)}].
Proof.
  intros.
  destruct eq.
  simpl.
  exact X.
Defined.

Lemma r_proves_rw_prt_ctx_rewrite_ro : forall {Γ1 Γ2 Δ} {e} {τ} (eq : Γ1 = Γ2) {w : Γ1 ;;; Δ ||- e : τ} {ϕ} {ψ},
    w ||~ {{ϕ}} e {{ψ}} -> (tr (fun Γ => Γ ;;; Δ ||- e : τ)  eq w) ||~ {{fun x => ϕ (fst x, tr sem_ro_ctx (eq_sym eq) (snd x))}} e {{fun y x => ψ y (fst x, tr sem_ro_ctx (eq_sym eq) (snd x))}}.
Proof. intros. destruct eq. simpl. replace (fun x : sem_ro_ctx Δ * sem_ro_ctx Γ1 => ϕ (fst x, snd x)) with ϕ. replace (fun y x => ψ y (fst x, snd x)) with ψ. exact X.
       apply dfun_ext. intro x. apply dfun_ext. intro y.
       destruct y; auto.
       apply dfun_ext. intro x.
       destruct x; auto.
Defined.

Lemma r_proves_rw_tot_ctx_rewrite_ro : forall {Γ1 Γ2 Δ} {e} {τ} (eq : Γ1 = Γ2) {w : Γ1 ;;; Δ ||- e : τ} {ϕ} {ψ},
    w ||~ [{ϕ}] e [{ψ}] -> (tr (fun Γ => Γ ;;; Δ ||- e : τ)  eq w) ||~ [{fun x => ϕ (fst x, tr sem_ro_ctx (eq_sym eq) (snd x))}] e [{fun y x => ψ y (fst x, tr sem_ro_ctx (eq_sym eq) (snd x))}].
Proof. intros. destruct eq. simpl. replace (fun x : sem_ro_ctx Δ * sem_ro_ctx Γ1 => ϕ (fst x, snd x)) with ϕ. replace (fun y x => ψ y (fst x, snd x)) with ψ. exact X.
       apply dfun_ext. intro x. apply dfun_ext. intro y.
       destruct y; auto.
       apply dfun_ext. intro x.
       destruct x; auto.
Defined.


Axiom magic : forall T, T.


Lemma r_admissible_ro_prt_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |~ {{ϕ}} e {{ψ}}) :
  ψ ->>> θ -> w |~ {{ϕ}} e {{θ}}.
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (r_ro_imply_prt _ _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma r_admissible_ro_prt_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |~ {{ϕ}} e {{ψ}}) :
  θ ->> ϕ -> w |~ {{θ}} e {{ψ}}.
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (r_ro_imply_prt _ _ _ _ _ _ _ _ _ H X H0).
Defined.

Lemma r_admissible_ro_tot_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |~ [{ϕ}] e [{ψ}]) :
  ψ ->>> θ -> w |~ [{ϕ}] e [{θ}].
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (r_ro_imply_tot _ _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma r_admissible_ro_tot_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |~ [{ϕ}] e [{ψ}]) :
  θ ->> ϕ -> w |~ [{θ}] e [{ψ}].
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (r_ro_imply_tot _ _ _ _ _ _ _ _ _ H X H0).
Defined.

Fixpoint r_admissible_ro_prt_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |~ {{ϕ}} e {{ψ}}) {struct X} :
  w |~ {{ϕ /\\ θ}} e {{ψ /\\\ fun _ => θ}}
with r_admissible_ro_tot_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |~ [{ϕ}] e [{ψ}]) {struct X} :
  w |~ [{ϕ /\\ θ}] e [{ψ /\\\ fun _ => θ}]
with r_admissible_rw_prt_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||~ {{ϕ}} e {{ψ}}) {struct X} :
  w ||~ {{ϕ /\\ fun δγ => θ (snd δγ) }} e {{ψ /\\\ fun _ δγ => θ (snd δγ)}}
with r_admissible_rw_tot_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||~ [{ϕ}] e [{ψ}]) {struct X} :
  w ||~ [{ϕ /\\ fun δγ => θ (snd δγ)}] e [{ψ /\\\ fun _ δγ => θ (snd δγ)}].
Proof.
  +
    dependent induction X.
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    assert ((ϕ /\\ θ) ->> (P /\\ θ)).
    intros γ p; split; destruct p.
    apply a; exact H.
    exact H0.
    assert ((Q /\\\ fun _ => θ) ->>> (ψ /\\\ fun _ => θ)).
    intros y γ p; split; destruct p.
    apply a0; exact H0.
    exact H1.
    apply (r_ro_imply_prt _ _ _ _ _ _ _ _ _ H X0 H0).

    pose proof (r_ro_var_prt _ _ _ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    apply (r_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (r_ro_skip_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (r_ro_true_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (r_ro_false_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (r_ro_int_prt _ _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ r).
    pose proof (r_rw_ro_prt _ _ _ _ _ _ w' X).
    simpl in X0.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros a b.
    destruct b; split; auto.
    intros h1 h2 h3.
    split; destruct h3; auto.

    pose proof (r_admissible_ro_prt_pose_readonly Γ (e) INTEGER w ϕ (fun y x => ψ (IZR y) x) (fun x => (θ (x))) X).
    apply (r_ro_coerce_prt _ _ w).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    exact h2.
    intros h1 h2 h3.
    destruct h3.
    split; auto.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (r_ro_exp_prt _ _ w _ _ w').
    apply (r_admissible_ro_prt_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (r_ro_recip_prt _ _ w _ _ w' _ X0).    
    intros h1 h2 h3.
    destruct h3.
    split.
    apply a.
    split.
    destruct H; auto.
    auto.
    destruct H; auto.
    
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.
    auto.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x : sem_ro_ctx (INTEGER :: Γ) => θ (snd x)) r).
    apply (r_ro_lim_prt _ _ _ _ _ _ _ X).
    intros.
    destruct H.
    pose proof (e0 _ H).
    destruct H1.
    exists x.
    split.
    split; auto.
    destruct H1; auto.
    intros.
    destruct H2.
    destruct H1.
    pose proof (H4 x0 z H2).
    exact H5.

  +
    dependent induction X.
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    assert ((ϕ /\\ θ) ->> (P /\\ θ)).
    intros γ p; split; destruct p.
    apply a; exact H.
    exact H0.
    assert ((Q /\\\ fun _ => θ) ->>> (ψ /\\\ fun _ => θ)).
    intros y γ p; split; destruct p.
    apply a0; exact H0.
    exact H1.
    apply (r_ro_imply_tot _ _ _ _ _ _ _ _ _ H X0 H0).

    pose proof (r_ro_var_tot _ _ _ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    apply (r_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (r_ro_skip_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (r_ro_true_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (r_ro_false_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (r_ro_int_tot _ _  w (ψ /\\\ (fun _ => θ))).
    apply (r_admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ r).
    pose proof (r_rw_ro_tot _ _ _ _ _ _ w' X).
    simpl in X0.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros a b.
    destruct b; split; auto.
    intros h1 h2 h3.
    split; destruct h3; auto.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (r_ro_coerce_tot _ _ w _ _ w').
    apply (r_admissible_ro_tot_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (r_ro_exp_tot _ _ w _ _ w').
    apply (r_admissible_ro_tot_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_op_plus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_op_mult_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_op_minus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_op_plus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_op_mult_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_op_minus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (r_ro_recip_tot _ _ w _ _ w' _ X0).    
    intros h1 h2 h3.
    destruct h3.
    destruct (a _ _ H).
    
    split; auto.
    split; auto.
    
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_comp_eq_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_int_comp_lt_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (r_ro_real_lt_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    destruct (a _ _ _ H H0).
    split; auto.
    split; auto.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x : sem_ro_ctx (INTEGER :: Γ) => θ (snd x)) X).
    apply (r_ro_lim_tot _ _ _ _ _ _ _ X0).
    intros.
    destruct H.
    pose proof (e0 _ H).
    destruct H1.
    exists x.
    split.
    split; auto.
    destruct H1; auto.
    intros.
    destruct H2.
    destruct H1.
    pose proof (H4 x0 z H2).
    exact H5.

    
  +
    dependent induction X.
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; auto.
    split; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app δγ)) r).
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ w' X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2.
    split; auto.
    destruct h1.
    simpl in H0.
    unfold snd_app; rewrite tedious_equiv_1; auto.
    intros h1 h2 h3.
    destruct h2, h3.
    split; auto.
    simpl.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ w' X X0).

    clear IHX.
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (snd_app ( δγγ'))) r).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (r_rw_new_var_prt Γ Δ e c τ σ w1 w2 (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) (ψ /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx Δ * sem_ro_ctx Γ) => θ (snd δγ))) (θ0 /\\\ (fun (_ : sem_datatype σ) (δγγ' : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγγ'))) w').
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    apply (r_rw_assign_prt _ _ _ _ _ w _ (θ0 /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) _ w').
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    intros.
    destruct H; split; auto.
    simpl; unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.

    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (r_rw_cond_prt _ _ _ _ _ _ w w1 w2 w' _ (θ0 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.

    clear IHX1 IHX2.
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r0).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (r_rw_case_prt _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X4).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.

    apply (r_rw_case_list_prt _ _ _ _ wty_l wty (ForallT_map (fun _ p => p /\\\ (fun _ x => θ (snd_app x))) θ0)).
    clear wty.
    dependent induction f.
    apply ForallT2_nil.
    simpl.
    apply ForallT2_cons.
    apply IHf.
    destruct p.
    simpl.
    destruct r.
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ r0).
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X).    
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; destruct h3; split; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).    
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    auto.
    intros h1 h2 h3; auto.
    assert
      (wty ||~ {{(ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ)))}} (WHILE e DO c END) {{y
                                                                                                    | ((fun _ : unit => (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) /\\
                                                                                                                                                                                     ro_to_rw_pre
                                                                                                                                                                                     ((θ0 /\\\ (fun _ δγ => θ (snd_app δγ))) false))) y}}).
    apply (r_rw_while_prt _ _ _ _ wty_e wty_c wty).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; auto.
    split; auto.
    pose proof (r_admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0.
    destruct h1; rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3.
    auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.

  +
    dependent induction X.
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; auto.
    split; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app δγ)) r).
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ w' X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2.
    split; auto.
    destruct h1.
    simpl in H0.
    unfold snd_app; rewrite tedious_equiv_1; auto.
    intros h1 h2 h3.
    destruct h2, h3.
    split; auto.
    simpl.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ w' X X0).

    clear IHX.
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (snd_app ( δγγ'))) r).
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (r_rw_new_var_tot Γ Δ e c τ σ w1 w2 (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) (ψ /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx Δ * sem_ro_ctx Γ) => θ (snd δγ))) (θ0 /\\\ (fun (_ : sem_datatype σ) (δγγ' : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγγ'))) w').
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    apply (r_rw_assign_tot _ _ _ _ _ w _ (θ0 /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) _ w').
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    intros.
    destruct H; split; auto.
    simpl; unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.

    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (r_rw_cond_tot _ _ _ _ _ _ w w1 w2 w' _ (θ0 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.

    clear IHX1 IHX2.
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r0).
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r1).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r2).

    apply (r_rw_case_tot _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ)))
                       _
                       (ϕ1 /\\ (fun δγ : sem_ro_ctx (Δ ++ Γ) => θ (snd_app δγ)))      
                       (ϕ2 /\\ (fun δγ : sem_ro_ctx (Δ ++ Γ) => θ (snd_app δγ)))
          ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X4).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X5).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    destruct h3.
    auto.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X6).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    destruct h3.
    auto.
    intros.
    destruct H.
    destruct (o _ H). 
    left; split; auto.
    right; split; auto.

    
    apply (r_rw_case_list_tot _ _ _ _ wty_l wty
                            (ForallT_map (fun _ p => p /\\\ (fun _ x => θ (snd_app x))) θ0)
                            (ForallT_map (fun _ p => p /\\ (fun x => θ (snd_app x))) ϕi)
          ).
    clear wty.
    clear f0.
    dependent induction f.
    apply ForallT3_nil.
    simpl.
    apply ForallT3_cons.
    simpl.
    apply IHf.
    repeat split.
    destruct j as [[j _] _].
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) j) as i.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct j as [[_ j] _].
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _  θ j) as i.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    destruct h2; split; auto.
    destruct h1; unfold snd_app in H0;  auto.
    rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.
    destruct j as [_ j].
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) j) as i.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct h3; auto.
    intros.
    destruct H.
    pose proof (f0 x H).
    clear f f0 wty wty_l θ0.

    induction ϕi.
    simpl in H1; simpl; auto.
    simpl.
    simpl in H1.
    destruct H1.
    left; split; auto.
    right.
    apply IHϕi.
    exact H1.

    assert
      (wty ||~ [{(ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ)))}] (WHILE e DO c END) [{y
                                                                                                    | ((fun _ : unit => (ϕ /\\ (fun δγ : sem_ro_ctx Δ * sem_ro_ctx Γ => θ (snd δγ))) /\\
                                                                                                                                                                                     ro_to_rw_pre
                                                                                                                                                                                     ((θ0 /\\\ (fun _ δγ => θ (snd_app δγ))) false))) y}]).
    apply (r_rw_while_tot _ _ _ _ wty_e wty_c wty _ _ ψ0).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; auto.
    split; auto.
    pose proof (r_admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ (fun x => θ ((fst_app x))) X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    destruct H; split; auto.
    destruct H.
    unfold snd_app in H1.
    rewrite tedious_equiv_1 in H1.
    exact H1.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split; auto.
    split; auto.
    intros.
    destruct H.
    apply n; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.
Defined.

Fixpoint r_admissible_rw_tot_pose_readonly_ext Γ Δ Ω e τ (w : Γ ;;; (Δ ++ Ω) ||- e : τ) (w' : (Ω ++ Γ) ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||~ [{ϕ}] e [{ψ}]) {struct X} :
  w ||~ [{fun x => ϕ x /\ θ (snd_app (fst x), snd x)}] e [{fun y x => ψ y x /\ θ (snd_app (fst x), snd x)}].
Proof.
  dependent induction X.
  {
    apply (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w' _ _ θ) in X.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; split; auto.
    intro.
    destruct H; split; auto.
  }

  {
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ w0 _ _
                  (fun x => θ (snd_app (fst_app x), snd_app x))
                  r).
    apply (r_ro_rw_tot _ _ _ _ _ _ _ w) in X.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2; split; auto.
    unfold snd_app, fst_app; rewrite tedious_equiv_0.
    destruct h1; simpl.
    simpl in H0.
    exact H0.
    destruct h2.
    simpl.
    intro.
    destruct H.
    rewrite tedious_equiv_fst in H0.
    rewrite tedious_equiv_snd in H0.
    auto.
  }

  {
    pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w') as [w1' w2'].
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w1' _ _ θ X1).
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w2' _ _ θ X2).
    apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ w X X0).
  }
  {    
    (* clear IHX. *)
    pose proof (has_type_rw_Newvar_inverse w') as [σ' [w1' w2']].
    
    assert (σ = σ').
    rewrite app_assoc in w1'.
    apply (has_type_ro_unambiguous _ _ _ _  w1 w1'). 
    induction H.
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x => θ (snd_app (fst_app x), snd_app x)) r).
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w2' _ _ θ X).
    simpl in X0, X1.
    apply (r_rw_new_var_tot _ _ e c τ σ w1 w2 _ _
             (fun y => (θ0 /\\\ (fun (_ : sem_datatype σ) (x : sem_ro_ctx ((Δ ++ Ω) ++ Γ)) => θ (snd_app (fst_app x), snd_app x))) y)
             w).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    rewrite tedious_equiv_fst in H0.
    destruct h1.
    simpl; simpl in H0.
    destruct s.
    simpl; simpl in H0.
    unfold snd_app.
    simpl.
    destruct (tedious_sem_app Δ Ω s1).
    exact H0.
    intros h2 h3 h4; auto.
    split; destruct h4; auto.
    destruct h3.
    destruct s.
    simpl; simpl in H0.
    unfold snd_app.
    unfold snd_app in H0.
    simpl in H0.
    destruct (tedious_sem_app Δ Ω s1).
    exact H0.
  }
  
  {
    pose proof (has_type_rw_Assign_inverse  w') as [σ [a' w0']].
    assert (τ = σ).
    rewrite app_assoc in w0'.
    apply (has_type_ro_unambiguous _ _ _ _  w0 w0'). 
    induction H.
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x => θ (snd_app (fst_app x), snd_app x)) r).
    apply (r_rw_assign_tot _ _ _ _ _ _ _
             _
          _ _ X).
    intros.
    destruct H.
    split.
    apply ψ0.
    exact H.
    unfold update'.
    simpl.
    Search update.
    rewrite (tedious_equiv_2 δ).
    rewrite <- (assign_concat_fst _ _ _ _ a' _ x
      ).
    rewrite tedious_equiv_snd.
    rewrite tedious_equiv_snd in H0.
    rewrite tedious_equiv_fst in H0.
    exact H0.
  }
  {
    pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w') as [[w0' w1'] w2'].
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x => θ (snd_app (fst_app x), snd_app x)) r).
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w1' _ _  θ X1).
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w2' _ _  θ X2).
    apply (r_rw_cond_tot _ _ _ _ _ _ w0 w1 w2 w _ _ _ X). 
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    rewrite tedious_equiv_fst in H0.
    split; auto.    
    intros h1 h2 h3; auto.

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    rewrite tedious_equiv_fst in H0.
    split; auto.
    intros h1 h2 h3; auto.
  }
  
  {  
    apply magic.
  }
  
    (* pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ w') as [[w0' w1'] w2']. *)

    (* pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r). *)
    (* pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ _ θ X1). *)
    (* pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r0). *)
    (* pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ _ θ X2). *)
    (* pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r1). *)
    (* pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) r2). *)

    (* apply (r_rw_case_tot _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ro_ctx (Δ ++ Γ)) => θ (snd_app δγ))) *)
    (*                    _ *)
    (*                    (ϕ1 /\\ (fun δγ : sem_ro_ctx (Δ ++ Γ) => θ (snd_app δγ)))       *)
    (*                    (ϕ2 /\\ (fun δγ : sem_ro_ctx (Δ ++ Γ) => θ (snd_app δγ))) *)
    (*       ). *)
    (* apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X). *)
    (* intros h1 h2. *)
    (* split; destruct h2. *)
    (* exact H. *)
    (* exact H0. *)
    (* intros h1 h2 h3; auto. *)
    (* apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X3). *)
    (* intros h1 h2. *)
    (* split; destruct h2. *)
    (* exact H. *)
    (* exact H0. *)
    (* intros h1 h2 h3; auto. *)
    (* apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0). *)
    (* intros h1 h2. *)
    (* split; destruct h2. *)
    (* exact H. *)
    (* unfold snd_app in H0. *)
    (* destruct h1. *)
    (* rewrite tedious_equiv_1 in H0. *)
    (* exact H0. *)
    (* intros h1 h2 h3; auto. *)
    (* apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X4). *)
    (* intros h1 h2. *)
    (* split; destruct h2. *)
    (* exact H. *)
    (* unfold snd_app in H0. *)
    (* destruct h1. *)
    (* rewrite tedious_equiv_1 in H0. *)
    (* exact H0. *)
    (* intros h1 h2 h3; auto. *)
    (* apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X5). *)
    (* intros h1 h2. *)
    (* split; destruct h2. *)
    (* exact H. *)
    (* exact H0. *)
    (* intros h1 h2 h3; auto. *)
    (* destruct h3. *)
    (* auto. *)
    (* apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X6). *)
    (* intros h1 h2. *)
    (* split; destruct h2. *)
    (* exact H. *)
    (* exact H0. *)
    (* intros h1 h2 h3; auto. *)
    (* destruct h3. *)
    (* auto. *)
    (* intros. *)
    (* destruct H. *)
    (* destruct (o _ H).  *)
    (* left; split; auto. *)
    (* right; split; auto. *)

  {
    pose proof (has_type_rw_CaseList_inverse _ _ _ _ w') as wty_l'.
    apply (r_rw_case_list_tot _ _ _ _ wty_l w
                            (ForallT_map (fun _ p => p /\\\ (fun _ x => θ (snd_app (fst_app x), snd_app x))) θ0)
                            (ForallT_map (fun _ p => p /\\ (fun x => θ (snd_app (fst_app x), snd_app x))) ϕi)
          ).
    clear w w' f0.

    dependent induction f.
    apply ForallT3_nil.
    simpl.
    apply ForallT3_cons.
    simpl.
    dependent destruction wty_l'.
    apply IHf.
    apply wty_l'.
    repeat split.
    destruct j as [[j _] _].
    pose proof (r_admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun x => θ (snd_app (fst_app x), snd_app x)) j) as i.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct j as [[_ j] _].
    dependent destruction wty_l'.
    destruct p0 as [w1' w2'].
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ w2' _ _ θ j) as i.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    destruct h2; split; auto.
    destruct h1; unfold snd_app in H0;  auto.
    rewrite tedious_equiv_1 in H0; auto.
    rewrite tedious_equiv_fst in H0.
    simpl.
    exact H0.
    intros h1 h2 h3; auto.
    destruct j as [_ j].
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x => θ (snd_app (fst_app x), snd_app x)) j) as i.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct h3; auto.

    intros.
    destruct H.
    pose proof (f0 x H).
    clear f f0 w wty_l wty_l' w' θ0.

    induction ϕi.
    simpl in H1; simpl; auto.
    simpl.
    simpl in H1.
    destruct H1.
    left; split; auto.
    right.
    apply IHϕi.
    exact H1.
  }

  {
    assert
      (w ||~ [{(ϕ /\\ (fun x => θ (snd_app (fst x), snd x)))}]
         (WHILE e DO c END)
         [{y | ((fun _ : unit => (ϕ /\\ (fun x => θ (snd_app (fst x), snd x))) /\\
                                   ro_to_rw_pre
                                   ((θ0 /\\\ (fun _ x => θ (snd_app (fst_app x), snd_app x))) false))) y}]).
    apply (r_rw_while_tot _ _ _ _ wty_e wty_c w _ _ ψ0).
    pose proof (r_admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x => θ (snd_app (fst_app x), snd_app x)) r).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; auto.
    split; auto.

    pose proof (has_type_rw_While_inverse w') as [we' wc'].
    pose proof (has_type_rw_add_auxiliary _ _ _ _ wc' (Δ ++ Ω)) as wc''.
    rewrite <- app_assoc in wc''.
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ wc'' _ _ (fun x => θ (fst x, fst_app (snd x)))
                  X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    destruct H; split; auto.
    destruct H.
    simpl.
    rewrite tedious_equiv_fst in H1.
    rewrite tedious_equiv_snd in H1.
    exact H1.
    intros h1 h2 h3.
    destruct h3.
    destruct H.
    split; auto.
    split; auto.
    intros.
    destruct H.
    apply n; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.
  }
Defined.


Lemma eq_sym_twice : forall A (a b : A) (e : a = b), eq_sym (eq_sym e) = e.
Proof.
  intros.
  destruct e.
  simpl.
  reflexivity.
Defined.

Lemma r_has_type_ro_rw : forall Γ c τ, Γ ;;; nil ||~ c : τ -> Γ |~ c : τ.
Proof.
  intros.
  apply r_has_type_rw_has_type_rw in H.
  apply has_type_ro_r_has_type_ro.
  apply has_type_ro_rw.
  exact H.
Defined.

Lemma r_has_type_rw_ro : forall Γ Δ c τ, (Δ ++ Γ) |~ c : τ -> Γ ;;; Δ ||~ c : τ.
Proof.
  intros.
  apply r_has_type_ro_has_type_ro in H.
  apply has_type_rw_r_has_type_rw.
  apply has_type_rw_ro.
  exact H.
Defined.

Fixpoint r_has_type_rw_move_ro Γ1 Γ2 Δ1 Δ2 e τ
  (w : Γ1 ;;; (Δ1 ++ Δ2) ||~ e : τ)
  (w' : (Δ2 ++ Γ1 ++ Γ2) ;;; Δ1 ||~ e : τ) :
  (Δ2 ++ Γ1) ;;; Δ1 ||~ e : τ.
Proof.
  dependent destruction w; 
    try
      (rewrite <- app_assoc in r;
       apply (r_has_type_rw_ro) in r;
       exact r).
  
  dependent destruction w'.
  pose proof (r_has_type_rw_move_ro _ _ _ _ _ _ w1 w'1).
  pose proof (r_has_type_rw_move_ro _ _ _ _ _ _ w2 w'2).
  apply r_has_type_rw_Seq.
  exact H.
  exact H0.

  dependent destruction w'.
  assert (τ = τ0).
  pose proof (r_has_type_ro_add_auxiliary _ _ _ r Γ2).
  rewrite <- app_assoc in H.
  rewrite <- app_assoc in H.
  apply (r_has_type_ro_unambiguous _ _ _ _ H r0).
  induction H.
  apply (r_has_type_rw_Assign _ _ _ τ ).
  exact a0.
  rewrite <- app_assoc in r.
  exact r.

  dependent destruction w'.
  assert (σ = σ0).
  pose proof (r_has_type_ro_add_auxiliary _ _ _ r Γ2).
  rewrite <- app_assoc in H.
  rewrite <- app_assoc in H.
  apply (r_has_type_ro_unambiguous _ _ _ _ H r0).
  induction H.
  apply (r_has_type_rw_Newvar _ _ _ _ σ).
  rewrite <- app_assoc in r.
  exact r.
  rewrite (app_comm_cons) in w.
  exact (r_has_type_rw_move_ro _ _ _ _ _ _ w w').

  dependent destruction w'.
  apply r_has_type_rw_Cond.
  rewrite <- app_assoc in r.
  exact r.
  exact (r_has_type_rw_move_ro _ _ _ _ _ _ w1 w'1).
  exact (r_has_type_rw_move_ro _ _ _ _ _ _ w2 w'2).

  apply magic.

  dependent destruction w'.
  apply r_has_type_rw_CaseList.
  exact l2.
  clear l0 l2.
  dependent induction f.
  apply ForallT_nil.
  apply ForallT_cons.
  dependent destruction f0.
  destruct p, p0.
  split.
  rewrite <- app_assoc in r.
  exact r.
  exact (r_has_type_rw_move_ro _ _ _ _ _ _ r0 r2).
  apply IHf.
  dependent destruction f0.
  exact f0.

  dependent destruction w'.
  apply r_has_type_rw_While.
  rewrite <- app_assoc in r.
  exact r.
  exact (r_has_type_rw_move_ro _ _ _ _ _ _ w w').
Defined.
  
  
Lemma has_type_rw_to_ro_res Γ Δ Δ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Δ ++ Γ ++ Δ') |- e : τ) : (Δ ++ Γ) |- e : τ.
Proof.
  apply r_has_type_ro_has_type_ro.
  apply has_type_ro_r_has_type_ro in w'.
  apply has_type_rw_r_has_type_rw in w.
  apply (r_has_type_rw_ro  _ nil) in w'.
  apply (r_has_type_ro_rw).
  apply (r_has_type_rw_move_ro _ _ nil _ _ _ w w').
Defined.

Lemma r_rw_new_var_prt_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ}
  {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}:
  w1 |~ {{ϕ'}} e {{θ}} ->
  w2 ||~ {{θ'}} c {{ψ'}} ->
  ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
  ((fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') ->
  (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) ->
  w ||~ {{ϕ}} Newvar e c {{ψ}}.
Proof.
  intros.
  pose proof (r_ro_imply_prt _ _ _ w1 w1 _ _ _ _
                H X (fun x h p => p)
    ).
  pose proof (r_rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                H0 X0 H1
    ).
  pose proof (r_rw_new_var_prt).
  apply (r_rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ X1 X2).
Defined.

Lemma r_rw_new_var_tot_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ}
  {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}:
  w1 |~ [{ϕ'}] e [{θ}] ->
  w2 ||~ [{θ'}] c [{ψ'}] ->
  ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
  ((fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') ->
  (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) ->
  w ||~ [{ϕ}] Newvar e c [{ψ}].
Proof.
  intros.
  pose proof (r_ro_imply_tot _ _ _ w1 w1 _ _ _ _
                H X (fun x h p => p)
    ).
  pose proof (r_rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                H0 X0 H1
    ).
  pose proof (r_rw_new_var_tot).
  apply (r_rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ _ X1 X2).
Defined.

Lemma r_rw_assign_prt_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
  {ϕ} {ϕ'} {ψ : post} {θ} :
  w |~ {{ϕ'}} e {{θ}} ->
  ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
  (forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
  w' ||~ {{ϕ}} Assign k e {{ψ}}.
Proof.
  intros.
  pose proof (r_ro_imply_prt _ _ _ w w _ _ _ _
                H X (fun x h p => p)
    ).
  apply (r_rw_assign_prt _ _ _ _ _ _ _ _ _ _ X0 H0).
Defined.

Lemma r_rw_assign_tot_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
  {ϕ} {ϕ'} {ψ : post} {θ} :
  w |~ [{ϕ'}] e [{θ}] ->
  ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
  (forall (x : sem_datatype τ) (γ : sem_ro_ctx Γ) (δ : sem_ro_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
  w' ||~ [{ϕ}] Assign k e [{ψ}].
Proof.
  intros.
  pose proof (r_ro_imply_tot _ _ _ w w _ _ _ _
                H X (fun x h p => p)
    ).
  apply (r_rw_assign_tot _ _ _ _ _ _ _ _ _ _ X0 H0).
Defined.

Lemma r_rw_cond_prt_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
  {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
  w |~ {{ϕ'}} e {{θ}} ->
  w1 ||~ {{θ1'}} c1 {{ψ1'}} ->
  w2 ||~ {{θ2'}} c2 {{ψ2'}} ->
  ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
  (ro_to_rw_pre (θ true) ->> θ1') -> 
  (ψ1' ->>> ψ) ->
  (ro_to_rw_pre (θ false) ->> θ2') -> 
  (ψ2' ->>> ψ) ->
  w' ||~ {{ϕ}} Cond e c1 c2 {{ψ}}.
Proof.
  intros.
  pose proof (r_ro_imply_prt _ _ _ w w _ _ _ _
                H X (fun x h p => p)
    ).
  pose proof (r_rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                H0 X0 H1
    ).
  pose proof (r_rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                H2 X1 H3
    ).

  apply (r_rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
Defined.

Lemma r_rw_cond_tot_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
  {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
  w |~ [{ϕ'}] e [{θ}] ->
  w1 ||~ [{θ1'}] c1 [{ψ1'}] ->
  w2 ||~ [{θ2'}] c2 [{ψ2'}] ->
  ((fun γδ : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
  (ro_to_rw_pre (θ true) ->> θ1') -> 
  (ψ1' ->>> ψ) ->
  (ro_to_rw_pre (θ false) ->> θ2') -> 
  (ψ2' ->>> ψ) ->
  w' ||~ [{ϕ}] Cond e c1 c2 [{ψ}].
Proof.
  intros.
  pose proof (r_ro_imply_tot _ _ _ w w _ _ _ _
                H X (fun x h p => p)
    ).
  pose proof (r_rw_imply_tot _ _ _ _ w1 w1 _ _ _ _
                H0 X0 H1
    ).
  pose proof (r_rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                H2 X1 H3
    ).

  apply (r_rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
Defined.

Lemma r_rw_while_prt_util {Γ Δ} {e c}  {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c : UNIT} 
  {w' : Γ ;;; Δ ||- While e c : UNIT} {ϕ} {ϕ'} {θ} {θ'} {ψ'}  {ψ : post} :
  w |~ {{ϕ'}} e {{θ}} ->
  w1 ||~ {{θ'}} c {{ψ'}} ->
  ((rw_to_ro_pre ϕ) ->> ϕ') ->
  (ro_to_rw_pre (θ true) ->> θ') -> 
  (ψ' ->>> (fun _ => ϕ)) -> 
  ((fun _ => ϕ /\\ ro_to_rw_pre (θ false)) ->>> ψ) ->
  w' ||~ {{ϕ}} While e c {{ψ}}.
Proof.
  intros.
  pose proof (r_ro_imply_prt _ _ _ w w _ _ _ _
                H X (fun x h p => p)
    ).
  pose proof (r_rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                H0 X0 H1
    ).
  pose proof (r_rw_while_prt _ _ _ _ _ _ w' _ _ X1 X2).
  exact (r_rw_imply_prt _ _ _ _ w' w' _ _ _ _
                (fun _ p => p) X3 H2
    ).
Defined.


Structure ctx_perm Γ Δ := {
    permuting : sem_ro_ctx Γ -> sem_ro_ctx Δ ;
    unpermuting : sem_ro_ctx Δ -> sem_ro_ctx Γ ;
    permuting_eq : forall x, unpermuting (permuting x) = x    
  }.
Arguments permuting {_} {_}.
Arguments unpermuting {_} {_}.
Arguments permuting_eq {_} {_}.
       
Definition ctx_perm_app_const_r_permuting {Γ Δ} (π : ctx_perm Γ Δ) Γ' : sem_ro_ctx (Γ ++ Γ') -> sem_ro_ctx (Δ ++ Γ')
  := (fun x => (permuting  π (fst_app x); snd_app x)).
Definition ctx_perm_app_const_r_unpermuting {Γ Δ} (π : ctx_perm Γ Δ) Γ' : sem_ro_ctx (Δ ++ Γ') ->  sem_ro_ctx (Γ ++ Γ')
  := (fun x => (unpermuting  π (fst_app x); snd_app x)).
Definition ctx_perm_app_const_r_permuting_eq {Γ Δ} (π : ctx_perm Γ Δ) Γ' :
  forall x, ctx_perm_app_const_r_unpermuting π Γ' (ctx_perm_app_const_r_permuting  π Γ' x) = x.  
Proof. intros. rewrite (tedious_equiv_2 x).
       unfold ctx_perm_app_const_r_permuting, ctx_perm_app_const_r_unpermuting.
       repeat (rewrite tedious_equiv_fst;
               rewrite tedious_equiv_snd).
       rewrite (permuting_eq π).
       reflexivity.
Defined.
Definition ctx_perm_app_const_r {Γ Δ} (π : ctx_perm Γ Δ) Γ' : ctx_perm (Γ ++ Γ') (Δ ++ Γ') :=
  {|
    permuting := ctx_perm_app_const_r_permuting π Γ' ;
    unpermuting := ctx_perm_app_const_r_unpermuting π Γ' ;
    permuting_eq := ctx_perm_app_const_r_permuting_eq π Γ' |}.

Definition ctx_perm_swap_permuting Γ Δ  : sem_ro_ctx (Γ ++ Δ) -> sem_ro_ctx (Δ ++ Γ)
  := (fun x => (snd_app x; fst_app x)).
Definition ctx_perm_swap_unpermuting Γ Δ : sem_ro_ctx (Δ ++ Γ) ->  sem_ro_ctx (Γ ++ Δ)
  := (fun x => (snd_app x; fst_app x)).
Definition ctx_perm_swap_permuting_eq Γ Δ :
  forall x, ctx_perm_swap_unpermuting Γ Δ (ctx_perm_swap_permuting Γ Δ x) = x.  
Proof. intros. rewrite (tedious_equiv_2 x).
       unfold ctx_perm_swap_permuting, ctx_perm_swap_unpermuting.
       repeat (rewrite tedious_equiv_fst;
               rewrite tedious_equiv_snd).
       reflexivity.
Defined.
Definition ctx_perm_swap Γ Δ : ctx_perm (Γ ++ Δ) (Δ ++ Γ) :=
  {|
    permuting := ctx_perm_swap_permuting Γ Δ ;
    unpermuting := ctx_perm_swap_unpermuting Γ Δ ;
    permuting_eq := ctx_perm_swap_permuting_eq Γ Δ |}.

Definition ctx_perm_translate {Γ Δ} (π : ctx_perm Γ Δ) (ϕ : sem_ro_ctx Γ -> Prop) : sem_ro_ctx Δ -> Prop.
Proof.
  intro x.
  exact (ϕ (unpermuting π x)). 
Defined.

Fixpoint r_admissible_permutate_auxiliary_ro_prt Γ Γ1 Γ2  e τ ϕ ψ
         (π : ctx_perm Γ1 Γ2)
         (w  : Γ |- e : τ)
         (w1 : (Γ ++ Γ1) |- e : τ)
         (w2 : (Γ ++ Γ2) |- e : τ)
         (p : w1 |~ {{ϕ}} e {{ψ}}) {struct p} :
  w2 |~ {{fun x => ϕ (fst_app x; unpermuting π (snd_app x))}} e {{y | fun x => ψ y (fst_app x; unpermuting π (snd_app x))}}
with r_admissible_permutate_auxiliary_ro_tot Γ Γ1 Γ2 e τ ϕ ψ
                                             (π : ctx_perm Γ1 Γ2)
         (w  : Γ |- e : τ)
         (w1 : (Γ ++ Γ1) |- e : τ)
         (w2 : (Γ ++ Γ2) |- e : τ)
         (p : w1 |~ [{ϕ}] e [{ψ}]) {struct p} :
  w2 |~ [{fun x => ϕ (fst_app x; unpermuting π (snd_app x))}] e [{y | fun x => ψ y (fst_app x; unpermuting π (snd_app x))}]
with r_admissible_permutate_auxiliary_rw_prt Γ Δ Γ1 Γ2 e τ ϕ ψ
  (π : ctx_perm Γ1 Γ2)
  (w   : Γ ;;; Δ ||- e : τ)
  (w1  : (Γ ++ Γ1) ;;; Δ ||- e : τ)
  (w2  : (Γ ++ Γ2) ;;; Δ  ||- e : τ)
  (p   : w1 ||~ {{ϕ}} e {{ψ}}) {struct p} :
  w2 ||~
    {{fun x => ϕ (fst x, (fst_app (snd x); unpermuting π (snd_app (snd x))))}}
    e
    {{fun y x => ψ y (fst x, (fst_app (snd x); unpermuting π (snd_app (snd x))))}}
with r_admissible_permutate_auxiliary_rw_tot Γ Δ Γ1 Γ2 e τ ϕ ψ
  (π : ctx_perm Γ1 Γ2)
  (w   : Γ ;;; Δ ||- e : τ)
  (w1  : (Γ ++ Γ1) ;;; Δ ||- e : τ)
  (w2  : (Γ ++ Γ2) ;;; Δ  ||- e : τ)
  (p   : w1 ||~ [{ϕ}] e [{ψ}]) {struct p} :
  w2 ||~
    [{fun x => ϕ (fst x, (fst_app (snd x); unpermuting π (snd_app (snd x))))}]
    e
    [{fun y x => ψ y (fst x, (fst_app (snd x); unpermuting π (snd_app (snd x))))}].
Proof.
  +
    dependent induction p; try clear IHp; try clear IHp1 IHp2.
    {
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w w0 w2) in p.
      clear r_admissible_permutate_auxiliary_ro_prt.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_var_prt _ _ _ w2 (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      assert ((ro_access (Γ ++ Γ2) k τ w2 h1) = (ro_access (Γ ++ Γ1) k τ w1 (fst_app h1; unpermuting π (snd_app h1)))).
      rewrite (tedious_equiv_2 h1) at 1.
      rewrite <- (ro_access_app _ _ _ _ w _ _ w2).
      rewrite <- (ro_access_app _ _ _ _ w _ _ w1).
      reflexivity.
      rewrite H.
      exact h2.
    }
    {
      pose proof (r_ro_skip_prt _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_true_prt _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_false_prt _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_int_prt _ _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _
                                                     π                                                     
               (has_type_rw_ro _ nil _ _ w)
               w0
               (has_type_rw_ro _ nil _ _ w2)
            ) in r.
      pose proof (r_rw_ro_prt _ _ _ _ _ _ w2 r).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
    }
    {
      pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w'.
      pose proof (has_type_ro_OpZRcoerce_inverse _ _ w2) as w2'.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w' w0 w2') in p.
      apply (r_ro_coerce_prt _ _ _ _ _ _ p).
    }
    {
      pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w'.
      pose proof (has_type_ro_OpZRexp_inverse _ _ w2) as w2'.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w' w0 w2') in p.
      apply (r_ro_exp_prt _ _ _ _ _ _ p).
    }
    {
      pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZplus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZmult_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZminus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRplus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRmult_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRminus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w'.
      pose proof (has_type_ro_OpRrecip_inverse _ _ w2) as w2'.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w' w0 w2') in p.
      apply (r_ro_recip_prt _ _ _ _ _  _ _ p).
      intros h1 h2 h3.
      apply a.
      auto.
    }
    {
      pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZeq_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZlt_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRlt_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_Lim_inverse _ _ w) as w'.
      pose proof (has_type_ro_Lim_inverse _ _ w2) as w2'. 
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _ π w' _ w2') in r.
      apply (r_ro_lim_prt _ _ w2' _
               (fun y (x : sem_ro_ctx ((INTEGER :: Γ) ++ Γ2)) => θ y (fst_app x; unpermuting π (snd_app x)))
               w2).
            (*         (fun y x => ψ y (fst_app x; (snd_app (snd_app x); fst_app (snd_app x)))) *)
            (* ). *)
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      destruct h1.
      simpl.
      simpl in h2.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2_fst).
      simpl.
      rewrite (tedious_equiv_fst).
      rewrite (tedious_equiv_2_snd).
      simpl.
      rewrite (tedious_equiv_snd).
      exact h2.
      intros.
      pose proof (e0 (fst_app γ ; (unpermuting π (snd_app γ))) H) as [y [h1 h2]].
      exists y.
      split.
      exact h1.
      intros.
      apply h2.
      rewrite (tedious_equiv_2_fst) in H0.
      rewrite (tedious_equiv_2_snd) in H0.
      simpl in H0.
      exact H0.
    }
  +
    dependent induction p; try clear IHp; try clear IHp1 IHp2.
    {
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w w0 w2) in p.
      clear r_admissible_permutate_auxiliary_ro_tot.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_var_tot _ _ _ w2 (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      assert ((ro_access (Γ ++ Γ2) k τ w2 h1) = (ro_access (Γ ++ Γ1) k τ w1 (fst_app h1; unpermuting π (snd_app h1)))).
      rewrite (tedious_equiv_2 h1) at 1.
      rewrite <- (ro_access_app _ _ _ _ w _ _ w2).
      rewrite <- (ro_access_app _ _ _ _ w _ _ w1).
      reflexivity.
      rewrite H.
      exact h2.
    }
    {
      pose proof (r_ro_skip_tot _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_true_tot _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_false_tot _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_int_tot _ _ w2  (fun y x => ψ y (fst_app x; unpermuting π (snd_app x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _
                                                     π                                                     
               (has_type_rw_ro _ nil _ _ w)
               w0
               (has_type_rw_ro _ nil _ _ w2)
            ) in r.
      pose proof (r_rw_ro_tot _ _ _ _ _ _ w2 r).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
    }
    {
      pose proof (has_type_ro_OpZRcoerce_inverse _ _ w) as w'.
      pose proof (has_type_ro_OpZRcoerce_inverse _ _ w2) as w2'.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w' w0 w2') in p.
      apply (r_ro_coerce_tot _ _ _ _ _ _ p).
    }
    {
      pose proof (has_type_ro_OpZRexp_inverse _ _ w) as w'.
      pose proof (has_type_ro_OpZRexp_inverse _ _ w2) as w2'.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w' w0 w2') in p.
      apply (r_ro_exp_tot _ _ _ _ _ _ p).
    }
    {
      pose proof (has_type_ro_OpZplus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZplus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_op_plus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpZmult_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZmult_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_op_mult_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpZminus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZminus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_op_minus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRplus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRplus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_op_plus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRmult_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRmult_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_op_mult_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRminus_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRminus_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_op_minus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRrecip_inverse _ _ w) as w'.
      pose proof (has_type_ro_OpRrecip_inverse _ _ w2) as w2'.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w' w0 w2') in p.
      apply (r_ro_recip_tot _ _ _ _ _  _ _ p).
      intros h1 h2 h3.
      apply a.
      auto.
    }
    {
      pose proof (has_type_ro_OpZeq_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZeq_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_comp_eq_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpZlt_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpZlt_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_int_comp_lt_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      apply ψ0; auto.      
    }
    {
      pose proof (has_type_ro_OpRlt_inverse _ _ _ w) as [w'1 w'2].
      pose proof (has_type_ro_OpRlt_inverse _ _ _ w2) as [w2'1 w2'2].
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'1 _ w2'1) in p1.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _  π w'2 _ w2'2) in p2.
      apply (r_ro_real_lt_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros.
      split.
      apply (a _ _ _ H H0).      
      apply a; auto.      
    }
    {
      pose proof (has_type_ro_Lim_inverse _ _ w) as w'.
      pose proof (has_type_ro_Lim_inverse _ _ w2) as w2'. 
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _ π w' _ w2') in p.
      apply (r_ro_lim_tot _ _ w2' _
               (fun y (x : sem_ro_ctx ((INTEGER :: Γ) ++ Γ2)) => θ y (fst_app x; unpermuting π (snd_app x)))
               w2).
            (*         (fun y x => ψ y (fst_app x; (snd_app (snd_app x); fst_app (snd_app x)))) *)
            (* ). *)
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      destruct h1.
      simpl.
      simpl in h2.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2_fst).
      simpl.
      rewrite (tedious_equiv_fst).
      rewrite (tedious_equiv_2_snd).
      simpl.
      rewrite (tedious_equiv_snd).
      exact h2.
      intros.
      pose proof (e0 (fst_app γ ; (unpermuting π (snd_app γ))) H) as [y [h1 h2]].
      exists y.
      split.
      exact h1.
      intros.
      apply h2.
      rewrite (tedious_equiv_2_fst) in H0.
      rewrite (tedious_equiv_2_snd) in H0.
      simpl in H0.
      exact H0.
    }

  +
    dependent induction p; try clear IHp; try clear IHp1 IHp2.
    {
      apply (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π w w0 w2) in p.
      clear r_admissible_permutate_auxiliary_rw_prt.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_proves_ro_prt_ctx_rewrite ( (app_assoc _ _ _))) in r.
      pose proof (has_type_rw_to_ro_res _ _ _ _ _ w w0).
      pose proof (has_type_ro_add_auxiliary _ _ _ H (Γ2)).
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _
               π H
               _
               H0
            ) in r.
      simpl in r.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.
      apply (r_ro_rw_prt _ _ _ _ _ _ _ w2) in r.
      simpl in r.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      clear r.
      destruct h1.
      rewrite (tedious_equiv_2 s0).
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite eq_sym_app_assoc_tr.
      simpl in h2.
      exact h2.
      clear r.
      destruct h2.
      rewrite (tedious_equiv_2 s0).
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite eq_sym_app_assoc_tr.
      simpl.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      intro x; exact x.
    }
    {
      pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w2) as [w0' w3'].
      pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w) as [w0'' w3''].
      pose proof (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π w0'' _ w0' p1). 
      pose proof (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π w3'' _ w3' p2). 
      apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ X X0).
    }
    {
      pose proof (has_type_rw_Newvar_inverse w) as [σ' [w0' w3']].
      pose proof (has_type_rw_Newvar_inverse w2) as [σ'' [w0'' w3'']].
      apply (r_proves_ro_prt_ctx_rewrite ( (app_assoc _ _ _))) in r.
      rewrite app_assoc in w0''.
      induction (has_type_ro_unambiguous _ _ _ _ w0''
                   (has_type_ro_add_auxiliary _ _ _ w0' (Γ2)) ).
      induction (has_type_ro_unambiguous _ _ _ _ (tr (fun Γ : ro_ctx => Γ |- e : σ) (app_assoc Δ Γ (Γ1 )) w0)
                   (has_type_ro_add_auxiliary _ _ _ w0' (Γ1 )) ).
      pose proof (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _ π w0' _ w0'' r). 
      pose proof (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π w3' _ w3'' p).
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in X.
      simpl in X, X0.
      apply (r_rw_new_var_prt_util X X0).
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      rewrite tedious_equiv_0.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      
      rewrite eq_sym_app_assoc_tr.
      rewrite tedious_equiv_0.
      intro y; exact y.

      intro x.
      destruct x.
      destruct s.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro x; exact x.

      intros x y.
      destruct y.
      destruct s.
      rewrite (tedious_equiv_2 s0).
      simpl.
      intro z; exact z.
    }
    {
      pose proof (has_type_rw_Assign_inverse w) as [σ [a' w']].
      pose proof (has_type_rw_Assign_inverse w2) as [σ2 [a'2 w'2]].
      pose proof (has_type_ro_add_auxiliary _ _ _ w' (Γ1)).
      rewrite <- app_assoc in H.
      induction (has_type_ro_unambiguous _ _ _ _  w0 H).
      pose proof (has_type_ro_add_auxiliary _ _ _ w' (Γ2)).
      rewrite <- app_assoc in H0.
      induction (has_type_ro_unambiguous _ _ _ _  w'2 H0).
      rewrite app_assoc in H0.
      apply (r_proves_ro_prt_ctx_rewrite ((app_assoc _ _ _))) in r.
      rewrite ( ( (app_assoc _ _ _))) in H.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _
               π w'
               (tr (fun Γ : ro_ctx => Γ |- e : σ2) (app_assoc Δ Γ (Γ1)) w0)
               H0
            ) in r.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_rw_assign_prt_util r).
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      rewrite tedious_equiv_1.
      intro y; exact y.
      intros x γ δ.
      rewrite (tedious_equiv_2 γ).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro h.
      pose proof (ψ0 _ _ _ h) .
      unfold update'.
      unfold update' in H1.
      assert (update k x δ (assign_wty_assignable (Γ ++ Γ1) Δ k e σ2 w0 w1) =
                update k x δ (assign_wty_assignable (Γ ++ Γ2) Δ k e σ2 (tr (fun Γ0 : ro_ctx => Γ0 |- e : σ2) (eq_sym (app_assoc Δ Γ (Γ2 ))) H0) w2)).
      apply update_assignable_irrl.
      rewrite H2 in H1.
      exact H1.
    }
    {
      pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w) as [[a0 a1] a2].
      pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w2) as [[b0 b1] b2].
      rewrite app_assoc in  b0.
      apply (r_proves_ro_prt_ctx_rewrite ((app_assoc _ _ _))) in r.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _
               π a0 _ b0
            ) in r.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.
      apply (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π a1 _ b1) in p1. 
      apply (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π a2 _ b2) in p2.
      apply (r_rw_cond_prt_util r p1 p2);
        try (intros h1 h2; auto; fail); try (intros h1 h2 h3; auto; fail).
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      unfold rw_to_ro_pre.
      rewrite tedious_equiv_1.
      intro y; exact y.
      unfold ro_to_rw_pre.
      intros x.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro h.
      exact h.
      unfold ro_to_rw_pre.
      intros x.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro h.
      exact h.
    }

    {
      apply magic.
    }
    
    {
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ w).
      assert (ForallT (fun ec : exp * exp => (((Δ ++ Γ ++ Γ2) |- fst ec : BOOL) * ((Γ ++ Γ2);;; Δ ||- snd ec : τ))%type) l) as wty_l'.
      clear w1 θ ϕ ψ f w w2 wty_l.
      dependent induction H.
      apply ForallT_nil.
      apply ForallT_cons.
      destruct p.
      split.
      rewrite app_assoc.
      apply (has_type_ro_add_auxiliary).
      exact h.
      
      apply (has_type_rw_add_auxiliary).
      exact h0.
      exact IHForallT.
      
      apply (r_rw_case_list_prt  (Γ ++ Γ2) Δ l τ wty_l' w2
               (ForallT_map (fun _ θ =>
                               fun y x => θ y (fst_app x; (fst_app (snd_app x); unpermuting π (snd_app (snd_app x))))) θ)).
      simpl.

      clear w w2 w1.
      dependent induction f.
      simpl.
      dependent destruction wty_l'.
      
      apply ForallT2_nil.
      simpl.
      dependent destruction wty_l'.
      simpl.
      apply ForallT2_cons.
      apply IHf.
      dependent destruction H.
      exact H.
      clear IHf f.
      destruct r, p, p0. 
      split.
      simpl.

      generalize h1; intro.
      rewrite app_assoc in h1.
      simpl in r.
      apply (r_proves_ro_prt_ctx_rewrite ((app_assoc _ _ _))) in r.
      dependent destruction H.
      destruct p.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _
               π h4 _ h1
            ) in r.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.

      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold rw_to_ro_pre.
      intro x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      unfold rw_to_ro_pre.
      rewrite tedious_equiv_1.
      intro y; exact y.


      unfold rw_to_ro_pre.
      intros y x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro z; exact z.
      
      dependent destruction H.
      destruct p.
      apply (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π h4 _ h2) in r0. 

      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold ro_to_rw_pre.
      intro x.
      destruct x.
      simpl.
      rewrite (tedious_equiv_2 s0).
      simpl.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      intro y; exact y.
    }
    {
      pose proof (has_type_rw_While_inverse w) as [ae ac].
      
      apply (r_proves_ro_prt_ctx_rewrite ((app_assoc _ _ _))) in r.
      pose proof (has_type_ro_add_auxiliary _ _ _ ae (Γ2 )) as be.
      pose proof (has_type_rw_add_auxiliary _ _ _ _ ac (Γ2 )) as bc.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _
               π ae _ be
            ) in r.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.
      apply (r_admissible_permutate_auxiliary_rw_prt _ _ _ _ _ _ _ _ π ac _ bc) in p. 

      apply (r_rw_while_prt_util r p);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).
      unfold rw_to_ro_pre.
      intros x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite (tedious_equiv_0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      rewrite (tedious_equiv_0).
      intro z; exact z.

      unfold ro_to_rw_pre.
      intro x.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro x; exact x.

      intros t x.
      unfold ro_to_rw_pre.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      intro.
      destruct H.
      simpl in H, H0.
      
      rewrite app_assoc_tr in H0.
      repeat try 
        (rewrite tedious_equiv_fst in H0;
         rewrite tedious_equiv_snd in H0).
      rewrite eq_sym_app_assoc_tr in H0.
      split.
      repeat try 
        (rewrite tedious_equiv_fst in H;
         rewrite tedious_equiv_snd in H).
      exact H.
      exact H0.
    }

  +
    dependent induction p; try clear IHp; try clear IHp1 IHp2.
    {
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π w w0 w2) in p.
      clear r_admissible_permutate_auxiliary_rw_tot.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_proves_ro_tot_ctx_rewrite ( (app_assoc _ _ _))) in r.
      pose proof (has_type_rw_to_ro_res _ _ _ _ _ w w0).
      pose proof (has_type_ro_add_auxiliary _ _ _ H (Γ2)).
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _
               π H
               _
               H0
            ) in r.
      simpl in r.
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.
      apply (r_ro_rw_tot _ _ _ _ _ _ _ w2) in r.
      simpl in r.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      clear r.
      destruct h1.
      rewrite (tedious_equiv_2 s0).
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite eq_sym_app_assoc_tr.
      simpl in h2.
      exact h2.
      clear r.
      destruct h2.
      rewrite (tedious_equiv_2 s0).
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite eq_sym_app_assoc_tr.
      simpl.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      intro x; exact x.
    }
    {
      pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w2) as [w0' w3'].
      pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w) as [w0'' w3''].
      pose proof (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π w0'' _ w0' p1). 
      pose proof (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π w3'' _ w3' p2). 
      apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ X X0).
    }
    {
      pose proof (has_type_rw_Newvar_inverse w) as [σ' [w0' w3']].
      pose proof (has_type_rw_Newvar_inverse w2) as [σ'' [w0'' w3'']].
      apply (r_proves_ro_tot_ctx_rewrite ( (app_assoc _ _ _))) in r.
      rewrite app_assoc in w0''.
      induction (has_type_ro_unambiguous _ _ _ _ w0''
                   (has_type_ro_add_auxiliary _ _ _ w0' (Γ2)) ).
      induction (has_type_ro_unambiguous _ _ _ _ (tr (fun Γ : ro_ctx => Γ |- e : σ) (app_assoc Δ Γ (Γ1 )) w0)
                   (has_type_ro_add_auxiliary _ _ _ w0' (Γ1 )) ).
      pose proof (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _ π w0' _ w0'' r). 
      pose proof (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π w3' _ w3'' p).
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in X.
      simpl in X, X0.
      apply (r_rw_new_var_tot_util X X0).
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      rewrite tedious_equiv_0.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      
      rewrite eq_sym_app_assoc_tr.
      rewrite tedious_equiv_0.
      intro y; exact y.

      intro x.
      destruct x.
      destruct s.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro x; exact x.

      intros x y.
      destruct y.
      destruct s.
      rewrite (tedious_equiv_2 s0).
      simpl.
      intro z; exact z.
    }
    {
      pose proof (has_type_rw_Assign_inverse w) as [σ [a' w']].
      pose proof (has_type_rw_Assign_inverse w2) as [σ2 [a'2 w'2]].
      pose proof (has_type_ro_add_auxiliary _ _ _ w' (Γ1)).
      rewrite <- app_assoc in H.
      induction (has_type_ro_unambiguous _ _ _ _  w0 H).
      pose proof (has_type_ro_add_auxiliary _ _ _ w' (Γ2)).
      rewrite <- app_assoc in H0.
      induction (has_type_ro_unambiguous _ _ _ _  w'2 H0).
      rewrite app_assoc in H0.
      apply (r_proves_ro_tot_ctx_rewrite ((app_assoc _ _ _))) in r.
      rewrite ( ( (app_assoc _ _ _))) in H.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _
               π w'
               (tr (fun Γ : ro_ctx => Γ |- e : σ2) (app_assoc Δ Γ (Γ1)) w0)
               H0
            ) in r.
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_rw_assign_tot_util r).
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      rewrite tedious_equiv_1.
      intro y; exact y.
      intros x γ δ.
      rewrite (tedious_equiv_2 γ).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro h.
      pose proof (ψ0 _ _ _ h) .
      unfold update'.
      unfold update' in H1.
      assert (update k x δ (assign_wty_assignable (Γ ++ Γ1) Δ k e σ2 w0 w1) =
                update k x δ (assign_wty_assignable (Γ ++ Γ2) Δ k e σ2 (tr (fun Γ0 : ro_ctx => Γ0 |- e : σ2) (eq_sym (app_assoc Δ Γ (Γ2 ))) H0) w2)).
      apply update_assignable_irrl.
      rewrite H2 in H1.
      exact H1.
    }
    {
      pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w) as [[a0 a1] a2].
      pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w2) as [[b0 b1] b2].
      rewrite app_assoc in  b0.
      apply (r_proves_ro_tot_ctx_rewrite ((app_assoc _ _ _))) in r.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _
               π a0 _ b0
            ) in r.
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π a1 _ b1) in p1. 
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π a2 _ b2) in p2.
      apply (r_rw_cond_tot_util r p1 p2);
        try (intros h1 h2; auto; fail); try (intros h1 h2 h3; auto; fail).
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      unfold rw_to_ro_pre.
      rewrite tedious_equiv_1.
      intro y; exact y.
      unfold ro_to_rw_pre.
      intros x.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro h.
      exact h.
      unfold ro_to_rw_pre.
      intros x.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro h.
      exact h.
    }

    {
      apply magic.
    }
    {
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ w).
      assert (ForallT (fun ec : exp * exp => (((Δ ++ Γ ++ Γ2) |- fst ec : BOOL) * ((Γ ++ Γ2);;; Δ ||- snd ec : τ))%type) l) as wty_l'.
      clear w1 f0 ϕi θ ϕ ψ f w w2 wty_l.
      dependent induction H.
      apply ForallT_nil.
      apply ForallT_cons.
      destruct p.
      split.
      rewrite app_assoc.
      apply (has_type_ro_add_auxiliary).
      exact h.
      
      apply (has_type_rw_add_auxiliary).
      exact h0.
      exact IHForallT.
      apply (r_rw_case_list_tot  (Γ ++ Γ2) Δ l τ wty_l' w2
               (ForallT_map (fun _ θ =>
                             fun y x => θ y (fst_app x; (fst_app (snd_app x); unpermuting π (snd_app (snd_app x))))) θ) 
               (ForallT_map (fun _ ϕi =>
                             fun  x => ϕi   (fst_app x; (fst_app (snd_app x); unpermuting π (snd_app (snd_app x))))) ϕi)).

      clear w w2 w1 f0.
      dependent induction f.
      simpl.
      dependent destruction wty_l'.
      
      apply ForallT3_nil.
      simpl.
      dependent destruction wty_l'.
      simpl.
      apply ForallT3_cons.
      apply IHf.
      
      dependent destruction H.
      exact H.
      clear IHf f.
      repeat split.
      destruct j as [[j _] _].
      destruct p0.
      destruct p.

      generalize h.
      intro.
      simpl.
      rewrite  (app_assoc) in h.
      apply (r_proves_ro_prt_ctx_rewrite ((app_assoc _ _ _))) in j.
      dependent destruction H.
      destruct p.
      apply (r_admissible_permutate_auxiliary_ro_prt _ _ _ _ _ _ _
               π h4 _ h
            ) in j.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in j.
      simpl in j.

      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a j);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold rw_to_ro_pre.
      intro x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      unfold rw_to_ro_pre.
      rewrite tedious_equiv_1.
      intro y; exact y.


      unfold rw_to_ro_pre.
      intros y x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro z; exact z.

      destruct j as [[_ j] _].
      dependent destruction H.
      destruct p , p0, p1.

      
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ π h2 _ h4) in j. 

      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a j);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold ro_to_rw_pre.
      intro x.
      destruct x.
      simpl.
      rewrite (tedious_equiv_2 s0).
      simpl.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      intro y; exact y.

      destruct j as [_ j].
      destruct p0.
      destruct p.

      generalize h.
      intro.
      simpl.
      rewrite  (app_assoc) in h.
      apply (r_proves_ro_tot_ctx_rewrite ((app_assoc _ _ _))) in j.
      dependent destruction H.
      destruct p.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _ π
               h4 _ h
            ) in j.
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in j.
      simpl in j.

      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a j);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold rw_to_ro_pre.
      intro x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro y; exact y.

      unfold rw_to_ro_pre.
      intro x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_1.
      simpl.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      intro h.
      unfold rw_to_ro_pre in f0.
      pose proof (f0 (fst_app x; (fst_app (snd_app x); unpermuting π (snd_app (snd_app x))))).
      rewrite tedious_equiv_1 in H0.
      apply H0 in h.
      clear H0 wty_l' H w2 w f0 f ψ ϕ θ w1 wty_l τ.
      induction ϕi.
      simpl.
      simpl in h.
      contradict h.
      simpl.
      simpl in IHϕi.
      destruct h.
      left.
      repeat rewrite <- tedious_equiv_2.
      exact H.
      right.
      apply IHϕi.
      exact H.
    }
    {
      pose proof (has_type_rw_While_inverse w) as [ae ac].
      
      apply (r_proves_ro_tot_ctx_rewrite ((app_assoc _ _ _))) in r.
      pose proof (has_type_ro_add_auxiliary _ _ _ ae (Γ2)) as be.
      pose proof (has_type_rw_add_auxiliary _ _ _ _ ac (Γ2 ++ Δ )) as bc.
      apply (r_admissible_permutate_auxiliary_ro_tot _ _ _ _ _ _ _ π 
               ae _ be
            ) in r.
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      simpl in r.
      
      apply (r_proves_rw_tot_ctx_rewrite_ro (eq_sym (app_assoc _ _ _))) in p.
      Check  tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (eq_sym (app_assoc Γ Γ1 Δ)) wty_c.

      
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _
                                                     (ctx_perm_app_const_r π Δ)
                                                     ac _ bc) in p. 
      apply (r_proves_rw_tot_ctx_rewrite_ro ( (app_assoc _ _ _))) in p.
      Check tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (app_assoc Γ Γ2 Δ) bc.
      (* Check  tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (app_assoc Γ Δ (Γ1 ++ Γ2)) bc. *)
      (* pose proof (has_type_rw_add_auxiliary _ _ _ _ ac (Δ )) as acc. *)
      (* pose proof (has_type_rw_add_auxiliary _ _ _ _ acc (Γ2 ++ Γ1 )) as bcc. *)
      (* apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ acc _ bcc) in p. *)
      (* apply (r_proves_rw_tot_ctx_rewrite_ro (eq_sym (app_assoc _ _ _))) in p. *)
      (* Check tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (eq_sym (app_assoc Γ Δ (Γ2 ++ Γ1))) bcc. *)
      (* pose proof (has_type_rw_add_auxiliary _ _ _ _ ac ((Γ2 ++ Γ1) ++ Δ)) as bccc. *)
      (* apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _ ac _ bccc) in p.  *)
      (* apply (r_proves_rw_tot_ctx_rewrite_ro ( (app_assoc _ _ _))) in p. *)
      simpl in r, p.

      assert (w2
  ||~ [{(fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Γ2) =>
         ϕ (fst x, (fst_app (snd x); unpermuting π (snd_app (snd x)))))}] (WHILE e DO c END) [{_
  | ((fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Γ2) => ϕ (fst x, (fst_app (snd x); unpermuting π (snd_app (snd x))))) /\\
     ro_to_rw_pre
       (fun x : sem_ro_ctx (Δ ++ Γ ++ Γ2) =>
          θ false (fst_app x; (fst_app (snd_app x); unpermuting π (snd_app (snd_app x))))))}]).
      
      apply (r_rw_while_tot (Γ ++ Γ2) Δ e c
                            (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Γ2)) be)
                            (tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (app_assoc Γ Γ2 Δ) bc)
                            w2
                            (fun x => ϕ (fst x, (fst_app (snd x); (unpermuting π (snd_app (snd x))))))
                            (fun b x => θ b (fst_app x; (fst_app (snd_app x); (unpermuting π (snd_app (snd_app x))))))
                            (fun x => ψ0 (fst x,
                                           ((fst_app (fst_app (snd x)) ; (unpermuting π (snd_app (fst_app (snd x)))));
                                            snd_app (snd x))))).

      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold rw_to_ro_pre.
      intro x.

      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite tedious_equiv_0.
      simpl.      
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      rewrite tedious_equiv_0.
      intro y; exact y.

      intros y x.
      rewrite (tedious_equiv_2 x).
      rewrite (tedious_equiv_2 (snd_app x)).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      intro z; exact z.

      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold rw_to_ro_pre, ro_to_rw_pre.
      intro x.
      destruct x.
      unfold ctx_perm_app_const_r_unpermuting.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2 (fst_app s0)).
      
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      simpl.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      intro x; exact x.

      intros y x.
      unfold ctx_perm_app_const_r_unpermuting.
      destruct y.
      destruct x.
            rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2 (fst_app s0)).
      simpl.
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite eq_sym_app_assoc_tr.
      simpl.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      rewrite <- tedious_equiv_2.
      intro x; exact x.

      intros.
      intro.
      clear p r.
      simpl in  H.
      
      pose proof (n δ _ H).
      contradict H1.
      destruct H0.
      exists x.
      destruct H0; split; auto.
      intro.
      pose proof (H1 n0).
      simpl in H2.
      rewrite tedious_equiv_fst in H2.
      rewrite tedious_equiv_snd in H2.
      exact H2.

      
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros j1 j2; auto; fail); try (intros j1 j2 j3; auto; fail).      
      unfold rw_to_ro_pre, ro_to_rw_pre.
      intros y x.
      destruct y.
      destruct x.
      rewrite (tedious_equiv_2 s0).
      simpl.
      intro.
      destruct H.
      simpl in H, H0.
      
      repeat try 
        (rewrite tedious_equiv_fst in H;
         rewrite tedious_equiv_snd in H).
      repeat try 
        (rewrite tedious_equiv_fst in H0;
         rewrite tedious_equiv_snd in H0).
      split.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      exact H.
      repeat try 
        (rewrite tedious_equiv_fst;
         rewrite tedious_equiv_snd).
      exact H0.
    }
Defined.

Fixpoint r_admissible_gen_ro_prt Γ1 Γ2 e τ (w : Γ1 |- e : τ) ϕ ψ (p : w |~ {{ϕ}} e {{ψ}}) :
  (has_type_ro_add_auxiliary _ _ _ w Γ2) |~ {{fun x => ϕ (fst_app x)}} e {{fun y x => ψ y (fst_app x)}}
with r_admissible_gen_ro_tot Γ1 Γ2 e τ (w : Γ1 |- e : τ) ϕ ψ (p : w |~ [{ϕ}] e [{ψ}]) :
  (has_type_ro_add_auxiliary _ _ _ w Γ2) |~ [{fun x => ϕ (fst_app x)}] e [{fun y x => ψ y (fst_app x)}]
with r_admissible_gen_rw_prt Γ Δ1 Δ2 e τ (w : Γ ;;; Δ1 ||- e : τ) ϕ ψ (p : w ||~ {{ϕ}} e {{ψ}}) :
  (has_type_rw_add_auxiliary _ _ _ _ w Δ2) ||~ {{fun x => ϕ (fst x, fst_app (snd x))}} e {{fun y x => ψ y (fst x, fst_app (snd x))}}
with r_admissible_gen_rw_tot Γ Δ1 Δ2 e τ (w : Γ ;;; Δ1 ||- e : τ) ϕ ψ (p : w ||~ [{ϕ}] e [{ψ}]) :
  (has_type_rw_add_auxiliary _ _ _ _ w Δ2) ||~ [{fun x => ϕ (fst x, fst_app (snd x))}] e [{fun y x => ψ y (fst x, fst_app (snd x))}].
Proof.
  +
    dependent induction p.
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_var_prt _ _ _ (has_type_ro_add_auxiliary Γ (VAR k) τ w Γ2)
                               (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite (ro_access_app _ (fst_app h1) _ _ w Γ2 (snd_app h1) (has_type_ro_add_auxiliary Γ (VAR k) τ w Γ2)) in h2.
      rewrite <- tedious_equiv_2 in h2.
      exact h2.
    }
    {
      pose proof (r_ro_skip_prt _ (has_type_ro_add_auxiliary Γ SKIP UNIT w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_true_prt _ (has_type_ro_add_auxiliary Γ TRUE BOOL w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_false_prt _ (has_type_ro_add_auxiliary Γ FALSE BOOL w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_int_prt _ _ (has_type_ro_add_auxiliary Γ (INT k) INTEGER w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_admissible_gen_rw_prt _ _ Γ2) in r.
      pose proof (r_rw_ro_prt _ _ _ _ _ _ (has_type_ro_add_auxiliary Γ c τ w' Γ2) r).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p.
      apply (r_ro_coerce_prt _ _ _ _ _ _ p).
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p.
      apply (r_ro_exp_prt _ _ _ _ _ _ p).
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p.
      apply (r_ro_recip_prt _ _ _ _ _ _ _ p).
      intros h1 h2 [h3 h4].
      apply a.
      split; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_prt _ Γ2) in p1.
      apply (r_admissible_gen_ro_prt _ Γ2) in p2.
      apply (r_ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in r.
      apply (r_ro_lim_prt _ _ (has_type_ro_add_auxiliary (INTEGER :: Γ) e REAL w Γ2)
                          (fun x : sem_ro_ctx (Γ ++ Γ2) => ϕ (fst_app x))
                          (fun y x => θ y (fst x, fst_app (snd x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h1.
      simpl in h2.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2 s0) in h2.
      rewrite tedious_equiv_fst in h2.
      rewrite tedious_equiv_2_fst.
      simpl.
      rewrite tedious_equiv_fst.
      exact h2.
      destruct h2.
      rewrite (tedious_equiv_2 s0).
      rewrite tedious_equiv_2_fst.
      simpl.
      intro x; exact x.
      intros.
      apply (e0 (fst_app γ) H).
    }

  +
    dependent induction p.
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_var_tot _ _ _ (has_type_ro_add_auxiliary Γ (VAR k) τ w Γ2)
                               (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite (ro_access_app _ (fst_app h1) _ _ w Γ2 (snd_app h1) (has_type_ro_add_auxiliary Γ (VAR k) τ w Γ2)) in h2.
      rewrite <- tedious_equiv_2 in h2.
      exact h2.
    }
    {
      pose proof (r_ro_skip_tot _ (has_type_ro_add_auxiliary Γ SKIP UNIT w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_true_tot _ (has_type_ro_add_auxiliary Γ TRUE BOOL w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_false_tot _ (has_type_ro_add_auxiliary Γ FALSE BOOL w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      pose proof (r_ro_int_tot _ _ (has_type_ro_add_auxiliary Γ (INT k) INTEGER w Γ2)
                                (fun y x => ψ y (fst_app x))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_admissible_gen_rw_tot _ _ Γ2) in r.
      pose proof (r_rw_ro_tot _ _ _ _ _ _ (has_type_ro_add_auxiliary Γ c τ w' Γ2) r).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p.
      apply (r_ro_coerce_tot _ _ _ _ _ _ p).
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p.
      apply (r_ro_exp_tot _ _ _ _ _ _ p).
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_int_op_plus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_int_op_mult_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_int_op_minus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_real_op_plus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_real_op_mult_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_real_op_minus_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p.
      apply (r_ro_recip_tot _ _ _ _ _ _ _ p).
      intros h1 h2 h3.
      apply a.
      exact h3.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_int_comp_eq_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_int_comp_lt_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply ψ0; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p1.
      apply (r_admissible_gen_ro_tot _ Γ2) in p2.
      apply (r_ro_real_lt_tot _ _ _ _ _ _ _ _ _ _ p1 p2).
      intros; apply a; auto.
    }
    {
      apply (r_admissible_gen_ro_tot _ Γ2) in p.
      apply (r_ro_lim_tot _ _ (has_type_ro_add_auxiliary (INTEGER :: Γ) e REAL w Γ2)
                          (fun x : sem_ro_ctx (Γ ++ Γ2) => ϕ (fst_app x))
                          (fun y x => θ y (fst x, fst_app (snd x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h1.
      simpl in h2.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2 s0) in h2.
      rewrite tedious_equiv_fst in h2.
      rewrite tedious_equiv_2_fst.
      simpl.
      rewrite tedious_equiv_fst.
      exact h2.
      destruct h2.
      rewrite (tedious_equiv_2 s0).
      rewrite tedious_equiv_2_fst.
      simpl.
      intro x; exact x.
      intros.
      apply (e0 (fst_app γ) H).
    }
  +
    dependent induction p.

    {
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p. 
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
     apply (r_admissible_gen_ro_prt _ Δ2) in r. 
     pose proof (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_add_auxiliary Γ Δ e τ w' Δ2)
                   (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _)) r)
       ).
     apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     destruct h1.
     rewrite eq_sym_twice.
     rewrite (tedious_equiv_2 s0).
     rewrite app_assoc_tr.
     simpl in h2.
     rewrite tedious_equiv_fst.
     exact h2.

     intro.
     rewrite eq_sym_twice in H.
     destruct h2.
     rewrite (tedious_equiv_2 s0) in H.
     rewrite app_assoc_tr in H.
     rewrite tedious_equiv_fst in H.
     simpl.
     exact H.
    }
    {
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p1. 
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p2. 
      apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ p1 p2).     
    }
    {
      apply (r_admissible_gen_ro_prt _ Δ2) in r. 
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p.
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_rw_new_var_prt (Γ ++ Δ2) Δ e c _ _

               (tr (fun Γ : ro_ctx => Γ |- e : σ) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e σ w1 Δ2))
               (has_type_rw_add_auxiliary Γ (σ :: Δ) c τ w2 Δ2)
               _ _
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice.
     rewrite (tedious_equiv_2 h1).
     rewrite (tedious_equiv_2 (snd_app h1)).
     rewrite app_assoc_tr.
     unfold fst_app, snd_app.
     unfold fst_app in h2.
     destruct (tedious_sem_app Δ (Γ ++ Δ2) h1).
     simpl in h2.
     destruct (tedious_sem_app Γ Δ2 s0).
     rewrite tedious_equiv_1.
     rewrite tedious_equiv_1.
     exact h2.
     apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice in h2.
     destruct h1.
     destruct s.
     rewrite (tedious_equiv_2 s0) in h2.
     simpl in h2.
     rewrite app_assoc_tr in h2.
     simpl.
     rewrite tedious_equiv_fst in h2.
     exact h2.
    }
    {
      apply (r_admissible_gen_ro_prt _ Δ2) in r. 
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      pose proof (r_rw_assign_prt).
      simpl in r.
      apply (r_rw_assign_prt _ _ _ _ _
               (tr (fun Γ : ro_ctx => Γ |- e : τ) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e τ w Δ2))
               _
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice.
     rewrite (tedious_equiv_2 h1).
     rewrite (tedious_equiv_2 (snd_app h1)).
     rewrite app_assoc_tr.
     unfold fst_app, snd_app.
     unfold fst_app in h2.
     destruct (tedious_sem_app Δ (Γ ++ Δ2) h1).
     simpl in h2.
     destruct (tedious_sem_app Γ Δ2 s0).
     rewrite tedious_equiv_1.
     rewrite tedious_equiv_1.
     exact h2.
     intros x y z.
     unfold update'.
     simpl.
     rewrite (tedious_equiv_2 y).
     rewrite eq_sym_twice.
     rewrite app_assoc_tr.
     rewrite tedious_equiv_fst.
     intro.
     pose proof (ψ0 _ _ _ H).
     unfold update' in H0.
     rewrite <- (tedious_equiv_2 y).
     rewrite (update_assignable_irrl _ _ _ _ _
                (assign_wty_assignable (Γ ++ Δ2) Δ k e τ
                   (tr (fun Γ0 : ro_ctx => Γ0 |- e : τ) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e τ w Δ2))
                   (has_type_rw_add_auxiliary Γ Δ (LET k := e) UNIT w' Δ2))
                (assign_wty_assignable Γ Δ k e τ w w')).
     exact H0.
    }
    {
      apply (r_admissible_gen_ro_prt _ Δ2) in r. 
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p1. 
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p2. 
      simpl in r, p1, p2.
      apply (r_rw_cond_prt _ _ _ _ _ _
               (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e BOOL w Δ2))
               (has_type_rw_add_auxiliary Γ Δ c1 τ w1 Δ2)
               (has_type_rw_add_auxiliary Γ Δ c2 τ w2 Δ2)
               _ _
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))
            ).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice.
      rewrite (tedious_equiv_2 h1).
      rewrite (tedious_equiv_2 (snd_app h1)).
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      rewrite (tedious_equiv_2 h1) in h2.
      rewrite tedious_equiv_0 in h2.
      simpl in h2.
      rewrite tedious_equiv_0.
      exact h2.

      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice in h2.
     destruct h1.
     rewrite (tedious_equiv_2 s0) in h2.
     unfold ro_to_rw_pre in h2.
     rewrite app_assoc_tr in h2.
     simpl.
     unfold ro_to_rw_pre.
     rewrite tedious_equiv_fst in h2.
     exact h2.
     
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice in h2.
     destruct h1.
     rewrite (tedious_equiv_2 s0) in h2.
     unfold ro_to_rw_pre in h2.
     rewrite app_assoc_tr in h2.
     simpl.
     unfold ro_to_rw_pre.
     rewrite tedious_equiv_fst in h2.
     exact h2.
    }
    {
      apply magic.
    }
    {
      apply (r_rw_case_list_prt _ _ _ _
                                (ForallT_map (fun (ec : exp * exp) (x : (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type) => 
                                               (tr (fun Γ : ro_ctx => Γ |- (fst ec) : BOOL)
                                                  (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) (fst ec) BOOL (fst x) Δ2), 
                                                 has_type_rw_add_auxiliary Γ Δ (snd ec) τ (snd x) Δ2)) wty_l)
                                _
                                (ForallT_map (fun _ θ =>
                                               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))) θ)).
      clear wty.
      dependent induction f.
      simpl.
      apply ForallT2_nil.
      simpl.
      apply ForallT2_cons.
      apply IHf.
      clear IHf; destruct r; split.
      apply (r_admissible_gen_ro_prt _ Δ2) in r. 
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice.
      rewrite (tedious_equiv_2 h1).
      rewrite (tedious_equiv_2 (snd_app h1)).
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      rewrite (tedious_equiv_2 h1) in h2.
      rewrite tedious_equiv_0 in h2.
      simpl in h2.
      rewrite tedious_equiv_0.
      exact h2.

      apply (r_admissible_gen_rw_prt _ _ Δ2) in r0. 
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice in h2.
      destruct h1.
      rewrite (tedious_equiv_2 s0) in h2.
      unfold ro_to_rw_pre in h2.
      rewrite app_assoc_tr in h2.
      simpl.
      unfold ro_to_rw_pre.
      rewrite tedious_equiv_fst in h2.
      exact h2.
    }
    {
      apply (r_admissible_gen_ro_prt _ Δ2) in r. 
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_admissible_gen_rw_prt _ _ Δ2) in p. 
      simpl in r, p.
      Check r_rw_while_prt.
      pose proof (r_rw_while_prt _ _ _ _
               (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e BOOL wty_e Δ2))
               (has_type_rw_add_auxiliary Γ Δ c _ wty_c Δ2)
               (has_type_rw_add_auxiliary Γ Δ (WHILE e DO c END) UNIT wty Δ2)
               (fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ2) => ϕ (fst x, fst_app (snd x)))
               
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))
            ).
      
      assert ( tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e BOOL wty_e Δ2)
      |~ {{rw_to_ro_pre (fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ2) => ϕ (fst x, fst_app (snd x)))}} e {{y
      | (fun x : sem_ro_ctx (Δ ++ Γ ++ Δ2) => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))}} ).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice.
      rewrite (tedious_equiv_2 h1).
      rewrite (tedious_equiv_2 (snd_app h1)).
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      rewrite (tedious_equiv_2 h1) in h2.
      rewrite tedious_equiv_0 in h2.
      simpl in h2.
      rewrite tedious_equiv_0.
      exact h2.

      apply X in X0.
      clear X.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2.
      simpl.
      intros.
      destruct H.
      simpl in H, H0.
      
      split.
      exact H.
      unfold ro_to_rw_pre in H0.
      rewrite (tedious_equiv_2 s0) in H0.
      rewrite eq_sym_twice in H0.
      rewrite app_assoc_tr in H0.
      unfold ro_to_rw_pre.
      rewrite tedious_equiv_fst in H0.
      exact H0.

      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice in h2.
      destruct h1.
      rewrite (tedious_equiv_2 s0) in h2.
      unfold ro_to_rw_pre in h2.
      rewrite app_assoc_tr in h2.
      simpl.
      unfold ro_to_rw_pre.
      rewrite tedious_equiv_fst in h2.
      exact h2.
    }
  +
    dependent induction p.

    {
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p. 
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }
    {
     apply (r_admissible_gen_ro_tot _ Δ2) in r. 
     pose proof (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_add_auxiliary Γ Δ e τ w' Δ2)
                   (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _)) r)
       ).
     apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     destruct h1.
     rewrite eq_sym_twice.
     rewrite (tedious_equiv_2 s0).
     rewrite app_assoc_tr.
     simpl in h2.
     rewrite tedious_equiv_fst.
     exact h2.

     intro.
     rewrite eq_sym_twice in H.
     destruct h2.
     rewrite (tedious_equiv_2 s0) in H.
     rewrite app_assoc_tr in H.
     rewrite tedious_equiv_fst in H.
     simpl.
     exact H.
    }
    {
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p1. 
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p2. 
      apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ p1 p2).     
    }
    {
      apply (r_admissible_gen_ro_tot _ Δ2) in r. 
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p.
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_rw_new_var_tot (Γ ++ Δ2) Δ e c _ _

               (tr (fun Γ : ro_ctx => Γ |- e : σ) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e σ w1 Δ2))
               (has_type_rw_add_auxiliary Γ (σ :: Δ) c τ w2 Δ2)
               _ _
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice.
     rewrite (tedious_equiv_2 h1).
     rewrite (tedious_equiv_2 (snd_app h1)).
     rewrite app_assoc_tr.
     unfold fst_app, snd_app.
     unfold fst_app in h2.
     destruct (tedious_sem_app Δ (Γ ++ Δ2) h1).
     simpl in h2.
     destruct (tedious_sem_app Γ Δ2 s0).
     rewrite tedious_equiv_1.
     rewrite tedious_equiv_1.
     exact h2.
     apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice in h2.
     destruct h1.
     destruct s.
     rewrite (tedious_equiv_2 s0) in h2.
     simpl in h2.
     rewrite app_assoc_tr in h2.
     simpl.
     rewrite tedious_equiv_fst in h2.
     exact h2.
    }
    {
      apply (r_admissible_gen_ro_tot _ Δ2) in r. 
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      pose proof (r_rw_assign_tot).
      simpl in r.
      apply (r_rw_assign_tot _ _ _ _ _
               (tr (fun Γ : ro_ctx => Γ |- e : τ) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e τ w Δ2))
               _
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice.
     rewrite (tedious_equiv_2 h1).
     rewrite (tedious_equiv_2 (snd_app h1)).
     rewrite app_assoc_tr.
     unfold fst_app, snd_app.
     unfold fst_app in h2.
     destruct (tedious_sem_app Δ (Γ ++ Δ2) h1).
     simpl in h2.
     destruct (tedious_sem_app Γ Δ2 s0).
     rewrite tedious_equiv_1.
     rewrite tedious_equiv_1.
     exact h2.
     intros x y z.
     unfold update'.
     simpl.
     rewrite (tedious_equiv_2 y).
     rewrite eq_sym_twice.
     rewrite app_assoc_tr.
     rewrite tedious_equiv_fst.
     intro.
     pose proof (ψ0 _ _ _ H).
     unfold update' in H0.
     rewrite <- (tedious_equiv_2 y).
     rewrite (update_assignable_irrl _ _ _ _ _
                (assign_wty_assignable (Γ ++ Δ2) Δ k e τ
                   (tr (fun Γ0 : ro_ctx => Γ0 |- e : τ) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e τ w Δ2))
                   (has_type_rw_add_auxiliary Γ Δ (LET k := e) UNIT w' Δ2))
                (assign_wty_assignable Γ Δ k e τ w w')).
     exact H0.
    }
    {
      apply (r_admissible_gen_ro_tot _ Δ2) in r. 
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p1. 
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p2. 
      simpl in r, p1, p2.
      apply (r_rw_cond_tot _ _ _ _ _ _
               (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e BOOL w Δ2))
               (has_type_rw_add_auxiliary Γ Δ c1 τ w1 Δ2)
               (has_type_rw_add_auxiliary Γ Δ c2 τ w2 Δ2)
               _ _
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))
            ).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice.
      rewrite (tedious_equiv_2 h1).
      rewrite (tedious_equiv_2 (snd_app h1)).
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      rewrite (tedious_equiv_2 h1) in h2.
      rewrite tedious_equiv_0 in h2.
      simpl in h2.
      rewrite tedious_equiv_0.
      exact h2.

      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice in h2.
     destruct h1.
     rewrite (tedious_equiv_2 s0) in h2.
     unfold ro_to_rw_pre in h2.
     rewrite app_assoc_tr in h2.
     simpl.
     unfold ro_to_rw_pre.
     rewrite tedious_equiv_fst in h2.
     exact h2.
     
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
     rewrite eq_sym_twice in h2.
     destruct h1.
     rewrite (tedious_equiv_2 s0) in h2.
     unfold ro_to_rw_pre in h2.
     rewrite app_assoc_tr in h2.
     simpl.
     unfold ro_to_rw_pre.
     rewrite tedious_equiv_fst in h2.
     exact h2.
    }
    {
      apply magic.
    }
    {
      Check r_rw_case_list_tot.
      apply (r_rw_case_list_tot _ _ _ _
                                (ForallT_map (fun (ec : exp * exp) (x : (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type) => 
                                               (tr (fun Γ : ro_ctx => Γ |- (fst ec) : BOOL)
                                                  (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) (fst ec) BOOL (fst x) Δ2), 
                                                 has_type_rw_add_auxiliary Γ Δ (snd ec) τ (snd x) Δ2)) wty_l)
                                _
                                (ForallT_map (fun _ θ =>
                                                (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))) θ)
                                (ForallT_map (fun _ ϕi =>
                                                (fun x => ϕi (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))) ϕi)
            ).
      clear wty f0.
      dependent induction f.
      simpl.
      apply ForallT3_nil.
      simpl.
      apply ForallT3_cons.
      apply IHf.
      clear IHf; destruct j as [[j1 j2] j3]; repeat split.
      apply (r_admissible_gen_ro_prt _ Δ2) in j1. 
      apply (r_proves_ro_prt_ctx_rewrite (eq_sym (app_assoc _ _ _))) in j1.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a j1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice.
      rewrite (tedious_equiv_2 h1).
      rewrite (tedious_equiv_2 (snd_app h1)).
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      rewrite (tedious_equiv_2 h1) in h2.
      rewrite tedious_equiv_0 in h2.
      simpl in h2.
      rewrite tedious_equiv_0.
      exact h2.

      apply (r_admissible_gen_rw_tot _ _ Δ2) in j2. 
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a j2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice in h2.
      destruct h1.
      rewrite (tedious_equiv_2 s0) in h2.
      unfold ro_to_rw_pre in h2.
      rewrite app_assoc_tr in h2.
      simpl.
      unfold ro_to_rw_pre.
      rewrite tedious_equiv_fst in h2.
      exact h2.

      apply (r_admissible_gen_ro_tot _ Δ2) in j3. 
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in j3.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a j3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

      intros.
      pose proof (f0 (fst_app x; fst_app (snd_app x))).
      assert (rw_to_ro_pre ϕ (fst_app x; fst_app (snd_app x))).
      unfold rw_to_ro_pre in H.
      unfold rw_to_ro_pre.
      rewrite tedious_equiv_1.
      rewrite (tedious_equiv_2 x) in H.
      rewrite tedious_equiv_1 in H.
      simpl in H.
      exact H.
      apply H0 in H1.

      clear f f0 wty θ H0 H ϕ ψ wty_l.
      dependent induction ϕi.
      simpl in H1.
      contradict H1.
      simpl.
      simpl in H1.
      destruct H1.
      left.
      rewrite (tedious_equiv_2 x0).
      rewrite (tedious_equiv_2 (snd_app x0)).
      rewrite eq_sym_twice.
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      exact H.

      right.
      apply IHϕi.
      exact H.
    }
    {
      apply (r_admissible_gen_ro_tot _ Δ2) in r. 
      apply (r_proves_ro_tot_ctx_rewrite (eq_sym (app_assoc _ _ _))) in r.
      apply (r_admissible_gen_rw_tot _ _ Δ2) in p.
      apply (r_proves_rw_tot_ctx_rewrite_ro (eq_sym (app_assoc _ _ _))) in p.
      Check tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (eq_sym (app_assoc Γ Δ Δ2)) (has_type_rw_add_auxiliary (Γ ++ Δ) Δ c UNIT wty_c Δ2).
      pose proof (has_type_rw_While_inverse wty) as [_ jjj].
      Check has_type_rw_add_auxiliary (Γ ++ Δ) Δ c UNIT wty_c Δ2.
      apply (r_admissible_permutate_auxiliary_rw_tot _ _ _ _ _ _ _ _
                                                     (ctx_perm_swap Δ Δ2)
                                                     jjj
               _
               (has_type_rw_add_auxiliary _ _ _ _ jjj (Δ2 ++ Δ))
               
            ) in p.
      unfold  ctx_perm_swap_unpermuting in p.
      apply (r_proves_rw_tot_ctx_rewrite_ro ( (app_assoc _ _ _))) in p.
      simpl in p.
      Check has_type_rw_add_auxiliary Γ Δ c UNIT jjj (Δ2 ++ Δ).
      simpl in r, p.
      Check r_rw_while_tot.
      pose proof (r_rw_while_tot _ _ _ _
               (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e BOOL wty_e Δ2))
               ( tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (app_assoc Γ Δ2 Δ) (has_type_rw_add_auxiliary Γ Δ c UNIT jjj (Δ2 ++ Δ)))
               (has_type_rw_add_auxiliary Γ Δ (WHILE e DO c END) UNIT wty Δ2)
               (fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ2) => ϕ (fst x, fst_app (snd x)))
               
               (fun y x => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))
               (fun x => ψ0 (fst x, (fst_app (fst_app (snd x)); snd_app (snd x))))
        ).
      assert ( tr (fun Γ : ro_ctx => Γ |- e : BOOL) (eq_sym (app_assoc Δ Γ Δ2)) (has_type_ro_add_auxiliary (Δ ++ Γ) e BOOL wty_e Δ2)
      |~ [{rw_to_ro_pre (fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ2) => ϕ (fst x, fst_app (snd x)))}] e [{y
      | (fun x : sem_ro_ctx (Δ ++ Γ ++ Δ2) => θ y (fst_app (tr sem_ro_ctx (eq_sym (eq_sym (app_assoc Δ Γ Δ2))) x)))}]).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice.
      rewrite (tedious_equiv_2 h1).
      rewrite (tedious_equiv_2 (snd_app h1)).
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      rewrite (tedious_equiv_2 h1) in h2.
      rewrite tedious_equiv_0 in h2.
      simpl in h2.
      rewrite tedious_equiv_0.
      exact h2.

      
      apply X in X0.
      clear X.
      
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h2.
      simpl.
      intros.
      destruct H.
      simpl in H, H0.
      
      split.
      exact H.
      unfold ro_to_rw_pre in H0.
      rewrite (tedious_equiv_2 s0) in H0.
      rewrite eq_sym_twice in H0.
      rewrite app_assoc_tr in H0.
      unfold ro_to_rw_pre.
      rewrite tedious_equiv_fst in H0.
      exact H0.

      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      rewrite eq_sym_twice in h2.
      
      destruct h1.
      rewrite (tedious_equiv_2 s0) in h2.
      unfold ro_to_rw_pre in h2.
      unfold ro_to_rw_pre.
      simpl.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2 (fst_app s0)).
      rewrite eq_sym_app_assoc_tr.
      simpl in h2.
      rewrite eq_sym_twice.
      unfold  ctx_perm_swap_unpermuting.
      rewrite app_assoc_tr.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite tedious_equiv_fst.
      rewrite tedious_equiv_snd.
      rewrite tedious_equiv_fst in h2.
      rewrite tedious_equiv_snd in h2.
      rewrite (tedious_equiv_2 (fst_app s0)) in h2.
      rewrite app_assoc_tr in h2.
      rewrite tedious_equiv_fst in h2.
      exact h2.


      destruct h2.
      rewrite (tedious_equiv_2 s0).
      rewrite (tedious_equiv_2 (fst_app s0)).
      rewrite eq_sym_twice.
      unfold  ctx_perm_swap_unpermuting.
      rewrite app_assoc_tr.
      simpl.
      rewrite eq_sym_app_assoc_tr.
      repeat (try rewrite tedious_equiv_fst; try
                                               rewrite tedious_equiv_snd).
      auto.

      intros.
      intro.
      pose proof (n δ (fst_app γ) H).
      contradict H1.
      destruct H0 as [f [h1 h2]].
      exists f.
      split; auto.
      intro.
      pose proof (h2 n0).
      simpl in H0.
      rewrite tedious_equiv_fst in H0.
      rewrite tedious_equiv_snd in H0.
      exact H0.

    }
Defined.    

Fixpoint r_admissible_move_rw_prt Γ Δ1 Δ2 e τ (w : (Δ2 ++ Γ) ;;; Δ1 ||- e : τ) ϕ ψ (p : w ||~ {{ϕ}} e {{ψ}}) {struct p}:
  (has_type_rw_move Γ Δ1 Δ2 e τ w) ||~ {{fun x => ϕ (fst_app (fst x), (snd_app (fst x); snd x))}} e {{fun y x => ψ y (fst_app (fst x), (snd_app (fst x); snd x))}}.
Proof.
  dependent induction p.
  {
    apply r_admissible_move_rw_prt in p.
    clear r_admissible_move_rw_prt.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  }

  {
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    
    pose proof (r_ro_rw_prt _ _ _ _ _ _ _ ( has_type_rw_move Γ Δ Δ2 e τ w) X).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl in h2.
    rewrite (tedious_equiv_2 s).
    rewrite eq_sym_app_assoc_tr.
    exact h2.

    destruct h2.
    rewrite (tedious_equiv_2 s).
    rewrite eq_sym_app_assoc_tr.
    simpl.
    unfold fst_app, snd_app.
    
    rewrite tedious_equiv_1.
    intro x; exact x.
  } 

  {
    apply r_admissible_move_rw_prt in p1, p2.
    clear r_admissible_move_rw_prt.
    apply (r_rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  }

  {    
    apply r_admissible_move_rw_prt in p.
    clear r_admissible_move_rw_prt.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    simpl in X.
    apply (r_rw_new_var_prt _ _ _ _ _ _
                            (tr (fun Γ : ro_ctx => Γ |- e : σ) (app_assoc Δ Δ2 Γ) w1)
                            (has_type_rw_move Γ (σ :: Δ) Δ2 c τ w2)
                            _ _
                            (fun y x => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                            (has_type_rw_move Γ Δ Δ2 (NEWVAR e IN c) τ w)
          ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    
    rewrite (tedious_equiv_2 h1) in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    rewrite tedious_equiv_1.
    exact h2.

    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl in h2.
    destruct s.
    simpl in h2.
    rewrite (tedious_equiv_2 s1) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    rewrite tedious_equiv_2_fst.
    simpl.
    rewrite tedious_equiv_2_snd.
    simpl.
    exact h2.
    simpl.
    destruct h2.
    destruct s.
    rewrite (tedious_equiv_2 s1).
    simpl.
    rewrite tedious_equiv_2_fst.
    rewrite tedious_equiv_2_snd.
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    simpl.
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    intro x; exact x.
  }

  {
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    apply (r_rw_assign_prt _ _ _ _ _
                           (tr (fun Γ : ro_ctx => Γ |- e : τ) (app_assoc Δ Δ2 Γ) w0)
                           _
                           (fun y x  => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                           _
                           (has_type_rw_move Γ Δ Δ2 (LET k := e) UNIT w)
          ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    
    rewrite (tedious_equiv_2 h1) in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    rewrite tedious_equiv_1.
    exact h2.

    intros.
    unfold update'.
    simpl.
    rewrite (tedious_equiv_2 δ) in H.
    rewrite eq_sym_app_assoc_tr in H.
    pose proof (ψ0 _ _ _ H).
    unfold update' in H0.
    rewrite (tedious_equiv_2 δ).
    replace  (@update τ (@app datatype Δ Δ2) k x
             (tedious_prod_sem Δ Δ2 (@pair (sem_ro_ctx Δ) (sem_ro_ctx Δ2) (@fst_app Δ Δ2 δ) (@snd_app Δ Δ2 δ)))
             (assign_wty_assignable Γ (@app datatype Δ Δ2) k e τ
                (@tr ro_ctx (fun Γ0 : ro_ctx => has_type_ro Γ0 e τ) (@app datatype Δ (@app datatype Δ2 Γ))
                   (@app datatype (@app datatype Δ Δ2) Γ) (@app_assoc datatype Δ Δ2 Γ) w0)
                (has_type_rw_move Γ Δ Δ2 (Assign k e) DUnit w)))
      with (tedious_prod_sem Δ Δ2
                             (@pair (sem_list_datatype Δ) (sem_ro_ctx Δ2)
                                (@update τ Δ k x (@fst_app Δ Δ2 δ)
                                   (assign_wty_assignable (@app datatype Δ2 Γ) Δ k e τ w0 w)) 
                                (@snd_app Δ Δ2 δ))).
    
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    exact H0.
    rewrite (assign_concat_fst _ _ _ _
                               (assign_wty_assignable (Δ2 ++ Γ) Δ k e τ w0 w)
                               (assign_wty_assignable Γ (Δ ++ Δ2) k e τ (tr (fun Γ0 : ro_ctx => Γ0 |- e : τ) (app_assoc Δ Δ2 Γ) w0)
                                                      (has_type_rw_move Γ Δ Δ2 (LET k := e) UNIT w))
                               x
                               (fst_app δ) (snd_app δ)

            ).
    reflexivity.
  }

  {
    apply r_admissible_move_rw_prt in p1, p2.
    clear r_admissible_move_rw_prt.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    pose proof (r_rw_cond_prt). 
    apply (r_rw_cond_prt _ _ _ _ _ _
                         (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (app_assoc Δ Δ2 Γ) w0)
                         (has_type_rw_move Γ Δ Δ2 c1 τ w1)
                         (has_type_rw_move Γ Δ Δ2 c2 τ w2)
                         (has_type_rw_move Γ Δ Δ2 (IF e THEN c1 ELSE c2 END) τ w)
                         _
                         (fun y x => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                         _
          ). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.

    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.
    
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.
  }

  {
    apply r_admissible_move_rw_prt in p1, p2.
    clear r_admissible_move_rw_prt.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r0).
    apply (r_rw_case_prt _ _ _ _ _ _ _
                              (tr (fun Γ : ro_ctx => Γ |- e1 : BOOL) (app_assoc Δ Δ2 Γ) wty_e1)
                              (tr (fun Γ : ro_ctx => Γ |- e2 : BOOL) (app_assoc Δ Δ2 Γ) wty_e2)
                              (has_type_rw_move Γ Δ Δ2 c1 τ wty_c1)
                              (has_type_rw_move Γ Δ Δ2 c2 τ wty_c2)
                              (has_type_rw_move Γ Δ Δ2 (CASE e1 ==> c1 OR e2 ==> c2 END) τ w)
                              _
                              (fun y x => θ1 y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                              (fun y x => θ2 y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                              
               ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.

    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.
    
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.
    
    
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.  
  }

  {
    apply (r_rw_case_list_prt _ _ l τ
                              (ForallT_map (fun x ec =>
                                              (tr (fun Γ : ro_ctx => Γ |- fst x : BOOL) (app_assoc Δ Δ2 Γ) (fst ec),
                                                has_type_rw_move Γ Δ Δ2 (snd x) τ (snd ec))) wty_l)   
                              (has_type_rw_move Γ Δ Δ2 (CaseList l) τ w)
                              (ForallT_map (fun _ t => (fun y x => t y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x)))
                                               θ)

          ).
    clear w.
    dependent induction f.
    simpl.
    apply ForallT2_nil.
    simpl.
    apply ForallT2_cons.
    apply IHf.
    destruct r.
    split.
    simpl.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.

    simpl.
    apply r_admissible_move_rw_prt in r0.
    clear r_admissible_move_rw_prt.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.  
  }

  {
    apply r_admissible_move_rw_prt in p.
    clear r_admissible_move_rw_prt.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    pose proof (r_rw_while_prt _ _ _ _
                          (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (app_assoc Δ Δ2 Γ) wty_e)
                          (has_type_rw_move Γ Δ Δ2 c UNIT wty_c)
                          (has_type_rw_move Γ Δ Δ2 (WHILE e DO c END) UNIT w)
                          (fun x => ϕ (fst_app (fst x), (snd_app (fst x); snd x)))
                          (fun y x => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
          ).
    assert (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (app_assoc Δ Δ2 Γ) wty_e
       |~ {{rw_to_ro_pre
              (fun x : sem_ro_ctx (Δ ++ Δ2) * sem_ro_ctx Γ => ϕ (fst_app (fst x), (snd_app (fst x); snd x)))}} e {{y
                                                                                                                  | (fun x : sem_ro_ctx ((Δ ++ Δ2) ++ Γ) => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))}}).
    
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.
    
    
    assert (has_type_rw_move Γ Δ Δ2 c UNIT wty_c
       ||~ {{ro_to_rw_pre
               ((fun (y : sem_datatype BOOL) (x : sem_ro_ctx ((Δ ++ Δ2) ++ Γ)) =>
                 θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x)) true)}} c {{_
       | (fun x : sem_ro_ctx (Δ ++ Δ2) * sem_ro_ctx Γ => ϕ (fst_app (fst x), (snd_app (fst x); snd x)))}}).
    
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
      try (intros t1 t2; auto); try (intros t1 t2 t3; auto).
    unfold  ro_to_rw_pre in t2.
    destruct t1.
    rewrite (tedious_equiv_2 s) in t2.
    rewrite eq_sym_app_assoc_tr in t2.
    simpl.
    unfold ro_to_rw_pre.
    exact t2.  
    pose proof (X0 X1 X2).

    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3);
      try (intros t1 t2; auto); try (intros t1 t2 t3; auto).
    destruct t2.
    intros.
    destruct H.
    simpl in H, H0.
    simpl.
    split.
    exact H.
    unfold ro_to_rw_pre in H0.
    rewrite (tedious_equiv_2 s) in H0.
    rewrite eq_sym_app_assoc_tr in H0.
    exact H0.
  }
Defined.

  
Fixpoint r_admissible_move_rw_tot Γ Δ1 Δ2 e τ (w : (Δ2 ++ Γ) ;;; Δ1 ||- e : τ) ϕ ψ (p : w ||~ [{ϕ}] e [{ψ}]) {struct p} :
  (has_type_rw_move Γ Δ1 Δ2 e τ w) ||~ [{fun x => ϕ (fst_app (fst x), (snd_app (fst x); snd x))}] e [{fun y x => ψ y (fst_app (fst x), (snd_app (fst x); snd x))}].
Proof.
  dependent induction p.
  {
    apply r_admissible_move_rw_tot in p.
    clear r_admissible_move_rw_tot.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  }

  {
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    
    pose proof (r_ro_rw_tot _ _ _ _ _ _ _ ( has_type_rw_move Γ Δ Δ2 e τ w) X).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl in h2.
    rewrite (tedious_equiv_2 s).
    rewrite eq_sym_app_assoc_tr.
    exact h2.

    destruct h2.
    rewrite (tedious_equiv_2 s).
    rewrite eq_sym_app_assoc_tr.
    simpl.
    unfold fst_app, snd_app.
    
    rewrite tedious_equiv_1.
    intro x; exact x.
  } 

  {
    apply r_admissible_move_rw_tot in p1, p2.
    clear r_admissible_move_rw_tot.
    apply (r_rw_sequence_tot _ _ _ _ _ _ _ _ _ _ _ p1 p2).
  }

  {    
    apply r_admissible_move_rw_tot in p.
    clear r_admissible_move_rw_tot.
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    simpl in X.
    apply (r_rw_new_var_tot _ _ _ _ _ _
                            (tr (fun Γ : ro_ctx => Γ |- e : σ) (app_assoc Δ Δ2 Γ) w1)
                            (has_type_rw_move Γ (σ :: Δ) Δ2 c τ w2)
                            _ _
                            (fun y x => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                            (has_type_rw_move Γ Δ Δ2 (NEWVAR e IN c) τ w)
          ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    
    rewrite (tedious_equiv_2 h1) in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    rewrite tedious_equiv_1.
    exact h2.

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl in h2.
    destruct s.
    simpl in h2.
    rewrite (tedious_equiv_2 s1) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    rewrite tedious_equiv_2_fst.
    simpl.
    rewrite tedious_equiv_2_snd.
    simpl.
    exact h2.
    simpl.
    destruct h2.
    destruct s.
    rewrite (tedious_equiv_2 s1).
    simpl.
    rewrite tedious_equiv_2_fst.
    rewrite tedious_equiv_2_snd.
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    simpl.
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    intro x; exact x.
  }

  {
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    apply (r_rw_assign_tot _ _ _ _ _
                           (tr (fun Γ : ro_ctx => Γ |- e : τ) (app_assoc Δ Δ2 Γ) w0)
                           _
                           (fun y x  => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                           _
                           (has_type_rw_move Γ Δ Δ2 (LET k := e) UNIT w)
          ).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    
    rewrite (tedious_equiv_2 h1) in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    rewrite tedious_equiv_1.
    exact h2.

    intros.
    unfold update'.
    simpl.
    rewrite (tedious_equiv_2 δ) in H.
    rewrite eq_sym_app_assoc_tr in H.
    pose proof (ψ0 _ _ _ H).
    unfold update' in H0.
    rewrite (tedious_equiv_2 δ).
    replace  (@update τ (@app datatype Δ Δ2) k x
             (tedious_prod_sem Δ Δ2 (@pair (sem_ro_ctx Δ) (sem_ro_ctx Δ2) (@fst_app Δ Δ2 δ) (@snd_app Δ Δ2 δ)))
             (assign_wty_assignable Γ (@app datatype Δ Δ2) k e τ
                (@tr ro_ctx (fun Γ0 : ro_ctx => has_type_ro Γ0 e τ) (@app datatype Δ (@app datatype Δ2 Γ))
                   (@app datatype (@app datatype Δ Δ2) Γ) (@app_assoc datatype Δ Δ2 Γ) w0)
                (has_type_rw_move Γ Δ Δ2 (Assign k e) DUnit w)))
      with (tedious_prod_sem Δ Δ2
                             (@pair (sem_list_datatype Δ) (sem_ro_ctx Δ2)
                                (@update τ Δ k x (@fst_app Δ Δ2 δ)
                                   (assign_wty_assignable (@app datatype Δ2 Γ) Δ k e τ w0 w)) 
                                (@snd_app Δ Δ2 δ))).
    
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    exact H0.
    rewrite (assign_concat_fst _ _ _ _
                               (assign_wty_assignable (Δ2 ++ Γ) Δ k e τ w0 w)
                               (assign_wty_assignable Γ (Δ ++ Δ2) k e τ (tr (fun Γ0 : ro_ctx => Γ0 |- e : τ) (app_assoc Δ Δ2 Γ) w0)
                                                      (has_type_rw_move Γ Δ Δ2 (LET k := e) UNIT w))
                               x
                               (fst_app δ) (snd_app δ)

            ).
    reflexivity.
  }

  {
    apply r_admissible_move_rw_tot in p1, p2.
    clear r_admissible_move_rw_tot.
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    pose proof (r_rw_cond_tot). 
    apply (r_rw_cond_tot _ _ _ _ _ _
                         (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (app_assoc Δ Δ2 Γ) w0)
                         (has_type_rw_move Γ Δ Δ2 c1 τ w1)
                         (has_type_rw_move Γ Δ Δ2 c2 τ w2)
                         (has_type_rw_move Γ Δ Δ2 (IF e THEN c1 ELSE c2 END) τ w)
                         _
                         (fun y x => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                         _
          ). 
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.
    
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.
  }

  {
    apply r_admissible_move_rw_tot in p1, p2.
    clear r_admissible_move_rw_tot.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r0).
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r1).
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r2).
    Check r_rw_case_tot.
    apply (r_rw_case_tot _ _ _ _ _ _ _
                              (tr (fun Γ : ro_ctx => Γ |- e1 : BOOL) (app_assoc Δ Δ2 Γ) wty_e1)
                              (tr (fun Γ : ro_ctx => Γ |- e2 : BOOL) (app_assoc Δ Δ2 Γ) wty_e2)
                              (has_type_rw_move Γ Δ Δ2 c1 τ wty_c1)
                              (has_type_rw_move Γ Δ Δ2 c2 τ wty_c2)
                              (has_type_rw_move Γ Δ Δ2 (CASE e1 ==> c1 OR e2 ==> c2 END) τ w)
                              _
                              (fun y x => θ1 y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                              (fun y x => θ2 y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                              _
                              (fun x => ϕ1 (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                              (fun x => ϕ2 (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
          ).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.

    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.
    
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.
    
    
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.

    exact X1.
    exact X2.

    intros.
    unfold rw_to_ro_pre in H.
    rewrite (tedious_equiv_2 x) in H.
    rewrite (tedious_equiv_1) in H.
    simpl in H.
    
    pose proof (o (fst_app (fst_app x); (snd_app (fst_app x); snd_app x))).
    unfold rw_to_ro_pre in H0.
    rewrite (tedious_equiv_1) in H0.
    destruct (H0 H).
    left.
    rewrite (tedious_equiv_2 x).
    rewrite (tedious_equiv_2 (fst_app x)).
    rewrite eq_sym_app_assoc_tr.
    exact H1.
    right.
    rewrite (tedious_equiv_2 x).
    rewrite (tedious_equiv_2 (fst_app x)).
    rewrite eq_sym_app_assoc_tr.
    exact H1.
  }

  {
    Check r_rw_case_list_tot.
    apply (r_rw_case_list_tot _ _ l τ
                              (ForallT_map (fun x ec =>
                                              (tr (fun Γ : ro_ctx => Γ |- fst x : BOOL) (app_assoc Δ Δ2 Γ) (fst ec),
                                                has_type_rw_move Γ Δ Δ2 (snd x) τ (snd ec))) wty_l)   
                              (has_type_rw_move Γ Δ Δ2 (CaseList l) τ w)
                              (ForallT_map (fun _ t => (fun y x => t y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x)))
                                           θ)
                              (ForallT_map (fun _ t => (fun x => t (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x)))
                                           ϕi)
          ).
    clear w f0.
    dependent induction f.
    simpl.
    apply ForallT3_nil.
    simpl.
    apply ForallT3_cons.
    apply IHf.
    clear IHf.
    destruct j as [[r0 r1] r2].
    repeat split.
    simpl.
    pose proof (r_proves_ro_prt_ctx_rewrite (app_assoc Δ Δ2 Γ) r0).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre. 
    rewrite tedious_equiv_1.
    exact h2.

    simpl.
    apply r_admissible_move_rw_tot in r1.
    clear r_admissible_move_rw_tot.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a r1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold  ro_to_rw_pre in h2.
    destruct h1.
    rewrite (tedious_equiv_2 s) in h2.
    rewrite eq_sym_app_assoc_tr in h2.
    simpl.
    unfold ro_to_rw_pre.
    exact h2.

    simpl.
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r2).
    simpl in X.
    exact X.

    intros.
    pose proof (f0 (fst_app (fst_app x); (snd_app (fst_app x); snd_app x))).
    unfold rw_to_ro_pre in H0.
    rewrite (tedious_equiv_1) in H0.
    unfold rw_to_ro_pre in H.
    rewrite (tedious_equiv_2 x) in H.
    rewrite tedious_equiv_1 in H.
    simpl in H.
    pose proof (H0 H).

    clear f wty_l f0 H H0 ψ θ w ϕ.
    induction l.
    dependent induction ϕi.
    simpl in H1.
    contradict H1.
    
    
    dependent destruction ϕi.
    simpl.
    simpl in H1.
    destruct H1.
    left.
    rewrite (tedious_equiv_2 x).
    rewrite (tedious_equiv_2 (fst_app x)).
    rewrite eq_sym_app_assoc_tr.
    exact H.
    right.
    apply IHl.
    exact H.
  }

  {
    pose proof (r_proves_ro_tot_ctx_rewrite (app_assoc Δ Δ2 Γ) r).
    pose proof (r_proves_rw_tot_ctx_rewrite_ro (eq_sym (app_assoc Δ2 Γ Δ)) p).
    (* apply (r_admissible_gen_rw_tot _ _ Δ2) in X0. *)

    apply r_admissible_move_rw_tot in X0.
    simpl in X0.
    Check has_type_rw_move (Γ ++ Δ) Δ Δ2 c UNIT
          (tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (eq_sym (app_assoc Δ2 Γ Δ)) wty_c).
    pose proof r_admissible_gen_rw_tot.
    apply (r_admissible_gen_rw_tot _ _ Δ2) in X0.
    pose proof (r_proves_rw_tot_ctx_rewrite_ro (eq_sym (app_assoc Γ Δ Δ2)) X0).
    assert ((Δ2 ++ (Γ ++ Δ ++ Δ2));;; (Δ ) ||- c : UNIT) as www.
    pose proof (has_type_rw_add_auxiliary _ _ _ _ wty_c Δ2).
    rewrite app_assoc.
    rewrite app_assoc.
    exact H.

    pose proof r_admissible_rw_tot_pose_readonly_ext.
    pose proof (r_admissible_rw_tot_pose_readonly_ext _ _ _ _ _ _ www _ _
                  (fun x => fst x = snd_app (snd_app (snd x)))  X2)
    .
    simpl in X4.

    pose proof (r_rw_while_tot _ _ _ _
                          (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (app_assoc Δ Δ2 Γ) wty_e)
                          (tr (fun Γ : ro_ctx => Γ;;; (Δ ++ Δ2) ||- c : UNIT) (eq_sym (app_assoc Γ Δ Δ2))
         (has_type_rw_add_auxiliary (Γ ++ Δ) (Δ ++ Δ2) c UNIT
            (has_type_rw_move (Γ ++ Δ) Δ Δ2 c UNIT
               (tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (eq_sym (app_assoc Δ2 Γ Δ)) wty_c)) Δ2))
                          (has_type_rw_move Γ Δ Δ2 (WHILE e DO c END) UNIT w)
                          (fun x => ϕ (fst_app (fst x), (snd_app (fst x); snd x)))
                          (fun y x => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))
                          (fun x => ψ0 (fst_app (fst x), ((snd_app (fst x) ; fst_app (snd x)); fst_app (snd_app (snd x)))) /\ snd_app (fst x) = snd_app (snd_app (snd x)))

                                        (* ((snd_app (snd_app (snd x)); fst_app (snd x)); fst_app (snd_app (snd x))))) *)
               ).
    assert (tr (fun Γ : ro_ctx => Γ |- e : BOOL) (app_assoc Δ Δ2 Γ) wty_e
       |~ [{rw_to_ro_pre
              (fun x : sem_ro_ctx (Δ ++ Δ2) * sem_ro_ctx Γ => ϕ (fst_app (fst x), (snd_app (fst x); snd x)))}] e [{y
                                                                                                                  | (fun x : sem_ro_ctx ((Δ ++ Δ2) ++ Γ) => θ y (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x))}] ).
    
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite (tedious_equiv_2 h1).
    rewrite (tedious_equiv_2 (fst_app h1)).
    rewrite eq_sym_app_assoc_tr.
    rewrite (tedious_equiv_2 h1) in h2.
    unfold rw_to_ro_pre in h2.
    rewrite tedious_equiv_1 in h2.
    simpl in h2.
    unfold rw_to_ro_pre.
    rewrite tedious_equiv_1.
    exact h2.
    simpl in X5.
    assert (tr (fun Γ : ro_ctx => Γ;;; (Δ ++ Δ2) ||- c : UNIT) (eq_sym (app_assoc Γ Δ Δ2))
         (has_type_rw_add_auxiliary (Γ ++ Δ) (Δ ++ Δ2) c UNIT
            (has_type_rw_move (Γ ++ Δ) Δ Δ2 c UNIT (tr (fun Γ : ro_ctx => Γ;;; Δ ||- c : UNIT) (eq_sym (app_assoc Δ2 Γ Δ)) wty_c)) Δ2)
       ||~ [{(fun δγδ' : sem_ro_ctx (Δ ++ Δ2) * sem_ro_ctx (Γ ++ Δ ++ Δ2) =>
              ro_to_rw_pre (fun x : sem_ro_ctx ((Δ ++ Δ2) ++ Γ) => θ true (tr sem_ro_ctx (eq_sym (app_assoc Δ Δ2 Γ)) x)) (fst δγδ', fst_app (snd δγδ')) /\
              fst δγδ' = snd_app (snd δγδ'))}] c [{_
       | (fun δγδ' : sem_ro_ctx (Δ ++ Δ2) * sem_ro_ctx (Γ ++ Δ ++ Δ2) =>
          ϕ (fst_app (fst δγδ'), (snd_app (fst δγδ'); fst_app (snd δγδ'))) /\
          ψ0 (fst_app (fst δγδ'), ((snd_app (fst δγδ'); fst_app (snd δγδ')); fst_app (snd_app (snd δγδ')))) /\
          snd_app (fst δγδ') = snd_app (snd_app (snd δγδ')))}]).
    simpl in X2.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X4);
      try (intros t1 t2; auto); try (intros t1 t2 t3; auto); simpl.

    unfold ro_to_rw_pre in t2.
    destruct t1.
    simpl.
    simpl in t2.
    unfold ro_to_rw_pre.
    rewrite eq_sym_twice.
    rewrite eq_sym_twice.
    rewrite (tedious_equiv_2 s0).
    rewrite (tedious_equiv_2 (snd_app s0)).
    rewrite app_assoc_tr.
    rewrite tedious_equiv_fst.
    rewrite app_assoc_tr.
    split; destruct t2.
    rewrite (tedious_equiv_2 s) in H.
    rewrite eq_sym_app_assoc_tr in H.
    rewrite tedious_equiv_fst.
    split.
    exact H.
    rewrite tedious_equiv_snd.
    rewrite H0; reflexivity.
    
    rewrite tedious_equiv_snd.
    rewrite tedious_equiv_snd.
    rewrite H0.
    reflexivity.

    destruct t2.
    simpl.
    simpl.
    rewrite (tedious_equiv_2 s0).
    rewrite (tedious_equiv_2 (snd_app s0)).

    rewrite (tedious_equiv_2 s).
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_fst.
    rewrite tedious_equiv_snd.
    rewrite tedious_equiv_snd.
    rewrite tedious_equiv_fst.
    rewrite eq_sym_twice.
    rewrite eq_sym_twice.
    rewrite app_assoc_tr.
    rewrite tedious_equiv_fst.
    rewrite app_assoc_tr.
    rewrite tedious_equiv_fst.
    intro.
    destruct H.
    rewrite tedious_equiv_snd in H0.
    rewrite H0.
    split.
    destruct H.
    rewrite H0 in H.
    exact H.
    split.
    destruct H.
    rewrite <- H0.
    exact H1.
    rewrite <- H0.
    rewrite tedious_equiv_snd.
    reflexivity.

    

    pose proof (X5 X6 X7).

    assert ((forall (δ : sem_ro_ctx (Δ ++ Δ2)) (γ : sem_ro_ctx Γ),
        ϕ (fst_app δ, (snd_app δ; γ)) ->
        ~
        (exists f : nat -> sem_ro_ctx (Δ ++ Δ2),
           f 0 = δ /\
           (forall n : nat,
            ψ0 (fst_app (f (S n)), ((snd_app (f (S n)); fst_app (γ; f n)); fst_app (snd_app (γ; f n)))) /\ snd_app (f (S n)) = snd_app (snd_app (γ; f n)))))).
    intros.
    intro.
    simpl in H.
    simpl in H0.
    pose proof (n _ _ H).
    contradict H1.
    destruct H0.
    exists (fun n => fst_app (x n)).
    destruct H0.
    split.
    rewrite H0; reflexivity.

    intros.
    assert (forall n,  snd_app (x n) = snd_app δ).
    intro.
    induction n1.
    rewrite H0; reflexivity.
    pose proof (H1 n1).
    rewrite tedious_equiv_snd in H2.    
    rewrite tedious_equiv_fst in H2.
    destruct H2.
    
    rewrite H3.
    rewrite IHn1.
    reflexivity.

    
    
    pose proof (H1 n0).
    rewrite tedious_equiv_snd in H3.    
    rewrite tedious_equiv_fst in H3.
    destruct H3.
    rewrite H2 in H3.
    exact H3.

    pose proof (X8 H).

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X9);
      try (intros t1 t2; auto); try (intros t1 t2 t3; auto); simpl.
    intros.
    destruct H0.
    split.
    exact H0.
    destruct t2.
    simpl.
    simpl in H1.
    rewrite (tedious_equiv_2 s) in H1.
    unfold ro_to_rw_pre in H1.
    rewrite eq_sym_app_assoc_tr in H1.
    exact H1.

    
  }
  
Defined.

