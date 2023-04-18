Require Import List.
Require Import Reals.
Require Import Coq.Program.Equality.


Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.
Require Import Clerical.ReasoningAdmissible.

(* Ths file proves the soundnsess of our Reasoning rules.
   The main thoerems are

   Lemma proves_ro_prt_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- {{ϕ}} e {{ψ}} -> w |= {{ϕ}} e {{ψ}}
   with proves_ro_tot_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- [{ϕ}] e [{ψ}] -> w |= [{ϕ}] e [{ψ}]
   with proves_rw_prt_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- {{ϕ}} e {{ψ}} -> w ||= {{ϕ}} e {{ψ}}
   with proves_rw_tot_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- [{ϕ}] e [{ψ}] -> w ||= [{ϕ}] e [{ψ}].

   that comes at the end of this file. Before getting there, in this file we prove various sublemmas
   which include that about finitely branching trees that are used in while loop termination proof.  *)


Fixpoint p_ro_access  Γ k τ (w : r_has_type_ro Γ (Var k) τ) : sem_ro_ctx Γ -> sem_datatype τ.
Proof.
  inversion w.  
  intro.
  simpl in X.
  destruct X.
  exact s.
  intro.
  apply (p_ro_access _ _ _ H1).
  destruct X.
  exact s0.
Defined.
 
Fixpoint ro_access_Var_0 Γ τ (w : (τ :: Γ) |- Var 0 : τ) {struct w} : forall x (γ : sem_ro_ctx Γ), ro_access (τ :: Γ) 0 τ w (x, γ) = x.
Proof.
  intros.
  dependent destruction w.
  dependent destruction h.
  assert (ro_access (τ :: Γ) 0 τ (has_type_ro_rw (τ :: Γ) (VAR 0) τ (has_type_rw_ro (τ :: Γ) nil (VAR 0) τ h)) (x, γ) = ro_access _ _ _ h (x, γ)).
  auto.
  rewrite H.
  apply ro_access_Var_0.
  simpl.
  clear ro_access_Var_0.
  auto.  
Defined.

Fixpoint has_type_ro_Var_S_inv Γ k τ σ (w : (τ :: Γ) |- Var (S k) : σ) : Γ |- Var k : σ.
Proof.
  dependent destruction w.
  dependent destruction h.
  apply (has_type_ro_Var_S_inv _ _ _ _ h).
  exact w.
Defined.

Fixpoint ro_access_Var_S Γ k τ σ (w : (τ :: Γ) |- Var (S k) : σ) {struct w} : forall x (γ : sem_ro_ctx Γ),
    ro_access (τ :: Γ) (S k) σ w (x, γ) = ro_access Γ k σ (has_type_ro_Var_S_inv _ _ _ _ w) γ .
Proof.
  intros.
  dependent destruction w.
  dependent destruction h.
  assert (ro_access (τ :: Γ) (S k) τ0 (has_type_ro_rw (τ :: Γ) (VAR S k) τ0 (has_type_rw_ro (τ :: Γ) nil (VAR S k) τ0 h)) (x, γ) = ro_access _ _ _ h (x, γ)).
  auto.
  rewrite H.
  assert ((has_type_ro_Var_S_inv Γ k τ τ0 (has_type_ro_rw (τ :: Γ) (VAR S k) τ0 (has_type_rw_ro (τ :: Γ) nil (VAR S k) τ0 h))) = (has_type_ro_Var_S_inv Γ k τ τ0 h)).
  simpl.
  unfold simplification_heq.
  unfold solution_left.
  unfold eq_rect_r.
  simpl.
  
  rewrite (prop_irrl _ (eq_sym _) eq_refl).
  simpl.
  auto.
  rewrite H0.
  apply ro_access_Var_S.
  simpl.
  
  unfold eq_rect_r.
  simpl.  
  unfold simplification_heq.
  unfold solution_left.
  unfold eq_rect_r.
  rewrite (prop_irrl _ (eq_sym _) eq_refl).
  simpl.
  rewrite (prop_irrl _ (eq_sym _) eq_refl).
  simpl.
  auto.
Defined.

Lemma ro_access_typing_irrl k : forall Γ τ (w1 : Γ |- Var k : τ) (w2 : Γ |- Var k : τ) γ, ro_access Γ k τ w1 γ = ro_access Γ k τ w2 γ.
Proof.
  dependent induction k; intros.
  destruct Γ.
  contradict w1.
  intro.
  apply has_type_ro_r_has_type_ro in w1.
  apply r_has_type_ro_Var_absurd in w1.
  auto.
  simpl in γ.
  destruct γ.
  pose proof (has_type_ro_unambiguous _ _ _ _ w1 (has_type_ro_Var_0 Γ d)).
  induction H.
  rewrite (ro_access_Var_0 Γ τ w1 ).
  rewrite (ro_access_Var_0 Γ τ w2 ).
  auto.
  destruct Γ.
  contradict w1.
  intro.
  apply has_type_ro_r_has_type_ro in w1.
  apply r_has_type_ro_Var_absurd in w1.
  auto.
  simpl in γ.
  destruct γ.
  rewrite ro_access_Var_S.
  rewrite ro_access_Var_S.
  apply (IHk _ _ (has_type_ro_Var_S_inv Γ k d τ w1) (has_type_ro_Var_S_inv Γ k d τ w2)).
Defined.

Fixpoint Var_sem_ro_access_equiv k Γ τ (w : Γ |- Var k : τ) γ {struct w}: 
    sem_ro_exp _ _ _ w γ = pdom_unit (ro_access _ _ _ w γ).
Proof.
  intros.
  dependent induction w.
  dependent destruction h.
  easy_rewrite_uip.
  rewrite pdom_lift_comp.
  simpl.
  rewrite pdom_lift_id.
  apply Var_sem_ro_access_equiv.
  easy_rewrite_uip.
  destruct γ; simpl.
  apply eq_refl.
  assert (sem_ro_exp (σ :: Γ) (VAR S k0) τ (has_type_ro_Var_S Γ σ τ k0 w) γ
          = sem_ro_exp Γ (Var k0) τ w (snd γ)).
  simpl.
  auto.
  rewrite H.
  rewrite Var_sem_ro_access_equiv.
  destruct γ.
  rewrite ro_access_Var_S.
  apply lp.
  apply ro_access_typing_irrl.
Defined.

  
Fixpoint proves_ro_prt_Var_sound  k Γ τ (w : Γ |- Var k : τ) ϕ {struct w} :
    w |= {{fun γ => ϕ (ro_access Γ k τ w γ) γ}} Var k {{ϕ}}.
Proof.
  intros γ m.
  rewrite Var_sem_ro_access_equiv.
  simpl.
  split.
  apply (pdom_is_neg_empty_by_evidence _ (total (ro_access Γ k τ w γ))).
  simpl; auto.
  intros p1 p2 p3 p4.
  rewrite p4 in p2.
  apply total_is_injective in p2.
  rewrite <- p2.
  simpl in m.
  auto.
Defined.

Fixpoint proves_ro_tot_Var_sound  k Γ τ (w : Γ |- Var k : τ) ϕ {struct w} :
    w |= [{fun γ => ϕ (ro_access Γ k τ w γ) γ}] Var k [{ϕ}].
Proof.
  intros γ m.
  rewrite Var_sem_ro_access_equiv.
  simpl.
  split.
  apply (pdom_is_neg_empty_by_evidence _ (total (ro_access Γ k τ w γ))).
  simpl; auto.
  intros p1 p2.
  exists (ro_access _ _ _ w γ); split; auto.  
Defined.

Lemma update_assignable_irrl : forall k Δ τ  x δ (a1 a2 : assignable Δ τ k),
    update k x δ a1 = update k x δ a2.
Proof.
  intro k.
  dependent induction k.
  intros.
  dependent destruction a1.
  dependent destruction a2; auto.
  intros.
  dependent destruction a1.
  dependent destruction a2; auto.
  destruct δ.
  assert (
      (@update τ (@cons datatype σ Δ) (S k) x (@pair (sem_datatype σ) (sem_list_datatype Δ) s s0) (assignable_S Δ τ σ k a1))
            = (s, update k x s0 a1)). 
  simpl.
  unfold update.
  unfold assignable_rect.
  destruct a1; auto.
  assert (
      (@update τ (@cons datatype σ Δ) (S k) x (@pair (sem_datatype σ) (sem_list_datatype Δ) s s0) (assignable_S Δ τ σ k a2))
            = (s, update k x s0 a2)). 
  simpl.
  unfold update.
  unfold assignable_rect.
  destruct a2; auto.
  rewrite H, H0; auto.
  assert (update k x s0 a1 = update k x s0 a2).
  apply IHk.
  rewrite H1; auto.
Defined.

Lemma update'_typing_irrl_2 Γ Δ k e τ (w1 w2 : (Δ ++ Γ) |- e : τ) (w' : Γ ;;; Δ ||- Assign k e : DUnit) δ x :
  update' w1 w' δ x = update' w2 w' δ x.
Proof.
  unfold update'.
  apply update_assignable_irrl.
Defined.


Lemma proves_rw_prt_Assign_sound
  Γ Δ e k τ ϕ0 (ψ0 :post) θ (w : (Δ ++ Γ) |- e : τ) (w' : Γ ;;; Δ ||- Assign k e : DUnit)  :
  w |= {{(fun δγ : sem_ro_ctx (Δ ++ Γ) => ϕ0 (tedious_sem_app Δ Γ δγ))}} e {{θ}}
  -> (forall x γ δ , θ x (δ; γ) -> ψ0 tt (update' w w' δ x, γ))
  ->  w' ||= {{ϕ0}} Assign k e {{ψ0}}.
Proof.
  intros.
  dependent destruction w'.
  dependent destruction h.
  contradict (has_type_rw_Assign_absurd _ _ _ h).
  intros γ δ m; simpl; simpl in m.
  easy_rewrite_uip.
  split.
  intro.
  apply pdom_lift_empty_2 in H1.
  apply pdom_lift_empty_2 in H1.
  pose proof (H (δ; γ)).
  simpl in H2.
  rewrite tedious_equiv_1 in H2.
  pose proof (H2 m); clear H2.
  destruct H3.
  pose proof (has_type_ro_unambiguous _ _ _ _ h w).
  induction H4.
  rewrite  (sem_ro_exp_unique _ _ _ h w) in H1.
  auto.
  intros h1 h2 h3 h4.
  destruct h2.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct x0.
  simpl in H3.
  rewrite <- H3 in H2.
  simpl in H2.
  rewrite <- H2 in h4.
  contradict (flat_bot_neq_total _ h4).
  simpl in H3.
  rewrite <- H3 in H2.
  simpl in H2.
  rewrite <- H2 in h4.
  apply total_is_injective in h4.
  rewrite <- h4.
  simpl.
  pose proof (H (δ; γ)).
  simpl in H4.
  rewrite tedious_equiv_1 in H4.
  pose proof (H4 m); clear H4.
  destruct H5 as [_ H5].
  pose proof (has_type_ro_unambiguous _ _ _ _ h w).
  induction H4.
  rewrite <- (sem_ro_exp_unique _ _ _ h w) in H5.
  pose proof (H5 (total s) H1 _ eq_refl).
  pose proof (H0 s γ δ H4).
  unfold update' in H6.
  assert (
      update k s δ (assign_wty_assignable Γ Δ k e τ0 w (has_type_rw_Assign Γ Δ e τ0 k a h)) =
        update k s δ a).
  apply update_assignable_irrl.
  rewrite H7 in H6; auto.
Defined.

Lemma proves_rw_tot_Assign_sound
  Γ Δ e k τ ϕ0 (ψ0 :post) θ (w : (Δ ++ Γ) |- e : τ) (w' : Γ ;;; Δ ||- Assign k e : DUnit)  :
  w |= [{(fun δγ : sem_ro_ctx (Δ ++ Γ) => ϕ0 (tedious_sem_app Δ Γ δγ))}] e [{θ}]
  -> (forall x γ δ , θ x (δ; γ) -> ψ0 tt (update' w w' δ x, γ))
  ->  w' ||= [{ϕ0}] Assign k e [{ψ0}].
Proof.
  intros.
  apply sem_ro_tot_is_prt_excludes_bot in H as [h1 h2].
  apply sem_rw_prt_excludes_bot_is_tot.
  apply (proves_rw_prt_Assign_sound _ _ _ _ _ _ _ _ _ _ h1 H0).
  (* non bottom *)
  intros.
  dependent destruction w'.
  dependent destruction h.
  contradict (has_type_rw_Assign_absurd _ _ _ h).
  simpl.
  intro.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct x0.

  pose proof (has_type_ro_unambiguous _ _ _ _ h w).
  induction H4.
  rewrite  (sem_ro_exp_unique _ _ _ h w) in H1.
  pose proof (h2 (δ; γ)).
  rewrite tedious_equiv_1 in H4.
  apply (H4 H H1).
  
  pose proof (has_type_ro_unambiguous _ _ _ _ h w).
  induction H4.
  rewrite  (sem_ro_exp_unique _ _ _ h w) in H1.
  simpl in H3.
  rewrite <- H3 in H2.
  simpl in H2.
  contradict (flat_total_neq_bot _ H2).
Defined.

Lemma proves_rw_while_prt_sound : forall Γ Δ  e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ,   
    wty_e |= {{rw_to_ro_pre ϕ}} e {{θ}} ->
    wty_c ||= {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||= {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}}.
Proof.
  intros Γ Δ e c wty_e wty_c wty ϕ θ BB CC.
  intros γ δ m; simpl; simpl in m.
  pose (fun d => sem_ro_exp _ _ _ wty_e (d; γ)) as B.
  pose (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ wty_c γ d)) as C.
      replace (sem_rw_exp Γ Δ (WHILE e DO c END) UNIT wty γ δ) with
        (pdom_lift (fun x => (x, tt)) (pdom_while B C δ))
        by (rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_While _ _ _ _ wty_e  wty_c)); simpl; auto).
      assert ( (rw_to_ro_pre ϕ) (δ; γ)) as m'
          by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
      pose proof (BB _ m') as [p1 p2].

      (* important sub lemmas *)
      pose (fun n δ => pdom_fun_bot_chain (pdom_W B C) (pdom_W_monotone B C) n δ) as thechain.
      (* the chain respects invariant *)
      assert (forall n, forall δ1 δ2, ϕ (δ1, γ) -> total δ2 ∈ thechain n δ1 -> ϕ (δ2, γ) /\ ro_to_rw_pre (θ false) (δ2, γ)) as l.
      {
        (* base *)
        intro n.
        induction n.
        intros.
        simpl in H0.
        contradiction (flat_bot_neq_total _ H0).
        (* induction step *)
        intros.
        simpl in H0.
        destruct H0 as [h1 [h2 [[h3 h4] | [h3 h4]]]].
        contradict (flat_total_neq_bot _ h3).
        destruct h4 as [H1 [b [H3 H4]]].
        destruct b.
        simpl in H4.
        contradiction (flat_bot_neq_total _ H4).
        simpl in H4.
        destruct b.
        apply total_is_injective in H4.
        rewrite <- H4 in H1; clear H4.
        apply pdom_bind_total_2 in H1 as [_ [d [hh1 hh2]]].
        apply (IHn d δ2).
        assert (rw_to_ro_pre ϕ (δ1; γ))        
          by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
          
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((BB)) true (δ1 ; γ) H0 H3) as m''.
        pose proof (CC _ _ m'') as [_ r2].
        simpl in r2.
        assert (total (d, tt) ∈  sem_rw_exp Γ Δ c UNIT wty_c γ δ1).
        {
          unfold C in hh1.
          apply pdom_lift_total_2 in hh1.
          destruct hh1.
          destruct H1.
          destruct x.
          destruct s0.
          simpl in H2.
          rewrite H2; auto.
        }
        pose proof (r2 (total (d, tt)) H1 _ eq_refl).
        simpl in H2; auto.
        exact hh2.
        apply total_is_injective in H4.
        rewrite <- H4 in H1.
        simpl in H1.
        apply total_is_injective in H1.
        assert (rw_to_ro_pre ϕ (δ1; γ))        
          by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
        
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((BB)) false (δ1 ; γ) H0 H3) as m''.
        rewrite <- H1; split; auto.
      }

      (* nondempty *)
      assert (forall n, forall δ1, ϕ (δ1, γ) -> ~ pdom_is_empty (thechain n δ1)) as r.
      {
        intro n.
        induction n.
        intros.
        simpl.
        apply (pdom_is_neg_empty_by_evidence _ (bot _)); simpl; auto.

        intros.
        simpl.
        pose proof (IHn _ H).
        apply pdom_neg_empty_exists in H0 as [δ' h1].
        intro.
        unfold pdom_W in H0.
        apply pdom_bind_empty_2 in H0.
        destruct H0.
        assert ( (rw_to_ro_pre ϕ) (δ1; γ)) as m''
            by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).

        pose proof (BB _ m'') as [h _]; auto.
        destruct H0.
        destruct H0.
        destruct x.
        apply pdom_bind_empty_2 in H1.
        destruct H1.
        unfold C in H1.
        apply pdom_lift_empty_2 in H1.
        assert ( (rw_to_ro_pre ϕ) (δ1; γ)) as m''
            by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).

        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((BB)) true (δ1 ; γ) m'' H0) as m'''.
        pose proof (CC _ _ m''') as [r1 _].
        auto.
        destruct H1.
        destruct H1.
        apply (fun k => IHn x k H2).
        assert ( (rw_to_ro_pre ϕ) (δ1; γ)) as m''
            by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).

        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((BB)) true (δ1 ; γ) m'' H0) as m'''.
        pose proof (CC _ _ m''') as [_ r2].
        unfold C in H1.
        apply pdom_lift_total_2 in H1.
        destruct H1.
        destruct H1.
        destruct x0.
        destruct s0.
        simpl in H3.
        induction H3.
        pose proof (r2 (total (x, tt)) H1 _ eq_refl).
        simpl in H3.
        auto.
        contradict H1.
        apply (pdom_is_neg_empty_by_evidence _ (total δ1)); simpl; auto.
      }
      split.
      intro.
      apply pdom_lift_empty_2 in H.
      unfold pdom_while in H.
      unfold pdom_fun_lfp in H.
      apply pdom_fun_chain_empty_2 in H as [n h].
      apply (r n δ m h).
      intros.
      rewrite H0 in H; clear H0.
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      unfold pdom_while in H.
      unfold pdom_fun_lfp in H.
      unfold pdom_fun_chain_sup in H.
      apply pdom_chain_membership_2 in H as [n h].
      
      pose proof (l n δ x m h).
      rewrite H0 ; simpl; auto.
Defined.

(* Now let us detour and proves some properties of finitely branchign trees
   that will establish termination of while loops later in the total correctness
   proof. *)
Section FinitelyBranchingTree.

  Definition E_tree_is_fin {X} (E : X -> X -> Prop) :=
    forall x, ~ infinite {y | E x y}.

  Inductive E_finite_chain {X} (E : X -> X -> Prop) x : nat -> Type :=
    nil_chain : E_finite_chain E x 0
  | cons_chain : forall n y, E x y -> E_finite_chain E y n -> E_finite_chain E x (S n).

  Definition E_is_infinite_chain {X} (E : X -> X -> Prop) x f : Prop
    := f O = x /\ forall n, E (f n) (f (S n)).

  Definition E_finite_chains {X} (E : X -> X -> Prop) x := {n : nat & E_finite_chain E x n}.

  Definition E_finite_chains_next {X} (E : X -> X -> Prop) x (c : E_finite_chains E x) :
    projT1 c <> O -> {y & (E x y * E_finite_chains E y)%type}.
  Proof.
    intros.
    destruct c.
    destruct x0.
    dependent destruction e.
    simpl in H; contradict H; auto.
    dependent destruction e.
    exists y.
    split; auto.
    exists x0.
    auto.
  Defined.

  Lemma E_infinite_finite_chains_S_aux1 :   forall {X} (E : X -> X -> Prop) (x : X),
      {y' : {y : X | E x y} &  (E_finite_chains E (proj1_sig y'))} ->
      E_finite_chains E x.
  Proof.
    intros.
    destruct X0.
    destruct x0.
    simpl in e.
    destruct e.
    exists (S x1).
    exact (cons_chain _ _ _ _ e0 e).
  Defined.

  Lemma E_infinite_finite_chains_S_aux2 :forall {X} (E : X -> X -> Prop) (x : X),
      {y' : {y : X | E x y} & E_finite_chains E (proj1_sig y')} -> {c : E_finite_chains E x | projT1 c <> O}.
  Proof.
    intros.
    destruct X0.
    destruct x0.
    simpl in e.
    destruct e.
    exists (existT (S x1) (cons_chain _ _ _ _ e0 e)).
    simpl.
    auto.
  Defined.

  Open Scope nat_scope.

  Lemma E_infinite_finite_chains_S :
    forall {X} (E : X -> X -> Prop), E_tree_is_fin E -> forall (x : X),  
        infinite (E_finite_chains E x) -> exists y, E x y /\ infinite (E_finite_chains E y).
  Proof.
    intros X E fin x H.
    assert (infinite {y' : {y | E x y} & (E_finite_chains E (proj1_sig y'))}).
    {
      assert (infinite {c : E_finite_chains E x | projT1 c <> 0}).
      {
        assert (infinite {c : E_finite_chains E x | projT1 c = 0 \/ projT1 c <> 0}).
        {
          destruct H.
          exists (fun n => exist _ (x0 n) (lem _)).
          intros i j e.
          injection e; intros.
          apply H; auto.
        }
        apply Pigeon2' in H0.
        destruct H0; auto.
        destruct H0 as [f i].
        case_eq (f 0); intros.
        case_eq (f 1); intros.
        assert (x0 = x1).
        destruct x0.
        destruct x1.
        simpl in e, e0.
        clear H0.
        clear H1.
        induction (eq_sym e0).
        induction (eq_sym e).
        dependent destruction e1.
        dependent destruction e2.
        auto.
        induction H2.
        assert (f 0 = f 1).
        rewrite H0, H1.
        apply sig_eq.
        simpl; auto.
        apply i in H2.
        contradict H2; auto.
      }
      apply (fun f => surjection_infinite2 f H0).
      exists (E_infinite_finite_chains_S_aux2 E x).
      intro.
      destruct b.
      destruct x0.
      simpl in n.
      
      assert (exists n, S n = x0).
      exists (pred x0).
      apply Nat.succ_pred; auto.
      destruct H1.
      induction H1.
      dependent destruction e.
      exists (existT (exist _ y e) (existT x1 e1)).
      simpl.
      apply sig_eq.
      simpl.
      auto.
    }
    apply Pigeon in  H0.
    destruct H0.
    contradict (fin _ H0).
    destruct H0.
    destruct x0.
    exists x0.
    split; auto.
  Defined.

  Lemma E_unbounded_tree_has_infinite_path :
    forall {X} (E : X -> X -> Prop), E_tree_is_fin E -> forall (x : X),
        (forall n, exists c : E_finite_chain E x n, True) ->
        exists f, E_is_infinite_chain E x f.
  Proof.
    intros X E fin x H.
    assert (infinite (E_finite_chains E x)).
    pose proof (dcchoice _ _ H).
    simpl in H0.
    destruct H0.
    exists (fun n => existT n (x0 n)).
    intros i j e.
    injection e; intro; auto.
    pose proof (
           dchoice_start (fun _ => {x & infinite (E_finite_chains E x)})
                         (fun n p q => E (projT1 p) (projT1 q))
                         (existT x H0)) as [f h].
    intros.
    destruct x0 as [y i].
    
    pose proof (E_infinite_finite_chains_S E fin y i) as [y' [h1 h2]].
    exists (existT y' h2).
    simpl.
    auto.
    exists (fun n => projT1 (f n)).
    destruct h; split; auto.
    rewrite H1; auto.
  Defined.

End FinitelyBranchingTree.

Open Scope nat_scope.
Lemma pdom_While_bot {X} (b : X -> pdom bool) (c : X -> pdom X)
      (ϕ : X -> Prop) (θ : bool -> X -> Prop) (ψ : X -> X -> Prop) :
  (forall x, ϕ x ->
        ~ pdom_is_empty (b x) /\ forall v, v ∈ b x -> exists v', v = total v' /\ θ v' x)
  ->
    (forall x, θ true x ->
          ~ pdom_is_empty (c x) /\ forall v, v ∈ c x -> exists v', v = total v' /\ ϕ v' /\ ψ x v')
  ->
    forall x, ϕ x ->
         ⊥ ∈ pdom_while b c x -> exists f, E_is_infinite_chain ψ x f. 
    
Proof.
  intros H H0 x mem H1.
  assert (exists f, E_is_infinite_chain
                 (
                   fun y z => ϕ y /\  ϕ z /\ total true ∈ b y /\ total z ∈ c y /\ ψ y z) x f).
  {
    apply E_unbounded_tree_has_infinite_path.
    {
      (* proving the tree is finitely branching *)
      intro.
      intro.
      assert (θ true x0 /\ ϕ x0).
      destruct H2.
      destruct (x1 0).
      destruct a.
      destruct H4; split; auto.
      destruct H5.
      pose proof (H x0 H3) as [_ p].
      pose proof (p _ H5).
      destruct H7.
      destruct H7.
      apply total_is_injective in H7.
      rewrite H7; auto.
      destruct H3.
      pose proof (H0 _ H3) as [p1 p2].
      assert (⊥ ∉ c x0).
      intro.
      pose proof (p2 _ H5).
      destruct H6.
      destruct H6.
      contradict (flat_bot_neq_total _ H6).
      assert (pset_infinite (proj1_sig (c x0))).
      destruct H2.
      exists (fun n => total (proj1_sig (x1 n))).
      split.
      intros i n e.
      apply total_is_injective in e.
      apply proj1_sig_injective in e.
      apply H2 in e; auto.
      intro.
      destruct (x1 n).
      simpl.
      destruct a as [a [b' [c' [d e]]]]; auto.
      destruct (c x0); simpl in H6, H5.
      apply (H5 (p H6)).
    }

    {

      
      assert (
          forall n, 
          forall x : X,
            ϕ x ->
            (⊥ ∈ pdom_fun_bot_chain (pdom_W b c) (pdom_W_monotone b c) n x) ->
            exists _ : E_finite_chain (fun y z : X => ϕ y /\ ϕ z /\ (total true ∈ b y) /\ (total z ∈ c y) /\ ψ y z) x n, True
        ).

      {
        intro n.
        induction n.
        intros.
        exists (nil_chain _ _); auto.
        
        intros.
        simpl in H3.
        destruct H3 as [_ [_ [[_ h2] |h3]]].
        destruct h2.
        destruct H3.
        destruct x1.
        pose proof (H _ H2) as [_ h].
        pose proof (h _ H3) as [p [q r]].
        contradict (flat_bot_neq_total _ q).
        simpl in H4.
        contradict (flat_total_neq_bot _ H4).
        destruct h3.
        destruct H3.
        destruct H4.
        destruct H4.
        destruct x2.
        simpl in H5.
        contradict (flat_bot_neq_total _ H5).
        simpl in H5.
        assert (θ b0 x0) as t.
        pose proof (H x0 H2) as [_ p].
        pose proof (p _ H4) as [t1 [t2 t3]].
        apply total_is_injective in t2.
        rewrite t2; auto.
        
        destruct b0.
        apply total_is_injective in H5.
        rewrite <- H5 in H3.
        clear H5.
        apply pdom_bind_bot_2 in H3.
        destruct H3.
        pose proof (H0 x0 t) as [_ p].
        pose proof (p _ H3) as [t1 [t2 [t3 t4]]].
        contradict (flat_bot_neq_total _ t2).
        destruct H3.
        destruct H3.
        pose proof (H0 x0 t) as [_ p].
        pose proof (p _ H3) as [t1 [t2 [t3 t4]]].
        apply total_is_injective in t2.
        induction t2.
        pose proof (IHn x2 t3 H5).
        destruct H6 as [H6 _].
        assert (ϕ x0 /\ ϕ x2 /\ (total true ∈ b x0) /\ (total x2 ∈ c x0) /\ ψ x0 x2).
        repeat split; auto.
        exists (cons_chain _ _ _ _ H7 H6); auto.
        apply total_is_injective in H5.
        rewrite <- H5 in H3.
        simpl in H3.
        contradict (flat_total_neq_bot _ H3).
      }
      intros.
      pose proof (H2 n x mem).

      unfold pdom_while in H1.
      unfold pdom_fun_lfp in H1.
      unfold pdom_fun_chain_sup in H1.
      pose proof (pdom_chain_bot_2 _ _ H1 n).
      exact (H3 H4).   
    }
  }
  destruct H2.
  exists x0.
  destruct H2.
  split; auto.
  intro.
  destruct (H3 n) as [_ [_ [_ [_ h]]]]; auto.
Defined. 

Lemma proves_rw_while_tot_sound :
  forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ, 
    wty_e |= [{rw_to_ro_pre ϕ}] e [{θ}] ->
    wty_c ||= [{fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] c [{fun _ δγδ' => ϕ (fst δγδ', fst_app (snd δγδ')) /\ ψ δγδ' }] ->
    (forall δ γ, ϕ (δ, γ) ->
            ~exists f : nat -> sem_ro_ctx Δ,
                f 0 = δ /\ forall n, ψ (f (S n), (γ ; f n))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    wty ||= [{ϕ}] While e c [{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}].
Proof.
  intros Γ Δ e c wty_e wty_c wty ϕ θ ψ BB CC chainp.
  apply sem_rw_prt_excludes_bot_is_tot.
  
  apply (proves_rw_while_prt_sound _ _ _ _ wty_e (has_type_while_inv_body _ _ _ _ wty)).
  apply sem_ro_tot_is_prt_excludes_bot in BB as [BB _]; auto.

  intros γ δ m; simpl; simpl in m.
  rewrite
    (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wty_c γ δ δ).
  pose proof (CC (γ; δ) δ).
  simpl in H.
  assert (ro_to_rw_pre (θ true) (δ, fst_app (γ; δ)) /\ δ = snd_app (γ; δ)).
  unfold fst_app, snd_app.
  rewrite tedious_equiv_1.
  split; auto.
  apply H in H0.
  destruct H0; split; auto.
  intro.
  pose proof (H1 v).
  unfold fst_app in H2; rewrite tedious_equiv_1 in H2.
  intro.
  pose proof (H2 H3).
  destruct H4.
  intros.
  destruct H4.
  rewrite H5 in H4.
  apply total_is_injective in H4.
  destruct H6.
  rewrite H4; auto.
  intros.


  (* non empty *)
  pose (fun d => sem_ro_exp _ _ _ wty_e (d ; γ)) as B.
  pose (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ (has_type_while_inv_body _ _ _ _ wty) γ d)) as C.
  replace (sem_rw_exp Γ Δ (WHILE e DO c END) UNIT wty γ δ) with
    (pdom_lift (fun x => (x, tt)) (pdom_while B C δ))
  by (
  rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_While _ _ _ _ wty_e
                                                             (has_type_while_inv_body _ _ _ _ wty))); simpl; auto).
  intro p.
  pose proof
       (pdom_While_bot B C
                       (fun d => ϕ (d, γ))
                       (fun b d => θ b (d; γ))
                       (fun d d' => ψ (d', (γ; d)))
       )
    as [f h].
  {
    intros x m.
    pose proof (BB (x; γ)).
    simpl in H0.
    unfold rw_to_ro_pre in H0.
    rewrite tedious_equiv_1 in H0.
    pose proof (H0 m).
    auto.
  }

  intros x m.
  pose proof (CC (γ; x) x).
  simpl in H0.
  unfold ro_to_rw_pre in H0.
  unfold fst_app, snd_app in H0.
  rewrite tedious_equiv_1 in H0.
  pose proof (H0 (conj m eq_refl)).
  destruct H1; split; auto.
  intro.
  unfold C in H3.
  apply pdom_lift_empty_2 in H3.
  rewrite
    (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wty_c γ x x) in H3.
  auto.
  
  
  intros.
  destruct v.
  unfold C in H3.
  apply pdom_lift_bot_2 in H3.
  rewrite
    (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wty_c γ x x) in H3.
  pose proof (H2 _ H3).
  destruct H4 as [t1 [t2 t3]].
  contradict (flat_bot_neq_total _ t2).
  unfold C in H3.
  apply pdom_lift_total_2 in H3.
  destruct H3.
  destruct H3.
  destruct x0.
  destruct s1.
  simpl in H4.
  induction H4.
  rewrite
    (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wty_c γ x x) in H3.
  pose proof (H2 _ H3).
  destruct H4 as [t1 [t2 [t3 t4]]].
  apply total_is_injective in t2.
  exists s; split; auto.
  rewrite <- t2 in t3, t4; simpl in t3, t4.
  split; auto.
  exact H.
  apply pdom_lift_bot_2 in p.
  auto.

  
  destruct h.
  pose proof (chainp δ γ H).
  contradict H2.
  exists f.
  split; auto.
Defined.

Lemma proves_ro_prt_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- {{ϕ}} e {{ψ}} -> w |= {{ϕ}} e {{ψ}}
with proves_ro_tot_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- [{ϕ}] e [{ψ}] -> w |= [{ϕ}] e [{ψ}]
with proves_rw_prt_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- {{ϕ}} e {{ψ}} -> w ||= {{ϕ}} e {{ψ}}
with proves_rw_tot_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- [{ϕ}] e [{ψ}] -> w ||= [{ϕ}] e [{ψ}].
Proof.
  + (*  partial correctness triple for read only expressions *)
    intros Γ e τ w ϕ ψ trip.
    induction trip.
    (** logical rules *)
    (* (*  partial correctness triple for read only expressions *) *)
    (* (** logical rules *) *)

    ++
      (* | ro_imply_prt : forall Γ e τ (w : Γ |- e : τ) P Q P' Q', *)
      
      (*     P' ->> P ->  *)
      (*     w |- {{ P }} e {{ Q }} ->  *)
      (*     Q ->>> Q' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{ P'}}  e {{ Q' }} *)


      intros γ m.
      simpl; simpl in m.
      apply a in m.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as H.
      simpl in H.
      split; destruct H as [h1 h2]; auto.
      intros t1 t2 t3 t4.
      apply a0, (h2 _ t2 _ t4).
      
    ++
      (* | ro_exfalso_prt : forall Γ e τ (w : Γ |- e : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*)     *)
      (*     w |- {{ (fun _ => False) }} e {{ Q }} *)
      intros γ m.
      simpl in m.
      contradict m; auto.
      
    ++
      (* | ro_conj_prt : forall Γ e τ (w : Γ |- e : τ) P Q Q', *)

      (*     w |- {{P}} e {{Q}} ->  *)
      (*     w |- {{P}} e {{Q'}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{P}} e {{Q /\\\ Q'}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as H1; simpl in H1.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as H2; simpl in H2.
      destruct H1 as [a p1]; destruct H2 as [_ p2]; split; auto.
      intros v p v' p'.
      split; try apply (p1 v p v' p'); try apply (p2 v p v' p').

    ++
      (* | ro_disj_prt : forall Γ e τ (w : Γ |- e : τ) P P' Q, *)

      (*     w |- {{P}} e {{Q}} ->  *)
      (*     w |- {{P'}} e {{Q}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{P \// P'}} e {{Q}} *)
    
      intros γ m; simpl in m; simpl.
      destruct m as [m|m]. 
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2]; split; auto.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [p1 p2]; split; auto.

    ++
      (* (** variables and constants *) *)
      (* | ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{fun γ => Q (ro_access Γ k τ w γ) γ}} VAR k {{Q}} *)

      apply proves_ro_prt_Var_sound.
      
    ++
      (* | ro_skip_prt : forall Γ (w : Γ |- SKIP : UNIT) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q tt}} SKIP {{Q}} *)
      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique Γ SKIP UNIT w (has_type_ro_Skip _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      destruct p3; auto.
      
    ++
      (* | ro_true_prt : forall Γ (w : Γ |- TRUE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q true}} TRUE {{Q}} *)
      
      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique _ _ _ w (has_type_ro_True _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* | ro_false_prt : forall Γ (w : Γ |- FALSE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q false}} FALSE {{Q}} *)


      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique _ _ _ w (has_type_ro_False _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* | ro_int_prt : forall Γ k (w : Γ |- INT k : INTEGER) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q k}} INT k {{Q}} *)


      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique _ _ _ w (has_type_ro_Int _ _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | rw_ro_prt : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ), *)
      
      (*     w ||- {{P}} c {{Q}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{fun γ => P (tt, γ)}} c {{fun v w => Q v (tt, w)}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p γ tt m) as [p1 p2].
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_rw _ _ _ w)).
      simpl.
      split.
      intro h.
      apply pdom_lift_empty_2 in h.
      apply (p1 h).
      intros x1 [x2 [q1 q2]] x3 x4.
      apply (p2 x2 q1 (tt, x3)).
      destruct x1.
      contradict (flat_bot_neq_total _ x4).
      destruct x2.
      simpl in q2.
      contradict (flat_bot_neq_total _ q2).
      injection x4; intro i.
      simpl in q2; injection q2; intro j.
      rewrite i in j.
      rewrite <- j.
      destruct p0, u; simpl; auto.
    ++
    (* (** restricting auxiliary variables *) *)
    (* | ro_proj_prt : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
    (*     w' |- {{ϕ}} e {{ψ}} -> *)
    (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
    (*     w |- {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}} *)
      intros γ [γ' m]; simpl in m; simpl.
      
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip (γ; γ')  m) as [p1 p2].
      split.
      rewrite <- (sem_ro_exp_auxiliary_ctx _ _ _ _ w) in p1; auto.
      intros h1 h2 h3 h4.
      exists γ'.
      rewrite <- (sem_ro_exp_auxiliary_ctx _ _ _ _ w) in p2; auto.
      pose proof (p2 h1 h2 _ h4).
      simpl in H; auto.
      
      
    ++
      (* (** coercion and exponentiation *) *)
      (* | ro_coerce_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL), *)
      
      (*     w |- {{P}} e {{y | Q (IZR y)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} RE e {{Q}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZRcoerce  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      injection H0; intro j; clear H0.
      induction j.
      destruct H as [a [b c]].
      destruct a.
      simpl in c.
      contradict (flat_bot_neq_total _ c).
      pose proof (p2 _ b z (eq_refl)) as h.
      simpl in h.
      simpl in c.
      injection c; intro i; rewrite <- i; exact h.

    ++
      (* | ro_exp_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- EXP e : REAL), *)
      
      (*     w |- {{P}} e {{y | Q (powerRZ 2 y)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} EXP e {{Q}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZRexp  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      injection H0; intro j; clear H0.
      induction j.
      destruct H as [a [b c]].
      destruct a.
      simpl in c.
      contradict (flat_bot_neq_total _ c).
      pose proof (p2 _ b z (eq_refl)) as h.
      simpl in h.
      simpl in c.
      injection c; intro i; rewrite <- i; exact h.
      
    ++
      (* (** integer arithmetic  *) *)
      (* | ro_int_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)-> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*      w' |- {{ϕ}} e1 :+: e2 {{ψ}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZplus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ (e1 :+: e2) INTEGER w' γ
              =
                pdom_lift2 (BinInt.Z.add) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZplus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).
               
      
    ++
      (* | ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :*: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZmult _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ (e1 :*: e2) INTEGER w' γ
              =
                pdom_lift2 (BinInt.Zmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZmult _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :-: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZminus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ (e1 :-: e2) INTEGER w' γ
              =
                pdom_lift2 (BinInt.Zminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZminus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* (** real arithmetic  *) *)
      (* | ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;+; e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRplus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ (e1 ;+; e2) REAL w' γ
              =
                pdom_lift2 (Rplus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRplus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;*; e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRmult _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ _ _ w' γ
              =
                pdom_lift2 (Rmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRmult _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post), *)

      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;-; e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRminus _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ _ _ w' γ
              =
                pdom_lift2 (Rminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRminus _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* (** reciprocal *) *)
      (* | ro_recip_prt : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ, *)

      (*     w |- {{ϕ}} e {{θ}} ->  *)
      (*     (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} UniOp OpRrecip e {{ψ}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      split.
      {
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRrecip  _ _ w)).
        simpl.
        intro.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (p1 H).
        destruct H as [x p].
        destruct p as [p q].
        unfold Rrecip in q.
        contradict q.
        destruct (Rrecip' x).
        apply (pdom_is_neg_empty_by_evidence _ (bot R)); simpl; auto.
        apply (pdom_is_neg_empty_by_evidence _ (total r)); simpl; auto.
      }
      intros v h1 h2 h3.
      assert (sem_ro_exp Γ (;/; e) REAL w' γ =
                pdom_bind Rrecip (sem_ro_exp Γ e REAL w γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRrecip  _ _ w)); simpl; auto.
      rewrite H in h1; clear H.
      simpl in p2.
      rewrite h3 in h1; rename h3 into j.
      apply pdom_bind_total_2 in h1.
      destruct h1 as [_ h1].
      destruct h1 as [x h].
      destruct h as [h1 h3].
      unfold Rrecip in h3.
      unfold Rrecip' in h3.
      destruct (total_order_T x 0).
      destruct s.
      {
        (* when x < 0 *)     
        unfold asrt_and2 in a.
        assert (H : x <> 0%R) by (apply Rlt_not_eq, r). 
        pose proof (a x γ (conj (p2 _ h1 x eq_refl) H)) as jj.
        simpl in jj; simpl in H; simpl in h3.
        injection h3; intro i; rewrite i in jj; auto.
      }
      {
        (* when x = 0 *)
        simpl in h3.
        contradict (flat_bot_neq_total _ h3).
      }
      {
        (* when x > 0 *)     
        unfold asrt_and2 in a.
        assert (H : x <> 0%R) by (apply Rgt_not_eq, r). 
        pose proof (a x γ (conj (p2 _ h1 x eq_refl) H)) as jj.
        simpl in jj; simpl in H; simpl in h3.
        injection h3; intro i; rewrite i in jj; auto.
      }

    ++
      (* (** integer exparison  *) *)
      (* | ro_int_exp_eq_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post), *)

      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :=: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZeq _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ _ _ w' γ
              =
                pdom_lift2 (BinInt.Z.eqb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZeq _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_int_exp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post), *)

      (*     w1 |- {{P}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{P}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} (e1 :<: e2) {{ψ}} *)


      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZlt _ _ _ w1 w2)); simpl.      
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [H1 H2]; destruct H2 as [H2 H3].
        apply pdom_lift_empty_2 in H3.
        apply (p1 H3).        
      }
      intros.
      assert (sem_ro_exp Γ _ _ w' γ
              =
                pdom_lift2 (BinInt.Z.ltb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZlt _ _ _ w1 w2)); simpl.      
      auto.
      rewrite H1 in H.
      clear H1.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      contradict (flat_bot_neq_total _ H0).
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      apply pdom_bind_total_2 in H.
      destruct H.
      clear H.
      destruct H2.
      destruct H.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      destruct H2.
      injection H0; intro j; induction j; clear H0.
      rewrite H3 in H1; simpl in H1.
      rewrite H1; apply (ψ3 x1 x0 _ (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* (** real exparison  *) *)
      (* | ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) P ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post), *)
      
      (*     w1 |- {{P}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{P}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} (e1 ;<; e2) {{ψ}} *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRlt _ _ _ w1 w2)); simpl.      
        intro.
        unfold pdom_bind2 in H.
        apply pdom_bind_empty_2 in H.
        unfold pdom_prod in H.
        destruct H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H.
        destruct H.
        apply pdom_lift_empty_2 in H0.
        apply (p1 H0).
        destruct H.
        destruct H.
        unfold Rltb in H0.
        contradict H0.
        apply flat_to_pdom_neg_empty.
      }
      
      intros v h1 h2 h3.
      assert (sem_ro_exp Γ _ _ w' γ  = pdom_bind2 Rltb (sem_ro_exp Γ e1 REAL w1 γ) (sem_ro_exp Γ e2 REAL w2 γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRlt _ _ _ w1 w2)); simpl; auto.
      rewrite H in h1; clear H.
      rewrite h3 in h1.
      unfold pdom_bind2 in h1.
      apply pdom_bind_total_2 in h1.
      destruct h1.
      destruct H0.
      destruct H0.
      destruct x.
      unfold pdom_prod in H0.
      apply pdom_bind_total_2 in H0.
      destruct H0.
      destruct H2.
      destruct H2.
      simpl in H3.
      destruct H3.
      simpl in H1.
      unfold Rltb' in H1.
      unfold Rltb'' in ψ3.
      clear H H0.
      destruct H3.
      destruct x0.
      simpl in H0.
      contradict (flat_bot_neq_total _ H0).
      simpl in H0.
      injection H0; intros i j.
      induction i, j.
      
      pose proof (ψ3 r1 x γ (p2 _ H _ eq_refl) (q2 _ H2 _ eq_refl)).
      destruct (total_order_T r1 x).
      destruct s.
      injection H1; intro i; rewrite <- i; apply H3; apply Rlt_not_eq; apply r.
      contradict (flat_bot_neq_total _ H1).
      injection H1; intro i; rewrite <- i; apply H3; apply Rgt_not_eq; apply r.
      
    ++
      (* (* Limit *) *)
      (* | ro_lim_prt : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ, *)

      (*     w |- [{fun γ' => ϕ (snd γ')}] e [{θ}] -> *)
      (*     (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} Lim e {{ψ}} *)

      intros γ m; simpl; simpl in m.
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_Lim _ _ w)).
      simpl.
      pose proof (fun z => proves_ro_tot_sound _ _ _ w (fun zγ => ϕ0 (snd zγ)) θ p (z, γ) m).
      simpl in H.
      pose proof (e0 γ m).
      destruct H0 as [y h1].
      destruct h1 as [h1 h2].
      split.
      {
        apply (pdom_is_neg_empty_by_evidence _ (total y)).
        simpl.
        unfold Rlim_def.
        exists y; split; auto.
        intros.
        split.
        destruct (H x); auto.
        
        intros.
        destruct z.
        destruct (H x) as [_ h].
        pose proof (h (bot R) H0).
        destruct H1.
        destruct H1.
        contradict (flat_bot_neq_total _ H1).
        exists r; split; auto.
        destruct (H x) as [_ h].
        pose proof (h _ H0).
        destruct H1.

        destruct H1.
        injection H1; intro j; rewrite <- j in H2; clear j.
        apply (h2 x r H2).
      }
      intros.
      assert (total y = total v').
      apply (Rlim_def_unique ((fun x : Z => sem_ro_exp (INTEGER :: Γ) e REAL w (x, γ)))); auto.
      unfold Rlim_def.
      exists y.
      split; auto.
      intros.
      split; intros.
      destruct (H x); auto. 
      destruct z.
      destruct (H x) as [_ h].
      pose proof (h (bot R) H2).
      destruct H3.
      destruct H3.
      contradict (flat_bot_neq_total _ H3).
      exists r; split; auto.
      destruct (H x) as [_ h].
      pose proof (h _ H2).
      destruct H3.
      destruct H3.
      apply h2.
      injection H3; intro j; rewrite j; auto.
      rewrite <- H1; auto.
      injection H2; intro j; rewrite <- j; auto.


  + (*  total correctness triple for read only expressions *)
    intros Γ e τ w ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | ro_imply_tot : forall Γ e τ (w : Γ |- e : τ) P Q P' Q', *)

      (*     P' ->> P ->  *)
      (*     w |- [{ P }] e [{ Q }] ->  *)
      (*     Q ->>> Q' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{ P'}]  e [{ Q' }] *)

      intros γ m; simpl; simpl in m.
      apply a in m.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as H.
      simpl in H.
      split; destruct H as [h1 h2]; auto.
      intros t1 t2.
      pose proof (h2 _ t2) as [p1 p2].
      destruct p2 as [p2 p3].
      exists p1; split; auto; try apply a0; auto.
      
    ++
      (* | ro_exfalso_tot : forall Γ e τ (w : Γ |- e : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*)     *)
      (*     w |- [{ (fun _ => False) }] e [{ Q }] *)

      intros γ m; simpl; simpl in m.
      contradict m.

    ++
      (* | ro_conj_tot : forall Γ e τ (w : Γ |- e : τ) P Q Q', *)
      

      (*     w |- [{P}] e [{Q}] ->  *)
      (*     w |- [{P}] e [{Q'}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{P}] e [{Q /\\\ Q'}] *)
      intros γ m; simpl; simpl in m.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [_ q2].
      split.
      intro.
      apply (p1 H).
      intros v i.
      pose proof (p2 _ i).
      pose proof (q2 _ i).
      destruct H, H0.
      destruct H, H0.
      exists x.
      split; auto.
      split; auto.
      rewrite H in H0; injection H0; intro j; rewrite j; auto.
      
    ++
      (* | ro_disj_tot : forall Γ e τ (w : Γ |- e : τ) P P' Q, *)

      (*     w |- [{P}] e [{Q}] ->  *)
      (*     w |- [{P'}] e [{Q}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{P \// P'}] e [{Q}] *)
      intros γ m; simpl; simpl in m.
      destruct m as [m|m].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      split; auto.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [p1 p2].
      split; auto.
      
    ++
      (* (** variables and constants *) *)
      (* | ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{fun γ => Q (ro_access Γ k τ w γ) γ}] VAR k [{Q}] *)
      apply proves_ro_tot_Var_sound.

    ++
      (* | ro_skip_tot : forall Γ (w : Γ |- SKIP : UNIT) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q tt}] SKIP [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique Γ SKIP UNIT w (has_type_ro_Skip _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists tt; split; auto.

    ++
      (* | ro_true_tot : forall Γ (w : Γ |- TRUE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q true}] TRUE [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique Γ _ _ w (has_type_ro_True _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists true; split; auto.

    ++
      (* | ro_false_tot : forall Γ (w : Γ |- FALSE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q false}] FALSE [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique Γ _ _ w (has_type_ro_False _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists false; split; auto.

    ++
      (* | ro_int_tot : forall Γ k (w : Γ |- INT k : INTEGER) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q k}] INT k [{Q}] *)

      intros γ m; simpl in m; simpl.
      rewrite (sem_ro_exp_unique Γ _ _ w (has_type_ro_Int _ _)).
      simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists k; split; auto.

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | rw_ro_tot : forall Γ c τ (w : Γ ;;; nil ||- c : τ) P Q (w' : Γ |- c : τ), *)
      
      (*     w ||- [{P}] c [{Q}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{fun γ => P (tt, γ)}] c [{fun v w => Q v (tt, w)}] *)
      
      intros γ m; simpl in m; simpl.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ p γ tt m) as [p1 p2].
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_rw _ _ _ w)).
      simpl.
      split.
      intro h.
      apply pdom_lift_empty_2 in h.
      apply (p1 h).
      intros x1 [x2 [x3 x4] ].
      destruct (p2 x2 x3) as [[u v] [h1 h2]].
      exists v.
      simpl in h2.
      rewrite h1 in x4; simpl in x4; rewrite <- x4; destruct u; split; auto.

    ++
      (* (** restricting auxiliary variables *) *)
      (* | ro_proj_tot : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ,  *)
      (*     w' |- [{ϕ}] e [{ψ}] -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{fun γ => exists γ', ϕ (γ ; γ')]} e [{y | fun γ => exists γ', ψ y (γ ; γ')}] *)
      intros γ [γ' m]; simpl in m; simpl.
      
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip (γ; γ')  m) as [p1 p2].
      split.
      rewrite <- (sem_ro_exp_auxiliary_ctx _ _ _ _ w) in p1; auto.
      intros h1 h2. 
      rewrite <- (sem_ro_exp_auxiliary_ctx _ _ _ _ w) in p2; auto.
      pose proof (p2 _ h2) as [p3 [p4 p5]].
      exists p3; split; auto.
      exists γ'; auto.
      

    ++
      (* (** coercion and exponentiation *) *)
      (* | ro_coerce_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- RE e : REAL), *)
      
      (*     w |- [{ϕ}] e [{y | ψ (IZR y)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] RE e [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZRcoerce  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros y [x [h1 h2]].
      destruct (p2 x h1) as [x' [h3 h4]].
      rewrite h3 in h2.
      simpl in h2.
      exists (IZR x'); split; auto; simpl in h4; auto.

    ++
      (* | ro_exp_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- EXP e : REAL), *)
      
      (*     w |- [{ϕ}] e [{y | ψ (powerRZ 2 y)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] EXP e [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZRexp  _ _ w)).
      simpl.
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros y [x [h1 h2]].
      destruct (p2 x h1) as [x' [h3 h4]].
      rewrite h3 in h2.
      simpl in h2.
      exists (powerRZ 2 x'); split; auto; simpl in h4; auto.

    ++
      (* (** integer arithmetic  *) *)
      (* | ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)-> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*      w' |- [{ϕ}] e1 :+: e2 [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZplus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp Γ (e1 :+: e2) INTEGER w' γ) with
        (pdom_lift2 (BinInt.Z.add) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZplus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists z; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
      
    ++
      (* | ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :*: e2) [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZmult _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp Γ (e1 :*: e2) INTEGER w' γ) with
        (pdom_lift2 (BinInt.Zmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZmult _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists z; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* | ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :-: e2) [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZminus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp Γ (e1 :-: e2) INTEGER w' γ) with
        (pdom_lift2 (BinInt.Zminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZminus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists z; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* (** real arithmetic  *) *)
      (* | ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;+; e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRplus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp _ _ _ w' γ) with
        (pdom_lift2 (Rplus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRplus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists r; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* | ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;*; e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRmult _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp _ _ _ w' γ) with
        (pdom_lift2 (Rmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRmult _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists r; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.

    ++
      (* | ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post), *)

      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;-; e2) [{ψ}] *)
      
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRminus _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp _ _ _ w' γ) with
        (pdom_lift2 (Rminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRminus _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists r; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.

    ++

      (* (** reciprocal *) *)
      (* | ro_recip_tot : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ, *)

      (*     w |- [{ϕ}] e [{θ}] ->  *)
      (*     (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] ;/; e [{ψ}] *)

      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip γ m) as [p1 p2].
      split.
      {
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRrecip  _ _ w)).
        simpl.
        intro.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (p1 H).
        destruct H as [x p].
        destruct p as [p q].
        unfold Rrecip in q.
        contradict q.
        destruct (Rrecip' x).
        apply (pdom_is_neg_empty_by_evidence _ (bot R)); simpl; auto.
        apply (pdom_is_neg_empty_by_evidence _ (total r)); simpl; auto.
      }
      intros v h1.
      assert (sem_ro_exp Γ (;/; e) REAL w' γ =
                pdom_bind Rrecip (sem_ro_exp Γ e REAL w γ)).
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRrecip  _ _ w)); simpl; auto.
      rewrite H in h1; clear H.
      simpl in p2.

      destruct v.
      {
        (* non bottom *)
        apply pdom_bind_bot_2 in h1.
        destruct h1.
        pose proof (p2 _ H).
        destruct H0.
        destruct H0.
        contradict (flat_bot_neq_total _ H0).
        destruct H.
        destruct H.
        pose proof (p2 _ H).
        destruct H1.
        destruct H1.
        
        unfold Rrecip in H0.
        unfold flat_to_pdom in H0.
        unfold Rrecip' in H0.
        simpl in H0.
        apply total_is_injective in H1.
        induction H1.
        pose proof (a x γ H2).
        destruct H1.
        destruct (total_order_T x 0).
        destruct s.
        contradict (flat_total_neq_bot _ H0).
        contradict H1; auto.
        contradict (flat_total_neq_bot _ H0).
      }
      apply  pdom_bind_total_2 in h1.
      destruct h1 as [_ h1].
      destruct h1 as [x h].
      destruct h as [h1 h3].
      unfold Rrecip in h3.
      unfold  flat_to_pdom in h3.
      unfold Rrecip' in h3.
      simpl in h3.
      destruct (total_order_T x 0) as [[s|s]|s].
      {
        (* when x < 0 *)     
        destruct (a x γ).
        destruct (p2 _ h1).
        destruct H.
        apply total_is_injective in H.
        rewrite H; auto.
        exists r; split; auto.
        apply total_is_injective in h3.
        rewrite <- h3.
        auto.
      }
      {
        (* when x = 0 *)
       contradict (flat_bot_neq_total _ h3).
      } 
      {
        (* when x > 0 *)     
        destruct (a x γ).
        destruct (p2 _ h1).
        destruct H.
        apply total_is_injective in H.
        rewrite H; auto.
        exists r; split; auto.
        apply total_is_injective in h3.
        rewrite <- h3.
        auto.
      }


    ++
      (* (** integer exparison  *) *)
      (* | ro_int_exp_eq_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2  (w' : Γ |- (e1 :=: e2) : BOOL) (ψ : post), *)

      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.eqb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :=: e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZeq _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp _ _ _ w' γ) with
        (pdom_lift2 (Z.eqb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZeq _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists b; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.


    ++
      (* | ro_int_exp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post), *)

      (*     w1 |- [{P}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{P}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{P}] (e1 :<: e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZlt _  _ _ w1 w2)).
        intro.
        apply pdom_lift_empty_2 in H.
        unfold pdom_prod in H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
      }
      replace (sem_ro_exp _ _ _ w' γ) with
        (pdom_lift2 (Z.ltb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpZlt _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_lift_bot_2 in H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
      }
      exists b; split; auto.
      apply pdom_lift_total_2 in H.
      destruct H as [[x1 x2] [h1 h2]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (ψ3 _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      rewrite h2; auto.
    ++
      (* (** real exparison  *) *)
      (* | ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2  (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;<; e2) [{ψ}] *)
      intros γ m; simpl in m; simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip1 γ m) as [p1 p2].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ trip2 γ m) as [q1 q2].
      split.
      {
        (* nonemptiness *)
        rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRlt _  _ _ w1 w2)); simpl.
        intro.
        unfold pdom_bind2 in H.
        apply pdom_bind_empty_2 in H.
        unfold pdom_prod in H.
        destruct H.
        apply pdom_bind_empty_2 in H.
        destruct H.
        apply (q1 H).
        destruct H as [h1 [h2  h3]].
        apply pdom_lift_empty_2 in h3.
        apply (p1 h3).
        destruct H as [[x1 x2] [h1 h2]].
        unfold Rltb in h2.
        apply flat_to_pdom_neg_empty in h2.
        auto.
      }
      replace (sem_ro_exp _ _ _ w' γ) with
        (pdom_bind2 Rltb (sem_ro_exp Γ e1 REAL w1 γ) (sem_ro_exp Γ e2 REAL w2 γ))
        by (rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_OpRlt _ _ _ w1 w2)); simpl; auto).
      intros v H.
      unfold pdom_bind2 in H.
      unfold pdom_prod in H.
      destruct v.
      {
        (* v is not bot *)
        apply pdom_bind_bot_2 in H.
        destruct H.
        apply pdom_bind_bot_2 in H.
        destruct H.
        destruct (q2 _ H) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        destruct H as [x [h1 [h2 [h3 h4]]]].
        destruct h2.
        destruct (p2 _ h3) as [v' [e _]].
        contradict (flat_bot_neq_total _ e).
        simpl in h4.
        contradict (flat_total_neq_bot _ h4).
        destruct H as [[x1 x2] [h1 h2]].
        apply pdom_bind_total_2 in h1 as [_ [x2' [h1 h3]]].
        apply pdom_lift_total_2 in h3 as [x1' [h3 h4]].
        rewrite h4 in h2.
        simpl in h2.
        unfold Rltb' in h2.
        destruct (total_order_T x1' x2').
        destruct s.
        contradict (flat_total_neq_bot _ h2).
        pose proof (p2 _ h3) as [x1'' [e1'' h1'']]; apply total_is_injective in e1''.
        pose proof (q2 _ h1) as [x2'' [e2'' h2'']]; apply total_is_injective in e2''.
        induction e1'', e2''.
        contradict (proj1 (a _ _ _ h1'' h2'') e).
        contradict (flat_total_neq_bot _ h2).
      }
      exists b; split; auto.
      apply pdom_bind_total_2 in H as [_ [[x1 x2] [h1 h2]]].
      apply pdom_bind_total_2 in h1 as [_ [x1' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [x2' [h3 h4]].
      pose proof (p2 _ h3) as [x1'' [eq1 pos1]].
      pose proof (q2 _ h1) as [x2'' [eq2 pos2]].
      pose proof (a _ _ _ pos1 pos2).
      rewrite <- (total_is_injective eq1) in H.
      rewrite <- (total_is_injective eq2) in H.
      rewrite h4 in h2.
      simpl in h2.
      unfold Rltb'' in H.
      unfold Rltb' in h2.
      destruct H as [p H].
      destruct (total_order_T x2' x1') as [[s | s]| s].
      apply total_is_injective in h2; rewrite<- h2; auto.
      contradict (p s).
      apply total_is_injective in h2; rewrite<- h2; auto.
      
    ++
      (* (* Limit *) *)
      (* | ro_lim_tot : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ, *)

      (*     w |- [{fun γ' => ϕ (snd γ')}] e [{θ}] -> *)
      (*     (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] Lim e [{ψ}] *)
      intros γ m; simpl; simpl in m.
      rewrite (sem_ro_exp_unique _ _ _ w' (has_type_ro_Lim _ _ w)).
      simpl.
      pose proof (fun z => proves_ro_tot_sound _ _ _ w (fun zγ => ϕ0 (snd zγ)) θ trip (z, γ) m).
      simpl in H.
      pose proof (e0 γ m).
      destruct H0 as [y h1].
      destruct h1 as [h1 h2].
      split.
      {
        apply (pdom_is_neg_empty_by_evidence _ (total y)).
        simpl.
        unfold Rlim_def.
        exists y; repeat split; intros; auto.
        destruct (H x); auto.
        intros.
        destruct z.
        destruct (H x) as [_ h].
        pose proof (h (bot R) H0).
        destruct H1.
        destruct H1.
        contradict (flat_bot_neq_total _ H1).
        exists r; split; auto.
        destruct (H x) as [_ h].
        pose proof (h _ H0).
        destruct H1.

        destruct H1.
        injection H1; intro j; rewrite <- j in H2; clear j.
        apply (h2 x r H2).
      }
      intros.
      destruct v.
      contradict (Rlim_def_never_bot _ H0).
      exists r; split; auto.      
      replace r with y; auto.
      apply total_is_injective.
      apply (Rlim_def_unique ((fun x : Z => sem_ro_exp (INTEGER :: Γ) e REAL w (x, γ)))); auto.
      
      unfold Rlim_def.
      exists y.
      split; auto.
      intros.
      destruct (H x); auto.
      split.
      auto.
      intros.
      destruct z.
      destruct (H x) as [_ h].
      pose proof (h (bot R) H3).
      destruct H4.
      destruct H4.
      contradict (flat_bot_neq_total _ H4).
      exists r0; split; auto.
      destruct (H x) as [_ h].
      pose proof (h _ H3).
      destruct H4.
      destruct H4.
      apply h2.
      injection H4; intro j; rewrite j; auto.
      
  + (*  partial correctness triple for read write expressions *)
    intros Γ Δ e τ w ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | rw_imply_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ', *)
      
      (*     ϕ' ->> ϕ ->  *)
      (*     w ||- {{ ϕ }} e {{ ψ }} ->  *)
      (*     ψ ->>> ψ' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ ϕ'}}  e {{ ψ' }} *)
      
      intros γ δ m; simpl; simpl in m.
      apply a in m.      
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip γ δ m) as [h1 h2]; split; auto.
      intros t1 t2 t3 t4.
      apply a0, (h2 _ t2 _ t4).

    ++
      (* | rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ (fun _ => False) }} e {{ ψ }} *)
      intros γ δ m; simpl; simpl in m.
      contradict m.
    ++
      (* | rw_conj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ', *)
      
      (*     w ||- {{ϕ}} e {{ψ}} ->  *)
      (*     w ||- {{ϕ}} e {{ψ'}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ϕ}} e {{ψ /\\\ ψ'}} *)
      intros γ δ m; simpl; simpl in m.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip1 γ δ m) as [p1 p2].
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip2 γ δ m) as [_ q2].
      split; auto.
      intros t1 t2 t3 t4.
      split.
      rewrite t4 in t2.
      apply (p2 _ t2); auto.
      apply (q2 _ t2); auto.

    ++
      (* | rw_disj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ, *)
      
      (*     w ||- {{ϕ}} e {{ψ}} ->  *)
      (*     w ||- {{ϕ'}} e {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ϕ \// ϕ'}} e {{ψ}} *)
      intros γ δ m; simpl; simpl in m.
      destruct m as [m|m].
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip1 γ δ m) as [p1 p2].
      split; auto.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip2 γ δ m) as [q1 q2].
      split; auto.
      
    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | ro_rw_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ), *)
      
      (*     w |- {{ϕ}} e {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}} e {{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}} *)
      intros γ δ m; simpl; simpl in m.
      rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_ro _ _ _ _ w)); simpl.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _  p (tedious_prod_sem _ _ (δ, γ)) m) as [p1 p2].
      split.
      auto.
      apply neg_forall_exists_neg in p1.
      destruct p1.
      apply dn_elim in H.
      destruct x.
      apply (pdom_is_neg_empty_by_evidence _ (bot _)).
      simpl.
      exists (bot _); split; simpl; auto.
      apply (pdom_is_neg_empty_by_evidence _ (total (δ, s))).
      simpl.
      exists (total s); split; simpl; auto.
      intros h1 [h2 [h3 h4]] h5 h6.
      pose proof (p2 _ h3 (snd h5)).
      destruct h2.
      simpl in h4.
      rewrite h6 in h4.
      contradict (flat_bot_neq_total _ h4).
      simpl in h4.
      rewrite h6 in h4.
      apply total_is_injective in h4.
      rewrite <- h4; rewrite <- h4 in H.
      apply H; auto.

    ++
      (* (** restricting auxiliary variables *) *)
      intros γ δ [γ' m]; simpl in m; simpl.
      
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip (γ; γ') δ  m) as [p1 p2].
      split.
      rewrite <- (sem_rw_exp_auxiliary_ctx _ _ _ _ _ w) in p1; auto.
      intros h1 h2 h3 h4.
      exists γ'.
      rewrite <- (sem_rw_exp_auxiliary_ctx _ _ _ _ _ w) in p2; auto.
      pose proof (p2 h1 h2 _ h4).
      simpl in H; auto.
      
    ++
      (* (** operational proof rules  *)                             *)
      (* | rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ), *)
      
      (*     w1 ||- {{ϕ}} c1 {{θ}} ->  *)
      (*     w2 ||- {{θ tt}} c2 {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} c1 ;; c2 {{ψ}} *)
      intros γ δ m; simpl; simpl in m.
      pose (sem_rw_exp _ _ _ _ w1 γ) as C1.
      pose (sem_rw_exp _ _ _ _ w2 γ) as C2.
      replace (sem_rw_exp Γ Δ (c1;; c2) τ w' γ δ) with
        (pdom_bind C2 ((pdom_lift (@fst _ (sem_datatype DUnit)) (C1 δ))))
        by  (rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_Seq _ _ _ _ _ w1 w2)); simpl; auto).
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip1 γ δ m) as [p1 p2]; auto.
      unfold C1, C2.
      split.
      {
        (* non empty *)
        intro h.      
        apply pdom_bind_empty_2 in h.
        destruct h as [h|[δ' [h1 h2]]].
        apply pdom_lift_empty_2 in h; auto.
        assert (total (δ', tt) ∈ sem_rw_exp Γ Δ c1 UNIT w1 γ δ).
        apply pdom_lift_total_2 in h1.
        destruct h1.
        destruct H.
        destruct x.
        simpl in H0.
        rewrite H0.
        destruct s0; auto.
        pose proof (p2 _ H _ eq_refl).
        simpl in H0.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip2 γ δ' H0) as [q1 q2]; auto.
      }
      intros h1 h2 [δ'' y] h4.
      simpl.
      rewrite h4 in h2; clear h4.
      apply pdom_bind_total_2 in h2 as [_ [δ' [h2 h3]]].
      apply pdom_lift_total_2 in h2 as [[tmp tmp'] [h4 h5]].
      simpl in h5.
      induction h5.
      destruct tmp'.
      pose proof (p2 _ h4 _ eq_refl) as H.
      simpl in H.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _  trip2 γ δ' H) as [q1 q2]; auto.
      apply (q2 _ h3 _ eq_refl).

    ++
      (* | rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ), *)

      (*     w1 |- {{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}} e {{θ}} ->  *)
      (*     w2 ||- {{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}} c {{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} NEWVAR e IN c {{ψ}} *)
      intros γ δ m; simpl; simpl in m.
      pose (sem_ro_exp _ _ _ w1 (tedious_prod_sem _ _ (δ, γ))) as V.
      pose (sem_rw_exp _ _ _ _ w2 γ) as f.
      pose (pdom_bind f (pdom_lift (fun v => (v, δ)) V)) as res.
      replace (sem_rw_exp Γ Δ (NEWVAR e IN c) τ w' γ δ) with
        (pdom_lift (fun x => (snd (fst x), snd x)) res) by
        (rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_Newvar _ _ _ _ _ _ w1 w2)); simpl; auto).
      unfold V, f, res.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p (tedious_prod_sem Δ Γ (δ, γ))).
      simpl in H.
      assert (ϕ0 (tedious_sem_app Δ Γ (tedious_prod_sem Δ Γ (δ, γ)))) as H'
          by (rewrite tedious_equiv_1; auto).
      apply H in H' as [p1 p2]; clear H.
      split.
      {
        (* non empty *)
        intro h.
        apply pdom_lift_empty_2 in h.
        apply pdom_bind_empty_2 in h.
        destruct h as [h|[x' [h1 h2]]].
        apply pdom_lift_empty_2 in h.
        unfold V in h.
        auto.
        unfold V in h1.
        apply pdom_lift_total_2 in h1 as [x'' [h h']].
        unfold f in h2.
        pose proof (p2 _ h _ eq_refl).
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip γ x').
        assert (rw_prt_pre w2
         (mk_rw_prt w2
            (fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ =>
             θ (fst (fst xδγ)) (tedious_prod_sem Δ Γ (snd (fst xδγ), snd xδγ)))
            (fun (x : sem_datatype τ) (xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ) => ψ0 x (snd (fst xδγ), snd xδγ)))
         (x', γ)).
        simpl.
        destruct x'.
        simpl.
        injection h'; intros.
        rewrite H1, H2; auto.
        apply H0 in H1 as [q1 q2]; clear H0.
        auto.
      }
      intros h1 h2 [δ' y] h3; simpl.
      rewrite h3 in h2; clear h3.
      apply pdom_lift_total_2 in h2 as [[[x' x''] y'] [h2 h3]].
      apply pdom_bind_total_2 in h2 as [_ [[x''' δ''] [h2 h4]]].
      apply pdom_lift_total_2 in h2 as [x'''' [h5 h6]].
      simpl in h3.
      unfold f in h4.
      injection h3; intros i j; induction i; induction j; clear h3.
      injection h6; intros i j; induction i; induction j; clear h6.
      unfold V in h5.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip γ (x''', δ'') (p2 _ h5 _ eq_refl)) as [_ h].
      simpl in h.
      apply (h _ h4 _ eq_refl).

    ++
      (* | rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT), *)

      (*     w |- {{fun δγ => ϕ (tedious_sem_app _ _ δγ)}} e {{θ}} ->  *)
      (*     (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} LET k := e {{ψ}} *)
      apply proves_ro_prt_sound in p.
      apply (proves_rw_prt_Assign_sound _ _ _ _ _ _ _ _ _ _ p ψ1).
    
    ++
      (* | rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ, *)

      (*     w |- {{rw_to_ro_pre ϕ}} e {{θ}} -> *)
      (*     w1 ||- {{ro_to_rw_pre (θ true)}} c1 {{ψ}} -> *)
      (*     w2 ||- {{ro_to_rw_pre (θ false)}} c2 {{ψ}} -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} Cond e c1 c2 {{ψ}} *)
      intros γ δ m; simpl; simpl in m.
      pose (sem_ro_exp _ _ _ w (δ; γ)) as B.
      pose (sem_rw_exp _ _ _ _ w1 γ δ) as X.
      pose (sem_rw_exp _ _ _ _ w2 γ δ) as Y.
      replace (sem_rw_exp Γ Δ (IF e THEN c1 ELSE c2 END) τ w' γ δ)
        with (pdom_bind (fun b : bool => if b then X else Y) B)
        by  (rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_Cond _ _ _ _ _ _ w w1 w2)); simpl; auto).
      assert (ro_prt_pre w (mk_ro_prt w (rw_to_ro_pre ϕ0) θ) (δ; γ)) as m'
          by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
       
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p (δ ; γ) m') as [nempty_e sem_e].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p) as E. 
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip1) as C1.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip2) as C2.
      split.
      {
        intro h.
        apply pdom_bind_empty_2 in h as [h|[x [h1 h2]]]; auto.
        pose proof (ro_prt_post_pre _ _ _ _ _ _ E x (δ ; γ) m').
        apply H in h1.
        destruct x.
        pose proof (C1 γ δ h1) as [h _]; auto.
        pose proof (C2 γ δ h1) as [h _]; auto.
      }

      intros h1 h2 h3 h4.
      rewrite h4 in h2; clear h4.
      apply pdom_bind_total_2 in h2 as [_ [b [semb h2]]].
      pose proof (ro_prt_post_pre _ _ _ _ _ _ E b (δ ; γ) m').
      apply H in semb; clear H.
      destruct b.
      pose proof (C1 γ δ semb) as [_ h].
      apply (h _ h2 h3 eq_refl).
      pose proof (C2 γ δ semb) as [_ h].
      apply (h _ h2 h3 eq_refl).
      
    ++
      (* | rw_case_prt : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ, *)

      (*     wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} ->  *)
      (*     wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}} ->  *)
      (*     wty_c1 ||- {{ro_to_rw_pre (θ1 true)}} c1 {{ψ}} ->  *)
      (*     wty_c2 ||- {{ro_to_rw_pre (θ2 true)}} c2 {{ψ}} -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- {{ϕ}} Case e1 c1 e2 c2 {{ψ}} *)
      intros γ δ m; simpl; simpl in m.


      pose (sem_ro_exp _ _ _ wty_e1 (δ; γ)) as B1.
      pose (sem_ro_exp _ _ _ wty_e2 (δ; γ)) as B2.
      pose (sem_rw_exp _ _ _ _ wty_c1 γ δ) as X.
      pose (sem_rw_exp _ _ _ _ wty_c2 γ δ) as Y.
      replace (sem_rw_exp Γ Δ (CASE e1 ==> c1 OR e2 ==> c2 END) τ wty γ δ) with
        (Case2 B1 B2 X Y) 
        by  (rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_Case _ _ _ _ _ _ _ wty_e1  wty_c1 wty_e2 wty_c2)); simpl; auto).
      assert ( (rw_to_ro_pre ϕ0) (δ; γ)) as m'
          by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m') as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p0 _ m') as [q1 q2].
      split.
      {
        (* non empty *)
        unfold Case2.
        intro h.
        apply pdom_case2_empty_2 in h.
        destruct h as [h| [h | [[h1 h2] | [h1 h2]]]].
        apply (p1 h).
        apply (q1 h).
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ ; γ) m' h1) as m''.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip1 _ _ m'') as [r1 r2].
        auto.
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p0)) true (δ ; γ) m' h1) as m''.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip2 _ _ m'') as [r1 r2].
        auto.
      }
      intros h1 h2 h3 h4.
      rewrite h4 in h2; clear h4.
      apply pdom_case2_total_2 in h2.
      destruct h2 as [[h2 h4]|[h2 h4]]. 
      pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ ; γ) m' h2) as m''.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip1 _ _ m'') as [_ r2].
      apply (r2 _ h4 _ (eq_refl)).
      pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p0)) true (δ ; γ) m' h2) as m''.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip2 _ _ m'') as [_ r2].
      apply (r2 _ h4 _ (eq_refl)).


    ++
      (* | Rw_case_list_prt *)
      intros γ δ m; simpl in m; simpl.
      assert (1 <= length l).
      pose proof (has_type_rw_r_has_type_rw _ _ _ _ wty).
      dependent destruction H; auto.
      
      rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_CaseList _ _ l _ H wty_l)).
      simpl.
      easy_rewrite_uip.
      split.
      {
        (* nonempty *)
        intro.
        apply pdom_case_list_empty_2 in H0.
        apply Exists_exists in H0.
        destruct H0.
        destruct H0.

        clear H wty.
        
        dependent induction f.
        simpl in H0.
        exact H0.

        simpl in H0.
        destruct p.
        simpl in H0.
        destruct H0.
        rewrite <- H in H1; simpl in H1.
        destruct r.
        assert (rw_to_ro_pre ϕ0 (δ; γ)) as m'.
        unfold rw_to_ro_pre.
        rewrite tedious_equiv_1.
        auto.
        pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m').
        (* pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0). *)
        destruct H1.
        destruct H0 as [H0 _]; auto.
        destruct H1.
        destruct H0 as [_ H0].
        pose proof (H0 _ H1 _ eq_refl).
        simpl in H3.
        assert (ro_to_rw_pre (q true) (δ, γ)).
        unfold ro_to_rw_pre.
        auto.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0 _ _ H4) as [H5 _].
        auto.
        apply (IHf γ δ m x H).
        exact H1.
      }

      intros.
      destruct H0.
      destruct H2.
      clear H0.
      apply Exists_exists in H2.
      destruct H2.
      clear H wty.
      dependent induction f.
      simpl in H0.
      destruct H0.
      contradict H.
      simpl in H0.
      destruct p.
      simpl in H0.
      destruct H0.
      destruct H.
      assert (rw_to_ro_pre ϕ0 (δ; γ)) as m'.
      unfold rw_to_ro_pre.
      rewrite tedious_equiv_1.
      auto.
      destruct r.
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m').
      (* pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0). *)
      destruct H0.
      destruct H2 as [_ H2].
      simpl in H2.
      rewrite <- H in H0.
      simpl in H0.
      pose proof (H2 _ H0 _ eq_refl).
      assert (ro_to_rw_pre (q true) (δ, γ)).
      unfold ro_to_rw_pre.
      auto.
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0 _ _ H5) as [_ H6].
      simpl in H6.
      rewrite <- H in H3.
      simpl in H3.
      pose proof (H6 _ H3 _ H1).
      exact H7.
      apply (IHf γ δ m v x).
      split.
      exact H.

      exact H0.
      exact H1.
      destruct H2.
      rewrite H2 in H1.
      contradict (flat_bot_neq_total _ H1).

  
      
    ++
      (* | Rw_while_prt : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ, *)

      (*     wty_e |- {{rw_to_ro_pre ϕ}} e {{θ}} ->  *)
      (*     wty_c ||- {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}} *)
      
      intros γ δ m; simpl; simpl in m.
      pose (fun d => sem_ro_exp _ _ _ wty_e (d; γ)) as B.
      pose (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ wty_c γ d)) as C.
      replace (sem_rw_exp Γ Δ (WHILE e DO c END) UNIT wty γ δ) with
        (pdom_lift (fun x => (x, tt)) (pdom_while B C δ))
        by (rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_While _ _ _ _ wty_e  wty_c)); simpl; auto).
      assert ( (rw_to_ro_pre ϕ0) (δ; γ)) as m'
          by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m') as [p1 p2].

      (* important sub lemmas *)
      pose (fun n δ => pdom_fun_bot_chain (pdom_W B C) (pdom_W_monotone B C) n δ) as thechain.
      (* the chain respects invariant *)
      assert (forall n, forall δ1 δ2, ϕ0 (δ1, γ) -> total δ2 ∈ thechain n δ1 -> ϕ0 (δ2, γ) /\ ro_to_rw_pre (θ false) (δ2, γ)) as l.
      {
        (* base *)
        intro n.
        induction n.
        intros.
        simpl in H0.
        contradiction (flat_bot_neq_total _ H0).
        (* induction step *)
        intros.
        simpl in H0.
        destruct H0 as [h1 [h2 [[h3 h4] | [h3 h4]]]].
        contradict (flat_total_neq_bot _ h3).
        destruct h4 as [H1 [b [H3 H4]]].
        destruct b.
        simpl in H4.
        contradiction (flat_bot_neq_total _ H4).
        simpl in H4.
        destruct b.
        apply total_is_injective in H4.
        rewrite <- H4 in H1; clear H4.
        apply pdom_bind_total_2 in H1 as [_ [d [hh1 hh2]]].
        apply (IHn d δ2).
        assert (rw_to_ro_pre ϕ0 (δ1; γ))        
          by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
          
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ1 ; γ) H0 H3) as m''.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip _ _ m'') as [_ r2].
        simpl in r2.
        assert (total (d, tt) ∈  sem_rw_exp Γ Δ c UNIT wty_c γ δ1).
        {
          unfold C in hh1.
          apply pdom_lift_total_2 in hh1.
          destruct hh1.
          destruct H1.
          destruct x.
          destruct s0.
          simpl in H2.
          rewrite H2; auto.
        }
        pose proof (r2 (total (d, tt)) H1 _ eq_refl).
        simpl in H2; auto.
        exact hh2.
        apply total_is_injective in H4.
        rewrite <- H4 in H1.
        simpl in H1.
        apply total_is_injective in H1.
        assert (rw_to_ro_pre ϕ0 (δ1; γ))        
          by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
        
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) false (δ1 ; γ) H0 H3) as m''.
        rewrite <- H1; split; auto.
      }

      (* nondempty *)
      assert (forall n, forall δ1, ϕ0 (δ1, γ) -> ~ pdom_is_empty (thechain n δ1)) as r.
      {
        intro n.
        induction n.
        intros.
        simpl.
        apply (pdom_is_neg_empty_by_evidence _ (bot _)); simpl; auto.

        intros.
        simpl.
        pose proof (IHn _ H).
        apply pdom_neg_empty_exists in H0 as [δ' h1].
        intro.
        unfold pdom_W in H0.
        apply pdom_bind_empty_2 in H0.
        destruct H0.
        assert ( (rw_to_ro_pre ϕ0) (δ1; γ)) as m''
            by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).

        pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m'') as [h _]; auto.
        destruct H0.
        destruct H0.
        destruct x.
        apply pdom_bind_empty_2 in H1.
        destruct H1.
        unfold C in H1.
        apply pdom_lift_empty_2 in H1.
        assert ( (rw_to_ro_pre ϕ0) (δ1; γ)) as m''
            by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).

        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ1 ; γ) m'' H0) as m'''.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip _ _ m''') as [r1 _].
        auto.
        destruct H1.
        destruct H1.
        apply (fun k => IHn x k H2).
        assert ( (rw_to_ro_pre ϕ0) (δ1; γ)) as m''
            by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).

        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ1 ; γ) m'' H0) as m'''.
        pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ trip _ _ m''') as [_ r2].
        unfold C in H1.
        apply pdom_lift_total_2 in H1.
        destruct H1.
        destruct H1.
        destruct x0.
        destruct s0.
        simpl in H3.
        induction H3.
        pose proof (r2 (total (x, tt)) H1 _ eq_refl).
        simpl in H3.
        auto.
        contradict H1.
        apply (pdom_is_neg_empty_by_evidence _ (total δ1)); simpl; auto.
      }
      split.
      intro.
      apply pdom_lift_empty_2 in H.
      unfold pdom_while in H.
      unfold pdom_fun_lfp in H.
      apply pdom_fun_chain_empty_2 in H as [n h].
      apply (r n δ m h).
      intros.
      rewrite H0 in H; clear H0.
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      unfold pdom_while in H.
      unfold pdom_fun_lfp in H.
      unfold pdom_fun_chain_sup in H.
      apply pdom_chain_membership_2 in H as [n h].
      
      pose proof (l n δ x m h).
      rewrite H0 ; simpl; auto.
      
  + (*  total correctness triple for read write expressions *)
    intros Γ Δ e τ w ϕ ψ trip.
    induction trip.

    ++
      (* (** logical rules *) *)
      (* | rw_imply_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ', *)
      
      (*     ϕ' ->> ϕ ->  *)
      (*     w ||- [{ ϕ }] e [{ ψ }] ->  *)
      (*     ψ ->>> ψ' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ ϕ'}]  e [{ ψ' }] *)
      intros γ δ m; simpl; simpl in m.
      apply a in m.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip γ δ m) as H.
      simpl in H.
      split; destruct H as [h1 h2]; auto.
      intros t1 t2.
      pose proof (h2 _ t2) as [p1 p2].
      destruct p2 as [p2 p3].
      exists p1; split; auto; try apply a0; auto.
      
    ++
      (* | rw_exfalso_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ (fun _ => False) }] e [{ ψ }] *)
      intros γ δ m; simpl; simpl in m.
      contradict m.

    ++
      (* | rw_conj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ', *)
      
      (*     w ||- [{ϕ}] e [{ψ}] ->  *)
      (*     w ||- [{ϕ}] e [{ψ'}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ϕ}] e [{ψ /\\\ ψ'}] *)
      intros γ δ m; simpl; simpl in m.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1 γ δ m) as [p1 p2].
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip2 γ δ m) as [_ q2].
      split.
      intro.
      apply (p1 H).
      intros v i.
      pose proof (p2 _ i).
      pose proof (q2 _ i).
      destruct H, H0.
      destruct H, H0.
      exists x.
      split; auto.
      split; auto.
      rewrite H in H0; injection H0; intro j; rewrite j; auto.
      
    ++
      (* | rw_disj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ, *)
      
      (*     w ||- [{ϕ}] e [{ψ}] ->  *)
      (*     w ||- [{ϕ'}] e [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ϕ \// ϕ'}] e [{ψ}] *)
      intros γ δ m; simpl; simpl in m.
      destruct m as [m|m].
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1 γ δ m) as [p1 p2].
      split; auto.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip2 γ δ m) as [p1 p2].
      split; auto.

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | ro_rw_tot : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ), *)
      
      (*     w |- [{ϕ}] e [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}] e [{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}] *)
      intros γ δ m; simpl; simpl in m.
      rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_ro _ _ _ _ w)); simpl.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _  p (tedious_prod_sem _ _ (δ, γ)) m) as [p1 p2].
      split.
      auto.
      apply neg_forall_exists_neg in p1.
      destruct p1.
      apply dn_elim in H.
      destruct x.
      apply (pdom_is_neg_empty_by_evidence _ (bot _)).
      simpl.
      exists (bot _); split; simpl; auto.
      apply (pdom_is_neg_empty_by_evidence _ (total (δ, s))).
      simpl.
      exists (total s); split; simpl; auto.
      intros h1 [h2 [h3 h4]].
      pose proof (p2 _ h3).
      destruct H as [q1 [q2 q3]].
      rewrite q2 in h3.
      rewrite q2 in h4.
      simpl in h4.
      exists (δ, q1); split; simpl; auto.
      
    ++
      (* (** restricting auxiliary variables *) *)
      intros γ δ [γ' m]; simpl in m; simpl.
      
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip (γ; γ') δ m) as [p1 p2].
      split.
      rewrite <- (sem_rw_exp_auxiliary_ctx _ _ _ _ _ w) in p1; auto.
      intros h1 h2. 
      rewrite <- (sem_rw_exp_auxiliary_ctx _ _ _ _ _ w) in p2; auto.
      pose proof (p2 _ h2) as [p3 [p4 p5]].
      exists p3; split; auto.
      exists γ'; auto.
      

    ++
      (* (** operational proof rules  *)                             *)
      (* | rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : UNIT) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ), *)
      
      (*     w1 ||- [{ϕ}] c1 [{θ}] ->  *)
      (*     w2 ||- [{θ tt}] c2 [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] c1 ;; c2 [{ψ}] *)
      intros γ δ m; simpl; simpl in m.
      pose (sem_rw_exp _ _ _ _ w1 γ) as C1.
      pose (sem_rw_exp _ _ _ _ w2 γ) as C2.
      replace (sem_rw_exp Γ Δ (c1;; c2) τ w' γ δ) with
        (pdom_bind C2 ((pdom_lift (@fst _ (sem_datatype DUnit)) (C1 δ))))
        by  (rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_Seq _ _ _ _ _ w1 w2)); simpl; auto).
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _  trip1 γ δ m) as [p1 p2]; auto.
      unfold C1, C2.
      split.
      {
        (* non empty *)
        intro h.      
        apply pdom_bind_empty_2 in h.
        destruct h as [h|[δ' [h1 h2]]].
        apply pdom_lift_empty_2 in h; auto.
        assert (total (δ', tt) ∈ sem_rw_exp Γ Δ c1 UNIT w1 γ δ).
        apply pdom_lift_total_2 in h1.
        destruct h1.
        destruct H.
        destruct x.
        simpl in H0.
        rewrite H0.
        destruct s0; auto.
        pose proof (p2 _ H).
        destruct H0.
        destruct H0.
        apply total_is_injective in H0.
        rewrite <- H0 in H1.
        pose proof (proves_rw_tot_sound _ _ _ _ _ _ _  trip2 γ δ' H1) as [q1 q2]; auto.
      }
      intros h1 h2.
      destruct h1.
      apply pdom_bind_bot_2 in h2.
      destruct h2.
      apply pdom_lift_bot_2 in H.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1 _ _ m) as [_ p].
      pose proof (p (bot _) H) as [x [e _]].
      contradict (flat_bot_neq_total _ e).
      destruct H as [y [h1 h2]].
      apply pdom_lift_total_2 in h1 as [[x u] [h3 h4]].
      destruct u.
      simpl in h4; rewrite <- h4 in h3; clear h4. 
      assert (θ tt (y, γ)).
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1 _ _ m) as [_ p].
      pose proof (p (total (y, tt)) h3) as [y' [e1 e2]]. 
      apply total_is_injective in e1.
      rewrite <- e1 in e2.
      simpl in e2.
      auto.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip2 _ _ H) as [_ q].
      pose proof (q _ h2) as [q' [e' _]].
      contradict (flat_bot_neq_total _ e').
      apply pdom_bind_total_2 in h2 as [_ [δ' [h2 h3]]].
      apply pdom_lift_total_2 in h2 as [[tmp tmp'] [h4 h5]].
      simpl in h5.
      induction h5.
      destruct tmp'.
      pose proof (p2 _ h4).
      destruct H as [hh1 [hh2 hh3]].
      apply total_is_injective in hh2.
      rewrite <- hh2 in hh3.

      simpl in hh3.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _  trip2 γ δ' hh3) as [_ q2]; auto.
     

    ++
      (* | rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ), *)

      (*     w1 |- [{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}] e [{θ}] ->  *)
      (*     w2 ||- [{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}] c [{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] NEWVAR e IN c [{ψ}] *)
      intros γ δ m; simpl; simpl in m.
      pose (sem_ro_exp _ _ _ w1 (δ; γ)) as V.
      pose (sem_rw_exp _ _ _ _ w2 γ) as f.
      pose (pdom_bind f (pdom_lift (fun v => (v, δ)) V)) as res.
      replace (sem_rw_exp Γ Δ (NEWVAR e IN c) τ w' γ δ) with
        (pdom_lift (fun x => (snd (fst x), snd x)) res) by
        (rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_Newvar _ _ _ _ _ _ w1 w2)); simpl; auto).
      unfold V, f, res.
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ p (tedious_prod_sem Δ Γ (δ, γ))).
      simpl in H.
      assert (ϕ0 (tedious_sem_app Δ Γ (tedious_prod_sem Δ Γ (δ, γ)))) as H'
          by (rewrite tedious_equiv_1; auto).
      apply H in H' as [p1 p2]; clear H.
      split.
      {
        (* non empty *)
        intro h.
        apply pdom_lift_empty_2 in h.
        apply pdom_bind_empty_2 in h.
        destruct h as [h|[x' [h1 h2]]].
        apply pdom_lift_empty_2 in h.
        unfold V in h.
        auto.
        unfold V in h1.
        apply pdom_lift_total_2 in h1 as [x'' [h h']].
        unfold f in h2.
        pose proof (p2 _ h) as [v'' [e1 e2]].
        pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip γ x').
        assert (rw_prt_pre w2
         (mk_rw_prt w2
            (fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ =>
             θ (fst (fst xδγ)) (tedious_prod_sem Δ Γ (snd (fst xδγ), snd xδγ)))
            (fun (x : sem_datatype τ) (xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ) => ψ0 x (snd (fst xδγ), snd xδγ)))
         (x', γ)).
        simpl.
        destruct x'.
        simpl.
        injection h'; intros; injection e1; intros.
        rewrite H0, H1, H2; auto.
        apply H in H0 as [q1 q2]; clear H.
        auto.
      }
      intros h1 h2.
      destruct h1.
      apply pdom_lift_bot_2 in h2.
      apply pdom_bind_bot_2 in h2.
      destruct h2.
      apply pdom_lift_bot_2 in H.
      pose proof (p2 _ H).
      destruct H0.
      destruct H0.
      contradict (flat_bot_neq_total _ H0).
      destruct H.
      destruct H.
      apply pdom_lift_total_2 in H.
      destruct H.
      destruct H.
      
      pose proof (p2 _ H).
      destruct H2.
      destruct H2.
      apply total_is_injective in  H2.
      induction H2.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip γ x).
      assert (rw_tot_pre w2
         (mk_rw_tot w2 (fun xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ))
            (fun (x : sem_datatype τ) (xδγ : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ) => ψ0 x (snd (fst xδγ), snd xδγ))) (x, γ)).
      simpl.
      destruct x.
      simpl.
      injection H1; intros i j; induction i, j; auto.
      apply H2 in H4; clear H2.
      simpl in H4.
      destruct H4.
      pose proof (H4 _ H0).
      destruct H5.
      destruct H5.
      contradict (flat_bot_neq_total _ H5).
      exists p0; split; auto.
      
      apply pdom_lift_total_2 in h2 as [[[x' x''] y'] [h2 h3]].
      apply pdom_bind_total_2 in h2 as [_ [[x''' δ''] [h2 h4]]].
      apply pdom_lift_total_2 in h2 as [x'''' [h5 h6]].
      simpl in h3.
      rewrite h3; clear h3; simpl.
      unfold f in h4.
      injection h6; intros i j; induction i; induction j.
      unfold V in h5.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip γ (x''', δ'')).
      simpl in H.
      assert (θ x''' (δ''; γ)).
      pose proof (p2 _ h5).
      destruct H0.
      destruct H0.
      apply total_is_injective in H0; rewrite H0; auto.
      apply H in H0 as [_ H0]; clear H.
      pose proof (H0 _ h4).
      destruct H.
      destruct H.
      destruct x.
      destruct p0.
      destruct p3.
      simpl.
      simpl in H1.
      apply total_is_injective in H.
      injection H; intros.
      rewrite H2, H3; auto. 


    ++
      (* | rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT), *)

      (*     w |- [{fun δγ => ϕ (tedious_sem_app _ _ δγ)}] e [{θ}] ->  *)
      (*     (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] LET k := e [{ψ}] *)
      apply proves_ro_tot_sound in p.
      apply (proves_rw_tot_Assign_sound _ _ _ _ _ _ _ _ _ _ p ψ1).

    ++
      (* | rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ, *)

      (*     w |- [{rw_to_ro_pre ϕ}] e [{θ}] -> *)
      (*     w1 ||- [{ro_to_rw_pre (θ true)}] c1 [{ψ}] -> *)
      (*     w2 ||- [{ro_to_rw_pre (θ false)}] c2 [{ψ}] -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] Cond e c1 c2 [{ψ}] *)
      intros γ δ m; simpl; simpl in m.
      pose (sem_ro_exp _ _ _ w (δ; γ)) as B.
      pose (sem_rw_exp _ _ _ _ w1 γ δ) as X.
      pose (sem_rw_exp _ _ _ _ w2 γ δ) as Y.
      replace (sem_rw_exp Γ Δ (IF e THEN c1 ELSE c2 END) τ w' γ δ)
        with (pdom_bind (fun b : bool => if b then X else Y) B)
        by  (rewrite (sem_rw_exp_unique _ _ _ _ w' (has_type_rw_Cond _ _ _ _ _ _ w w1 w2)); simpl; auto).
      assert (ro_prt_pre w (mk_ro_prt w (rw_to_ro_pre ϕ0) θ) (δ; γ)) as m'
          by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
      
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ p (δ ; γ) m') as [nempty_e sem_e].
      pose proof (proves_ro_tot_sound _ _ _ _ _ _ p) as E. 
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1) as C1.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip2) as C2.
      split.
      {
        (* non empty *)
        intro h.
        apply pdom_bind_empty_2 in h as [h|[x [h1 h2]]]; auto.
        pose proof (ro_tot_post_pre _ _ _ _ _ _ E x (δ ; γ) m').
        apply H in h1.
        destruct x.
        pose proof (C1 γ δ h1) as [h _]; auto.
        pose proof (C2 γ δ h1) as [h _]; auto.
      }

      intros h1 h2.
      destruct h1.
      {
        (* non bottom *)
        apply pdom_bind_bot_2 in h2.
        destruct h2.
        pose proof (E _ m') as [_ E'].
        pose proof (E' _ H) as [hh1 [hh2 hh3]].
        contradict (flat_bot_neq_total _ hh2).
        destruct H.
        destruct H.
        pose proof (E _ m') as [_ E'].
        pose proof (E' _ H) as [hh1 [hh2 hh3]].
        apply total_is_injective in hh2.
        induction hh2.
        destruct x.
        assert (rw_tot_pre w1 (mk_rw_tot w1 (ro_to_rw_pre (θ true)) ψ0) (δ, γ)).
        simpl.
        simpl in hh3.
        auto.
        pose proof (C1 γ δ H1) as [_ h].
        pose proof (h _ H0) as [v [ee _ ]].
        contradict (flat_bot_neq_total _ ee).
        assert (rw_tot_pre w1 (mk_rw_tot w1 (ro_to_rw_pre (θ false)) ψ0) (δ, γ)).
        simpl.
        simpl in hh3.
        auto.
        pose proof (C2 γ δ H1) as [_ h].
        pose proof (h _ H0) as [v [ee _ ]].
        contradict (flat_bot_neq_total _ ee).
      }
      
      apply pdom_bind_total_2 in h2 as [_ [b [semb h2]]].
      pose proof (ro_tot_post_pre _ _ _ _ _ _ E b (δ ; γ) m').
      apply H in semb; clear H.
      destruct b.
      pose proof (C1 γ δ semb) as [_ h].
      pose proof (h _ h2) as [x [p1 p2]].
      exists x; split; auto.
      pose proof (C2 γ δ semb) as [_ h].
      pose proof (h _ h2) as [x [p1 p2]].
      exists x; split; auto.
      
    ++

      (* | rw_case_tot : forall Γ Δ e1 e2 c1 c2 τ (wty_e1 : (Δ ++ Γ) |- e1 : BOOL) (wty_e2 : (Δ ++ Γ) |- e2 : BOOL) (wty_c1 : Γ ;;; Δ ||- c1 : τ) (wty_c2 : Γ ;;; Δ ||- c2 : τ) (wty : Γ ;;; Δ ||- Case e1 c1 e2 c2 : τ) ϕ θ1 θ2 ψ ϕ1 ϕ2, *)
      
      (*     wty_e1 |- {{rw_to_ro_pre ϕ}} e1 {{θ1}} ->  *)
      (*     wty_e2 |- {{rw_to_ro_pre ϕ}} e2 {{θ2}} ->  *)
      (*     wty_c1 ||- [{ro_to_rw_pre (θ1 true)}] c1 [{ψ}] ->  *)
      (*     wty_c2 ||- [{ro_to_rw_pre (θ2 true)}] c2 [{ψ}] ->  *)
      (*     wty_e1 |- [{ϕ1}] e1 [{b |fun _ => b = true}] ->  *)
      (*     wty_e2 |- [{ϕ2}] e2 [{b | fun _ => b = true}] ->  *)
      (*     (forall x, (rw_to_ro_pre ϕ x) -> (ϕ1 x \/ ϕ2 x)) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- [{ϕ}] Case e1 c1 e2 c2 [{ψ}] *)

      intros γ δ m; simpl; simpl in m.
      rename p1 into t1.
      rename p2 into t2.
      pose (sem_ro_exp _ _ _ wty_e1 (δ; γ)) as B1.
      pose (sem_ro_exp _ _ _ wty_e2 (δ; γ)) as B2.
      pose (sem_rw_exp _ _ _ _ wty_c1 γ δ) as X.
      pose (sem_rw_exp _ _ _ _ wty_c2 γ δ) as Y.
     

      replace (sem_rw_exp Γ Δ (CASE e1 ==> c1 OR e2 ==> c2 END) τ wty γ δ) with
        (Case2 B1 B2 X Y) 
        by  (rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_Case _ _ _ _ _ _ _ wty_e1  wty_c1 wty_e2 wty_c2)); simpl; auto).
      assert ( (rw_to_ro_pre ϕ0) (δ; γ)) as m'
          by (simpl; unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m') as [p1 p2].
      pose proof (proves_ro_prt_sound _ _ _ _ _ _ p0 _ m') as [q1 q2].
      split.
      {
        (* non empty *)
        unfold Case2.
        intro h.
        apply pdom_case2_empty_2 in h.
        destruct h as [h| [h | [[h1 h2] | [h1 h2]]]].
        apply (p1 h).
        apply (q1 h).
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ ; γ) m' h1) as m''.
        pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1 _ _ m'') as [r1 r2].
        auto.
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p0)) true (δ ; γ) m' h1) as m''.
        pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip2 _ _ m'') as [r1 r2].
        auto.
      }
      intros h1 h2.
      destruct h1.
      {
        (* non bottom *)
        apply pdom_case2_bot_2 in h2.

        destruct h2 as [[h2 h3] | [[h2  h3] | [h2 h3]]].
        contradict h3.
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ ; γ) m' h2) as m''.
        apply (sem_rw_tot_excludes_bot _ _ _ _ _ _ _ ((proves_rw_tot_sound _ _ _ _ _ _ _ trip1)) _ _ m'').
        contradict h3.
        pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p0)) true (δ ; γ) m' h2) as m''.
        apply (sem_rw_tot_excludes_bot _ _ _ _ _ _ _ ((proves_rw_tot_sound _ _ _ _ _ _ _ trip2)) _ _ m'').

        destruct (o (δ ; γ) m').
        
        pose proof (proves_ro_tot_sound _ _ _ _ _ _ t1 (δ; γ) H) as [_ h].
        destruct h2 as [h2 | h2]; contradict h2.
        intro.
        pose proof (h _ H0) as [v [H1 H2]].
        contradict (flat_bot_neq_total _ H1).
        intro.
        pose proof (h _ H0) as [v [H1 H2]].
        simpl in H2.
        rewrite H2 in H1.
        apply total_is_injective in H1.
        contradict H1; auto.
        pose proof (proves_ro_tot_sound _ _ _ _ _ _ t2 (δ; γ) H) as [_ h].
        clear h2; destruct h3 as [h2 | h2]; contradict h2.
        intro.
        pose proof (h _ H0) as [v [H1 H2]].
        contradict (flat_bot_neq_total _ H1).
        intro.
        pose proof (h _ H0) as [v [H1 H2]].
        simpl in H2.
        rewrite H2 in H1.
        apply total_is_injective in H1.
        contradict H1; auto.
      }
      
      apply pdom_case2_total_2 in h2.
      destruct h2 as [[h2 h4]|[h2 h4]]. 
      pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p)) true (δ ; γ) m' h2) as m''.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip1 _ _ m'') as [_ r2].
      pose proof (r2 _ h4) as [h2' [eq1 h3]].
      exists h2'.
      split; auto.
      pose proof (ro_prt_post_pre _ _ _ _ _ _ ((proves_ro_prt_sound _ _ _ _ _ _ p0)) true (δ ; γ) m' h2) as m''.
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ trip2 _ _ m'') as [_ r2].
      pose proof (r2 _ h4) as [h2' [eq1 h3]].
      exists h2'.
      split; auto.
      
    ++
      (* case_list *)
      apply sem_rw_prt_excludes_bot_is_tot.
      +++
        clear f0.      
        intros γ δ m; simpl in m; simpl.
        assert (rw_to_ro_pre ϕ0 (δ; γ)) as m' by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
        assert (1 <= length l).
        {
          pose proof (has_type_rw_r_has_type_rw _ _ _ _ wty).
          dependent destruction H; auto.
        }
        rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_CaseList _ _ l _ H wty_l)).
        easy_rewrite_uip.
        split.
        {
          (* nonempty *)
          intro.
          apply pdom_case_list_empty_2 in H0.
          apply Exists_exists in H0.
          destruct H0.
          destruct H0.

          clear H wty.
          dependent induction f.
          simpl in H0.
          exact H0.

          simpl in H0.
          destruct p.
          simpl in H0.
          destruct H0.
          rewrite <- H in H1; simpl in H1.
          destruct j.
          destruct p.
          pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m').
          (* pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0). *)
          destruct H1.
          destruct H0 as [H0 _]; auto.
          destruct H1.
          destruct H0 as [_ H0].
          pose proof (H0 _ H1 _ eq_refl).
          simpl in H3.
          assert (ro_to_rw_pre (q true) (δ, γ)).
          unfold ro_to_rw_pre.
          auto.
          pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ p1 _ _ H4) as [H5 _].
          auto.
          apply (IHf γ δ m m' x H).
          exact H1.
        }
        intros.
        destruct H0.
        clear H0.
        destruct H2.
        apply Exists_exists in H0.
        destruct H0.
        clear H wty.
        dependent induction f.
        simpl in H0.
        destruct H0.
        contradict H.
        simpl in H0.
        destruct p.
        simpl in H0.
        destruct H0.
        destruct H.
        destruct j.
        destruct p.
        pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m').
        (* pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0). *)
        destruct H0.
        destruct H2 as [_ H2].
        simpl in H2.
        rewrite <- H in H0.
        simpl in H0.
        pose proof (H2 _ H0 _ eq_refl).
        assert (ro_to_rw_pre (q true) (δ, γ)).
        unfold ro_to_rw_pre.
        auto.
        pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ p1 _ _ H5) as [_ H6].
        simpl in H6.
        rewrite <- H in H3.
        simpl in H3.
        pose proof (H6 _ H3).
        destruct H7.
        destruct H7.
        rewrite H1 in H7.
        apply total_is_injective in H7.
        rewrite H7.
        exact H8.

        apply (IHf γ δ m m' v x); auto.

        destruct H0.
        rewrite H0 in H1.
        contradict (flat_bot_neq_total _ H1).

      +++
        (* not bot *)
        intros γ δ m.
        assert (rw_to_ro_pre ϕ0 (δ; γ)) as m' by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto).
        assert (1 <= length l).
        {
          pose proof (has_type_rw_r_has_type_rw _ _ _ _ wty).
          dependent destruction H; auto.
        }
        rewrite (sem_rw_exp_unique _ _ _ _ wty (has_type_rw_CaseList _ _ l _ H wty_l)).
        easy_rewrite_uip.
        intro.
        destruct H0 as [_ H0].
        destruct H0.

        {
          (* when c yields bot *)

          apply Exists_exists in H0.
          destruct H0.
          clear H wty f0.
          dependent induction f.
          simpl in H0.
          destruct H0; auto. 

          simpl in H0.
          destruct p.
          simpl in H0.
          destruct H0.
          destruct H.
          rewrite <- H in H0; simpl in H0.
          destruct j.
          destruct p.
          pose proof (proves_ro_prt_sound _ _ _ _ _ _ p _ m').
          (* pose proof (proves_rw_prt_sound _ _ _ _ _ _ _ p0). *)
          destruct H0.
          destruct H1 as [_ H1].
          pose proof (H1 _ H0 _ eq_refl).
          simpl in H3.
          assert (ro_to_rw_pre (q true) (δ, γ)).
          unfold ro_to_rw_pre.
          auto.
          pose proof (proves_rw_tot_sound _ _ _ _ _ _ _ p1 _ _ H4) as [_ H5].
          pose proof (H5 _ H2).
          destruct H6.
          destruct H6.
          contradict (flat_bot_neq_total _ H6).
          apply (IHf γ δ m m' x); auto.          
        }

        {
          (* when there is no guard *)
          destruct H0 as [_ H0].
          pose proof (Forall_to_forall _ _ H0); clear H0.
          pose proof (f0 _ m').
          clear H wty f0.
          dependent induction f.
          simpl in H0.
          auto.
          simpl in H0.
          simpl in H1.

          destruct H0.
          destruct j.
          pose proof (proves_ro_tot_sound _ _ _ _ _ _  p1 _ H) as [_ H2].
          simpl in H2.
          destruct p; simpl in H1.
               
          pose proof (H1  (sem_ro_exp (Δ ++ Γ) (fst a) BOOL h (δ; γ), sem_rw_exp Γ Δ (snd a) τ h0 γ δ) ( or_introl eq_refl )) as hh.
          simpl in hh.
          destruct hh.
          pose proof (H2 _ H0).
          destruct H3.
          destruct H3.
          rewrite H4 in H3.
          apply total_is_injective in H3.
          contradict H3; auto.
          pose proof (H2 _ H0).
          destruct H3.
          destruct H3.
          contradict (flat_bot_neq_total _ H3).
          apply (IHf γ δ m m').
          intros.
          apply H1.
          simpl.
          auto.
          destruct p.
          simpl.
          right; auto.
          auto.
        }
        
      
    ++
      (* | rw_while_tot : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ, *)
      
      (*     wty_e |- [{rw_to_ro_pre ϕ}] e [{θ}] -> *)
      (*     wty_c ||- [{fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] c [{fun _ δγδ' => ϕ (fst δγδ', fst_app (snd δγδ')) /\ ψ δγδ' }] -> *)
      (*              (forall δ γ, ϕ (δ, γ) ->   *)
      (*                            ~exists f : nat -> sem_ro_ctx Δ, *)
      (*                                f 0 = δ /\ forall n, ψ (f (S n), (γ ; f n))) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- [{ϕ}] While e c [{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}] *)

      apply proves_ro_tot_sound in p.
      apply proves_rw_tot_sound in trip.
      apply (proves_rw_while_tot_sound _ _ _ _ _ _ _ _ _ _ p trip n).

Defined.
