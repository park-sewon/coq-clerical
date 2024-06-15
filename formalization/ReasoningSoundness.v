Require Import List.
Require Import Reals.
Require Import Coq.Program.Equality.
From Clerical.Preliminaries Require Import Preliminaries.
From Clerical.Powerdomain Require Import Powerdomain.
From Clerical Require Import Syntax.
From Clerical Require Import Typing.
From Clerical Require Import TypingProperties.
From Clerical Require Import Semantics.
From Clerical Require Import SemanticsProperties.
From Clerical Require Import Specification.
From Clerical Require Import ReasoningRules.

Arguments existT {_} {_}.

Fixpoint Var_sem_var_access_equiv k Γ τ (w : Γ |- Var k : τ) γ {struct w}: 
    sem_ro_exp _ _ _ w γ = pdom_unit (var_access _ _ _ w γ).
Proof.
  intros.
  dependent induction w.
  dependent destruction h.
  easy_rewrite_uip.
  rewrite pdom_lift_comp.
  simpl.
  rewrite pdom_lift_id.
  apply Var_sem_var_access_equiv.
  easy_rewrite_uip.
  destruct γ; simpl.
  apply eq_refl.
  assert (sem_ro_exp (Γ ::: σ) (VAR S k0) τ (has_type_ro_Var_S Γ σ τ k0 w) γ
          = sem_ro_exp Γ (Var k0) τ w (fst γ)).
  simpl.
  auto.
  rewrite H.
  rewrite Var_sem_var_access_equiv.
  destruct γ.
  rewrite var_access_Var_S.
  apply lp.
  apply var_access_typing_irrl.
Defined.

  
Fixpoint proves_ro_prt_Var_sound  k Γ τ (w : Γ |- Var k : τ) ϕ {struct w} :
    [| x : Γ|] |=  {{ϕ (x, var_access Γ k τ w x)}} Var k {{y : τ | ϕ (x, y)}}ᵖ.
Proof.
  exists w.
  simpl.
  intros γ m.
  rewrite Var_sem_var_access_equiv.
  simpl.
  split.
  apply (pdom_is_neg_empty_by_evidence _ (total (var_access Γ k τ w γ))).
  simpl; auto.
  intros p1 p2 p3 p4.
  rewrite p4 in p2.
  apply total_is_injective in p2.
  rewrite <- p2.
  simpl in m.
  auto.
Defined.

Fixpoint proves_ro_tot_Var_sound  k Γ τ (w : Γ |- Var k : τ) ϕ {struct w} :
    [|γ : Γ|] |= {{ϕ (γ, var_access Γ k τ w γ)}} Var k {{y : τ | ϕ (γ, y)}}ᵗ.
Proof.
  exists w.
  simpl.
  intros γ m.
  rewrite Var_sem_var_access_equiv.
  simpl.
  split.
  apply (pdom_is_neg_empty_by_evidence _ (total (var_access Γ k τ w γ))).
  simpl; auto.
  intros p1 p2.
  exists (var_access _ _ _ w γ); split; auto.  
Defined.

Lemma proves_rw_prt_Assign_sound
  Γ Δ e k τ ϕ0 (ψ0 :pred) θ (a : assignable Δ τ k)  :
  [|x : (Γ +++ Δ)|] |= {{ϕ0 (fst_app x, snd_app x)}} e {{y : τ | θ (x, y)}}ᵖ
  -> (forall γ δ x, θ ((γ; δ), x) -> ψ0 (γ, (update k x δ a, tt)))
  ->  [| γ : Γ ;;; δ : Δ |] ||= {{ϕ0 (γ, δ)}} Assign k e {{y : UNIT | ψ0 (γ, (δ, y))}}ᵖ.
Proof.
  intros.
  destruct H as [w H].
  simpl in H.
  exists (has_type_rw_Assign _ _ _ τ _ a w).
  simpl.

  intros γ δ m; simpl; simpl in m.
  split.
  intro.
  apply pdom_lift_empty_2 in H1.
  apply pdom_lift_empty_2 in H1.
  pose proof (H (γ; δ)).
  simpl in H2.
  reduce_tedious H2.  
  pose proof (H2 m); clear H2.
  destruct H3.
  exact (H2 H1).
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
  pose proof (H (γ; δ)).
  simpl in H4.
  reduce_tedious H4.
  pose proof (H4 m); clear H4.
  destruct H5 as [_ H5].
  pose proof (H5 (total s) H1 _ eq_refl).
  exact (H0 γ δ s H4).
Defined.

Lemma proves_rw_tot_Assign_sound
  Γ Δ e k τ ϕ0 (ψ0 :pred) θ (a : assignable Δ τ k) :
  [|x : (Γ +++ Δ)|] |= {{ϕ0 (fst_app x, snd_app x)}} e {{y : τ | θ (x, y)}}ᵗ
  -> (forall γ δ x, θ ((γ; δ), x) -> ψ0 (γ, (update k x δ a, tt)))
  ->  [|γ : Γ ;;; δ : Δ|] ||= {{ϕ0 (γ, δ)}} Assign k e {{y : UNIT | ψ0 (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  pose proof (sem_ro_tot_is_prt_excludes_bot _ _ _  _ _ H) as [[h1 h2] h3].
  simpl in h2, h3.
  apply (sem_rw_prt_excludes_bot_is_tot _ _ _ _ _ _
                                        (has_type_rw_Assign _ _ _ τ _ a h1)).
  apply (proves_rw_prt_Assign_sound _ _ _ _ _ _ _ _ a (existT h1 h2) H0).
  
  (* non bottom *)
  intros.
  simpl.
  intro.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct x0.

  pose proof (h3 (γ; δ)).
  reduce_tedious H5.
  pose proof (H5 H1).
  rewrite  (sem_ro_exp_unique _ _ _ h1 (projT1 H)) in H2.
  exact (H6 H2).

  reduce_tedious H4.
  unfold pdom_lift' in H3.
  rewrite <- H4 in H3.
  contradict (flat_total_neq_bot _ H3).
Defined.

Lemma proves_rw_while_prt_sound : forall Γ Δ  e c ϕ θ,   
    [|γ : _|]|= {{ϕ (fst_app γ, snd_app γ)}} e {{y : BOOL | θ (γ, y)}}ᵖ ->
    [|γ : Γ ;;; δ : Δ|] ||= {{θ ((γ ; δ), true)}} c {{_ : UNIT | ϕ (γ, δ)}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [|γ : Γ ;;; δ : Δ|] ||= {{ϕ (γ, δ)}} While e c {{_ : UNIT | ϕ (γ, δ) /\ θ  ((γ ; δ), false)}}ᵖ.
Proof.
  intros Γ Δ e c ϕ θ [wb BB] [wc CC].
  simpl in BB, CC.
  exists (has_type_rw_While _ _ _ _ wb wc).
  intros P Q.
  simpl in P.
  simpl in Q.
  unfold P, Q.
  clear P Q.
  intros γ δ m. 
  pose (fun d => sem_ro_exp _ _ _ wb (γ; d)) as B.
  pose (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ wc γ d)) as C.
  replace (sem_rw_exp Γ Δ (WHILE e DO c END) UNIT (has_type_rw_While _ _ _ _ wb wc) γ δ) with
    (pdom_lift (fun x => (x, tt)) (pdom_while B C δ)) by auto.
  pose proof (BB (γ ; δ)) as [p1 p2].
  reduce_tedious; auto.
                                 
  (* important sub lemmas *)
  pose (fun n δ => pdom_fun_bot_chain (pdom_W B C) (pdom_W_monotone B C) n δ) as thechain.
  (* the chain respects invariant *)
  assert (forall n, forall δ1 δ2, ϕ (γ, δ1) -> total δ2 ∈ thechain n δ1 -> ϕ (γ, δ2) /\ (θ ((γ; δ2), false)) ) as l.
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
    (* assert (rw_to_ro_pre ϕ (δ1; γ))         *)
    (*   by (unfold rw_to_ro_pre; rewrite tedious_equiv_1; auto). *)
    
    (* pose proof (ro_prt_post_pre _ _ _ _ _ _ ((BB)) true (δ1 ; γ) H0 H3) as m''. *)
    pose proof (CC γ δ1) as [_ r2].
    reduce_tedious; auto.
    apply  (ro_prt_post_pre _ _ _ _ _ wb ((existT wb BB)) true (γ; δ1) ).
    reduce_tedious; auto.
    auto.
    simpl in r2.
    assert (total (d, tt) ∈  sem_rw_exp Γ Δ c UNIT wc γ δ1).
    {
      unfold C in hh1.
      apply pdom_lift_total_2 in hh1.
      destruct hh1.
      destruct H0.
      destruct x.
      destruct s0.
      simpl in H1.
      rewrite H1; auto.
    }
    pose proof (r2 (total (d, tt)) H0 _ eq_refl).
    simpl in H1; auto.
    exact hh2.
    apply total_is_injective in H4.
    rewrite <- H4 in H1.
    simpl in H1.
    apply total_is_injective in H1.    
    induction H1.
    split; auto.
    apply (ro_prt_post_pre _ _ _ _ _ wb ((existT wb BB)) false (γ; δ1)); auto.
    reduce_tedious; auto.
  }

  (* nondempty *)
  assert (forall n, forall δ1, ϕ (γ, δ1) -> ~ pdom_is_empty (thechain n δ1)) as r.
  {
    intro n.
    induction n.
    (* base case *)
    intros; simpl.
    apply (pdom_is_neg_empty_by_evidence _ (bot _)); simpl; auto.
    (* induction step *)
    intros; simpl.
    pose proof (IHn _ H).
    apply pdom_neg_empty_exists in H0 as [δ' h1].
    intro.
    unfold pdom_W in H0.
    apply pdom_bind_empty_2 in H0.
    destruct H0.
    pose proof (BB (γ; δ1)) as [h _]; auto.
    reduce_tedious; auto.
    destruct H0.
    destruct H0.
    destruct x.
    apply pdom_bind_empty_2 in H1.
    destruct H1.
    unfold C in H1.
    apply pdom_lift_empty_2 in H1.
    pose proof (CC γ δ1 ) as [r1 _]; auto.
    reduce_tedious; auto.
    apply (ro_prt_post_pre _ _ _ _ _ wb ((existT wb BB)) true (γ; δ1)); auto.
    reduce_tedious; auto.
    destruct H1.
    destruct H1.
    apply (fun k => IHn x k H2).
    pose proof (CC γ δ1) as [_ r2].
    reduce_tedious; auto.
    apply (ro_prt_post_pre _ _ _ _ _ wb ((existT wb BB)) true (γ; δ1)); auto.
    reduce_tedious; auto.
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
      exists (Nat.pred x0).
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
  forall Γ Δ e c ϕ θ ψ, 
    [| x : _ |] |= {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y) }}ᵗ ->
    [|γ : Γ ;;; δ : Δ|] ||= {{θ ((γ ; δ), true)}} c {{_ : UNIT | ϕ (γ, δ)}}ᵗ ->
    [|γ : (Δ +++ Γ) ;;; δ : Δ|] ||= {{θ ((snd_app γ; δ), true) /\ δ = fst_app γ}} c {{_ : UNIT | ψ (γ, δ) }}ᵗ -> 
    (forall γ δ, ϕ (γ, δ) ->
                 ~exists f : nat -> sem_ctx Δ,
                     f 0 = δ /\ forall n, ψ ((f n; γ), f (S n))) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [|γ : Γ ;;; δ : Δ|] ||= {{ϕ (γ, δ)}} While e c {{_ : UNIT | ϕ (γ, δ) /\ θ  ((γ ; δ), false)}}ᵗ.
Proof.
  intros Γ Δ e c ϕ θ ψ [wb BB] [wc' CC'] [wc CC] chainp.
  apply (sem_rw_prt_excludes_bot_is_tot _ _ _ _ _ _ (has_type_rw_While _ _ _ _ wb wc')).
  
  apply (proves_rw_while_prt_sound).
  pose proof (fst (sem_ro_tot_is_prt_excludes_bot _ _ _ _ _ (existT wb BB))).
  exact H.
  pose proof (fst (sem_rw_tot_is_prt_excludes_bot _ _ _ _ _ _ (existT wc' CC'))).
  exact H.
  


  (* non empty *)
  intros.
  pose (fun d => sem_ro_exp _ _ _ wb (γ; d)) as B.
  pose (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ (wc') γ d)) as C.
  replace (sem_rw_exp Γ Δ (WHILE e DO c END) UNIT (has_type_rw_While _ _ _ _ wb wc') γ δ) with
    (pdom_lift (fun x => (x, tt)) (pdom_while B C δ)) by auto.
  intro p.

  assert (forall x : sem_ctx Δ,
             ϕ (γ, x) -> ~ pdom_is_empty (B x) /\ (forall v : flat bool, v ∈ B x -> exists v' : bool, v = total v' /\ θ ((γ; x), v'))) as p1.
  {
    
    intros x m.
    pose proof (BB (γ; x)).
    simpl in H0.
    reduce_tedious H0.
    pose proof (H0 m).
    auto.
  }
  
  assert (forall x : sem_ctx Δ,
             θ ((γ; x), true) ->
             ~ pdom_is_empty (C x) /\ (forall v : flat (sem_ctx Δ), v ∈ C x -> exists v' : sem_ctx Δ, v = total v' /\ ϕ (γ, v') /\ ψ ((x; γ), v'))) as p2.
  {
    intros x m.
    pose proof (CC (x; γ) x).
    simpl in H0.
    reduce_tedious H0.
    pose proof (H0 (conj m eq_refl)).
    destruct H1; split; auto.
    intro.
    unfold C in H3.
    apply pdom_lift_empty_2 in H3.
    rewrite
      (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wc γ x x) in H3.
    auto.

      intros.
  destruct v.
  unfold C in H3.
  apply pdom_lift_bot_2 in H3.
  rewrite
    (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wc γ x x) in H3.
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
    (sem_rw_exp_auxiliary_ctx _ _ _ _ _ _ wc γ x x) in H3.
  pose proof (H2 _ H3).
  destruct H4 as [t1 [t2 t3]].
  apply total_is_injective in t2.
  exists s; split; auto.
  rewrite <- t2 in t3; simpl in t3.
  split; auto.

  pose proof (CC' _ _ m).
  simpl in H4.
  destruct H4.
  rewrite (sem_rw_exp_auxiliary_ctx Γ Δ Δ _ _ wc' wc γ x x) in H5.
  pose proof (H5 (total (s, tt)) H3) as [h1 [h2 h3]].
  apply total_is_injective in h2.
  rewrite <- h2 in h3; simpl in h3; exact h3. 
  }
  
  pose proof
       
       (pdom_While_bot B C
                       (fun d => ϕ (γ, d))
                       (fun b d => θ ((γ; d), b))
                       (fun d d' => ψ ((d; γ), d')) 
       p1 p2 δ) as [f h]; auto.
  
  apply pdom_lift_bot_2 in p.
  auto.

  destruct h.
  pose proof (chainp γ δ H).
  contradict H2.
  exists f.
  split; auto.
Defined.



(* | rw_case_list_prt : forall Γ Δ l τ *)
(*                             (θ : ForallT (fun _ =>  sem_ctx (Γ +++ Δ) * bool -> Prop) l) *)
(*                             ϕ ψ,  (1 <= length l)%nat -> *)
(*     ForallT1 _  *)
(*     (fun ec  (θ : sem_ctx (Γ +++ Δ) * bool ->  Prop)  => *)
         
(*        ('x : (Γ +++ Δ) |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ) *)
(*        * ('γ : Γ ;;; 'δ : Δ ||- {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵖ) *)
(*     )%type l θ -> *)
(*     (*——————————-——————————-——————————-——————————-——————————-*) *)
(*     'γ : Γ ;;; 'δ : Δ ||- {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵖ *)
Lemma proves_rw_case_prt_sound_tmp :
  forall Γ Δ l τ (θ : ForallT (fun _ =>  sem_ctx (Γ +++ Δ) * bool -> Prop) l) ϕ ψ,
    (1 <= length l)%nat ->
    ForallT1 _ (fun ec (θ : sem_ctx (Γ +++ Δ) * bool ->  Prop) =>
                  ([| x : (Γ +++ Δ) |] |= {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ)
                  * ([| γ : Γ ;;; δ : Δ |] ||= {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵖ)
               )%type l θ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||- CaseList l : τ.
Proof.
  intros.
  apply (has_type_rw_CaseList _ _ l _ H).
  clear H.
  dependent induction X.
  apply ForallT_nil.
  apply ForallT_cons.
  destruct r.
  split.
  destruct s; auto.
  destruct s0; auto.
  apply IHX.
Defined.



Lemma proves_rw_case_prt_sound :
  forall Γ Δ l τ (θ : ForallT (fun _ =>  sem_ctx (Γ +++ Δ) * bool -> Prop) l) ϕ ψ,
    (1 <= length l)%nat ->
    ForallT1 _ (fun ec (θ : sem_ctx (Γ +++ Δ) * bool ->  Prop) =>
                  ([| x : (Γ +++ Δ) |] |= {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ)
                  * ([| γ : Γ ;;; δ : Δ |] ||= {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵖ)
               )%type l θ -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    [| γ : Γ ;;; δ : Δ |] ||= {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵖ.
Proof.
  intros.
  exists (proves_rw_case_prt_sound_tmp Γ Δ l τ θ ϕ ψ H X).
  intros P Q.
  simpl in P, Q.
  unfold P, Q.
  clear P Q.
  intros γ δ m.
  split.
  {
    (* nonempty semantics *)
    simpl.
    intro.
    apply pdom_case_list_empty_2 in H0.
    apply Exists_exists in H0.
    destruct H0.
    destruct H0.
    clear H .
    dependent induction X.
    simpl in H0.
    exact H0.
    simpl in H0.
    destruct x, r.
    simpl in H0.
    destruct H0.
    clear IHX.

    simpl in H1.
    injection H.
    intros.
    induction H0.
    induction H2.
    destruct s.
    destruct s0.
    simpl in a0, a1.
    clear H.
    assert (ϕ (fst_app (γ; δ), snd_app (γ; δ))) as m'.
    reduce_tedious; auto.
    
    destruct H1.
    pose proof (a0 _ m').
    destruct H0.
    exact (H0 H).
    destruct H.
    pose proof (a0 _ m').
    destruct H1 as [_ H1].
    pose proof (H1 _ H true eq_refl).
    pose proof (a1 _ _ H2) as [H3 _].
    exact (H3 H0).
    apply (IHX γ δ m _ H H1).
  }

  intros.
  
 
  rewrite H1 in H0.
  clear H1.
  apply pdom_case_list_total_2 in H0.
  simpl in H0.
  apply Exists_exists in H0.
  destruct H0.
  destruct H0.
  destruct x.
  simpl in H0.
  clear H.
  dependent induction X.
  simpl in H0.
  contradict H0.
  destruct  a, r, s1, s2.
  destruct v'.
  simpl in a, a0.
  simpl in H0.
  destruct H0.
  injection H.
  intros i j.
  induction i.
  induction j.
  clear H.
  simpl in H1.
  destruct H1.
  simpl in x.
  pose proof (a (γ; δ)).
  assert (ϕ (fst_app (γ; δ), snd_app (γ; δ))) as m'.
  reduce_tedious; auto.
  apply H1 in m'.
  destruct m'.
  pose proof (H3 _ H true eq_refl).
  pose proof (a0 _ _ H4).
  destruct H5.
  pose proof (H6 _ H0 _ eq_refl).
  exact H7.
  simpl in H.
  apply (IHX γ δ m v (s1, s2) s s0 H H1).
Defined.

Lemma proves_rw_case_tot_sound_tmp :
  forall Γ Δ l τ
         (θ : ForallT (fun _ =>  sem_ctx (Δ ++ Γ) * bool -> Prop) l)
         (ϕi : ForallT (fun _ => sem_ctx (Δ ++ Γ) -> Prop) l)
         ϕ ψ,  (1 <= length l)%nat -> 
     ForallT2 _ _
    (fun ec (θ : sem_ctx (Δ ++ Γ) * bool -> Prop) (ϕi : sem_ctx (Δ ++ Γ) -> Prop)  =>
         
    ([| x : (Δ ++ Γ) |] |= {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ) *
    ([| γ : Γ ;;; δ : Δ |] ||= {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵗ) * 
    ([| x : (Δ ++ Γ) |] |= {{ϕi x}} fst ec {{b : BOOL | b = true}}ᵗ)) %type l θ ϕi ->
    (forall x, (ϕ (fst_app x, snd_app x)) -> ForallT_disj _ (fun _ ϕi => ϕi x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    Γ ;;; Δ ||- CaseList l : τ.
Proof.
  intros.
  apply (has_type_rw_CaseList _ _ l _ H).
  clear H H0.
  
  dependent induction X.
  apply ForallT_nil.
  apply ForallT_cons.
  destruct r.
  split.
  destruct s; auto.
  destruct p0; auto.
  destruct s1; auto.
  apply IHX.
Defined.


  
Lemma proves_rw_case_tot_sound :
  forall Γ Δ l τ
         (θ : ForallT (fun _ =>  sem_ctx (Δ ++ Γ) * bool -> Prop) l)
         (ϕi : ForallT (fun _ => sem_ctx (Δ ++ Γ) -> Prop) l)
         ϕ ψ,  (1 <= length l)%nat -> 
     ForallT2 _ _
    (fun ec (θ : sem_ctx (Δ ++ Γ) * bool -> Prop) (ϕi : sem_ctx (Δ ++ Γ) -> Prop)  =>
         
    ([| x : (Δ ++ Γ) |] |= {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ (x, y)}}ᵖ) *
    ([| γ : Γ ;;; δ : Δ |] ||= {{θ ((γ ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵗ) * 
    ([| x : (Δ ++ Γ) |] |= {{ϕi x}} fst ec {{b : BOOL | b = true}}ᵗ)) %type l θ ϕi ->
    (forall x, (ϕ (fst_app x, snd_app x)) -> ForallT_disj _ (fun _ ϕi => ϕi x) l ϕi) ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [| γ : Γ ;;; δ : Δ |] ||= {{ϕ (γ, δ)}} CaseList l {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  
  intros.
  apply (sem_rw_prt_excludes_bot_is_tot _ _ _ _ _ _ 
                                        (proves_rw_case_tot_sound_tmp Γ Δ l τ θ ϕi ϕ ψ H X H0)).
  apply (proves_rw_case_prt_sound Γ Δ l τ θ ϕ ψ H).
  clear H H0.
  dependent induction X.
  apply ForallT1_nil.
  apply ForallT1_cons.
  exact IHX.
  destruct r.
  destruct p0.
  split; auto.
  apply sem_rw_tot_is_prt_excludes_bot in s1.
  auto.

  intros.
  intro.
  apply pdom_case_list_bot_2 in H2.

  destruct H2.
  {
    (* when there is a guarded command taht is bot *)
    simpl in H2.
    apply Exists_exists in H2.
    destruct H2.
    clear H.
    destruct H2.
    clear H0.
    assert (H0 : True) by auto.
    dependent induction X.
    simpl in H.
    exact H.
    simpl in H.
    destruct r as [[[w1 r1] [w2 r2]] [w3 r3]].
    simpl in r1, r2, r3.
    simpl in H.
    destruct x.
    simpl in H.
    destruct H.
    simpl in H2.
    injection H; intros i j; induction i; induction j.
    simpl in H1.
    assert (ϕ (fst_app (γ; δ), snd_app (γ; δ))) as m' by (reduce_tedious; auto).
    pose proof (r1 (γ; δ) m') as [_ tp].
    destruct H2 as [bb cc].
    rewrite (sem_ro_exp_unique _ _ _ w1 w3) in tp.
    pose proof (tp _ bb _ eq_refl).
    pose proof (r2 _ _ H2) as [_ tpp].
    pose proof (tpp _ cc).
    destruct H3.
    destruct H3.
    contradict (flat_bot_neq_total _ H3).
    apply (IHX  _ _ H1 _   H H2).
    exact H0.
  }
  {
    (* when there is no chooseable branch *)
    assert ( ϕ (fst_app (γ; δ), snd_app (γ; δ))) as m' by (reduce_tedious; auto).
    pose proof (H0 (γ; δ) m').
    clear H0 H.
    
    (* pose proof (Forall_to_forall _ _ H2); clear H2. *)
    dependent induction X.
    simpl in H2, H3.
    exact H3.
    simpl in H2, H3.
    destruct r as [[[h1 tt1] [w2 tt2]] [w t]].
    simpl in H2, H3, tt1, tt2, t.
    destruct H3.
    dependent destruction H2.
    clear H2.
    pose proof (t _ H0) as [_ r].
    destruct H as [H|H].
    destruct (r (total false) H) as [p1 [p2 p3]].
    rewrite p3 in p2.
    apply total_is_injective in p2.
    contradict p2; auto.
    destruct (r (bot _) H) as [p1 [p2 p3]].
    rewrite p3 in p2.
    apply flat_bot_neq_total in p2.
    contradict p2; auto.
        
    dependent destruction H2.
    apply (IHX _ _ H1 H2 m' H0).
  }
Defined.

Lemma proves_ro_prt_sound : forall Γ e τ ϕ ψ,
    [x : Γ]|- {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵖ -> [|x : Γ|]|= {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵖ
with proves_ro_tot_sound : forall Γ e τ ϕ ψ,
    [x : Γ]|- {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵗ -> [|x : Γ|]|= {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵗ
with proves_rw_prt_sound : forall Γ Δ e τ ϕ ψ,
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ -> [|γ : Γ ;;; δ : Δ|] ||= {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ 
with proves_rw_tot_sound : forall Γ Δ e τ ϕ ψ,
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ -> [|γ : Γ ;;; δ : Δ|] ||= {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ. 
Proof.
  + (*  partial correctness triple for read only expressions *)
    intros Γ e τ w ϕ trip.

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
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip).
      destruct H.
      exists x.
      simpl.
      simpl in a1.
      intros γ m.
      apply a in m.
      destruct (a1 γ m).
      split.
      exact H.      
      intros.
      apply a0.
      apply (H0 _ H1 _ H2).

    ++
      (* | ro_exfalso_prt : forall Γ e τ (w : Γ |- e : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*)     *)
      (*     w |- {{ (fun _ => False) }} e {{ Q }} *)
      exists h.
      simpl.
      intros γ m.
      simpl in m.
      contradict m; auto.
      
    ++
      (* | ro_conj_prt : forall Γ e τ (w : Γ |- e : τ) P Q Q', *)

      (*     w |- {{P}} e {{Q}} ->  *)
      (*     w |- {{P}} e {{Q'}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{P}} e {{Q /\\\ Q'}} *)
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ m; simpl in m; simpl.
      pose proof (t1 _ m) as [p1 p2].
      pose proof (t2 _ m) as [q1 q2].
      split; auto.
      intros v p v' p'.
      rewrite (sem_ro_exp_unique _ _ _ w2 w1) in q2.
      split; try apply (p2 v p v' p'); try apply (p2 v p v' p').
      apply (q2 v p v' p').
      
    ++

      
      (* | ro_disj_prt : forall Γ e τ (w : Γ |- e : τ) P P' Q, *)

      (*     w |- {{P}} e {{Q}} ->  *)
      (*     w |- {{P'}} e {{Q}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{P \// P'}} e {{Q}} *)
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ m; simpl in m; simpl.
      destruct m as [m|m].      
      apply (t1 _ m).
      rewrite (sem_ro_exp_unique _ _ _ w2 w1) in t2.
      apply (t2 _ m).

    ++
      (* (** variables and constants *) *)
      (* | ro_var_prt : forall Γ k τ (w : Γ |- VAR k : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{fun γ => Q (var_access Γ k τ w γ) γ}} VAR k {{Q}} *)
      apply proves_ro_prt_Var_sound.
      
    ++
      (* | ro_skip_prt : forall Γ (w : Γ |- SKIP : UNIT) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q tt}} SKIP {{Q}} *)
      exists (has_type_ro_Skip _).
      simpl.
      intros.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      destruct p3; auto.

      
    ++
      (* | ro_true_prt : forall Γ (w : Γ |- TRUE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q true}} TRUE {{Q}} *)
      
      exists (has_type_ro_True _).
      simpl.
      intros γ m; simpl in m; simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

    ++
      (* | ro_false_prt : forall Γ (w : Γ |- FALSE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q false}} FALSE {{Q}} *)

      exists (has_type_ro_False _).
      intros γ m; simpl in m; simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2 p3 p4.
      rewrite <- p2 in p4; injection p4; intro j; rewrite <- j; auto. 

      

    ++
      (* | ro_int_prt : forall Γ k (w : Γ |- INT k : INTEGER) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- {{Q k}} INT k {{Q}} *)

      exists (has_type_ro_Int _ _).
      intros γ m; simpl in m; simpl.
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
      pose proof (proves_rw_prt_sound _ _ _ _
                                      ([γ : Γ ;;; _ : nil]||- {{P (γ, tt)}})
                                      ([γ : Γ ;;; _ : nil]||- {{y : τ | Q (γ, (tt, y)) }})
                                      p) as [wty t].
      simpl in t.
      exists (has_type_ro_rw _ _ _ wty).
      simpl.
      intros γ m; simpl in m; simpl.
      split.
      intro h.
      apply pdom_lift_empty_2 in h.
      apply (t _ tt m).
      exact h.
      intros x1 [x2 [q1 q2]] x3 x4.
      pose proof (t _ tt m) as [_ p2].

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
      (* (** coercion and exponentiation *) *)
      (* | ro_coerce_prt : forall Γ e (w : Γ |- e : INTEGER) P Q (w' : Γ |- RE e : REAL), *)
      
      (*     w |- {{P}} e {{y | Q (IZR y)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} RE e {{Q}} *)

      pose proof (proves_ro_prt_sound _ _ _
                                      _
                                      ([γ : Γ]|- {{y : INTEGER | Q (γ, IZR y) }})
                                      trip) as [ty t].
      simpl in t.
      exists (has_type_ro_OpZRcoerce _ _ ty).
      simpl.
      intros γ m; simpl in m; simpl.
      pose proof (t γ m) as [p1 p2].
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

      
      pose proof (proves_ro_prt_sound _ _ _
                                      _
                                      ([γ : Γ]|- {{y : INTEGER | Q (γ, pow2 y) }})
                                      trip) as [ty t].
      simpl in t.
      exists (has_type_ro_OpZRexp _ _ ty).
      simpl.
      intros γ m; simpl in m; simpl.
      pose proof (t γ m) as [p1 p2].
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

      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZplus _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 :+: e2) INTEGER ((has_type_ro_OpZplus _ _ _ w1 w2))  γ
              =
                pdom_lift2 (BinInt.Z.add) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).
               
      
    ++
      (* | ro_int_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :*: e2) {{ψ}} *)


      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZmult _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 :*: e2) INTEGER ((has_type_ro_OpZmult _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Zmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).
               

    ++
      (* | ro_int_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 :-: e2) {{ψ}} *)


      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZminus _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 :-: e2) INTEGER ((has_type_ro_OpZminus _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Zminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).


    ++
      (* (** real arithmetic  *) *)
      (* | ro_real_op_plus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;+; e2) {{ψ}} *)

      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRplus _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 ;+; e2) REAL ((has_type_ro_OpRplus _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Rplus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

    ++
      (* | ro_real_op_mult_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;*; e2) {{ψ}} *)


      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRmult _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 ;*; e2) REAL ((has_type_ro_OpRmult _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Rmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).


    ++
      (* | ro_real_op_minus_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post), *)

      (*     w1 |- {{ϕ}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{ϕ}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} (e1 ;-; e2) {{ψ}} *)



      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRminus _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 ;-; e2) REAL ((has_type_ro_OpRminus _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Rminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).


    ++
      (* (** reciprocal *) *)
      (* | ro_recip_prt : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ, *)

      (*     w |- {{ϕ}} e {{θ}} ->  *)
      (*     (θ /\\\ (fun x γδ => x <> 0%R) ->>> fun x => ψ (/x)%R) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{ϕ}} UniOp OpRrecip e {{ψ}} *)

      pose proof (proves_ro_prt_sound _ _ _ _ _ trip) as [w1 p2'].
      simpl in p2'.
      exists (has_type_ro_OpRrecip _ _ w1).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.      
      intros γ m; simpl in m.
      pose proof (p2' _ m) as [p1 p2].
      split.
      {
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
      assert (sem_ro_exp Γ (;/; e) REAL (has_type_ro_OpRrecip _ _ w1) γ =
                pdom_bind Rrecip (sem_ro_exp Γ e REAL w1 γ)).
      auto.
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
        assert (H : x <> 0%R) by (apply Rlt_not_eq, r). 
        pose proof (ψ0 γ x (conj (p2 _ h1 x eq_refl) H)) as jj.
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
        assert (H : x <> 0%R) by (apply Rgt_not_eq, r). 
        pose proof (ψ0 γ x (conj (p2 _ h1 x eq_refl) H)) as jj.
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



      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZeq _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 :=: e2) BOOL ((has_type_ro_OpZeq _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Z.eqb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

      
    ++
      (* | ro_int_exp_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post), *)

      (*     w1 |- {{P}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{P}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} (e1 :<: e2) {{ψ}} *)


      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZlt _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ (e1 :<: e2) BOOL ((has_type_ro_OpZlt _ _ _ w1 w2))  γ
              =
                pdom_lift2 (Z.ltb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)).
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
      rewrite H1; apply (ψ0 _ x1 x0  (p2 _ H2 _ eq_refl) (q2 _ H _ eq_refl)).

      
    ++
      (* (** real exparison  *) *)
      (* | ro_real_lt_prt : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) P ψ1 ψ2 (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post), *)
      
      (*     w1 |- {{P}} e1 {{ψ1}} ->  *)
      (*     w2 |- {{P}} e2 {{ψ2}} ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- {{P}} (e1 ;<; e2) {{ψ}} *)

      pose proof (proves_ro_prt_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_prt_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRlt _ _ _ w1 w2).
      intros P Q.
      simpl in P, Q.
      unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
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
      assert (sem_ro_exp Γ _ _ (has_type_ro_OpRlt _ _ _ w1 w2) γ  = pdom_bind2 Rltb (sem_ro_exp Γ e1 REAL w1 γ) (sem_ro_exp Γ e2 REAL w2 γ)).
      auto.
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
      unfold Rltb'' in ψ0.
      clear H H0.
      destruct H3.
      destruct x0.
      simpl in H0.
      contradict (flat_bot_neq_total _ H0).
      simpl in H0.
      injection H0; intros i j.
      induction i, j.
      
      pose proof (ψ0  γ r1 x (p2 _ H _ eq_refl) (q2 _ H2 _ eq_refl)).
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

      pose proof (proves_ro_tot_sound _ _ _ _
                                      ([(γ, x) : (Γ ::: INTEGER)]|- {{y : REAL | θ (γ, x, y) }})
                                      p) as [w1 p2'].
      simpl in p2'.
      exists (has_type_ro_Lim _ _ w1).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.      
      intros γ m; simpl in m.
      pose proof (e0 γ m).
      destruct H as [y h1].
      destruct h1 as [h1 h2].
      
      split.
      {
        apply (pdom_is_neg_empty_by_evidence _ (total y)).
        simpl.
        unfold Rlim_def.
        exists y; split; auto.
        intros.
        split.
        simpl.
        destruct (p2' (γ, x)); auto.
        
        intros.
        destruct z.
        destruct (p2' (γ,  x) m) as [_ h].
        pose proof (h (bot R) H).
        destruct H0.
        destruct H0.
        contradict (flat_bot_neq_total _ H0).
        exists r; split; auto.
        destruct (p2' (γ,  x) m) as [_ h].
        pose proof (h _ H).
        destruct H0.
        destruct H0.
        injection H0; intro j; rewrite <- j in H1; clear j.
        exact (h2 _ _ H1).
      }

      intros.
      assert (total y = total v').
      apply (Rlim_def_unique ((fun x : Z => sem_ro_exp (INTEGER :: Γ) e REAL w1 (γ, x)))); auto.
      unfold Rlim_def.
      exists y.
      split; auto.
      intros.
      split; intros.
      destruct (p2' (γ, x) m); auto. 
      destruct z.
      destruct (p2' (γ, x) m) as [_ h].
      pose proof (h (bot R) H1).
      destruct H2.
      destruct H2.
      contradict (flat_bot_neq_total _ H2).
      exists r; split; auto.
      destruct (p2' (γ, x) m) as [_ h].
      pose proof (h _ H1).
      destruct H2.
      destruct H2.
      apply h2.
      injection H2; intro j; rewrite j; auto.
      rewrite <- H0; auto.
      injection H1; intro j; rewrite <- j; auto.


  + (*  total correctness triple for read only expressions *)
    intros Γ e τ ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | ro_imply_tot : forall Γ e τ (w : Γ |- e : τ) P Q P' Q', *)

      (*     P' ->> P ->  *)
      (*     w |- [{ P }] e [{ Q }] ->  *)
      (*     Q ->>> Q' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{ P'}]  e [{ Q' }] *)

      pose proof (proves_ro_tot_sound _ _ _ _ _ trip).
      destruct H.
      exists x.
      simpl.
      simpl in a1.
      intros γ m.
      apply a in m.
      destruct (a1 γ m).
      split.
      exact H.      
      intros.
      destruct (H0 _ H1).
      exists x0.
      destruct H2; split; auto.

    ++
      (* | ro_exfalso_tot : forall Γ e τ (w : Γ |- e : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*)     *)
      (*     w |- [{ (fun _ => False) }] e [{ Q }] *)

      exists h.
      simpl.
      intros γ m.
      simpl in m.
      contradict m; auto.
      
    ++
      (* | ro_conj_tot : forall Γ e τ (w : Γ |- e : τ) P Q Q', *)
      

      (*     w |- [{P}] e [{Q}] ->  *)
      (*     w |- [{P}] e [{Q'}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{P}] e [{Q /\\\ Q'}] *)

      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ m; simpl in m; simpl.
      pose proof (t1 _ m) as [p1 p2].
      pose proof (t2 _ m) as [q1 q2].
      split; auto.
      intros v p.
      pose proof (p2 _ p).
      destruct H.
      exists x.
      destruct H; split; auto.
      split; auto.
      rewrite (sem_ro_exp_unique _ _ _ w2 w1) in q2.
      pose proof (q2 _ p).
      destruct H1.
      destruct H1.
      rewrite H in H1.
      injection H1; intro j; rewrite j; auto.
      
    ++
      (* | ro_disj_tot : forall Γ e τ (w : Γ |- e : τ) P P' Q, *)

      (*     w |- [{P}] e [{Q}] ->  *)
      (*     w |- [{P'}] e [{Q}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{P \// P'}] e [{Q}] *)

      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ m; simpl in m; simpl.
      destruct m as [m|m].      
      apply (t1 _ m).
      rewrite (sem_ro_exp_unique _ _ _ w2 w1) in t2.
      apply (t2 _ m).

    ++
      (* (** variables and constants *) *)
      (* | ro_var_tot : forall Γ k τ (w : Γ |- VAR k : τ) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{fun γ => Q (var_access Γ k τ w γ) γ}] VAR k [{Q}] *)
      apply proves_ro_tot_Var_sound.

    ++
      (* | ro_skip_tot : forall Γ (w : Γ |- SKIP : UNIT) Q, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q tt}] SKIP [{Q}] *)

      exists (has_type_ro_Skip _).
      simpl.
      intros.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists tt.
      rewrite p2; auto.

    ++
      (* | ro_true_tot : forall Γ (w : Γ |- TRUE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q true}] TRUE [{Q}] *)

            
      exists (has_type_ro_True _).
      simpl.
      intros γ m; simpl in m; simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists true; split; auto.

    ++
      (* | ro_false_tot : forall Γ (w : Γ |- FALSE : BOOL) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q false}] FALSE [{Q}] *)


      exists (has_type_ro_False _).
      simpl.
      intros γ m; simpl in m; simpl.
      split.
      apply pdom_unit_neg_is_empty.
      intros p1 p2.
      exists false; split; auto.

    ++
      (* | ro_int_tot : forall Γ k (w : Γ |- INT k : INTEGER) Q, *)

      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w |- [{Q k}] INT k [{Q}] *)

      exists (has_type_ro_Int _ _).
      simpl.
      intros γ m; simpl in m; simpl.
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

      pose proof (proves_rw_tot_sound _ _ _ _
                                      ([γ : Γ ;;; _ : nil]||- {{P (γ, tt)}})
                                      ([γ : Γ ;;; _ : nil]||- {{y : τ | Q (γ, (tt, y)) }})
                                      p) as [wty t].
      simpl in t.
      exists (has_type_ro_rw _ _ _ wty).
      simpl.
      intros γ m; simpl in m; simpl.
      split.
      intro h.
      apply pdom_lift_empty_2 in h.
      apply (t _ tt m).
      exact h.
      intros x1 [x2 [q1 q2]].
      destruct (t _ tt m).
      pose proof (H0 _ q1).
      destruct H1.
      destruct x.
      exists s.
      destruct H1; split; auto.
      rewrite <- q2.
      rewrite H1.
      simpl.
      auto.


    ++
      (* (** coercion and exponentiation *) *)
      (* | ro_coerce_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- RE e : REAL), *)
      
      (*     w |- [{ϕ}] e [{y | ψ (IZR y)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] RE e [{ψ}] *)

      pose proof (proves_ro_tot_sound _ _ _
                                      _
                                      ([γ : Γ]|- {{y : INTEGER | Q (γ, IZR y) }})
                                      trip) as [ty t].
      simpl in t.
      exists (has_type_ro_OpZRcoerce _ _ ty).
      simpl.
      intros γ m; simpl in m; simpl.
      pose proof (t γ m) as [p1 p2].
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros.
      destruct H as [z [i1 i2]].
      pose proof (p2 _ i1).
      destruct H.
      exists (IZR x).
      rewrite <- i2.
      destruct H.
      rewrite H.
      simpl; split; auto.

    ++
      (* | ro_exp_tot : forall Γ e (w : Γ |- e : INTEGER) ϕ ψ (w' : Γ |- EXP e : REAL), *)
      
      (*     w |- [{ϕ}] e [{y | ψ (powerRZ 2 y)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] EXP e [{ψ}] *)

      pose proof (proves_ro_tot_sound _ _ _
                                      _
                                      ([γ : Γ]|- {{y : INTEGER | Q (γ, pow2 y) }})
                                      trip) as [ty t].
      simpl in t.
      exists (has_type_ro_OpZRexp _ _ ty).
      simpl.
      intros γ m; simpl in m; simpl.
      pose proof (t γ m) as [p1 p2].
      split.
      {
        (* nonemptiness *)
        intro.
        apply pdom_lift_empty_2 in H.
        apply (p1 H).        
      }
      intros.
      destruct H as [z [i1 i2]].
      pose proof (p2 _ i1).
      destruct H.
      exists (pow2 x).
      rewrite <- i2.
      destruct H.
      rewrite H.
      simpl; split; auto.

    ++
      (* (** integer arithmetic  *) *)
      (* | ro_int_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :+: e2) : INTEGER) (ψ :post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zplus y1 y2) γ)-> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*      w' |- [{ϕ}] e1 :+: e2 [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZplus _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 :+: e2) INTEGER ((has_type_ro_OpZplus _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Zplus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
       injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.

    ++
      (* | ro_int_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :*: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zmult y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :*: e2) [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZmult _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 :*: e2) INTEGER ((has_type_ro_OpZmult _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Zmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.

    ++
      (* | ro_int_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) ϕ ψ1 ψ2 (w' : Γ |- (e1 :-: e2) : INTEGER) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Zminus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 :-: e2) [{ψ}] *)

      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZminus _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 :-: e2) INTEGER ((has_type_ro_OpZminus _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Zminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
       injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.


    ++
      (* (** real arithmetic  *) *)
      (* | ro_real_op_plus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;+; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rplus y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;+; e2) [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRplus _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 ;+; e2) REAL ((has_type_ro_OpRplus _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Rplus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
       injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.

    ++
      (* | ro_real_op_mult_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;*; e2) : REAL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rmult y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;*; e2) [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRmult _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 ;*; e2) REAL ((has_type_ro_OpRmult _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Rmult) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.


    ++
      (* | ro_real_op_minus_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2 (w' : Γ |- (e1 ;-; e2) : REAL) (ψ : post), *)

      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Rminus y1 y2) γ) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;-; e2) [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRminus _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 ;-; e2) REAL ((has_type_ro_OpRminus _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Rminus) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.

    ++

      (* (** reciprocal *) *)
      (* | ro_recip_tot : forall Γ e (w : Γ |- e : REAL) ϕ θ (w' : Γ |- ;/; e : REAL) ψ, *)

      (*     w |- [{ϕ}] e [{θ}] ->  *)
      (*     (θ ->>> ((fun x γδ => x <> 0%R) /\\\ (fun x => ψ (/x)%R))) ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] ;/; e [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip) as [w1 p2'].
      simpl in p2'.
      exists (has_type_ro_OpRrecip _ _ w1).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.      
      intros γ m; simpl in m.
      pose proof (p2' _ m) as [p1 p2].
      split.
      {
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
      assert (sem_ro_exp Γ (;/; e) REAL (has_type_ro_OpRrecip _ _ w1) γ =
                pdom_bind Rrecip (sem_ro_exp Γ e REAL w1 γ)).
      auto.
      rewrite H in h1; clear H.
      destruct v.
      apply pdom_bind_bot_2 in h1.
      destruct h1.
      pose proof (p2 _ H).
      destruct H0 as [v' [ee _]].
      contradict (flat_bot_neq_total _ ee).
      destruct H as [y [i j]].
      unfold Rrecip in j.
      unfold Rrecip' in j.
      destruct (total_order_T y 0).
      destruct s.
      contradict (flat_total_neq_bot _ j).
      pose proof (p2 _ i).
      destruct H as [z [h1 h2]].
      injection h1; intro k; induction k.
      pose proof (a _ _ h2).
      destruct H.
      contradict (H e0).
      contradict (flat_total_neq_bot _ j).
      apply pdom_bind_total_2 in h1.
      destruct h1 as [_ h1].
      destruct h1 as [x h].
      destruct h as [h1 h3].
      unfold Rrecip in h3.
      unfold Rrecip' in h3.
      destruct (total_order_T x 0).
      destruct s0.
      {
        (* when x < 0 *)     
        destruct (a γ x).
        destruct (p2 _ h1).
        destruct H.
        apply total_is_injective in H.
        rewrite H; auto.
        exists s; split; auto.
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
        destruct (a γ x).
        destruct (p2 _ h1).
        destruct H.
        apply total_is_injective in H.
        rewrite H; auto.
        exists s; split; auto.
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
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZeq _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 :=: e2) BOOL ((has_type_ro_OpZeq _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Z.eqb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.

    ++
      (* | ro_int_exp_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : INTEGER) (w2 : Γ |- e2 : INTEGER) P ψ1 ψ2 (w' : Γ |- (e1 :<: e2) : BOOL) (ψ : post), *)

      (*     w1 |- [{P}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{P}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (Z.ltb y1 y2) γ) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{P}] (e1 :<: e2) [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpZlt _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].
      
      split.
      {
        (* nonemptiness *)
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
      replace (sem_ro_exp Γ (e1 :<: e2) BOOL ((has_type_ro_OpZlt _ _ _ w1 w2)) γ)
        with
                (pdom_lift2 (Z.ltb) (sem_ro_exp _ _ _ w1 γ) (sem_ro_exp _ _ _ w2 γ)) in H by auto.
      unfold pdom_lift2 in H.
      unfold pdom_prod in H.
      destruct v.
      apply pdom_lift_bot_2 in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H).
      destruct H0 as [i [j k]].      
      contradict (flat_bot_neq_total _ j).
      destruct H as [i [j k]].
      apply pdom_lift_bot_2 in k.
      destruct (p2 _ k) as [ii [jj kk]].      
      contradict (flat_bot_neq_total _ jj).
      
      apply pdom_lift_total_2 in H.
      destruct H as [x [H H0]].
      apply pdom_bind_total_2 in H.
      destruct H as [_ [x0 [H H1]]].      
      apply pdom_lift_total_2 in H1.
      destruct H1 as [x1 [H1 H2]].
      
      exists s.
      split; auto.
      rewrite H0.
      apply ψ3.
      pose proof (p2 _ H1) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.
      pose proof (q2 _ H) as [x2 [H3 H4]].
      injection H3.
      intro i; induction i.
      rewrite H2; simpl; exact H4.

    ++
      (* (** real exparison  *) *)
      (* | ro_real_lt_tot : forall Γ e1 e2 (w1 : Γ |- e1 : REAL) (w2 : Γ |- e2 : REAL) ϕ ψ1 ψ2  (w' : Γ |- (e1 ;<; e2) : BOOL) (ψ : post), *)
      
      (*     w1 |- [{ϕ}] e1 [{ψ1}] ->  *)
      (*     w2 |- [{ϕ}] e2 [{ψ2}] ->  *)
      (*     (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] (e1 ;<; e2) [{ψ}] *)

      pose proof (proves_ro_tot_sound _ _ _ _ _ trip1) as [w1 p2'].
      pose proof (proves_ro_tot_sound _ _ _ _ _ trip2) as [w2 q2'].
      simpl in p2', q2'.
      exists (has_type_ro_OpRlt _ _ _ w1 w2).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.
      intros γ m; simpl in m.
      pose proof (p2' γ m) as [p1 p2].
      pose proof (q2' γ m) as [q1 q2].

      split.
      {
        (* nonemptiness *)
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
      
      intros v h1. 
      assert (sem_ro_exp Γ _ _ (has_type_ro_OpRlt _ _ _ w1 w2) γ  = pdom_bind2 Rltb (sem_ro_exp Γ e1 REAL w1 γ) (sem_ro_exp Γ e2 REAL w2 γ)).
      auto.
      rewrite H in h1; clear H.
      destruct v.
      apply pdom_bind_bot_2 in h1.
      destruct h1.
      unfold pdom_prod in H.
      apply pdom_bind_bot_2 in H.
      destruct H.
      pose proof (q2 _ H) as [i [j k]].
      contradict (flat_bot_neq_total _ j).
      destruct H as [y [h1 h2]].
      apply pdom_lift_bot_2 in h2.
      pose proof (p2 _ h2) as [i [j k]].
      contradict (flat_bot_neq_total _ j).
      destruct H as [[x y] [h1 h2]].
      simpl in h2.
      unfold Rltb' in h2.
      destruct (total_order_T x y).
      destruct s.
      contradict (flat_total_neq_bot _ h2).
      unfold pdom_prod in h1.
      apply pdom_bind_total_2 in h1 as [_ [x' [h1 h3]]].
      apply pdom_lift_total_2 in h3 as [y' [h4 eqq]].
      pose proof (p2 _ h4) as [y'' [h44 h444]].
      pose proof (q2 _ h1) as [x'' [h11 h111]].
      injection h44; intro i; induction i; clear h44.
      injection h11; intro i; induction i; clear h11.
      injection eqq; intros i j; induction i; induction j. clear eqq.
      pose proof (a _ _ _ h444 h111).
      destruct H.
      contradict (H e).
      contradict (flat_total_neq_bot _ h2).
      exists s.
      split; auto.

      apply pdom_bind_total_2 in h1 as [_ [[x1 x2] [h1 h2]]].
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
      destruct (total_order_T x2' x1') as [[n | n]| n].
      apply total_is_injective in h2; rewrite<- h2; auto.
      contradict (p n).
      apply total_is_injective in h2; rewrite<- h2; auto.
      
    ++
      (* (* Limit *) *)
      (* | ro_lim_tot : forall Γ e (w : (INTEGER :: Γ) |- e : REAL) ϕ θ (w' : Γ |- Lim e : REAL) ψ, *)

      (*     w |- [{fun γ' => ϕ (snd γ')}] e [{θ}] -> *)
      (*     (forall γ, ϕ γ -> exists y, ψ y γ /\ forall x z, θ z (x, γ) -> (Rabs (z - y)%R < powerRZ 2 (- x))%R) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' |- [{ϕ}] Lim e [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _
                                      ([(γ, x) : (Γ ::: INTEGER)]|- {{y : REAL | θ (γ, x, y) }})
                                      trip) as [w1 p2'].
      simpl in p2'.
      exists (has_type_ro_Lim _ _ w1).
      intros P Q; simpl in P, Q; unfold P, Q; clear P Q.      
      intros γ m; simpl in m.
      pose proof (e0 γ m).
      destruct H as [y h1].
      destruct h1 as [h1 h2].
      
      split.
      {
        apply (pdom_is_neg_empty_by_evidence _ (total y)).
        simpl.
        unfold Rlim_def.
        exists y; split; auto.
        intros.
        split.
        simpl.
        destruct (p2' (γ, x)); auto.
        
        intros.
        destruct z.
        destruct (p2' (γ,  x) m) as [_ h].
        pose proof (h (bot R) H).
        destruct H0.
        destruct H0.
        contradict (flat_bot_neq_total _ H0).
        exists r; split; auto.
        destruct (p2' (γ,  x) m) as [_ h].
        pose proof (h _ H).
        destruct H0.
        destruct H0.
        injection H0; intro j; rewrite <- j in H1; clear j.
        exact (h2 _ _ H1).
      }

      intros.
      exists y.
      split; auto.
      destruct v.
      simpl in H.
      unfold Rlim_def in H.
      destruct H.
      destruct H.
      contradict (flat_bot_neq_total _ H).
      
      
      
      apply (Rlim_def_unique ((fun x : Z => sem_ro_exp (INTEGER :: Γ) e REAL w1 (γ, x)))); auto.
      unfold Rlim_def.
      exists y.
      split; auto.
      intros.
      split.
      auto.
      destruct (p2' (γ, x)); auto.
      intros.
      destruct z.
      destruct (p2' (γ, x) m).
      pose proof (H2 _ H0).
      destruct H3.
      destruct H3.
      contradict (flat_bot_neq_total _ H3).
      exists r.
      split; auto.
      apply h2.
      destruct (p2' (γ, x) m).
      pose proof (H2 _ H0).
      destruct H3.
      destruct H3.
      injection H3; intro i; induction i; auto.
      
      
  + (*  partial correctness triple for read write expressions *)
    intros Γ Δ e τ ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | rw_imply_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ', *)
      
      (*     ϕ' ->> ϕ ->  *)
      (*     w ||- {{ ϕ }} e {{ ψ }} ->  *)
      (*     ψ ->>> ψ' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ ϕ'}}  e {{ ψ' }} *)


      pose proof (proves_rw_prt_sound _ _ _ _ _ _ trip).
      destruct H.
      exists x.
      simpl.
      simpl in a1.
      intros γ δ m.
      apply a in m.
      destruct (a1 γ δ m).
      split.
      exact H.      
      intros.
      destruct v'.
      apply a0.
      apply (H0 _ H1 _ H2).

    ++
      (* | rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ (fun _ => False) }} e {{ ψ }} *)

      exists w.
      simpl.
      intros γ δ m; simpl; simpl in m.
      contradict m.
    ++
      (* | rw_conj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ', *)
      
      (*     w ||- {{ϕ}} e {{ψ}} ->  *)
      (*     w ||- {{ϕ}} e {{ψ'}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ϕ}} e {{ψ /\\\ ψ'}} *)
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ δ m; simpl in m; simpl.
      pose proof (t1 _ _ m) as [p1 p2].
      pose proof (t2 _ _ m) as [q1 q2].
      split; auto.
      intros v p v' p'.
      destruct v'.
      rewrite (sem_rw_exp_unique _ _ _ _ w2 w1) in q2.
      split; try apply (p2 v p v' p'); try apply (p2 v p v' p').
      apply (p2 v p _ p').
      apply (q2 v p _ p').
      
      
    ++
      (* | rw_disj_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ, *)
      
      (*     w ||- {{ϕ}} e {{ψ}} ->  *)
      (*     w ||- {{ϕ'}} e {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ϕ \// ϕ'}} e {{ψ}} *)
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_rw_prt_sound _ _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ δ m; simpl in m; simpl.
      destruct m as [m|m].      
      apply (t1 _ _ m).
      rewrite (sem_rw_exp_unique _ _ _ _ w2 w1) in t2.
      apply (t2 _ _ m).

      
    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | ro_rw_prt : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ), *)
      
      (*     w |- {{ϕ}} e {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}} e {{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}} *)

      pose proof (proves_ro_prt_sound _ _ _ _ _  p) as [w1 t1].
      simpl in t1.
      exists (has_type_rw_ro _ _ _ _ w1).
      simpl.
      intros γ δ m; simpl; simpl in m.
      split.
      pose proof (t1 _ m).
      destruct H.
      apply neg_forall_exists_neg in H.
      destruct H.
      apply dn_elim in H.
      destruct x.
      apply (pdom_is_neg_empty_by_evidence _ (bot _)).
      simpl.
      exists (bot _); split; simpl; auto.
      apply (pdom_is_neg_empty_by_evidence _ (total (δ, s))).
      simpl.
      exists (total s); split; simpl; auto.
      intros h1 [h2 [h3 h4]] h5 h6.
      destruct h5.
      rewrite h6 in h4.
      unfold pdom_lift' in h4.
      destruct h2.
      contradict (flat_bot_neq_total _ h4).
      injection h4; intros i j; induction i; induction j; clear h4.
      destruct (t1 _ m).
      pose proof (H0 _ h3).
      apply H1.
      auto.
      
    ++
      (* (** operational proof rules  *)                             *)
      (* | rw_sequence_prt : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : DUnit) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ), *)
      
      (*     w1 ||- {{ϕ}} c1 {{θ}} ->  *)
      (*     w2 ||- {{θ tt}} c2 {{ψ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} c1 ;; c2 {{ψ}} *)
      pose proof (proves_rw_prt_sound _ _ _ _ _ _  trip1) as [w1 t1].
      simpl in t1.
      pose proof (proves_rw_prt_sound _ _ _ _ ([γ : Γ ;;; δ : Δ]||- {{θ (γ, (δ, tt))}} ) ([γ : Γ ;;; δ : Δ]||- {{y : τ | ψ0 (γ, (δ, y)) }})  trip2) as [w2 t2].
      simpl in t2.
      exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
      intros P Q; simpl in P; simpl in Q; unfold P, Q; clear P Q.
      
      intros γ δ m; simpl in m.
      pose (sem_rw_exp _ _ _ _ w1 γ) as C1.
      pose (sem_rw_exp _ _ _ _ w2 γ) as C2.
      pose proof (t1 γ δ m) as [p1 p2]; auto.

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
        pose proof (t2 γ δ' H0) as [q1 q2]; auto.
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
      pose proof (t2 γ δ' H) as [q1 q2]; auto.
      apply (q2 _ h3 _ eq_refl).

    ++
      (* | rw_new_var_prt : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ), *)

      (*     w1 |- {{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}} e {{θ}} ->  *)
      (*     w2 ||- {{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}} c {{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} NEWVAR e IN c {{ψ}} *)
      pose proof (proves_ro_prt_sound _ _ _ _ _  p) as [w1 t1].
      pose proof (proves_rw_prt_sound _ _ _ _ ([γ : Γ ;;; (δ, x) : (Δ ::: σ)]||- {{θ ((γ; δ), x)}}) ([γ : Γ ;;; (δ, x) : (Δ ::: σ)]||- {{y : τ | ψ0 (γ, (δ, y)) }}) trip) as [w2 t2].
      simpl in t1, t2.
      exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).

      intros P Q; simpl in P; simpl in Q; unfold P, Q; clear P Q.

      intros γ δ m; simpl in m.
      pose (sem_ro_exp _ _ _ w1 (γ; δ)) as V.
      pose (sem_rw_exp _ _ _ _ w2 γ) as f.
      pose (pdom_bind f (pdom_lift (fun v => (δ, v)) V)) as res.
      unfold V, f, res.
      pose proof (t1 (γ; δ)).
      simpl in H.
      assert (ϕ0 (fst_app (γ; δ), snd_app (γ; δ))) as H'
          by (reduce_tedious; auto).
      apply H in H' as [p1 p2]; clear H.
      split.
      {
        (* non empty *)
        intro h.
        simpl in h.
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
        simpl in trip.
        pose proof (t2 γ x').

        destruct x'.
        simpl in h2.
        injection h'; intros i j; induction i; induction j.
        apply H0 in H.
        destruct H.
        exact (H h2).
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
      reduce_tedious p2.
      (* apply (p2 _ h5 _ eq_refl). *)
      (* auto. *)
      pose proof (t2 γ (x''', δ'')) as [_ h].
      simpl.
      apply (p2 _ h5 _ eq_refl).
      simpl in h.
      apply (h _ h4 _ eq_refl).

    ++
      (* | rw_assign_prt : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT), *)

      (*     w |- {{fun δγ => ϕ (tedious_sem_app _ _ δγ)}} e {{θ}} ->  *)
      (*     (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} LET k := e {{ψ}} *)
      apply proves_ro_prt_sound in p.
      apply (proves_rw_prt_Assign_sound _ _ _ _ _ _ _ _ _ p ψ1).
    
    ++
      (* | rw_cond_prt : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ, *)

      (*     w |- {{rw_to_ro_pre ϕ}} e {{θ}} -> *)
      (*     w1 ||- {{ro_to_rw_pre (θ true)}} c1 {{ψ}} -> *)
      (*     w2 ||- {{ro_to_rw_pre (θ false)}} c2 {{ψ}} -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- {{ϕ}} Cond e c1 c2 {{ψ}} *)
      pose proof (proves_ro_prt_sound _ _ _ _ _  p) as [wb tb].
      pose proof (proves_rw_prt_sound _ _ _ _ ([γ : Γ ;;; δ : Δ]||- {{θ ((γ; δ), true)}}) ([γ : Γ ;;; δ : Δ]||- {{y : τ | ψ0 (γ, (δ, y)) }}) trip1) as [w1 t1].
      pose proof (proves_rw_prt_sound _ _ _ _ ([γ : Γ ;;; δ : Δ]||- {{θ ((γ; δ), false)}}) ([γ : Γ ;;; δ : Δ]||- {{y : τ | ψ0 (γ, (δ, y)) }}) trip2) as [w2 t2].
      simpl in tb, t1, t2.
      exists (has_type_rw_Cond _ _ _ _ _ _ wb w1 w2).
      intros P Q; simpl in P; simpl in Q; unfold P, Q; clear P Q.

      intros γ δ m; simpl; simpl in m.
      pose (sem_ro_exp _ _ _ wb (γ; δ)) as B.
      pose (sem_rw_exp _ _ _ _ w1 γ δ) as X.
      pose (sem_rw_exp _ _ _ _ w2 γ δ) as Y.
      replace (sem_rw_exp Γ Δ (IF e THEN c1 ELSE c2 END) τ (has_type_rw_Cond _ _ _ _ _ _ wb w1 w2) γ δ)
        with (pdom_bind (fun b : bool => if b then X else Y) B)
        by auto.
      (* assert ( ro_prt_pre w *)
      (*                     (mk_ro_prt w ([x : (Γ +++ Δ)]|- {{([x0 : (Γ +++ Δ)]|- {{ϕ0 (fst_app x0, snd_app x0)}}) x}}) ([x : (Γ +++ Δ)]|- {{y : BOOL | θ (x, y)}}))  *)
      (*   (γ; δ)) as m'. *)
      (* simpl. *)
      (* reduce_tedious; auto. *)
      assert (ϕ0 (fst_app (γ; δ), snd_app (γ; δ))) as m'.
      reduce_tedious; auto.
      pose proof (tb (γ ; δ) m') as [nempty_e sem_e].
      split.
      {
        intro h.
        apply pdom_bind_empty_2 in h as [h|[x [h1 h2]]]; auto.
        pose proof (ro_prt_post_pre _ _ _ _ _ wb (existT wb tb) x (γ ; δ) m').
        apply H in h1.
        destruct x.
        pose proof (t1 γ δ h1) as [h _]; auto.
        pose proof (t2 γ δ h1) as [h _]; auto.
      }

      intros h1 h2 h3 h4.
      rewrite h4 in h2; clear h4.
      apply pdom_bind_total_2 in h2 as [_ [b [semb h2]]].
      pose proof (ro_prt_post_pre _ _ _ _ _ wb (existT wb tb) b (γ; δ) m').
      apply H in semb; clear H.
      destruct b.
      pose proof (t1 γ δ semb) as [_ h].
      apply (h _ h2 h3 eq_refl).
      pose proof (t2 γ δ semb) as [_ h].
      apply (h _ h2 h3 eq_refl).
      

    ++
      (* | Rw_case_list_prt *)
      apply (proves_rw_case_prt_sound _ _ _ _ θ).
      exact l0.
      clear l0.
      dependent induction f.
      apply ForallT1_nil.
      apply ForallT1_cons.
      exact IHf.
      destruct r.
      split.
      apply (proves_ro_prt_sound _ _ _ _ _ p0).
      apply (proves_rw_prt_sound _ _ _ _ _ _ p1).
  
      
    ++
      (* | Rw_while_prt : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : Γ ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT)  ϕ θ, *)

      (*     wty_e |- {{rw_to_ro_pre ϕ}} e {{θ}} ->  *)
      (*     wty_c ||- {{ro_to_rw_pre (θ true)}} c {{fun _ => ϕ}} ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- {{ϕ}} While e c {{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}} *)
      apply proves_ro_prt_sound in p.
      pose proof (proves_rw_prt_sound  _ _ _ _
                    (fun '(γ, δ) => θ ((γ; δ), true))
                    (fun '(γ, (δ, y)) => ϕ0 (γ, δ))
                    trip
        ).

      apply (proves_rw_while_prt_sound _ _ _ _ _ _ p H).
      
  + (*  total correctness triple for read write expressions *)
    intros Γ Δ e τ ϕ ψ trip.
    induction trip.
    ++
      (* (** logical rules *) *)
      (* | rw_imply_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ϕ' ψ', *)
      
      (*     ϕ' ->> ϕ ->  *)
      (*     w ||- {{ ϕ }} e {{ ψ }} ->  *)
      (*     ψ ->>> ψ' ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ ϕ'}}  e {{ ψ' }} *)

      pose proof (proves_rw_tot_sound _ _ _ _ _ _ trip).
      destruct H.
      exists x.
      simpl.
      simpl in a1.
      intros γ δ m.
      apply a in m.
      destruct (a1 γ δ m).
      split.
      exact H.      
      intros.
      destruct (H0 v H1).
      exists x0.
      destruct H2; split; auto.
      destruct x0.
      apply a0; auto.

    ++
      (* | rw_exfalso_prt : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ψ, *)
      
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- {{ (fun _ => False) }} e {{ ψ }} *)

      exists w.
      simpl.
      intros γ δ m; simpl; simpl in m.
      contradict m.

    ++
      (* | rw_conj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ ψ', *)
      
      (*     w ||- [{ϕ}] e [{ψ}] ->  *)
      (*     w ||- [{ϕ}] e [{ψ'}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ϕ}] e [{ψ /\\\ ψ'}] *)
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ δ m; simpl in m; simpl.
      pose proof (t1 _ _ m) as [p1 p2].
      pose proof (t2 _ _ m) as [q1 q2].
      split; auto.
      intros v p.
      pose proof (p2 _ p).
      rewrite (sem_rw_exp_unique _ _ _ _ w2 w1) in q2.
      pose proof (q2 _ p).
      destruct H.
      exists x.
      destruct H; split; auto.
      destruct x.
      destruct H0.
      destruct H0.
      destruct x.
      rewrite H0 in H.
      apply total_is_injective in H.
      rewrite H in H2.
      auto.

    ++
      (* | rw_disj_tot : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ϕ' ψ, *)
      
      (*     w ||- [{ϕ}] e [{ψ}] ->  *)
      (*     w ||- [{ϕ'}] e [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w ||- [{ϕ \// ϕ'}] e [{ψ}] *)
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ trip1) as [w1 t1].
      pose proof (proves_rw_tot_sound _ _ _ _ _ _ trip2) as [w2 t2].
      exists w1.
      simpl; simpl in t1, t2.
      intros γ δ m; simpl in m; simpl.
      destruct m as [m|m].      
      apply (t1 _ _ m).
      rewrite (sem_rw_exp_unique _ _ _ _ w2 w1) in t2.
      apply (t2 _ _ m).

    ++
      (* (** passage between read-only and read-write correctness *) *)
      (* | ro_rw_tot : forall Γ Δ e τ (w : (Δ ++ Γ) |- e : τ) ϕ ψ (w' : Γ ;;; Δ ||- e : τ), *)
      
      (*     w |- [{ϕ}] e [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{fun γδ => ϕ (tedious_prod_sem _ _ γδ)}] e [{fun v γδ => ψ v (tedious_prod_sem _ _ γδ)}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _  p) as [w1 t1].
      simpl in t1.
      exists (has_type_rw_ro _ _ _ _ w1).
      simpl.
      intros γ δ m; simpl; simpl in m.
      split.
      pose proof (t1 _ m).
      destruct H.
      apply neg_forall_exists_neg in H.
      destruct H.
      apply dn_elim in H.
      destruct x.
      apply (pdom_is_neg_empty_by_evidence _ (bot _)).
      simpl.
      exists (bot _); split; simpl; auto.
      apply (pdom_is_neg_empty_by_evidence _ (total (δ, s))).
      simpl.
      exists (total s); split; simpl; auto.
      intros h1 [h2 [h3 h4]].
      pose proof (t1 _ m).
      destruct H as [_ H].
      destruct (H _ h3).
      destruct H0.
      exists (δ, x).
      rewrite H0 in h4.
      simpl in h4.
      split; auto.
      

    ++
      (* (** operational proof rules  *)                             *)
      (* | rw_sequence_tot : forall Γ Δ c1 c2 τ (w1 : Γ ;;; Δ ||- c1 : UNIT) (w2 : Γ ;;; Δ ||- c2 : τ) ϕ θ ψ (w' : Γ ;;; Δ ||- (c1 ;; c2) : τ), *)
      
      (*     w1 ||- [{ϕ}] c1 [{θ}] ->  *)
      (*     w2 ||- [{θ tt}] c2 [{ψ}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] c1 ;; c2 [{ψ}] *)
      pose proof (proves_rw_tot_sound _ _ _ _ _ _  trip1) as [w1 t1].
      simpl in t1.
      pose proof (proves_rw_tot_sound _ _ _ _ ([γ : Γ ;;; δ : Δ]||- {{θ (γ, (δ, tt))}} ) ([γ : Γ ;;; δ : Δ]||- {{y : τ | ψ0 (γ, (δ, y)) }})  trip2) as [w2 t2].
      simpl in t2.
      exists (has_type_rw_Seq _ _ _ _ _ w1 w2).
      intros P Q; simpl in P; simpl in Q; unfold P, Q; clear P Q.
      
      intros γ δ m; simpl in m.
      pose (sem_rw_exp _ _ _ _ w1 γ) as C1.
      pose (sem_rw_exp _ _ _ _ w2 γ) as C2.
      pose proof (t1 γ δ m) as [p1 p2]; auto.

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
        pose proof (t2 γ δ' H1) as [q1 q2]; auto.
      }
      intros h1 h2.
      destruct h1.
      apply pdom_bind_bot_2 in h2.
      destruct h2.
      apply pdom_lift_bot_2 in H.
      pose proof (t1 _ _ m) as [_ p].
      pose proof (p (bot _) H) as [x [e _]].
      contradict (flat_bot_neq_total _ e).
      destruct H as [y [h1 h2]].
      apply pdom_lift_total_2 in h1 as [[x u] [h3 h4]].
      destruct u.
      simpl in h4; rewrite <- h4 in h3; clear h4. 
      assert (θ (γ, (y, tt))).
      pose proof (t1 _ _ m) as [_ p].
      pose proof (p (total (y, tt)) h3) as [y' [e1 e2]]. 
      apply total_is_injective in e1.
      rewrite <- e1 in e2.
      simpl in e2.
      auto.
      pose proof (t2 _ _ H) as [_ q].
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
      pose proof (t2 γ δ' hh3) as [_ q2]; auto.
     
    ++
      (* | rw_new_var_tot : forall Γ Δ e c τ σ (w1 : (Δ ++ Γ) |- e : σ) (w2 : Γ ;;; (σ :: Δ) ||- c : τ) ϕ ψ θ (w' : Γ ;;; Δ ||- (NEWVAR e IN c) : τ), *)

      (*     w1 |- [{fun γδ => (ϕ (tedious_sem_app _ _ γδ))}] e [{θ}] ->  *)
      (*     w2 ||- [{fun xδγ => θ (fst (fst xδγ)) (tedious_prod_sem _ _ (snd (fst xδγ), snd xδγ))}] c [{fun x xδγ => ψ x (snd (fst xδγ), snd xδγ)}] ->  *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] NEWVAR e IN c [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _  p) as [w1 t1].
      pose proof (proves_rw_tot_sound _ _ _ _ ([γ : Γ ;;; (δ, x) : (Δ ::: σ)]||- {{θ ((γ; δ), x)}}) ([γ : Γ ;;; (δ, x) : (Δ ::: σ)]||- {{y : τ | ψ0 (γ, (δ, y)) }}) trip) as [w2 t2].
      simpl in t1, t2.
      exists (has_type_rw_Newvar _ _ _ _ _ _ w1 w2).

      intros P Q; simpl in P; simpl in Q; unfold P, Q; clear P Q.

      intros γ δ m; simpl in m.
      pose (sem_ro_exp _ _ _ w1 (γ; δ)) as V.
      pose (sem_rw_exp _ _ _ _ w2 γ) as f.
      pose (pdom_bind f (pdom_lift (fun v => (δ, v)) V)) as res.
      unfold V, f, res.
      pose proof (t1 (γ; δ)).
      simpl in H.
      assert (ϕ0 (fst_app (γ; δ), snd_app (γ; δ))) as H'
          by (reduce_tedious; auto).
      apply H in H' as [p1 p2]; clear H.
      split.
      {
        (* non empty *)
        intro h.
        simpl in h.
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
        pose proof (t2 γ x').

        destruct x'.
        apply total_is_injective in e1; induction e1.
        injection h'; intros i j; induction i; induction j.
        pose proof (H e2).
        destruct H0.
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
      pose proof (t2 γ x).
      destruct x.
      injection H1; intros i j; induction i; induction j.
      apply H2 in H3.
      clear H2.
      simpl in H3.
      destruct H3.
      pose proof (H3 _ H0).
      destruct H4.
      destruct H4.
      contradict (flat_bot_neq_total _ H4).
      exists p0; split; auto.
      
      apply pdom_lift_total_2 in h2 as [[[x' x''] y'] [h2 h3]].
      apply pdom_bind_total_2 in h2 as [_ [[x''' δ''] [h2 h4]]].
      apply pdom_lift_total_2 in h2 as [x'''' [h5 h6]].
      simpl in h3.
      rewrite h3; clear h3; simpl.
      unfold f in h4.
      injection h6; intros i j; induction i; induction j.
      unfold V in h5.
      pose proof (t2 γ (x''', δ'')).
      simpl in H.
      assert ( θ ((γ; x'''), δ'')).
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
      rewrite H2, H4; auto. 


    ++
      (* | rw_assign_tot : forall Γ Δ e k τ (w : (Δ ++ Γ) |- e : τ) ϕ θ (ψ : post) (w' : Γ ;;; Δ ||- (LET k := e) : UNIT), *)

      (*     w |- [{fun δγ => ϕ (tedious_sem_app _ _ δγ)}] e [{θ}] ->  *)
      (*     (forall x γ δ, θ x (tedious_prod_sem _ _ (δ, γ)) -> ψ tt (update' w w' δ x, γ)) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] LET k := e [{ψ}] *)
      apply proves_ro_tot_sound in p.
      apply (proves_rw_tot_Assign_sound _ _ _ _ _ _ _ _ _ p ψ1).

    ++
      (* | rw_cond_tot : forall Γ Δ e c1 c2 τ (w : (Δ ++ Γ) |- e : BOOL) (w1 : Γ ;;; Δ ||- c1 : τ) (w2 : Γ ;;; Δ ||- c2 : τ) (w' : Γ ;;; Δ ||- Cond e c1 c2 : τ) ϕ θ ψ, *)

      (*     w |- [{rw_to_ro_pre ϕ}] e [{θ}] -> *)
      (*     w1 ||- [{ro_to_rw_pre (θ true)}] c1 [{ψ}] -> *)
      (*     w2 ||- [{ro_to_rw_pre (θ false)}] c2 [{ψ}] -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     w' ||- [{ϕ}] Cond e c1 c2 [{ψ}] *)
      pose proof (proves_ro_tot_sound _ _ _ _ _  p) as [wb tb].
      pose proof (proves_rw_tot_sound _ _ _ _ ([γ : Γ ;;; δ : Δ]||- {{θ ((γ; δ), true)}}) ([γ : Γ ;;; δ : Δ]||- {{y : τ | ψ0 (γ, (δ, y)) }}) trip1) as [w1 t1].
      pose proof (proves_rw_tot_sound _ _ _ _ ([γ : Γ ;;; δ : Δ]||- {{θ ((γ; δ), false)}}) ([γ : Γ ;;; δ : Δ]||- {{y : τ | ψ0 (γ, (δ, y)) }}) trip2) as [w2 t2].
      simpl in tb, t1, t2.
      exists (has_type_rw_Cond _ _ _ _ _ _ wb w1 w2).
      intros P Q; simpl in P; simpl in Q; unfold P, Q; clear P Q.

      intros γ δ m; simpl; simpl in m.
      pose (sem_ro_exp _ _ _ wb (γ; δ)) as B.
      pose (sem_rw_exp _ _ _ _ w1 γ δ) as X.
      pose (sem_rw_exp _ _ _ _ w2 γ δ) as Y.
      replace (sem_rw_exp Γ Δ (IF e THEN c1 ELSE c2 END) τ (has_type_rw_Cond _ _ _ _ _ _ wb w1 w2) γ δ)
        with (pdom_bind (fun b : bool => if b then X else Y) B)
        by auto.
      (* assert ( ro_prt_pre w *)
      (*                     (mk_ro_prt w ([x : (Γ +++ Δ)]|- {{([x0 : (Γ +++ Δ)]|- {{ϕ0 (fst_app x0, snd_app x0)}}) x}}) ([x : (Γ +++ Δ)]|- {{y : BOOL | θ (x, y)}}))  *)
      (*   (γ; δ)) as m'. *)
      (* simpl. *)
      (* reduce_tedious; auto. *)
      assert (ϕ0 (fst_app (γ; δ), snd_app (γ; δ))) as m'.
      reduce_tedious; auto.
      pose proof (tb (γ ; δ) m') as [nempty_e sem_e].
      split.
      {
        intro h.
        apply pdom_bind_empty_2 in h as [h|[x [h1 h2]]]; auto.
        pose proof (ro_tot_post_pre _ _ _ _ _ wb (existT wb tb) x (γ ; δ) m').
        apply H in h1.
        destruct x.
        pose proof (t1 γ δ h1) as [h _]; auto.
        pose proof (t2 γ δ h1) as [h _]; auto.
      }

      intros h1 h2.
      destruct h1.
      {
        (* non bottom *)
        apply pdom_bind_bot_2 in h2.
        destruct h2.
        pose proof (tb _ m') as [_ E'].
        pose proof (E' _ H) as [hh1 [hh2 hh3]].
        contradict (flat_bot_neq_total _ hh2).
        destruct H.
        destruct H.
        pose proof (tb _ m') as [_ E'].
        pose proof (E' _ H) as [hh1 [hh2 hh3]].
        apply total_is_injective in hh2.
        induction hh2.
        destruct x.
        (* assert (rw_tot_pre w1 (mk_rw_tot w1 (ro_to_rw_pre (θ true)) ψ0) (δ, γ)). *)
        (* simpl. *)
        (* simpl in hh3. *)
        (* auto. *)
        pose proof (t1 γ δ ) as [_ h].
        reduce_tedious; auto.
        pose proof (h _ H0) as [v [ee _ ]].
        contradict (flat_bot_neq_total _ ee).
        (* assert (rw_tot_pre w1 (mk_rw_tot w1 (ro_to_rw_pre (θ false)) ψ0) (δ, γ)). *)
        (* simpl. *)
        (* simpl in hh3. *)
        (* auto. *)
        pose proof (t2 γ δ ) as [_ h].
        reduce_tedious; auto.
        pose proof (h _ H0) as [v [ee _ ]].
        contradict (flat_bot_neq_total _ ee).
      }
      
      apply pdom_bind_total_2 in h2 as [_ [b [semb h2]]].
      pose proof (ro_tot_post_pre _ _ _ _ _ wb (existT wb tb) b (γ ; δ) m').
      apply H in semb; clear H.
      destruct b.
      pose proof (t1 γ δ semb) as [_ h].
      pose proof (h _ h2) as [x [p1 p2]].
      exists x; split; auto.
      pose proof (t2 γ δ semb) as [_ h].
      pose proof (h _ h2) as [x [p1 p2]].
      exists x; split; auto.
            
    ++
      (* case_list *)
      apply (proves_rw_case_tot_sound _ _ _ _ θ ϕi) .
      auto.
      clear f0 l0.
      dependent induction f.
      apply ForallT2_nil.
      apply ForallT2_cons.
      exact IHf.
      destruct r as [[r1 r2] r3].
      repeat split.
      apply proves_ro_prt_sound in r1.
      exact r1.
      apply (proves_rw_tot_sound _ _ _ _
                                 ([γ : Γ ;;;  δ : Δ] ||- {{p ((γ; δ), true)}})
                                 ([γ : Γ ;;;  δ : Δ] ||- {{y : τ | ψ0 (γ, (δ, y)) }})) in
                                 r2.
      exact r2.
      apply (proves_ro_tot_sound _ _ _
                                 ([x : (Γ +++ Δ)]|- {{q x}})
                                 ([x : (Γ +++ Δ)]|- {{b : BOOL | (b = true) }}))

              in r3.
      exact r3.
      exact f0.

          ++
      (* | rw_while_tot : forall Γ Δ e c (wty_e : (Δ ++ Γ) |- e : BOOL) (wty_c : (Γ ++ Δ) ;;; Δ ||- c : UNIT) (wty : Γ ;;; Δ ||- While e c : UNIT) ϕ θ ψ, *)
      
      (*     wty_e |- [{rw_to_ro_pre ϕ}] e [{θ}] -> *)
      (*     wty_c ||- [{fun δγδ' => ro_to_rw_pre (θ true) (fst δγδ', fst_app (snd δγδ')) /\ fst δγδ' = snd_app (snd δγδ')}] c [{fun _ δγδ' => ϕ (fst δγδ', fst_app (snd δγδ')) /\ ψ δγδ' }] -> *)
      (*              (forall δ γ, ϕ (δ, γ) ->   *)
      (*                            ~exists f : nat -> sem_ctx Δ, *)
      (*                                f 0 = δ /\ forall n, ψ (f (S n), (γ ; f n))) -> *)
      (*     (*——————————-——————————-——————————-——————————-——————————-*) *)
      (*     wty ||- [{ϕ}] While e c [{fun _ => (ϕ /\\ ro_to_rw_pre (θ false))}] *)

      apply proves_ro_tot_sound in p.
      pose proof (proves_rw_tot_sound _ _ _ _ 
                    (fun '(γ, δ) => θ ((γ; δ), true))
                    (fun '(γ, (δ, y)) => ϕ0 (γ, δ))
                    trip1
        ).
      pose proof (proves_rw_tot_sound _ _ _ _
                    (fun '(x, δ) => θ ((snd_app x; δ), true) /\ δ = fst_app x)
                    (fun '(x, (δ, y)) => ψ0 (x, δ))
                    trip2
        ).

      apply (proves_rw_while_tot_sound _ _ _ _ _ _ _ p H H0 n).

Defined.
