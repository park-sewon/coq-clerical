Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals.
Require Import ZArith.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Preliminaries.Preliminaries.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.

Lemma admissible_ro_prt_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- {{ϕ}} e {{ψ}}) :
  ψ ->>> θ -> w |- {{ϕ}} e {{θ}}.
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma admissible_ro_prt_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- {{ϕ}} e {{ψ}}) :
  θ ->> ϕ -> w |- {{θ}} e {{ψ}}.
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ H X H0).
Defined.

Lemma admissible_ro_tot_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- [{ϕ}] e [{ψ}]) :
  ψ ->>> θ -> w |- [{ϕ}] e [{θ}].
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma admissible_ro_tot_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- [{ϕ}] e [{ψ}]) :
  θ ->> ϕ -> w |- [{θ}] e [{ψ}].
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ H X H0).
Defined.




Fixpoint admissible_ro_prt_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |- {{ϕ}} e {{ψ}}) {struct X} :
  w |- {{ϕ /\\ θ}} e {{ψ /\\\ fun _ => θ}}
with admissible_ro_tot_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |- [{ϕ}] e [{ψ}]) {struct X} :
  w |- [{ϕ /\\ θ}] e [{ψ /\\\ fun _ => θ}]
with admissible_rw_prt_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||- {{ϕ}} e {{ψ}}) {struct X} :
  w ||- {{ϕ /\\ fun δγ => θ (snd δγ) }} e {{ψ /\\\ fun _ δγ => θ (snd δγ)}}
with admissible_rw_tot_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||- [{ϕ}] e [{ψ}]) {struct X} :
  w ||- [{ϕ /\\ fun δγ => θ (snd δγ)}] e [{ψ /\\\ fun _ δγ => θ (snd δγ)}].
Proof.
  +
    dependent induction X.
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    assert ((ϕ /\\ θ) ->> (P /\\ θ)).
    intros γ p; split; destruct p.
    apply a; exact H.
    exact H0.
    assert ((Q /\\\ fun _ => θ) ->>> (ψ /\\\ fun _ => θ)).
    intros y γ p; split; destruct p.
    apply a0; exact H0.
    exact H1.
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ H X0 H0).

    pose proof (ro_exfalso_prt Γ e τ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    assert (((fun _ : sem_ctx Γ => False) /\\ θ) ->> (fun _ : sem_ctx Γ => False)).
    intros a [b c]; contradict b.
    assert ((ψ /\\\ (fun _ : sem_datatype τ => θ)) ->>> (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    intros a b; auto.
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ H X H0).

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_conj_prt _ _ _ _ _ _ _  X X0).
    apply (admissible_ro_prt_post_weaken X3).
    intros a b [[c d] [f g]]; repeat split; auto.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_disj_prt _ _ _ _ _ _ _  X X0).
    apply (admissible_ro_prt_pre_strengthen X3).
    intros a b.
    destruct b.
    destruct H.
    left; split; auto.
    right; split; auto.

    pose proof (ro_var_prt _ _ _ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    apply (admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_skip_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (ro_true_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_false_prt _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_int_prt _ _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_prt_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ p).
    pose proof (ro_rw_prt _ _ _ _ _ _ w' X).
    simpl in X0.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros a b.
    destruct b; split; auto.
    intros h1 h2 h3.
    split; destruct h3; auto.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_coerce_prt _ _ w _ _ w').
    apply (admissible_ro_prt_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_exp_prt _ _ w _ _ w').
    apply (admissible_ro_prt_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_recip_prt _ _ w _ _ w' _ X0).    
    intros h1 h2 h3.
    destruct h3.
    split.
    apply a.
    split.
    destruct H; auto.
    auto.
    destruct H; auto.
    
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.
    auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x : sem_ctx (INTEGER :: Γ) => θ (snd x)) p).
    apply (ro_lim_prt _ _ _ _ _ _ _ X).
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
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    assert ((ϕ /\\ θ) ->> (P /\\ θ)).
    intros γ p; split; destruct p.
    apply a; exact H.
    exact H0.
    assert ((Q /\\\ fun _ => θ) ->>> (ψ /\\\ fun _ => θ)).
    intros y γ p; split; destruct p.
    apply a0; exact H0.
    exact H1.
    apply (ro_imply_tot _ _ _ _ _ _ _ _ _ H X0 H0).

    pose proof (ro_exfalso_tot Γ e τ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    assert (((fun _ : sem_ctx Γ => False) /\\ θ) ->> (fun _ : sem_ctx Γ => False)).
    intros a [b c]; contradict b.
    assert ((ψ /\\\ (fun _ : sem_datatype τ => θ)) ->>> (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    intros a b; auto.
    apply (ro_imply_tot _ _ _ _ _ _ _ _ _ H X H0).

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_conj_tot _ _ _ _ _ _ _  X X0).
    apply (admissible_ro_tot_post_weaken X3).
    intros a b [[c d] [f g]]; repeat split; auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    pose proof (ro_disj_tot _ _ _ _ _ _ _  X X0).
    apply (admissible_ro_tot_pre_strengthen X3).
    intros a b.
    destruct b.
    destruct H.
    left; split; auto.
    right; split; auto.

    pose proof (ro_var_tot _ _ _ w (ψ /\\\ (fun _ : sem_datatype τ => θ))).
    apply (admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_skip_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (ro_true_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_false_tot _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.
    
    pose proof (ro_int_tot _ _  w (ψ /\\\ (fun _ => θ))).
    apply (admissible_ro_tot_pre_strengthen X).
    intros a b; split; destruct b; auto.

    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ p).
    pose proof (ro_rw_tot _ _ _ _ _ _ w' X).
    simpl in X0.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros a b.
    destruct b; split; auto.
    intros h1 h2 h3.
    split; destruct h3; auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_coerce_tot _ _ w _ _ w').
    apply (admissible_ro_tot_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.
    
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_exp_tot _ _ w _ _ w').
    apply (admissible_ro_tot_post_weaken X0).
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_plus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_mult_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_op_minus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_plus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_mult_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_op_minus_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
    apply (ro_recip_tot _ _ w _ _ w' _ X0).    
    intros h1 h2 h3.
    destruct h3.
    destruct (a _ _ H).
    
    split; auto.
    split; auto.
    
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_eq_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_int_comp_lt_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0; split.
    apply ψ0.
    apply H.
    apply H0.
    apply H1.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
    apply (ro_real_lt_tot _ _ _ _ _ _ _ _ _ _ X X0).
    intros.
    destruct H, H0.
    destruct (a _ _ _ H H0).
    split; auto.
    split; auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun x : sem_ctx (INTEGER :: Γ) => θ (snd x)) X).
    apply (ro_lim_tot _ _ _ _ _ _ _ X0).
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
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; auto.
    split; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (rw_exfalso_prt _ _ _ _ w (ψ /\\\ fun (_ : sem_datatype τ) (δγ : sem_ctx Δ * sem_ctx Γ) => θ (snd δγ))).    
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_conj_prt _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H, H0; split; auto. 
    destruct H, H0;  auto.

    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_disj_prt _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    destruct h2.
    destruct H.
    left; split; auto.
    right; split; auto.
    intros h1 h2 h3; auto.

    
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app δγ)) p).
    pose proof (rw_ro_prt _ _ _ _ _ _ _ w' X).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
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
    
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ w' X X0).

    clear IHX.
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (snd_app ( δγγ'))) p).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (rw_new_var_prt Γ Δ e c τ σ w1 w2 (ϕ /\\ (fun δγ : sem_ctx Δ * sem_ctx Γ => θ (snd δγ))) (ψ /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ctx Δ * sem_ctx Γ) => θ (snd δγ))) (θ0 /\\\ (fun (_ : sem_datatype σ) (δγγ' : sem_ctx (Δ ++ Γ)) => θ (snd_app δγγ'))) w').
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (rw_assign_prt _ _ _ _ _ w _ (θ0 /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ))) _ w').
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    intros.
    destruct H; split; auto.
    simpl; unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.

    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_cond_prt _ _ _ _ _ _ w w1 w2 w' _ (θ0 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.

    clear IHX1 IHX2.
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p0).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_case_prt _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X4).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.


    apply (rw_case_list_prt _ _ _ _ wty_l wty (ForallT_map (fun _ p => p /\\\ (fun _ x => θ (snd_app x))) θ0)).
    clear wty.
    dependent induction f.
    apply ForallT2_nil.
    simpl.
    apply ForallT2_cons.
    apply IHf.
    destruct p.
    simpl.
    destruct r.
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ p0).
    split.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X).    
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; destruct h3; split; auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).    
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    auto.
    intros h1 h2 h3; auto.
    assert
      (wty ||- {{(ϕ /\\ (fun δγ : sem_ctx Δ * sem_ctx Γ => θ (snd δγ)))}} (WHILE e DO c END) {{y
                                                                                                    | ((fun _ : unit => (ϕ /\\ (fun δγ : sem_ctx Δ * sem_ctx Γ => θ (snd δγ))) /\\
                                                                                                                                                                                     ro_to_rw_pre
                                                                                                                                                                                     ((θ0 /\\\ (fun _ δγ => θ (snd_app δγ))) false))) y}}).
    apply (rw_while_prt _ _ _ _ wty_e wty_c wty).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; auto.
    split; auto.
    pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0.
    destruct h1; rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3.
    auto.
    apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.


  +
    dependent induction X.
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; auto.
    split; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (rw_exfalso_tot _ _ _ _ w (ψ /\\\ fun (_ : sem_datatype τ) (δγ : sem_ctx Δ * sem_ctx Γ) => θ (snd δγ))).    
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.

    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_conj_tot _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H, H0; split; auto. 
    destruct H, H0;  auto.

    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (rw_disj_tot _ _ _ _ _ _ _ _ X X0).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2; auto.
    destruct h2.
    destruct H.
    left; split; auto.
    right; split; auto.
    intros h1 h2 h3; auto.

    
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app δγ)) p).
    pose proof (rw_ro_tot _ _ _ _ _ _ _ w' X).
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _  a X0).
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
    
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_sequence_tot _ _ _ _ _ _ _ _ _ _ w' X X0).

    clear IHX.
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (snd_app ( δγγ'))) p).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
    apply (rw_new_var_tot Γ Δ e c τ σ w1 w2 (ϕ /\\ (fun δγ : sem_ctx Δ * sem_ctx Γ => θ (snd δγ))) (ψ /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ctx Δ * sem_ctx Γ) => θ (snd δγ))) (θ0 /\\\ (fun (_ : sem_datatype σ) (δγγ' : sem_ctx (Δ ++ Γ)) => θ (snd_app δγγ'))) w').
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X1).
    intros h1 h2.
    destruct h2; split; auto.
    unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    apply (rw_assign_tot _ _ _ _ _ w _ (θ0 /\\\ (fun (_ : sem_datatype τ) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ))) _ w').
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    destruct h2; split; auto.
    intros h1 h2 h3; auto.
    intros.
    destruct H; split; auto.
    simpl; unfold snd_app in H0; rewrite tedious_equiv_1 in H0; auto.

    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    apply (rw_cond_tot _ _ _ _ _ _ w w1 w2 w' _ (θ0 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ)))).
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    unfold ro_to_rw_pre in h2.
    unfold snd_app in h2.
    destruct h2.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    split; auto.
    intros h1 h2 h3; auto.

    clear IHX1 IHX2.
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p0).
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p1).
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p2).

    apply (rw_case_tot _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 wty _ (θ1 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ))) (θ2 /\\\ (fun (_ : sem_datatype BOOL) (δγ : sem_ctx (Δ ++ Γ)) => θ (snd_app δγ)))
                       _
                       (ϕ1 /\\ (fun δγ : sem_ctx (Δ ++ Γ) => θ (snd_app δγ)))      
                       (ϕ2 /\\ (fun δγ : sem_ctx (Δ ++ Γ) => θ (snd_app δγ)))
          ).
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X3).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X4).
    intros h1 h2.
    split; destruct h2.
    exact H.
    unfold snd_app in H0.
    destruct h1.
    rewrite tedious_equiv_1 in H0.
    exact H0.
    intros h1 h2 h3; auto.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X5).
    intros h1 h2.
    split; destruct h2.
    exact H.
    exact H0.
    intros h1 h2 h3; auto.
    destruct h3.
    auto.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X6).
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

    
    apply (rw_case_list_tot _ _ _ _ wty_l wty
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
    pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) j) as i.
    apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    intros h1 h2 h3; auto.
    destruct j as [[_ j] _].
    pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _  θ j) as i.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a i).
    intros h1 h2; auto.
    destruct h2; split; auto.
    destruct h1; unfold snd_app in H0;  auto.
    rewrite tedious_equiv_1 in H0; auto.
    intros h1 h2 h3; auto.
    destruct j as [_ j].
    pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) j) as i.
    apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a i).
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
      (wty ||- [{(ϕ /\\ (fun δγ : sem_ctx Δ * sem_ctx Γ => θ (snd δγ)))}] (WHILE e DO c END) [{y
                                                                                                    | ((fun _ : unit => (ϕ /\\ (fun δγ : sem_ctx Δ * sem_ctx Γ => θ (snd δγ))) /\\
                                                                                                                                                                                     ro_to_rw_pre
                                                                                                                                                                                     ((θ0 /\\\ (fun _ δγ => θ (snd_app δγ))) false))) y}]).
    {

      apply (rw_while_tot _ _ _ _ wty_e wty_c wty_c' wty _ _ ψ0).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (snd_app ( δγ))) p).
      apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X).
      intros h1 h2.
      split; destruct h2; auto.
      intros h1 h2 h3.
      destruct h3; auto.
      split; auto.
      
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ (fun x => θ (( x))) X1).
      simpl.
      apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X).
      intros [h1 h2] [h3 h4]; split; auto.
      rewrite tedious_equiv_snd in h4; auto.
      intros h1 h2 [h3 h4]; split; auto.

      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ (fun x => θ ((fst_app x))) X2).
      simpl.
      apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X).
      intros [h1 h2] [h3 h4]; split; auto.
      simpl.
      simpl in h3, h4.
      split; auto.
      destruct h3.
      auto.
      destruct h3; auto.
      simpl in H0.
      simpl.
      rewrite tedious_equiv_snd in H0.
      auto.
      intros h1 h2 [h3 h4];  auto.

      intros x y [h1 h2].
      apply n; auto.
    }
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X).
    intros h1 h2; auto.
    intros h1 h2 h3.
    destruct h3; split; auto.
    destruct H0.
    destruct H.
    split; auto.
    destruct H; auto.

Defined.




Fixpoint admissible_ro_tot_prt Γ e τ (w : Γ |- e : τ) ϕ ψ (X : w |- [{ϕ}] e [{ψ}]) {struct X} : w |- {{ϕ}} e {{ψ}}
with admissible_rw_tot_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ (X : w ||- [{ϕ}] e [{ψ}]) {struct X} : w ||- {{ϕ}} e {{ψ}}.
Proof.
  +
    intros.
    dependent induction X.
    
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ a (admissible_ro_tot_prt _ _ _ _ _ _ X) a0).
    apply ro_exfalso_prt.
    apply (ro_conj_prt _ _ _ _ _ _ _  (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2)).
    apply (ro_disj_prt _ _ _ _ _ _ _  (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2)).
    apply ro_var_prt.
    apply ro_skip_prt.
    apply ro_true_prt.
    apply ro_false_prt.
    apply ro_int_prt.
    apply (ro_rw_prt _ _ _ _ _ _ _ (admissible_rw_tot_prt _ _ _ _ _ _ _ p)).
    apply (ro_coerce_prt _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_exp_prt _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X)).
    apply (ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    assert (sc:  (θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ctx Γ) => x <> Rdefinitions.IZR BinNums.Z0)) ->>>
                                                                                                               (fun x : sem_datatype REAL => ψ (Rdefinitions.RinvImpl.Rinv x))).
    {
      intros γ δ [m1 m2].
      apply a; auto.
    }
    apply (ro_recip_prt _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X) sc).
    apply (ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).

    assert (sc : (forall (y1 y2 : sem_datatype REAL) (γ : sem_ctx Γ),
                     ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ)).
    {
      intros; apply a; auto.
    }
    apply (ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) sc).

    apply (ro_lim_prt _ _ _ _ _ _ _ X e0).

  +
    dependent induction X.
    
    
    apply (rw_imply_prt _ _ _ _ _ _ _ _ _ _ a (admissible_rw_tot_prt _ _ _ _ _ _ _ X) a0).
    apply rw_exfalso_prt.
    apply (rw_conj_prt _ _ _ _ _ _ _ _ (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).

    apply (rw_disj_prt _ _ _ _ _ _ _ _ (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_ro_prt _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p)).

    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _  (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p) (admissible_rw_tot_prt _ _ _ _ _ _ _ X)).
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p) ψ0).
    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p) (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_case_prt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p p0 (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).



    {
      (* case list *)
      apply (rw_case_list_prt _ _ _ _ wty_l wty θ).
      clear f0 wty.
      dependent induction f.
      simpl.
      apply ForallT2_nil.
      apply ForallT2_cons.
      apply IHf.
      destruct j.
      destruct p0.
      split.
      exact p0.
      exact ((admissible_rw_tot_prt _ _ _ _ _ _ _ p2)).      
    }


    
    apply (rw_while_prt _ _ _ _ wty_e _ wty ϕ _ 
             (admissible_ro_tot_prt _ _ _ _ _ _ p) 
             (admissible_rw_tot_prt _ _ _ _ _ _ _ X1)). 

Defined.
