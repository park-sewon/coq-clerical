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

Lemma admissible_ro_prt_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ}
      (X : [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y) }}ᵖ) :
  ψ ->> θ ->[x : Γ] |- w {{ϕ x}} e {{y : τ | θ (x, y) }}ᵖ.
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X H0 H).
Defined.

Lemma admissible_ro_prt_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ}  (X : [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y) }}ᵖ ) :
  θ ->> ϕ ->  [x : Γ] |- w {{θ x}} e {{y : τ | ψ (x, y) }}ᵖ.
Proof.
  intros.
  assert (ψ ->> ψ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X H H0).
Defined.

Lemma admissible_ro_tot_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ}  (X : [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y) }}ᵗ) :
  ψ ->> θ -> [x : Γ] |- w {{ϕ x}} e {{y : τ | θ (x, y) }}ᵗ.
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X H0 H).
Defined.

Lemma admissible_ro_tot_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ}  (X : [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y) }}ᵗ ) :
  θ ->> ϕ ->  [x : Γ] |- w {{θ x}} e {{y : τ | ψ (x, y) }}ᵗ.
Proof.
  intros.
  assert (ψ ->> ψ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X H H0).
Defined.

Lemma app_both : forall {A B} {f g : A -> B} (e : f = g) (x : A), f x = g x.
Proof.
  intros.
  induction e.
  reflexivity.
Defined.

Lemma app_both2 : forall {A B C} {f g : A -> B -> C} (e : f = g) (x : A) (y : B), f x y = g x y.
Proof.
  intros.
  induction e.
  reflexivity.
Defined.

Lemma app_both3 : forall {A B C D} {f g : A -> B -> C -> D} (e : f = g) (x : A) (y : B) (z : C), f x y z = g x y z.
Proof.
  intros.
  induction e.
  reflexivity.
Defined.
(* Lemma ro_imply_prt_f Γ e τ (w : Γ |- e : τ) (ϕ ϕ' : Prop) ψ (X : [x : Γ] |- w {{ϕ}} e {{y : τ | ψ}}ᵖ) : *)
(*   (forall x, ϕ -> ϕ') ->  *)
(*   [x : Γ] |- w {{ϕ'}} e {{y : τ | ψ}}ᵖ. *)

Lemma pop_context_ro_prt : forall σ Γ e τ w ϕ ψ,
    [x : (σ :: Γ)] |- w {{ϕ x}} e {{y : τ | ψ x y}}ᵖ = [(x', x) : (σ :: Γ)] |- w {{ϕ (x', x)}} e {{y : τ | ψ (x', x) y}}ᵖ.
Proof.
  intros.
  repeat apply lp.
  assert ((fun x : sem_ctx (σ :: Γ) => ϕ x) = (fun '(x', x) => ϕ (x', x))).
  simpl.
  auto.
  apply dfun_ext; intros [h1 h2]; auto.
  rewrite H.
  apply lp.
  apply dfun_ext; intros [h1 h2]; auto.
  destruct h1; auto.
Defined.

Lemma pop_context_ro_tot : forall σ Γ e τ w ϕ ψ,
    [x : (σ :: Γ)] |- w {{ϕ x}} e {{y : τ | ψ x y}}ᵗ = [(x', x) : (σ :: Γ)] |- w {{ϕ (x', x)}} e {{y : τ | ψ (x', x) y}}ᵗ.
Proof.
  intros.
  repeat apply lp.
  assert ((fun x : sem_ctx (σ :: Γ) => ϕ x) = (fun '(x', x) => ϕ (x', x))).
  simpl.
  auto.
  apply dfun_ext; intros [h1 h2]; auto.
  rewrite H.
  apply lp.
  apply dfun_ext; intros [h1 h2]; auto.
  destruct h1; auto.
Defined.

Fixpoint admissible_ro_prt_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵖ) {struct X} : [x : Γ] |- w {{ϕ x /\ θ x}} e {{y : τ | ψ (x, y) /\ θ x}}ᵖ
with admissible_ro_tot_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : [x : Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵗ) {struct X} : [x : Γ] |- w {{ϕ x /\ θ x}} e {{y : τ | ψ (x, y) /\ θ x}}ᵗ
with admissible_rw_prt_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : [γ : Γ ;;; δ : Δ] ||- w {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ) {struct X} : [γ : Γ ;;; δ : Δ] ||- w {{ϕ (γ, δ) /\ θ γ}} e {{y : τ | ψ (γ, (δ, y)) /\ θ γ}}ᵖ
with admissible_rw_tot_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : [γ : Γ ;;; δ : Δ] ||- w {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ) {struct X} : [γ : Γ ;;; δ : Δ] ||- w {{ϕ (γ, δ) /\ θ γ}} e {{y : τ | ψ (γ, (δ, y)) /\ θ γ}}ᵗ.
Proof.
  +
    dependent induction X.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
      assert ((ϕ /\\ θ) ->> (P /\\ θ)).
      intros γ p; split; destruct p.
      apply a.
      rewrite (app_both x γ).
      exact H.
      exact H0.
      assert ((fun '(x, y) => Q (x, y) /\ θ x) ->> (fun '(x, y) => ψ (x, y) /\ θ x)).
      intros [γ y] p; split; destruct p.
      rewrite <- (app_both x0 (γ, y)).
      apply a0.
      exact H0.
      exact H1.
      apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X0 H H0).

    ++
      pose proof (ro_exfalso_prt Γ e τ w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      simpl in X.
      simpl.
      
      apply (admissible_ro_prt_pre_strengthen
               (ψ := fun '(x1, y) => ψ (x1, y) /\ θ x1)
               X).
      intros γ y.
      rewrite (app_both x γ).
      destruct y; auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      pose proof (ro_conj_prt _ _ _ _ _
                    (fun '(x, y) => _)
                    (fun '(x, y) => _)
                    X X0).
      simpl  in X3.
      simpl in X3.
      (* apply (admissible_ro_prt_pre_strengthen *)
      (*          (θ := fun x => P x /\ θ x) *)
             
      (*          (ψ := fun '(x1, y) => _) *)

      (*          X3). *)
      
      apply (ro_imply_prt _ _ _ _ _ _
                                   (fun '(x1, y) => _)
                                   _
                                   (fun '(x1, y) => _)
                                   X3).
      intros a b.
      rewrite (app_both x a).
      exact b.
      
      intros a b.
      destruct a.
      
      rewrite <- (app_both x0 (s, s0)).
      destruct b as [[t1 t2] [t3 t4]].
      repeat split; auto.
      
    ++

      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      pose proof (ro_disj_prt _ _ _ _ _ _ patf  X X0).
      apply (ro_imply_prt _ _ _ _ _ _ _ _ patf X3). 
      intros a b.
      rewrite <- (app_both x a) in b.
      destruct b.
      destruct H.
      left; auto.
      right; auto.
      intros a b.
      destruct a.
      rewrite <- (app_both x0 (s, s0)).
      auto.

    ++
      pose proof (ro_var_prt _ _ _ w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_prt_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x a) in H.
      rewrite <- (app_both x0 (a, _)).
      auto.

    ++
      pose proof (ro_skip_prt _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_prt_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, tt)).
      rewrite <- (app_both x a) in H.
      auto.
      
    ++
      pose proof (ro_true_prt _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_prt_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, _)).
      rewrite <- (app_both x a) in H.
      auto.

    ++
      pose proof (ro_false_prt _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_prt_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, _)).
      rewrite <- (app_both x a) in H.
      auto.

    ++
      pose proof (ro_int_prt _ _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_prt_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, _)).
      rewrite <- (app_both x a) in H.
      auto.

    ++
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _
                    patf
                    pattf
                    θ p).
      simpl in X.
      pose proof (ro_rw_prt _ _ _ _
                            (fun '(x, _) => P (x, tt) /\ θ x)
                            (fun '(x, (_, y)) => (Q (x, (tt, y)) /\ θ x))
                            w' X).
      simpl in X0.
      apply (ro_imply_prt _ _ _ _ _ _ patf _ (fun '(γ, y) => (ψ (γ, y) /\ θ γ)) X0).
      intros a b.
      rewrite (app_both x a).
      auto.
      intros [h1 h2] h3.
      rewrite <- (app_both x0 (h1, h2)).
      auto.

    ++
      
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ patf θ X).
      apply (ro_coerce_prt _ _ w _ patf w').
      simpl in X0.
      apply (ro_imply_prt _ _ INTEGER _ _ _ patf _ (fun '(γ, y) => (ψ (γ, IZR y) /\ θ γ)) X0).
      intros a b.
      rewrite (app_both x a).
      auto.
      intros [h1 h2] h3.
      rewrite <- (app_both x0 (_, _)).
      auto.

    ++ 
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ patf θ X).
      apply (ro_exp_prt _ _ w _ patf w').
      apply (ro_imply_prt _ _ INTEGER _ _ _ patf _ (fun '(γ, y) => (ψ (γ, pow2 y) /\ θ γ)) X0).
      intros a b.
      rewrite (app_both x a).
      auto.
      intros [h1 h2] h3.
      rewrite <- (app_both x0 (_, _)).
      auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_op_plus_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _) ).
      destruct H0, H1; split; auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_op_mult_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_op_minus_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.


    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_op_plus_prt _ _ _ _ _ _  patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.
    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_op_mult_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.
    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_op_minus_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.
    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_recip_prt _ _ w _ patf w' patf X0).    
      intros h1 h2 h3.
      rewrite <- (app_both x0 (_, _)).
      destruct h3 as [[p1 p2] p3]; split; auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_comp_eq_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct  H0, H1; split; auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_comp_lt_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct  H0, H1; split; auto.

    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_lt_prt _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct  H0, H1; split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ patf (fun x : sem_ctx (INTEGER :: Γ) => θ (fst x)) p).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      simpl in X.
      rewrite pop_context_ro_tot in X .
      simpl in X.
      apply (ro_lim_prt Γ e w (fun x1 => ϕ0 x1 /\ θ x1) (fun '((x, x'), y) => (θ0 ((x, x'), y) /\ θ x)) _ patf X).
      clear H.
      intros.
      destruct H.
      pose proof (e0 _ H).
      destruct H1.
      exists x1.
      split.
      split; auto.
      rewrite <- (app_both x0 (_, _)).
      destruct H1; auto.
      intros.
      destruct H2.
      destruct H1.
      apply H4.
      exact H2.
      
  +
    dependent induction X.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
      assert ((ϕ /\\ θ) ->> (P /\\ θ)).
      intros γ p; split; destruct p.
      apply a.
      rewrite (app_both x γ).
      exact H.
      exact H0.
      assert ((fun '(x, y) => Q (x, y) /\ θ x) ->> (fun '(x, y) => ψ (x, y) /\ θ x)).
      intros [γ y] p; split; destruct p.
      rewrite <- (app_both x0 (γ, y)).  
      apply a0.
      exact H0.
      exact H1.
      apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X0 H H0).

    ++
      pose proof (ro_exfalso_tot Γ e τ w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      simpl in X.
      apply (admissible_ro_tot_pre_strengthen (ψ := patf) X).
      intros γ y.
      rewrite (app_both x γ).
      destruct y; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      pose proof (ro_conj_tot _ _ _ _ _ patf patf  X X0).
      simpl  in X3.
      apply (ro_imply_tot _ _ _ _ _ 
                                   _
                                   patf
                                   _
                                   (fun '(x1, y) => (ψ (x1, y) /\ θ x1))
                                   
                                   X3).
      intros a b.
      rewrite (app_both x a).
      exact b.
      intros [a b] [[c1 c2] [c3 c4]].
      rewrite <- (app_both x0 (a, b)).
      auto.

    ++

      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      pose proof (ro_disj_tot _ _ _ _ _ _ patf  X X0).
      apply (ro_imply_tot _ _ _ _ _ _ _ _ (fun '(x1, y) => (ψ (x1, y) /\ θ x1)) X3).
      intros a b.
      rewrite <- (app_both x a) in b.
      destruct b.
      destruct H.
      left; auto.
      right; auto.
      intros [a b] c.
      rewrite <- (app_both x0 (a, b)).
      auto.

    ++
      pose proof (ro_var_tot _ _ _ w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_tot_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x a) in H.
      rewrite <- (app_both x0 (a, _)).
      auto.

    ++
      pose proof (ro_skip_tot _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_tot_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, tt)).
      rewrite <- (app_both x a) in H.
      auto.
      
    ++
      pose proof (ro_true_tot _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_tot_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, _)).
      rewrite <- (app_both x a) in H.
      auto.

    ++
      pose proof (ro_false_tot _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_tot_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, _)).
      rewrite <- (app_both x a) in H.
      auto.

    ++
      pose proof (ro_int_tot _ _  w (fun '(x1, y) => ψ (x1, y) /\ θ x1)).
      apply (admissible_ro_tot_pre_strengthen X).
      intros a b; split; destruct b; auto.
      rewrite <- (app_both x0 (a, _)).
      rewrite <- (app_both x a) in H.
      auto.

    ++
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _
                    patf
                    pattf
                    θ p).
      simpl in X.
      pose proof (ro_rw_tot _ _ _ _
                            (fun '(x, _) => P (x, tt) /\ θ x)
                            (fun '(x, (_, y)) => (Q (x, (tt, y)) /\ θ x))
                            w' X).
      simpl in X0.
      apply (ro_imply_tot _ _ _ _ _ _ patf _ (fun '(γ, y) => (ψ (γ, y) /\ θ γ)) X0).
      intros a b.
      rewrite (app_both x a).
      auto.
      intros [h1 h2] h3.
      rewrite <- (app_both x0 (h1, h2)).
      auto.

    ++
      
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ patf θ X).
      apply (ro_coerce_tot _ _ w _ patf w').
      simpl in X0.
      apply (ro_imply_tot _ _ INTEGER _ _ _ patf _ (fun '(γ, y) => (ψ (γ, IZR y) /\ θ γ)) X0).
      intros a b.
      rewrite (app_both x a).
      auto.
      intros [h1 h2] h3.
      rewrite <- (app_both x0 (_, _)).
      auto.

    ++ 
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ patf θ X).
      apply (ro_exp_tot _ _ w _ patf w').
      apply (ro_imply_tot _ _ INTEGER _ _ _ patf _ (fun '(γ, y) => (ψ (γ, pow2 y) /\ θ γ)) X0).
      intros a b.
      rewrite (app_both x a).
      auto.
      intros [h1 h2] h3.
      rewrite <- (app_both x0 (_, _)).
      auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_op_plus_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _) ).
      destruct H0, H1; split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_op_mult_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_op_minus_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.


    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_op_plus_tot _ _ _ _ _ _  patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.
    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_op_mult_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.
    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_op_minus_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct H0, H1; split; auto.
    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_recip_tot _ _ w _ patf w' patf X0).    
      intros h1 h2 h3.
      rewrite <- (app_both x0 (_, _)).
      destruct (a h1 h2 (proj1 h3)).
      split; auto.
      destruct h3; split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_comp_eq_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct  H0, H1; split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_int_comp_lt_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct  H0, H1; split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X1).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ θ X2).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      apply (ro_real_lt_tot _ _ _ _ _ _ patf patf _ patf X X0).
      intros.
      rewrite <- (app_both x0 (_, _)).
      destruct (a γ y1 y2 (proj1 H0) (proj1 H1)).
      destruct H0, H1; repeat split; auto.

    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ patf (fun x : sem_ctx (INTEGER :: Γ) => θ (fst x)) X).
      assert ((fun x1 => ϕ x1 /\ θ x1) = (fun x  => ϕ0 x /\ θ x)).
      apply dfun_ext; intros h; rewrite (app_both x h); auto. 
      rewrite H.
      simpl in X0.
      rewrite pop_context_ro_tot in X0 .
      simpl in X0.
      apply (ro_lim_tot Γ e w (fun x1 => ϕ0 x1 /\ θ x1) (fun '((x, x'), y) => (θ0 ((x, x'), y) /\ θ x)) _ patf X0).
      clear H.
      intros.
      destruct H.
      pose proof (e0 _ H).
      destruct H1.
      exists x1.
      split.
      split; auto.
      rewrite <- (app_both x0 (_, _)).
      destruct H1; auto.
      intros.
      destruct H2.
      destruct H1.
      apply H4.
      exact H2.
      

      

  +
    dependent induction X.
    ++
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      destruct h3; split; auto.
      apply a.
      rewrite (app_both x (_, _)); auto.
      intros [h1 [h2 h3]] h4.
      destruct h4; split; auto.
      rewrite <- (app_both x0 (_, (_, _))).
      apply a0; auto.

    ++
    
      pose proof (rw_exfalso_prt _ _ _ _ w (fun '(γ, (δ, y)) => (ψ (γ, (δ, y)) /\ θ γ))).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      auto.
      destruct h3; auto.
      intros [h1 [h2 h3]] h4.
      auto.
    ++
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
      pose proof (rw_conj_prt _ _ _ _ _  patf pattf pattf X X0).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      intros [h1 [h2 h3]] h4.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      destruct h4.
      destruct H, H0; repeat split; auto.

    ++
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X2).
      pose proof (rw_disj_prt _ _ _ _ _ patf patf pattf X X0).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      destruct h3.
      destruct H.
      left; split; auto.
      right; split; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app δγ)) p).
      pose proof (rw_ro_prt _ _ _ _ _ _ patf w' X).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      destruct h3.
      rewrite tedious_equiv_fst; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      rewrite tedious_equiv_fst in h4; auto.
      
    ++
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ _ _ θ X1).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ patf pattf θ X2).
      pose proof (rw_sequence_prt _ _ _ _ _ _ _ patf pattf pattf w' X X0).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (fst_app ( δγγ'))) p).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ patf pattf θ X).
      apply (rw_new_var_prt Γ Δ e c τ σ w1 w2 (fun '(γ, δ) => ϕ (γ, δ) /\ θ γ) (fun '(γ, (δ, y)) => ψ (γ, (δ, y)) /\ θ γ) (fun '(x, y) => θ0 (x, y) /\ θ (fst_app x)) w').
      
      
      apply (ro_imply_prt _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1)) ) X0).
      intros h1 h2.
      destruct h2; split; auto.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; auto.
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X1).
      intros h1 h2.
      destruct h1; split; auto.
      destruct s0; auto.
      destruct h2; auto.
      intros.
      destruct s0.
      destruct h2.
      rewrite tedious_equiv_fst in H0; auto. 
      intros [h1 [[h2 h3] h4]] h5; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      apply (rw_assign_prt _ _ _ _ _ w patf (fun '(δ, y) => θ0 (δ, y)  /\ θ (fst_app δ)) pattf w').
      apply (ro_imply_prt _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1))) X).
      intros h1 h2.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; auto.
      intros.
      rewrite tedious_equiv_fst in H.
      destruct H; split; auto.
      rewrite <- (app_both x0 (_, (_, _))).
      apply ψ0.
      auto.

    ++
      
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ patf pattf θ X1).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ patf pattf θ X2).
      apply (rw_cond_prt _ _ _ _ _ _ w w1 w2 w' patf (fun '(x, y) => θ0 (x, y) /\  θ (fst_app x)) pattf).
      apply (ro_imply_prt _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1))) X).
      intros h1 h2.
      rewrite (app_both x (_, _)).
      auto.
      intros [h1 h2] h3; auto.
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      rewrite tedious_equiv_fst in h3.
      auto.
      intros [h1 [h2 h3]] h4.      
      rewrite <- (app_both x0 (_, (_, _))); auto.
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite tedious_equiv_fst in h3.
      auto.
      intros [h1 [h2 h3]] h4.      
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      apply (rw_case_list_prt _ _ _ _ wty_l wty (ForallT_map (fun _ p => fun '(x, y) => p (x, y) /\ θ (fst_app x)) θ0) patf pattf).
      clear wty.
      dependent induction f.
      apply ForallT2_nil.
      simpl.
      apply ForallT2_cons.
      apply IHf.
      auto.
      auto.
      destruct p.
      simpl.
      destruct r.
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ patf pattf θ p0).
      split.
      apply (ro_imply_prt _ _ BOOL _ _ _ patf _ (fun '(x1, y) => (q (x1, y) /\ θ (fst_app x1))) X).    
      intros h1 h2.
      destruct h2; split; auto.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; destruct h3; split; auto.
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      rewrite tedious_equiv_fst in h3.
      auto.
      intros [h1 [h2 h3]] h4.      
      rewrite <- (app_both x0 (_, (_, _))); auto.
            
    ++
      
      assert
        ( [γ : Γ ;;; δ : Δ]||- wty {{(ϕ (γ, δ) /\ θ γ)}} (WHILE e DO c END) {{y : UNIT| (ϕ (γ, δ) /\ θ γ) /\
                                                                                       (θ0 ((γ; δ), false) /\ θ (fst_app (γ ; δ)))}}ᵖ).
      apply (rw_while_prt _ _ _ _ wty_e wty_c wty
                          (fun '(γ, δ) => ϕ (γ, δ) /\ θ γ)
                          (fun '(x, y) => θ0 (x, y) /\ θ (fst_app x))
            ).
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      apply (ro_imply_prt _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1))) X0).
      intros h1 h2.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; auto.
      
      pose proof (admissible_rw_prt_pose_readonly _ _ _ _ _ patf pattf θ X).
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf (fun '(γ, (δ, y)) =>  (ϕ (γ, δ) /\ θ γ)) X0).

      intros h1 h2.
      destruct h1.
      rewrite tedious_equiv_fst in h2; auto.
      intros [h1 [h2 h3]] h4.
      rewrite <- (app_both x (_, _)); auto.
      
      apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf (fun '(γ, (δ, y)) => (ψ (γ, (δ, y)) /\ θ γ)) X0).
      intros h1 h2; auto.
      intros [h1 [h2 h3]].
      rewrite tedious_equiv_fst; auto.
      intros.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      rewrite (app_both x (_, _)); auto.
      destruct H as [[t1 t2] [t3 t4]]; repeat split; auto.


  +
    dependent induction X.
    ++
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X).
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      destruct h3; split; auto.
      apply a.
      rewrite (app_both x (_, _)); auto.
      intros [h1 [h2 h3]] h4.
      destruct h4; split; auto.
      rewrite <- (app_both x0 (_, (_, _))).
      apply a0; auto.

    ++
    
      pose proof (rw_exfalso_tot _ _ _ _ w (fun '(γ, (δ, y)) => (ψ (γ, (δ, y)) /\ θ γ))).
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      auto.
      destruct h3; auto.
      intros [h1 [h2 h3]] h4.
      auto.
    ++
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
      pose proof (rw_conj_tot _ _ _ _ _  patf pattf pattf X X0).
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      intros [h1 [h2 h3]] h4.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      destruct h4.
      destruct H, H0; repeat split; auto.

    ++
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X2).
      pose proof (rw_disj_tot _ _ _ _ _ patf patf pattf X X0).
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      destruct h3.
      destruct H.
      left; split; auto.
      right; split; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app δγ)) p).
      pose proof (rw_ro_tot _ _ _ _ _ _ patf w' X).
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      destruct h3.
      rewrite tedious_equiv_fst; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      rewrite tedious_equiv_fst in h4; auto.
      
    ++
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ _ _ θ X1).
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf θ X2).
      pose proof (rw_sequence_tot _ _ _ _ _ _ _ patf pattf pattf w' X X0).
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite <- (app_both x (_, _)) in h3; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγγ' => θ (fst_app ( δγγ'))) p).
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf θ X).
      apply (rw_new_var_tot Γ Δ e c τ σ w1 w2 (fun '(γ, δ) => ϕ (γ, δ) /\ θ γ) (fun '(γ, (δ, y)) => ψ (γ, (δ, y)) /\ θ γ) (fun '(x, y) => θ0 (x, y) /\ θ (fst_app x)) w').
      
      
      apply (ro_imply_tot _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1)) ) X0).
      intros h1 h2.
      destruct h2; split; auto.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; auto.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X1).
      intros h1 h2.
      destruct h1; split; auto.
      destruct s0; auto.
      destruct h2; auto.
      intros.
      destruct s0.
      destruct h2.
      rewrite tedious_equiv_fst in H0; auto. 
      intros [h1 [[h2 h3] h4]] h5; auto.
      rewrite <- (app_both x0 (_, (_, _))); auto.
      
    ++
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      apply (rw_assign_tot _ _ _ _ _ w patf (fun '(δ, y) => θ0 (δ, y)  /\ θ (fst_app δ)) pattf w').
      apply (ro_imply_tot _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1))) X).
      intros h1 h2.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; auto.
      intros.
      rewrite tedious_equiv_fst in H.
      destruct H; split; auto.
      rewrite <- (app_both x0 (_, (_, _))).
      apply ψ0.
      auto.

    ++
      
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf θ X1).
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf θ X2).
      apply (rw_cond_tot _ _ _ _ _ _ w w1 w2 w' patf (fun '(x, y) => θ0 (x, y) /\  θ (fst_app x)) pattf).
      apply (ro_imply_tot _ _ _ _ _ _ patf _ (fun '(x1, y) => (θ0 (x1, y) /\ θ (fst_app x1))) X).
      intros h1 h2.
      rewrite (app_both x (_, _)).
      auto.
      intros [h1 h2] h3; auto.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X0).
      intros [h1 h2] h3.
      rewrite tedious_equiv_fst in h3.
      auto.
      intros [h1 [h2 h3]] h4.      
      rewrite <- (app_both x0 (_, (_, _))); auto.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf X3).
      intros [h1 h2] h3.
      rewrite tedious_equiv_fst in h3.
      auto.
      intros [h1 [h2 h3]] h4.      
      rewrite <- (app_both x0 (_, (_, _))); auto.
      

    ++
      apply (rw_case_list_tot _ _ _ _ wty_l wty
                              (ForallT_map (fun _ p => fun '(x, y) => p (x, y) /\ θ (fst_app x)) θ0)
                              (ForallT_map (fun _ p => fun x => p x /\ θ (fst_app x)) ϕi)
                              patf pattf
            ).
      clear wty.
      clear f0.
      dependent induction f.
      apply ForallT3_nil.
      simpl.
      apply ForallT3_cons.
      simpl.
      apply IHf; auto.
      repeat split.
      destruct j as [[j _] _].
      pose proof (admissible_ro_prt_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) j) as i.
      apply (ro_imply_prt _ _ BOOL _ _ _ patf _ (fun '(x1, y) => (q (x1, y) /\ θ (fst_app x1))) i).
      intros h1 h2; auto.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3; auto.
      destruct j as [[_ j] _].
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf  θ j) as i.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf (fun '(γ, (δ, y)) => (ψ (γ, (δ, y)) /\ θ γ)) i).
      intros [h1 h2] h3; auto.
      rewrite tedious_equiv_fst in h3; auto.
      intros [h1 [h2 h3]] h4; auto.
      rewrite <- (app_both x0 (_, (_, _))).
      auto.
      destruct j as [_ j].
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ patf (fun δγ => θ (fst_app ( δγ))) j) as i.
      apply (ro_imply_tot _ _ BOOL _ _ _ patf _ (fun '(x1, b) => (b = true)) i).
      intros h1 h2; auto.
      intros [h1 h2] h3; auto.
      destruct h3; auto.
      intros.
      destruct H.
      rewrite <- (app_both x (_, _)) in H.
      pose proof (f0 x1 H).
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

    ++
      
      assert
        ( [γ : Γ ;;; δ : Δ]||- wty {{(ϕ (γ, δ) /\ θ γ)}} (WHILE e DO c END) {{y : UNIT| (ϕ (γ, δ) /\ θ γ) /\
                                                                                       (θ0 ((γ; δ), false) /\ θ (fst_app (γ ; δ)))}}ᵗ).
      apply (rw_while_tot _ _ _ _ wty_e wty_c wty_c' wty
                          (fun '(γ, δ) => ϕ (γ, δ) /\ θ γ)
                          (fun '(x, y) => θ0 (x, y) /\ θ (fst_app x))
                          ψ0
            ).
      pose proof (admissible_ro_tot_pose_readonly _ _ _ _ _ _ (fun δγ => θ (fst_app ( δγ))) p).
      apply (ro_imply_tot _ _ _ _ _ _ patf _ (fun '(x1, y) =>  (θ0 (x1, y) /\ θ (fst_app x1))) X).
      intros h1 h2.
      split; destruct h2; auto.
      rewrite (app_both x (_, _)); auto.
      intros [h1 h2] h3.
      destruct h3; auto.

      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf (fun x => θ (( x))) X1).
      simpl.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf (fun '(γ, (δ, y)) =>  (ϕ (γ, δ) /\ θ γ) ) X).
      intros [h1 h2] h3. 
      rewrite tedious_equiv_fst in h3; auto.
      intros [h1 [h2 h3]] h4. 
      rewrite <- (app_both x (_, _)).
      auto.
      
      pose proof (admissible_rw_tot_pose_readonly _ _ _ _ _ patf pattf (fun x => θ ((snd_app x))) X2).
      simpl.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf (fun '(x1, (δ, y)) => ψ0 (x1, δ)) X).
      intros [γ δ] [[h1 h2] h3].
      repeat split; auto.
      rewrite tedious_equiv_fst in h2; auto.
      intros.
      intros [h1 [h2 h3]] [h4 _]; auto.

      intros.
      apply n; auto.
      rewrite (app_both x (_, _)).
      destruct H; auto.
      apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf (fun '(γ, (δ, y)) => (ψ (γ, (δ, y)) /\ θ γ)) X).
      intros h1 h2; auto.
      intros [h1 [h2 h3]] h4.
      rewrite tedious_equiv_fst in h4.
      rewrite <- (app_both x0 (_, (_, _))).
      rewrite (app_both x (_, _)).
      destruct h4 as [[t1 t2] [t3 t4]].
      repeat split; auto.
Defined.




Fixpoint admissible_ro_tot_prt Γ e τ (w : Γ |- e : τ) ϕ ψ (X : [x: Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵗ) {struct X} :
  [x: Γ] |- w {{ϕ x}} e {{y : τ | ψ (x, y)}}ᵖ
with admissible_rw_tot_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ (X : [x: Γ ;;; y : Δ] ||- w {{ϕ (x, y)}} e {{z : τ | ψ (x, (y, z))}}ᵗ) {struct X} : [x: Γ ;;; y : Δ] ||- w {{ϕ (x, y)}} e {{z : τ | ψ (x, (y, z))}}ᵖ.
Proof.
  +
    intros.
    dependent induction X; simpl;
      try (rewrite <- x); try rewrite  <- x0.
    apply (ro_imply_prt _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X)); auto.
    apply ro_exfalso_prt.
    apply (ro_conj_prt _ _ _ _ _ _ _  (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2)).
    apply (ro_disj_prt _ _ _ _ _ _ _  (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2)).
    apply ro_var_prt.
    apply ro_skip_prt.
    apply ro_true_prt.
    apply ro_false_prt.
    apply ro_int_prt.
    pose proof (admissible_rw_tot_prt _ _ _ _ _ patf pattf p).
    exact (ro_rw_prt _ _ _ _ _ _ _ X).
    pose proof (admissible_ro_tot_prt _ _ _ _ _ patf X).
    exact (ro_coerce_prt _ _ _ _ _ _ X0).
    pose proof (admissible_ro_tot_prt _ _ _ _ _ patf X).
    exact (ro_exp_prt _ _ _ _ _ _ X0).

    apply (ro_int_op_plus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_op_mult_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_op_minus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_plus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_mult_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_real_op_minus_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    assert (sc:  (forall x y, θ (x, y) /\ y <> 0%R -> ψ (x, (/ y)))).
    {
      intros γ δ [m1 m2].
      rewrite <- (app_both x0 (_, _)).
      apply a; auto.
    }
    rewrite x0.
    apply (ro_recip_prt _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X) sc).
    apply (ro_int_comp_eq_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).
    apply (ro_int_comp_lt_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) ψ0).

    assert (sc : (forall γ y1 y2,
                     ψ1 (γ, y1) -> ψ2 (γ, y2) -> y1 <> y2 -> ψ (γ, Rltb'' y1 y2))).
    {
      intros.
      rewrite <- (app_both x0 (_, _)).
      intros; apply a; auto.
    }
    rewrite x0.
    apply (ro_real_lt_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ X1) (admissible_ro_tot_prt _ _ _ _ _ _ X2) sc).

    apply (ro_lim_prt _ _ _ _ _ _ _ X e0).

  +
    dependent induction X; simpl;
      try (rewrite <- x); try rewrite  <- x0.

    
    apply (rw_imply_prt _ _ _ _ _ _ _ _ _ _ (admissible_rw_tot_prt _ _ _ _ _ _ _ X) a a0).
    apply rw_exfalso_prt.
    apply (rw_conj_prt _ _ _ _ _ _ _ _ (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).

    apply (rw_disj_prt _ _ _ _ _ _ _ _ (admissible_rw_tot_prt _ _ _ _ _ _ _ X1) (admissible_rw_tot_prt _ _ _ _ _ _ _ X2)).
    apply (rw_ro_prt _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p)).

    pose proof (admissible_rw_tot_prt _ _ _ _ _ _ _ X1).
    pose proof (admissible_rw_tot_prt _ _ _ _ _ patf pattf X2).
    
    apply (rw_sequence_prt _ _ _ _ _ _ _ _ _ _ _ X X0).

    
    pose proof (admissible_rw_tot_prt _ _ _ _ _ patf pattf X).
    
    apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p) X0). 
    apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p) ψ0).

    pose proof (admissible_rw_tot_prt _ _ _ _ _ patf pattf X1).
    pose proof ((admissible_rw_tot_prt _ _ _ _ _ patf pattf X2)).
    apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ (admissible_ro_tot_prt _ _ _ _ _ _ p) X X0). 

    {
      clear x x0 ϕ ψ.
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
      exact ((admissible_rw_tot_prt _ _ _ _ _ patf _ p2)).      
    }

    pose proof (admissible_rw_tot_prt _ _ _ _ _ patf pattf X1).
    apply (rw_while_prt _ _ _ _ wty_e _ wty ϕ0 _ 
             (admissible_ro_tot_prt _ _ _ _ _ _ p) 
             X). 
Defined.
