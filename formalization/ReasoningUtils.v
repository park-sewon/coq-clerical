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
Require Import Clerical.ReasoningAdmissible.
Require Import Clerical.ReasoningTyPaired.

Require Import List.

(* when we know where the limit converges to *)
Lemma ro_lim_prt_util {Γ} {e}
  {w : Γ |- Lim e : REAL}
  {ϕ} {ψ} (f : sem_ctx Γ -> R) :
   [(z, x) : Γ ::: INTEGER ] |- (has_type_ro_Lim_inverse Γ e w)
        {{ϕ z}}
          e
          {{y : REAL| Rabs (y - f z) < pow2 (- x)}}ᵗ ->
        ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
        [x : Γ] |- w {{ϕ x}} Lim e {{y : REAL | ψ (x, y)}}ᵖ.
Proof.
  intros.
  pose proof
       (ro_lim_prt _ _ _
                   ϕ (fun '((z, x), y)  =>  (Rabs (y - f z) < pow2 (- x)))
                   w
       (fun '(x, y) => ϕ x /\ y = f x)
       X
    ).
  assert ((forall γ, ϕ γ ->
                     exists y : R,
                       (fun y0 x => ϕ x /\ y0 = f x) y γ /\
                         (forall x z,
                             (fun y0 x0 => Rabs (y0 - f (snd x0)) < pow2 (- fst x0)) z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x)))).
  intros.
  exists (f γ).
  split.
  split; auto.
  intros.
  exact H1.
  apply X0 in H0.
  apply (ro_imply_prt _ _ _ _ _ _ patf _ patf H0).
  intro h; auto.
  intros [h1 h2] h3.
  apply H.
  auto.
Defined.

Lemma ro_lim_tot_util {Γ} {e}
  {w : Γ |- Lim e : REAL}
  {ϕ} {ψ} (f : sem_ctx Γ -> R) :
   [(z, x) : Γ ::: INTEGER ] |- (has_type_ro_Lim_inverse Γ e w)
        {{ϕ z}}
          e
          {{y : REAL| Rabs (y - f z) < pow2 (- x)}}ᵗ ->
        ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
        [x : Γ] |- w {{ϕ x}} Lim e {{y : REAL | ψ (x, y)}}ᵗ.
Proof.
  intros.
  pose proof
       (ro_lim_tot _ _ _
                   ϕ (fun '((z, x), y)  =>  (Rabs (y - f z) < pow2 (- x)))
                   w
       (fun '(x, y) => ϕ x /\ y = f x)
       X
    ).
  assert ((forall γ, ϕ γ ->
                     exists y : R,
                       (fun y0 x => ϕ x /\ y0 = f x) y γ /\
                         (forall x z,
                             (fun y0 x0 => Rabs (y0 - f (snd x0)) < pow2 (- fst x0)) z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x)))).
  intros.
  exists (f γ).
  split.
  split; auto.
  intros.
  exact H1.
  apply X0 in H0.
  apply (ro_imply_tot _ _ _ _ _ _ patf _ patf H0).
  intro h; auto.
  intros [h1 h2] h3.
  apply H.
  auto.
Defined.

Lemma pp_ro_rw_prt_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ ;;; _ : nil] ||- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (pp_ro_rw_prt
                (Γ := Γ) (c := e) (τ := τ) (ϕ := fun '(x, _) => ϕ x) (ψ := fun '(x, (_, y)) => ψ (x, y))).
  simpl in X0.
  apply X0; auto.
Defined.


Lemma pp_ro_rw_tot_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ ;;; _ : nil] ||- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (pp_ro_rw_tot
                (Γ := Γ) (c := e) (τ := τ) (ϕ := fun '(x, _) => ϕ x) (ψ := fun '(x, (_, y)) => ψ (x, y))).
  simpl in X0.
  apply X0; auto.
Defined.

Lemma pp_ro_var_prt_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ (x, var_access Γ k τ w x)) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (@pp_ro_var_prt Γ k τ ψ w).
  apply (pp_ro_imply_prt X).
  apply H.
  intro h; auto.
Defined.

Lemma pp_ro_var_tot_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ (x, var_access Γ k τ w x)) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (@pp_ro_var_tot Γ k τ ψ w).
  apply (pp_ro_imply_tot X).
  apply H.
  intro h; auto.
Defined.

Lemma pp_ro_skip_prt_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, tt)) -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_Skip Γ).
  pose proof (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_skip_tot_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, tt)) -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_Skip Γ).
  pose proof (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_true_prt_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, true)) -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_True Γ).
  pose proof (ro_true_prt _  (has_type_ro_True Γ) ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_true_tot_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, true)) -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_True Γ).
  pose proof (ro_true_tot _  (has_type_ro_True Γ) ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_false_prt_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, false)) -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_False Γ).
  pose proof (ro_false_prt _  (has_type_ro_False Γ) ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_false_tot_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, false)) -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_False Γ).
  pose proof (ro_false_tot _  (has_type_ro_False Γ) ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_int_prt_back {Γ} {k} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, k)) -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_Int Γ k).
  pose proof (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_int_tot_back {Γ} {k} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, k)) -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_Int Γ k).
  pose proof (ro_int_tot _ _ (has_type_ro_Int Γ k) ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.


Lemma pp_ro_recip_prt_back {Γ} {e} {ϕ : pred} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ (γ, / y)}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ (γ, y)}}ᵖ.
Proof.
  intros [w p].
  exists (has_type_ro_OpRrecip _ _ w).
  apply (ro_recip_prt _ _ w _ patf _ _ p).
  intros x h [j _]; auto.
Defined.

Lemma pp_ro_recip_tot_back {Γ} {e} {ϕ} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ  (γ, / y) /\ y <> 0 %R}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ (γ, y)}}ᵗ.
Proof.
  intros [w p].
  exists (has_type_ro_OpRrecip _ _ w).
  apply (ro_recip_tot _ _ w _ patf _ _ p).
  intros x h [j jj]; auto.
Defined.

Lemma pp_ro_lim_prt_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(γ, z) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_Lim _ _ x).
  apply (ro_lim_prt_util f).
  
  apply (ro_imply_tot _ _ REAL _ _ _ patf  _
                      patf  p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma pp_ro_lim_tot_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(γ, z) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_Lim _ _ x).
  apply (ro_lim_tot_util f).
  
  apply (ro_imply_tot _ _ REAL _ _ _ patf  _
                      patf  p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma pp_rw_ro_prt_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | ψ (fst_app x, (snd_app x, y))}}ᵖ -> 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ.
Proof.
  intros [w p].
  exists (has_type_rw_ro _ _ _ _ w).
  apply (rw_ro_prt _ _ _ _ w
                        _ patf (has_type_rw_ro Γ Δ e τ w)
             ) in p.
  apply (rw_imply_prt _ _ _ _ _ _ patf patf pattf pattf p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  destruct h1.
  reduce_tedious; auto.
  destruct h1.
  destruct p0.
  reduce_tedious h2; auto.  
Defined.

Lemma pp_rw_ro_tot_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | ψ (fst_app x, (snd_app x, y))}}ᵗ -> 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros [w p].
  exists (has_type_rw_ro _ _ _ _ w).
  apply (rw_ro_tot _ _ _ _ w
                        _ patf (has_type_rw_ro Γ Δ e τ w)
             ) in p.
  apply (rw_imply_tot _ _ _ _ _ _ patf patf pattf pattf p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  destruct h1.
  reduce_tedious; auto.
  destruct h1.
  destruct p0.
  reduce_tedious h2; auto.  
Defined.


Lemma pp_ro_tot_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ (γ, y) /\ θ γ) }}ᵗ.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_tot_pose_readonly _ _ _ _ _ _ _ p).
Defined.

Lemma pp_ro_prt_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ (γ, y) /\ θ γ) }}ᵖ.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_prt_pose_readonly _ _ _ _ _ _ _ p).
Defined.

Lemma pp_rw_while_tot_back {Γ Δ} {e c} ϕ θ ψ {ϕ' : pred} {ψ' : pred}:
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{θ ((γ ; δ), true)}} c {{y : UNIT | ϕ (γ, δ)}}ᵗ ->  
    [γ' : (Δ +++ Γ) ;;; δ : Δ] ||- {{θ ((snd_app γ'; δ), true) /\ δ = fst_app γ'}} c {{y : UNIT | ψ (γ', δ)  }}ᵗ -> 
    (forall γ δ,
        ϕ (γ, δ) -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ ((f n ; γ), f (S n))))) -> 
    (ϕ'  ->> ϕ ) ->
    (fun '(x, (y, z)) => ϕ (x, y) /\ θ ((x ; y), false)) ->> ψ' ->    
    [γ : Γ ;;; δ : Δ] ||- {{ϕ' (γ, δ)}} While e c {{y : UNIT | ψ' (γ, (δ, y)) }}ᵗ.
  Proof.
    intros p1 p2 p3 h h1 h2.
    apply (fun a => pp_rw_imply_tot a h1 h2).
    apply (pp_rw_while_tot
             (ψ := ψ))
           ; auto.
  Defined.
  

Lemma pp_ro_tot_prt {Γ} {e} {τ} {ϕ} {ψ} :  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ -> [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ.
Proof.
  intros [w h].
  exists w.
  apply admissible_ro_tot_prt.
  exact h.
Defined.

Lemma pp_rw_tot_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ ->[γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ.
Proof.
Proof.
  intros [w h].
  exists w.
  apply admissible_rw_tot_prt.
  exact h.
Defined.


Lemma pp_rw_assign_tot_util {Γ Δ} {k} {e} τ {ϕ} {θ} {ψ : pred} :
  forall (a : assignable Δ τ k),
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ (x, y)}}ᵗ ->
    (forall x γ δ, ϕ (γ, δ) -> θ ((γ; δ), x) -> ψ (γ, (update k x δ a, tt))) ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (LET k := e) {{y : UNIT | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (pp_rw_assign_tot a
           (θ := fun '(x, y) => θ (x, y) /\ ϕ (fst_app x, snd_app x))).
  apply (pp_ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (pp_ro_imply_tot (ψ := patf) X).
  intros h1 h2; split; auto.
  intros [h1 h2]; auto.
  intros h1 h2 h3 h4.
  destruct h4.
  reduce_tedious H1.
  auto.
 Defined.
  
Lemma pp_rw_new_var_tot_util2 {Γ Δ} {e c} {τ} σ {ϕ}
         θ
         {ψ : pred} :
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ (x, y)}}ᵗ ->
                  [γ : Γ ;;; (δ, x) : Δ ::: σ] ||- {{θ ((γ ; δ), x) /\ ϕ (γ, δ) }}
   c
   {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (NEWVAR e IN c) {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (pp_rw_new_var_tot
           (σ := σ)
           (θ := fun '(x, y) => θ (x, y) /\ ϕ (fst_app x, snd_app x))).
  apply (pp_ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (pp_ro_imply_tot (ψ := patf) X).
  intros h1 h2; split; auto.
  intros [h1 h2] h3; auto.
  apply (pp_rw_imply_tot (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf) X0).
  intros [h1 [h2 h3]] h4.
  reduce_tedious h4.
  auto.
  intro h;
    auto.
Defined.

Lemma pp_rw_cond_tot_util {Γ Δ} {τ} {e c1 c2} {ϕ} θ {ψ} :
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ) /\ θ ((γ ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ) /\ θ ((γ ; δ), false)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (IF e THEN c1 ELSE c2 END) {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (pp_rw_cond_tot (θ := fun '(x, y) => ϕ (fst_app x, snd_app x) /\ θ (x, y))) .
  apply (pp_ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (pp_ro_imply_tot (ψ := patf) X).
  intros h1 h2; split; auto.
  intros [h1 h2] [h3 h4]; auto.
  apply (pp_rw_imply_tot (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf) X0).
  intros [h1 h2] h3.
  reduce_tedious h3; auto.
  intro h;
    auto.
  apply (pp_rw_imply_tot (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf) X1).
  intros [h1 h2] h3.
  reduce_tedious h3; auto.
  intro h;
    auto.
Defined.

Lemma pp_ro_real_comp_lt_tot_util {Γ} {e1 e2} {ϕ} ψ1 ψ2 {ψ} :
  [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ ->
  (forall x y1 y2, (ϕ x /\ ψ1 (x, y1) /\ ψ2 (x, y2)) -> (y1 <> y2 /\ ψ (x ,Rltb'' y1 y2))) ->
  [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  apply
    (pp_ro_real_comp_lt_tot
       ψ1
       (fun '(x, y) => ϕ x /\ ψ2 (x, y))).
  exact X.
  apply (pp_ro_tot_pose_readonly ϕ) in X0.
  apply (pp_ro_imply_tot (ψ := patf) X0).
  intros h1 h2; split; auto.
  intros [h1 h2] [h3 h4]; auto.
  intros.
  apply H.
  repeat split; destruct H1 as [h1 h2]; auto.
Defined.


Lemma pp_rw_while_tot_back_util {Γ Δ} {e c} ϕ θ ψ {ϕ' : pred} {ψ' : pred}:
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ) /\ θ ((γ ; δ), true)}} c {{y : UNIT | ϕ (γ, δ)}}ᵗ ->  
    [γ' : (Δ +++ Γ) ;;; δ : Δ] ||- {{ϕ (snd_app γ', δ) /\ θ ((snd_app γ'; δ), true) /\ δ = fst_app γ'}} c {{y : UNIT | ψ (γ', δ)  }}ᵗ -> 
    (forall γ δ,
        ϕ (γ, δ) -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ ((f n ; γ), f (S n))))) -> 
    (ϕ' ->> ϕ) ->
    (fun '(x, (y, z)) => ϕ (x, y) /\ θ ((x ; y), false)) ->> ψ' ->    
    [γ : Γ ;;; δ : Δ] ||- {{ϕ' (γ, δ)}} While e c {{y : UNIT | ψ' (γ, (δ, y)) }}ᵗ.
  Proof.
    intros p1 p2 p3 h h1 h2.
    apply (pp_rw_while_tot_back ϕ (fun '(x, y) => θ (x, y) /\ ϕ (fst_app x, snd_app x)) ψ).
    
    
    apply (pp_ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in p1.
    apply (pp_ro_imply_tot (ψ := patf) p1).
    intros x1 x2; auto.
    intros [x1 x2]; auto.

    apply (pp_rw_imply_tot
             (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf)
             p2).
    intros [q1 q2] H.
    reduce_tedious H; auto.
    destruct H; auto.
    intros q; auto.

    apply (pp_rw_imply_tot
                          (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf)
                          p3).
    intros [q1 q2] H.
    reduce_tedious H; auto.
    destruct H.
    destruct H.
    auto.
    intros q; auto.
    intros; auto.
    intros; auto.
    intros [q1 [q2 q3]] q4; auto.
    apply h2; auto.
    destruct q4; auto.
    destruct H0.
    split; auto.
  Defined.
