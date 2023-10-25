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
(* Require Import Clerical.ReasoningTyPaired. *)

Require Import List.


Arguments ro_rw_prt {Γ} {c} {τ} {ϕ} {ψ} :rename.

Arguments ro_rw_tot {Γ} {c} {τ} {ϕ} {ψ} :rename.

Arguments rw_assign_tot {Γ Δ} {e} {k} {τ} {ϕ} {θ} {ψ} (a).

Arguments rw_new_var_tot {Γ Δ} {e} {c} {τ σ} {ϕ} {ψ} {θ}.

Arguments rw_cond_prt {Γ Δ} {e} {c1 c2} {τ} {ϕ} {θ} {ψ}.

Arguments rw_cond_tot {Γ Δ} {e} {c1 c2} {τ} {ϕ} {θ} {ψ}.

(* (has_type_ro_Lim_inverse Γ e w) *)
(* when we know where the limit converges to *)
Lemma ro_lim_prt_util {Γ} {e} {ϕ} {ψ} (f : sem_ctx Γ -> R) :
  [(z, x) : Γ ::: INTEGER ] |- 
        {{ϕ z}}
          e
          {{y : REAL| Rabs (y - f z) < pow2 (- x)}}ᵗ ->
        ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
        [x : Γ] |- {{ϕ x}} Lim e {{y : REAL | ψ (x, y)}}ᵖ.
Proof.
  intros.
  pose proof
       (ro_lim_prt _ _
                   ϕ (fun '((z, x), y)  =>  (Rabs (y - f z) < pow2 (- x)))
                   
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
  apply (ro_imply_prt  _ _ _ _ patf _ patf H0).
  intro h; auto.
  intros [h1 h2] h3.
  apply H.
  auto.
Defined.

Lemma ro_lim_tot_util {Γ} {e} {ϕ} {ψ} (f : sem_ctx Γ -> R) :
  [(z, x) : Γ ::: INTEGER ] |- 
        {{ϕ z}}
          e
          {{y : REAL| Rabs (y - f z) < pow2 (- x)}}ᵗ ->
        ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
        [x : Γ] |- {{ϕ x}} Lim e {{y : REAL | ψ (x, y)}}ᵗ.
Proof.
  intros.
  pose proof
       (ro_lim_tot _ _
                   ϕ (fun '((z, x), y)  =>  (Rabs (y - f z) < pow2 (- x)))
                   
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
  apply (ro_imply_tot _ _ _ _ patf _ patf H0).
  intro h; auto.
  intros [h1 h2] h3.
  apply H.
  auto.
Defined.

Definition ro_imply_prt' {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ ->
               ϕ' ->> ϕ -> ψ ->> ψ' ->
               [γ : Γ] |- {{ϕ' γ}} e {{y : τ | ψ' (γ, y)}}ᵖ.
Proof.
  intros.
  apply (ro_imply_prt _ _ _ _ _ _ _ X); auto.
Defined.
Definition ro_imply_tot' {Γ} {e} {τ} {ϕ ϕ'} {ψ ψ'} :
    [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ ->
               ϕ' ->> ϕ -> ψ ->> ψ' ->
               [γ : Γ] |- {{ϕ' γ}} e {{y : τ | ψ' (γ, y)}}ᵗ.
Proof.
  intros.
  apply (ro_imply_tot _ _ _ _ _ _ _ X); auto.
Defined.
    
Lemma rw_imply_prt' {Γ Δ} {e} {τ} {ϕ ϕ' :pred} {ψ ψ' : pred} :
  [ γ : Γ ;;; δ : Δ ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y)) }}ᵖ ->
  (ϕ' ->> ϕ) -> (ψ ->> ψ') ->
  [ γ : Γ ;;; δ : Δ ]  ||- {{ϕ' (γ, δ)}} e {{y : τ | ψ' (γ, (δ, y))}}ᵖ.
Proof.
  intros.
  apply (rw_imply_prt _ _ _ _ _ _ _ _ X); auto.
Defined.

Lemma rw_imply_tot' {Γ Δ} {e} {τ} {ϕ ϕ' : pred} {ψ ψ' : pred} :
  [ γ : Γ ;;; δ : Δ ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y)) }}ᵗ ->
  (ϕ' ->> ϕ) -> (ψ ->> ψ') ->
  [ γ : Γ ;;; δ : Δ ]  ||- {{ϕ' (γ, δ)}} e {{y : τ | ψ' (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (rw_imply_tot _ _ _ _ _ _ _ _ X); auto.
Defined.

                          
Lemma ro_rw_prt_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ ;;; _ : nil] ||- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (ro_rw_prt
                (Γ := Γ) (c := e) (τ := τ) (ϕ := fun '(x, _) => ϕ x) (ψ := fun '(x, (_, y)) => ψ (x, y))).
  simpl in X0.
  apply X0; auto.
Defined.


Lemma ro_rw_tot_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ ;;; _ : nil] ||- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (ro_rw_tot
                (Γ := Γ) (c := e) (τ := τ) (ϕ := fun '(x, _) => ϕ x) (ψ := fun '(x, (_, y)) => ψ (x, y))).
  simpl in X0.
  apply X0; auto.
Defined.

Lemma ro_var_prt_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ (x, var_access Γ k τ w x)) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (ro_var_prt Γ k τ w ψ).
  apply (ro_imply_prt' X).
  apply H.
  intro h; auto.
Defined.

Lemma ro_var_tot_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ (x, var_access Γ k τ w x)) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (ro_var_tot Γ k τ w ψ).
  apply (ro_imply_tot' X).
  apply H.
  intro h; auto.
Defined.

Lemma ro_skip_prt_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, tt)) -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (ro_skip_prt _ ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_skip_tot_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, tt)) -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (ro_skip_tot _ ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_true_prt_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, true)) -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (ro_true_prt _ ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_true_tot_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, true)) -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (ro_true_tot _  ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_false_prt_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, false)) -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (ro_false_prt _ ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_false_tot_back {Γ} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, false)) -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (ro_false_tot _ ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_int_prt_back {Γ} {k} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, k)) -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  pose proof (ro_int_prt _ k ψ).
  apply (ro_imply_prt _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_int_tot_back {Γ} {k} {ϕ : pred} {ψ : pred} :
  (forall γ, ϕ γ -> ψ (γ, k)) -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  pose proof (ro_int_tot _ k ψ).
  apply (ro_imply_tot _ _ _ _ _ _ _ X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.


Lemma ro_recip_prt_back {Γ} {e} {ϕ : pred} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ (γ, / y)}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ (γ, y)}}ᵖ.
Proof.
  intros p.
  apply (ro_recip_prt _ _ _ patf _ p).
  intros x h [j _]; auto.
Defined.

Lemma ro_recip_tot_back {Γ} {e} {ϕ} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ  (γ, / y) /\ y <> 0 %R}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ (γ, y)}}ᵗ.
Proof.
  intros p.
  apply (ro_recip_tot _ _ _ patf _ p).
  intros x h [j jj]; auto.
Defined.

Lemma ro_lim_prt_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(γ, z) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ (γ, y)}}ᵖ.
Proof.
  intros.
  apply (ro_lim_prt_util f). 
  apply (ro_imply_tot (Γ ::: INTEGER) _ REAL _ patf _ patf X);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma ro_lim_tot_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(γ, z) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun '(x, y) => ϕ x /\ y = f x) ->> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  apply (ro_lim_tot_util f). 
  apply (ro_imply_tot (Γ ::: INTEGER) _ REAL _ patf _ patf X);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma rw_ro_prt_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | ψ (fst_app x, (snd_app x, y))}}ᵖ -> 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ.
Proof.
  intros p.
  apply (rw_ro_prt _ _ _ _ 
                        _ patf
             ) in p.
  apply (rw_imply_prt _ _ _ _  patf patf pattf pattf p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  destruct h1.
  reduce_tedious; auto.
  destruct h1.
  destruct p0.
  reduce_tedious h2; auto.  
Defined.

Lemma rw_ro_tot_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | ψ (fst_app x, (snd_app x, y))}}ᵗ -> 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros p.
  apply (rw_ro_tot _ _ _ _ 
                        _ patf) in p.
  apply (rw_imply_tot _ _ _ _  patf patf pattf pattf p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  destruct h1.
  reduce_tedious; auto.
  destruct h1.
  destruct p0.
  reduce_tedious h2; auto.  
Defined.


Lemma ro_tot_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ (γ, y) /\ θ γ) }}ᵗ.
Proof.
  intros p.
  apply (admissible_ro_tot_pose_readonly _ _ _ _ _ _ p).
Defined.

Lemma ro_prt_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ (γ, y) /\ θ γ) }}ᵖ.
Proof.
  intros p.
  apply (admissible_ro_prt_pose_readonly _ _ _ _ _ _ p).
Defined.

Lemma rw_while_tot_back {Γ Δ} {e c} ϕ θ ψ {ϕ' : pred} {ψ' : pred}:
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
    apply (fun a => rw_imply_tot' a h1 h2).
    apply (@rw_while_tot _ _ _ _ _ _ ψ 
 )
           ; auto.
  Defined.
  

Lemma ro_tot_prt {Γ} {e} {τ} {ϕ} {ψ} :  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ -> [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ.
Proof.
  intros h.
  apply admissible_ro_tot_prt.
  exact h.
Defined.

Lemma rw_tot_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ ->[γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ.
Proof.
Proof.
  intros h.
  apply admissible_rw_tot_prt.
  exact h.
Defined.

  
Lemma rw_assign_tot_util {Γ Δ} {k} {e} τ {ϕ} {θ} {ψ : pred} :
  forall (a : assignable Δ τ k),
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ (x, y)}}ᵗ ->
    (forall x γ δ, ϕ (γ, δ) -> θ ((γ; δ), x) -> ψ (γ, (update k x δ a, tt))) ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (LET k := e) {{y : UNIT | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (rw_assign_tot a
           (θ := fun '(x, y) => θ (x, y) /\ ϕ (fst_app x, snd_app x))).
  apply (ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (ro_imply_tot' (ψ' := patf) (ψ := patf) X).
  intros h1 h2; split; auto.
  intros [h1 h2]; auto.
  intros h1 h2 h3 h4.
  destruct h4.
  reduce_tedious H1.
  auto.
 Defined.
  
Lemma rw_new_var_tot_util2 {Γ Δ} {e c} {τ} σ {ϕ}
         θ
         {ψ : pred} :
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ (x, y)}}ᵗ ->
                  [γ : Γ ;;; (δ, x) : Δ ::: σ] ||- {{θ ((γ ; δ), x) /\ ϕ (γ, δ) }}
   c
   {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (NEWVAR e IN c) {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (rw_new_var_tot
           (σ := σ)
           (θ := fun '(x, y) => θ (x, y) /\ ϕ (fst_app x, snd_app x))).
  apply (ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X).
  intros h1 h2; split; auto.
  intros [h1 h2] h3; auto.
  apply (rw_imply_tot' (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf) X0).
  intros [h1 [h2 h3]] h4.
  reduce_tedious h4.
  auto.
  intro h;
    auto.
Defined.

Lemma rw_cond_tot_util {Γ Δ} {τ} {e c1 c2} {ϕ} θ {ψ} :
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ (x, y)}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ) /\ θ ((γ ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ) /\ θ ((γ ; δ), false)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} (IF e THEN c1 ELSE c2 END) {{y : τ | ψ (γ, (δ, y))}}ᵗ.
Proof.
  intros.
  apply (rw_cond_tot (θ := fun '(x, y) => ϕ (fst_app x, snd_app x) /\ θ (x, y))) .
  apply (ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in X.
  apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X).
  intros h1 h2; split; auto.
  intros [h1 h2] [h3 h4]; auto.
  apply (rw_imply_tot' (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf) X0).
  intros [h1 h2] h3.
  reduce_tedious h3; auto.
  intro h;
    auto.
  apply (rw_imply_tot' (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf) X1).
  intros [h1 h2] h3.
  reduce_tedious h3; auto.
  intro h;
    auto.
Defined.

Lemma ro_real_comp_lt_tot_util {Γ} {e1 e2} {ϕ} ψ1 ψ2 {ψ} :
  [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 (γ, y)}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 (γ, y)}}ᵗ ->
  (forall x y1 y2, (ϕ x /\ ψ1 (x, y1) /\ ψ2 (x, y2)) -> (y1 <> y2 /\ ψ (x ,Rltb'' y1 y2))) ->
  [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ (γ, y)}}ᵗ.
Proof.
  intros.
  apply
    (@ro_real_comp_lt_tot _ _ _ _
       ψ1
       (fun '(x, y) => ϕ x /\ ψ2 (x, y))).
  exact X.
  apply (ro_tot_pose_readonly ϕ) in X0.
  apply (ro_imply_tot' (ψ := patf) (ψ' := patf) X0).
  intros h1 h2; split; auto.
  intros [h1 h2] [h3 h4]; auto.
  intros.
  apply H.
  repeat split; destruct H1 as [h1 h2]; auto.
Defined.


Lemma rw_while_tot_back_util {Γ Δ} {e c} ϕ θ ψ {ϕ' : pred} {ψ' : pred}:
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
    apply (rw_while_tot_back ϕ (fun '(x, y) => θ (x, y) /\ ϕ (fst_app x, snd_app x)) ψ).
    
    
    apply (ro_tot_pose_readonly (fun x => ϕ (fst_app x, snd_app x))) in p1.
    apply (ro_imply_tot' (ψ := patf) (ψ' := patf) p1).
    intros x1 x2; auto.
    intros [x1 x2]; auto.

    apply (rw_imply_tot'
             (ϕ := patf) (ϕ' := patf) (ψ := pattf) (ψ' := pattf)
             p2).
    intros [q1 q2] H.
    reduce_tedious H; auto.
    destruct H; auto.
    intros q; auto.

    apply (rw_imply_tot'
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


Lemma rw_case2_prt {Γ Δ} {e1 e2 c1 c2} {τ}
      {ϕ} {θ1} {θ2} {ψ} :
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e1 {{y : BOOL | θ1 (x, y)}}ᵖ -> 
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e2 {{y : BOOL | θ2 (x, y)}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ1 ((γ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ2 ((γ; δ), true)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵖ ->
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} CASE e1 ==> c1 | e2 ==> c2 END {{y : τ | ψ (γ, (δ, y))}}ᵖ.
  Proof.
    intros.
    assert (1 <= length ((e1, c1) :: (e2, c2) :: nil))%nat.
    simpl; auto.
    apply (@rw_case_list_prt _ _ _ _
             (ForallT_cons _ (e1, c1) ((e2, c2) :: nil) θ1
                           (ForallT_cons _ (e2, c2) nil θ2
                                         (ForallT_nil _))) _ _ H).
    apply ForallT1_cons.
    apply ForallT1_cons.
    apply ForallT1_nil.
    split; auto.
    split; auto.
  Defined.

  Lemma rw_case2_tot {Γ Δ} {e1 e2 c1 c2} {τ}
    {ϕ} {θ1} {θ2} {ψ} {ϕ1 ϕ2}:
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e1 {{y : BOOL | θ1 (x, y)}}ᵖ -> 
    [x : Γ +++ Δ] |- {{ϕ (fst_app x, snd_app x)}} e2 {{y : BOOL | θ2 (x, y)}}ᵖ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ1 ((γ; δ), true)}} c1 {{y : τ | ψ (γ, (δ, y))}}ᵗ -> 
    [γ : Γ ;;; δ : Δ] ||- {{θ2 ((γ; δ), true)}} c2 {{y : τ | ψ (γ, (δ, y))}}ᵗ ->
    [x : Γ +++ Δ] |- {{ϕ1 x}} e1 {{y : BOOL | y = true}}ᵗ -> 
    [x : Γ +++ Δ] |- {{ϕ2 x}} e2 {{y : BOOL | y = true}}ᵗ -> 
    (forall x, (ϕ (fst_app x, snd_app x) -> (ϕ1 x \/ ϕ2 x))) -> 
    (*——————————-——————————-——————————-——————————-——————————-*)
    [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} CASE e1 ==> c1 | e2 ==> c2 END {{y : τ | ψ (γ, (δ, y))}}ᵗ.
  Proof.
    intros.
    assert (1 <= length ((e1, c1) :: (e2, c2) :: nil))%nat.
    simpl; auto.
    apply (@rw_case_list_tot _ _ _ _ 
             (ForallT_cons _ (e1, c1) ((e2, c2) :: nil) θ1
                           (ForallT_cons _ (e2, c2) nil θ2
                                         (ForallT_nil _)))
             (ForallT_cons _ (e1, c1) ((e2, c2) :: nil) ϕ1
                           (ForallT_cons _ (e2, c2) nil ϕ2
                                         (ForallT_nil _))) _ _ H0).
    apply ForallT2_cons.
    apply ForallT2_cons.
    apply ForallT2_nil.
    repeat split; auto.
    repeat split; auto.
    simpl.
    intros.
    destruct (H x H1); auto.
  Defined.



Ltac prove_lt p q:=
  lazymatch goal with
  | |- proves_ro_prt ?Γ (?e1 ;<; ?e2) ?τ (@mk_ro_prt _ _ _ ?ϕ ?ψ) =>
      apply (ro_real_comp_lt_prt Γ e1 e2 ϕ p q ψ)
  | |- proves_ro_tot ?Γ (?e1 ;<; ?e2) ?τ (@mk_ro_tot _ _ _ ?ϕ ?ψ) =>
      apply (ro_real_comp_lt_tot Γ e1 e2 ϕ p q ψ)
  end. 


Ltac prove_lt_add_pre p q:=
  lazymatch goal with
  | |- proves_ro_tot ?Γ (?e1 ;<; ?e2) ?τ (@mk_ro_tot _ _ _ ?ϕ ?ψ) =>
      apply (@ro_real_comp_lt_tot_util Γ e1 e2 ϕ p q ψ)
  end. 


Ltac prove_sequence p :=
  lazymatch goal with
  | |- proves_rw_prt ?Γ ?Δ (?e1 ;; ?e2) ?τ (@mk_rw_prt _ _ _ _ ?ϕ ?ψ) =>
      apply (rw_sequence_prt Γ Δ e1 e2 τ ϕ p ψ)
  | |- proves_rw_tot ?Γ ?Δ (?e1 ;; ?e2) ?τ (@mk_rw_tot _ _ _ _ ?ϕ ?ψ) =>
      apply (rw_sequence_tot Γ Δ e1 e2 τ ϕ p ψ)
  end.

  
