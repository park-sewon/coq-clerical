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
Require Import Clerical.ReasoningPrettyprinting.

Require Import List.

Lemma rw_new_var_prt_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ}
      {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}:
  w1 |- {{ϕ'}} e {{θ}} ->
        w2 ||- {{θ'}} c {{ψ'}} ->
        ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
        ((fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') ->
        (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) ->
        w ||- {{ϕ}} Newvar e c {{ψ}}.
Proof.
  intros.
  pose proof (ro_imply_prt _ _ _ w1 w1 _ _ _ _
                           H X (fun x h p => p)
             ).
  pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                           H0 X0 H1
             ).
  pose proof (rw_new_var_prt).
  apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ X1 X2).
Defined.

Lemma rw_new_var_tot_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ}
      {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}:
  w1 |- [{ϕ'}] e [{θ}] ->
        w2 ||- [{θ'}] c [{ψ'}] ->
        ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
        ((fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') ->
        (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) ->
        w ||- [{ϕ}] Newvar e c [{ψ}].
Proof.
  intros.
  pose proof (ro_imply_tot _ _ _ w1 w1 _ _ _ _
                           H X (fun x h p => p)
             ).
  pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                           H0 X0 H1
             ).
  pose proof (rw_new_var_tot).
  apply (rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ _ X1 X2).
Defined.

Lemma rw_assign_prt_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
      {ϕ} {ϕ'} {ψ : post} {θ} :
  w |- {{ϕ'}} e {{θ}} ->
       ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
       (forall (x : sem_datatype τ) (γ : sem_ctx Γ) (δ : sem_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
       w' ||- {{ϕ}} Assign k e {{ψ}}.
Proof.
  intros.
  pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                           H X (fun x h p => p)
             ).
  apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ X0 H0).
Defined.

Lemma rw_assign_tot_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT}
      {ϕ} {ϕ'} {ψ : post} {θ} :
  w |- [{ϕ'}] e [{θ}] ->
       ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
       (forall (x : sem_datatype τ) (γ : sem_ctx Γ) (δ : sem_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) ->
       w' ||- [{ϕ}] Assign k e [{ψ}].
Proof.
  intros.
  pose proof (ro_imply_tot _ _ _ w w _ _ _ _
                           H X (fun x h p => p)
             ).
  apply (rw_assign_tot _ _ _ _ _ _ _ _ _ _ X0 H0).
Defined.

Lemma rw_cond_prt_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
      {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
  w |- {{ϕ'}} e {{θ}} ->
       w1 ||- {{θ1'}} c1 {{ψ1'}} ->
       w2 ||- {{θ2'}} c2 {{ψ2'}} ->
       ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
       (ro_to_rw_pre (θ true) ->> θ1') -> 
       (ψ1' ->>> ψ) ->
       (ro_to_rw_pre (θ false) ->> θ2') -> 
       (ψ2' ->>> ψ) ->
       w' ||- {{ϕ}} Cond e c1 c2 {{ψ}}.
Proof.
  intros.
  pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                           H X (fun x h p => p)
             ).
  pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                           H0 X0 H1
             ).
  pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _
                           H2 X1 H3
             ).

  apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
Defined.

Lemma rw_cond_tot_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ}
      {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} :
  w |- [{ϕ'}] e [{θ}] ->
       w1 ||- [{θ1'}] c1 [{ψ1'}] ->
       w2 ||- [{θ2'}] c2 [{ψ2'}] ->
       ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') ->
       (ro_to_rw_pre (θ true) ->> θ1') -> 
       (ψ1' ->>> ψ) ->
       (ro_to_rw_pre (θ false) ->> θ2') -> 
       (ψ2' ->>> ψ) ->
       w' ||- [{ϕ}] Cond e c1 c2 [{ψ}].
Proof.
  intros.
  pose proof (ro_imply_tot _ _ _ w w _ _ _ _
                           H X (fun x h p => p)
             ).
  pose proof (rw_imply_tot _ _ _ _ w1 w1 _ _ _ _
                           H0 X0 H1
             ).
  pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _
                           H2 X1 H3
             ).

  apply (rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4).
Defined.

Lemma rw_while_prt_util {Γ Δ} {e c}  {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c : UNIT} 
      {w' : Γ ;;; Δ ||- While e c : UNIT} {ϕ} {ϕ'} {θ} {θ'} {ψ'}  {ψ : post} :
  w |- {{ϕ'}} e {{θ}} ->
       w1 ||- {{θ'}} c {{ψ'}} ->
       ((rw_to_ro_pre ϕ) ->> ϕ') ->
       (ro_to_rw_pre (θ true) ->> θ') -> 
       (ψ' ->>> (fun _ => ϕ)) -> 
       ((fun _ => ϕ /\\ ro_to_rw_pre (θ false)) ->>> ψ) ->
       w' ||- {{ϕ}} While e c {{ψ}}.
Proof.
  intros.
  pose proof (ro_imply_prt _ _ _ w w _ _ _ _
                           H X (fun x h p => p)
             ).
  pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _
                           H0 X0 H1
             ).
  pose proof (rw_while_prt _ _ _ _ _ _ w' _ _ X1 X2).
  exact (rw_imply_prt _ _ _ _ w' w' _ _ _ _
                      (fun _ p => p) X3 H2
        ).
Defined.

(* when we know where the limit converges to *)
Lemma ro_lim_prt_util {Γ} {e}
  {w : Γ |- Lim e : REAL}
  {ϕ} {ψ} (f : sem_ctx Γ -> R) :
  (has_type_ro_Lim_inverse Γ e w) |-
        [{fun x => ϕ (snd x)}]
          e
          [{y | fun x => Rabs (y - f(snd x)) < pow2 (- fst x)}] ->
        ((fun y (x : sem_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
        w |- {{ϕ}} Lim e {{ψ}}.
Proof.
  intros.
  pose proof
    (ro_lim_prt _ _ _ _ _ w
       (fun y (x : sem_ctx Γ) => ϕ x /\ y = f x)
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
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a H0 H);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_lim_tot_util {Γ} {e}
      {w : Γ |- Lim e : REAL}
      {ϕ} {ψ} (f : sem_ctx Γ -> R) :
  (has_type_ro_Lim_inverse Γ e w) |-
        [{fun x => ϕ (snd x)}]
          e
          [{y | fun x => Rabs (y - f(snd x)) < pow2 (- fst x)}] ->
        ((fun y (x : sem_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
        w |- [{ϕ}] Lim e [{ψ}].
Proof.
  intros.
  pose proof
       (ro_lim_tot _ _ _ _ _ w (fun y (x : sem_ctx Γ) => ϕ x /\ y = f x) X).
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
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a H0 H);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_rw_prt_util {Γ } {e} {τ} {w : (Γ) |- e : τ} {ϕ} {ψ} :
  has_type_rw_ro Γ nil e τ w ||-
                 {{fun x => ϕ (snd x)}}
                 e
                 {{y | fun x => ψ y (snd x)}} ->
  w |- {{ϕ}} e {{ψ}}.
Proof.
  intro.
  pose proof (ro_rw_prt _ _ _ (has_type_rw_ro Γ nil e τ w) _ _ w X).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X0);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma ro_rw_tot_util {Γ} {e} {τ} {w : (Γ) |- e : τ} {ϕ} {ψ} :
  has_type_rw_ro Γ nil e τ w ||-
                 [{fun x => ϕ (snd x)}]
                 e
                 [{y | fun x => ψ y (snd x)}] ->
  w |- [{ϕ}] e [{ψ}].
Proof.
  intro.
  pose proof (ro_rw_tot _ _ _ (has_type_rw_ro Γ nil e τ w) _ _ w X).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X0);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.




Lemma pp_ro_rw_prt_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ] ; [_ : nil] ||- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵖ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_rw _ _ _ x).
  apply (ro_rw_prt_util ).  
  apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
Defined.

Lemma pp_ro_rw_tot_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ] ; [_ : nil] ||- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵗ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_rw _ _ _ x).
  apply (ro_rw_tot_util ).  
  apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
Defined.

Lemma pp_ro_var_prt_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ (ro_access Γ k τ w x) x) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ y γ}}ᵖ.
Proof.
  intros.
  exists w.
  pose proof (ro_var_prt _ _ _ w ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_var_tot_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ (ro_access Γ k τ w x) x) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ y γ}}ᵗ.
Proof.
  intros.
  exists w.
  pose proof (ro_var_tot _ _ _ w ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.


Lemma pp_ro_skip_prt_back {Γ} {ϕ} {ψ} :
  ϕ ->> ψ tt -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ y γ}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_Skip Γ).
  pose proof (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_skip_tot_back {Γ} {ϕ} {ψ} :
  ϕ ->> ψ tt -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ y γ}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_Skip Γ).
  pose proof (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_true_prt_back {Γ} {ϕ} {ψ} :
  ϕ ->> ψ true -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ y γ}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_True Γ).
  pose proof (ro_true_prt _  (has_type_ro_True Γ) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_true_tot_back {Γ} {ϕ} {ψ} :
  ϕ ->> ψ true -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ y γ}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_True Γ).
  pose proof (ro_true_tot _  (has_type_ro_True Γ) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_false_prt_back {Γ} {ϕ} {ψ} :
  ϕ ->> ψ false -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ y γ}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_False Γ).
  pose proof (ro_false_prt _  (has_type_ro_False Γ) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_false_tot_back {Γ} {ϕ} {ψ} :
  ϕ ->> ψ false -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ y γ}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_False Γ).
  pose proof (ro_false_tot _  (has_type_ro_False Γ) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_int_prt_back {Γ} {k} {ϕ} {ψ} :
  ϕ ->> ψ k -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ y γ}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_Int Γ k).
  pose proof (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_int_tot_back {Γ} {k} {ϕ} {ψ} :
  ϕ ->> ψ k -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ y γ}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_Int Γ k).
  pose proof (ro_int_tot _ _ (has_type_ro_Int Γ k) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.


Lemma pp_ro_recip_prt_back {Γ} {e} {ϕ} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ (/ y) γ }}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ y γ}}ᵖ.
Proof.
  intros [w p].
  exists (has_type_ro_OpRrecip _ _ w).
  apply (ro_recip_prt _ _ w _ _ _ _ p).
  intros x h [j _]; auto.
Defined.

Lemma pp_ro_recip_tot_back {Γ} {e} {ϕ} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ (/ y) γ /\ y <> 0 %R}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ y γ}}ᵗ.
Proof.
  intros [w p].
  exists (has_type_ro_OpRrecip _ _ w).
  apply (ro_recip_tot _ _ w _ _ _ _ p).
  intros x h [j jj]; auto.
  split.
  exact jj.
  exact j.
Defined.

Lemma pp_ro_lim_prt_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(z, γ) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun y (x : sem_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ y γ}}ᵖ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_Lim _ _ x).
  apply (ro_lim_prt_util f).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma pp_ro_lim_tot_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(z, γ) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun y (x : sem_ctx Γ) => ϕ x /\ y = f x) ->>> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ y γ}}ᵗ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_Lim _ _ x).
  apply (ro_lim_tot_util f).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma pp_rw_ro_prt_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | ψ y (fst_app x, snd_app x)}}ᵖ -> 
  [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ)}}ᵖ.
Proof.
  intros [w p].
  exists (has_type_rw_ro _ _ _ _ w).
  apply (rw_ro_prt _ _ _ _ w
                        _ _ (has_type_rw_ro Γ Δ e τ w)
             ) in p.
  apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  destruct h1.
  rewrite tedious_equiv_fst, tedious_equiv_snd.
  exact h2.
  destruct h2.
  rewrite tedious_equiv_fst, tedious_equiv_snd.
  auto.
Defined.

Lemma pp_rw_ro_tot_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | ψ y (fst_app x, snd_app x)}}ᵗ -> 
  [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ)}}ᵗ.
Proof.
  intros [w p].
  exists (has_type_rw_ro _ _ _ _ w).
  apply (rw_ro_tot _ _ _ _ w
                        _ _ (has_type_rw_ro Γ Δ e τ w)
             ) in p.
  apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  destruct h1.
  rewrite tedious_equiv_fst, tedious_equiv_snd.
  exact h2.
  destruct h2.
  rewrite tedious_equiv_fst, tedious_equiv_snd.
  auto.
Defined.


Lemma pp_ro_tot_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵗ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ y γ /\ θ γ) }}ᵗ.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_tot_pose_readonly _ _ _ _ _ _ _ p).
Defined.

Lemma pp_ro_prt_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵖ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ y γ /\ θ γ) }}ᵖ.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_prt_pose_readonly _ _ _ _ _ _ _ p).
Defined.

 Lemma pp_rw_while_tot_back {Γ Δ} {e c} {ϕ} {θ} {ψ} {ϕ'} {ψ'}:
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : BOOL | θ y x}}ᵗ ->
    [γ : Γ] ; [δ : Δ] ||- {{θ true (δ ; γ)}} c {{y : UNIT | ϕ (δ, γ)}}ᵗ -> 
    [γ' : Γ ++ Δ] ; [δ : Δ] ||- {{θ true (δ; fst_app γ') /\ δ = snd_app γ'}} c {{y : UNIT | ψ (δ, γ') }}ᵗ ->
    (forall δ γ,
        ϕ (δ, γ) -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ (f (S n), (γ; f n))))) ->
    ϕ' ->> ϕ ->
    (fun _ => ϕ /\\ ro_to_rw_pre (θ false)) ->>> ψ' ->    
    [γ : Γ] ; [δ : Δ] ||- {{ϕ' (δ, γ)}} While e c {{y : UNIT | ψ' y (δ, γ)}}ᵗ.
  Proof.
    intros p1 p2 p3 h h1 h2.
    apply (fun a => pp_rw_imply_tot a h1 h2).
    apply (pp_rw_while_tot
             (ψ := ψ))
           ; auto.
  Defined.
  


Lemma pp_ro_tot_prt {Γ} {e} {τ} {ϕ} {ψ} :  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵗ -> [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ y γ}}ᵖ.
Proof.
  intros [w h].
  exists w.
  apply admissible_ro_tot_prt.
  exact h.
Defined.

Lemma pp_rw_tot_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ)}}ᵗ ->[γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ)}}ᵖ.
Proof.
Proof.
  intros [w h].
  exists w.
  apply admissible_rw_tot_prt.
  exact h.
Defined.


Lemma pp_rw_assign_tot_util {Γ Δ} {k} {e} τ {ϕ} {θ} {ψ : post} :
  forall (a : assignable Δ τ k),
    [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : τ | θ y x}}ᵗ ->
    (forall x γ δ, ϕ (δ, γ) -> θ x (δ; γ) -> ψ tt (update k x δ a, γ)) ->
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} (LET k := e) {{y : UNIT | ψ y (δ, γ)}}ᵗ.
Proof.
  intros.
  apply (pp_rw_assign_tot a
           (θ := θ /\\\ (fun _ => rw_to_ro_pre ϕ))).
  apply (pp_ro_tot_pose_readonly (rw_to_ro_pre ϕ)) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  unfold rw_to_ro_pre.
  rewrite tedious_equiv_4.
  auto.
  intros h1 h2 [h3 h4]; split; auto.
  intros.
  apply H; destruct H0; auto.
  unfold rw_to_ro_pre in H1.
  rewrite tedious_equiv_0 in H1.
  exact H1.
Defined.



  Lemma pp_rw_imply_tot {Γ Δ} {e} {τ} {ϕ ϕ'} {ψ ψ' : sem_datatype τ -> sem_ctx Δ * sem_ctx Γ -> Prop} :
    [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} e {{y : τ | ψ y (δ, γ)}}ᵗ -> ϕ' ->> ϕ -> ψ ->>> ψ' ->
              [γ' : Γ] ; [δ' : Δ] ||- {{ϕ' (δ', γ')}} e {{y : τ | ψ' y (δ', γ')}}ᵗ.
  Proof.
    intros.
    destruct X.
    exists x.
    apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; apply H; auto.
    intro.
    destruct h2; apply H0; auto.
  Defined.
  
Lemma pp_rw_new_var_tot_util2 {Γ Δ} {e c} {τ} σ {ϕ}
         (θ : sem_datatype σ -> sem_ctx (Δ ++ Γ) -> Prop)
         {ψ : post} :
  [x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} e {{y : σ | θ y x}}ᵗ ->
                  [γ : Γ] ; [(x, δ ) : σ :: Δ] ||- {{θ x (δ; γ) /\ ϕ (δ,γ) }}
   c
   {{y : τ | ψ y (δ, γ)}}ᵗ ->
  [γ : Γ] ; [δ : Δ] ||- {{ϕ (δ, γ)}} (NEWVAR e IN c) {{y : τ | ψ y (δ, γ)}}ᵗ.
Proof.
  intros.
  apply (pp_rw_new_var_tot
           (σ := σ)
           (θ := fun y x => θ y x /\ rw_to_ro_pre ϕ x)).
  apply (pp_ro_tot_pose_readonly (rw_to_ro_pre ϕ)) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  unfold rw_to_ro_pre.
  rewrite tedious_equiv_4.
  auto.

  intros h1 h2 [h3 h4]; split; auto.
  Set Printing All.
  pose proof (pp_rw_imply_tot
                (Γ := Γ)
                (e := c)
                (τ := τ)
                (ϕ := fun '( '(x, δ), γ) =>  (θ x (δ; γ) /\ ϕ (δ, γ)))
                (ψ := fun y '((x, δ), γ) =>  ψ y (δ, γ))
                (ϕ' := fun '((z, δ), γ) => (θ z (δ; γ) /\ rw_to_ro_pre ϕ (δ; γ)))
                (ψ' := fun y '((z, δ), γ) =>  ψ y (δ, γ))).
                
                (Δ := σ :: Δ)
                              (ϕ' := (fun ( => θ (

           X0).
  intros h1 [h2 h3]; split; auto.
  unfold rw_to_ro_pre in h3.
  rewrite tedious_equiv_0 in h3.
  auto.
  intros h1 h2 h3; auto.
Defined.

Lemma pp_rw_cond_tot_util {Γ Δ} {τ} {e c1 c2} {ϕ} θ {ψ}
     : (Δ ++ Γ) |-- {{rw_to_ro_pre ϕ}}ᵗ e {{y : BOOL | θ y}}ᵗ ->
       Γ;;; Δ ||-- {{ϕ /\\ ro_to_rw_pre (θ true)}}ᵗ c1 {{y : τ | ψ y γ}}ᵗ ->
       Γ;;; Δ ||-- {{ϕ /\\ ro_to_rw_pre (θ false)}}ᵗ c2 {{y : τ | ψ y γ}}ᵗ ->
       Γ;;; Δ ||-- {{ϕ}}ᵗ (IF e THEN c1 ELSE c2 END) {{y : τ | ψ y γ}}ᵗ.
Proof.
  intros.
  apply (pp_rw_cond_tot (θ := fun y x => rw_to_ro_pre ϕ x /\ θ y x)) .
  apply (pp_ro_tot_pose_readonly (rw_to_ro_pre ϕ)) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; auto.
  apply (pp_rw_imply_tot X0).
  intros h1 [h2 h3]; split; auto.
  unfold rw_to_ro_pre in h2.
  rewrite tedious_equiv_0 in h2.
  exact h2.
  intros h1 h2 h3; auto.
  apply (pp_rw_imply_tot X1).
  intros h1 [h2 h3]; split; auto.
  unfold rw_to_ro_pre in h2.
  rewrite tedious_equiv_0 in h2.
  exact h2.
  intros h1 h2 h3; auto.
Defined.

Lemma pp_ro_real_comp_lt_tot_util {Γ} {e1 e2} {ϕ} ψ1 ψ2 {ψ} :
  [γ : Γ] |- {{ϕ}}ᵗ e1 {{y : REAL | ψ1 y}}ᵗ ->
  [γ : Γ] |- {{ϕ}}ᵗ e2 {{y : REAL | ψ2 y}}ᵗ ->
  (forall y1 y2 x, (ϕ x /\ ψ1 y1 x /\ ψ2 y2 x) -> (y1 <> y2 /\ ψ (Rltb'' y1 y2) x)) ->
  [γ : Γ] |- {{ϕ}}ᵗ e1 ;<; e2 {{y : BOOL | ψ y γ}}ᵗ.
Proof.
  intros.
  apply
    (pp_ro_real_comp_lt_tot
       ψ1
       (fun y x => ϕ x /\ ψ2 y x)).
  exact X.
  apply (pp_ro_tot_pose_readonly ϕ) in X0.
  apply (pp_ro_imply_tot X0).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; auto.
  intros.
  apply H.
  repeat split; destruct H1 as [h1 h2]; auto.
Defined.

