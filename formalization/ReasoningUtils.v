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

(* Lemma rw_new_var_prt_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ} *)
(*       {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}: *)
(*   w1 |- {{ϕ'}} e {{θ}} -> *)
(*         w2 ||- {{θ'}} c {{ψ'}} -> *)
(*         ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') -> *)
(*         ((fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') -> *)
(*         (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) -> *)
(*         w ||- {{ϕ}} Newvar e c {{ψ}}. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_prt _ _ _ w1 w1 _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _ *)
(*                            H0 X0 H1 *)
(*              ). *)
(*   pose proof (rw_new_var_prt). *)
(*   apply (rw_new_var_prt _ _ _ _ _ _ _ _ _ _ _ _ X1 X2). *)
(* Defined. *)

(* Lemma rw_new_var_tot_util {Γ Δ} {e c} {τ σ} {w1 : (Δ ++ Γ) |- e : σ} {w2 : Γ;;; (σ :: Δ) ||- c : τ} {w : Γ ;;; Δ ||- Newvar e c : τ} *)
(*       {ϕ} {ϕ'} {ψ} {θ} {θ'} {ψ'}: *)
(*   w1 |- [{ϕ'}] e [{θ}] -> *)
(*         w2 ||- [{θ'}] c [{ψ'}] -> *)
(*         ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') -> *)
(*         ((fun xδγ : sem_ctx (σ :: Δ) * sem_ctx Γ => θ (fst (fst xδγ)) (snd (fst xδγ); snd xδγ)) ->> θ') -> *)
(*         (ψ' ->>> (fun x xδγ => ψ x (snd (fst xδγ), snd xδγ))) -> *)
(*         w ||- [{ϕ}] Newvar e c [{ψ}]. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_tot _ _ _ w1 w1 _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _ *)
(*                            H0 X0 H1 *)
(*              ). *)
(*   pose proof (rw_new_var_tot). *)
(*   apply (rw_new_var_tot _ _ _ _ _ _ _ _ _ _ _ _ X1 X2). *)
(* Defined. *)

(* Lemma rw_assign_prt_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT} *)
(*       {ϕ} {ϕ'} {ψ : post} {θ} : *)
(*   w |- {{ϕ'}} e {{θ}} -> *)
(*        ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') -> *)
(*        (forall (x : sem_datatype τ) (γ : sem_ctx Γ) (δ : sem_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) -> *)
(*        w' ||- {{ϕ}} Assign k e {{ψ}}. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_prt _ _ _ w w _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   apply (rw_assign_prt _ _ _ _ _ _ _ _ _ _ X0 H0). *)
(* Defined. *)

(* Lemma rw_assign_tot_util {Γ Δ} {k} {e} {τ} {w : (Δ ++ Γ) |- e : τ}  {w' : Γ ;;; Δ ||- Assign k e : UNIT} *)
(*       {ϕ} {ϕ'} {ψ : post} {θ} : *)
(*   w |- [{ϕ'}] e [{θ}] -> *)
(*        ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') -> *)
(*        (forall (x : sem_datatype τ) (γ : sem_ctx Γ) (δ : sem_ctx Δ), θ x (δ; γ) -> ψ tt (update' w w' δ x, γ)) -> *)
(*        w' ||- [{ϕ}] Assign k e [{ψ}]. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_tot _ _ _ w w _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   apply (rw_assign_tot _ _ _ _ _ _ _ _ _ _ X0 H0). *)
(* Defined. *)

(* Lemma rw_cond_prt_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ} *)
(*       {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} : *)
(*   w |- {{ϕ'}} e {{θ}} -> *)
(*        w1 ||- {{θ1'}} c1 {{ψ1'}} -> *)
(*        w2 ||- {{θ2'}} c2 {{ψ2'}} -> *)
(*        ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') -> *)
(*        (ro_to_rw_pre (θ true) ->> θ1') ->  *)
(*        (ψ1' ->>> ψ) -> *)
(*        (ro_to_rw_pre (θ false) ->> θ2') ->  *)
(*        (ψ2' ->>> ψ) -> *)
(*        w' ||- {{ϕ}} Cond e c1 c2 {{ψ}}. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_prt _ _ _ w w _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _ *)
(*                            H0 X0 H1 *)
(*              ). *)
(*   pose proof (rw_imply_prt _ _ _ _ w2 w2 _ _ _ _ *)
(*                            H2 X1 H3 *)
(*              ). *)

(*   apply (rw_cond_prt _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4). *)
(* Defined. *)

(* Lemma rw_cond_tot_util {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c1 : τ} {w2 : Γ ;;; Δ ||- c2 : τ} *)
(*       {w' : Γ ;;; Δ ||- Cond e c1 c2 : τ} {ϕ} {ϕ'} {θ} {θ1'} {θ2'} {ψ1'} {ψ2'} {ψ : post} : *)
(*   w |- [{ϕ'}] e [{θ}] -> *)
(*        w1 ||- [{θ1'}] c1 [{ψ1'}] -> *)
(*        w2 ||- [{θ2'}] c2 [{ψ2'}] -> *)
(*        ((fun γδ : sem_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ γδ)) ->> ϕ') -> *)
(*        (ro_to_rw_pre (θ true) ->> θ1') ->  *)
(*        (ψ1' ->>> ψ) -> *)
(*        (ro_to_rw_pre (θ false) ->> θ2') ->  *)
(*        (ψ2' ->>> ψ) -> *)
(*        w' ||- [{ϕ}] Cond e c1 c2 [{ψ}]. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_tot _ _ _ w w _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   pose proof (rw_imply_tot _ _ _ _ w1 w1 _ _ _ _ *)
(*                            H0 X0 H1 *)
(*              ). *)
(*   pose proof (rw_imply_tot _ _ _ _ w2 w2 _ _ _ _ *)
(*                            H2 X1 H3 *)
(*              ). *)

(*   apply (rw_cond_tot _ _ _ _ _ _ _ _ _ _ _ _ _ X2 X3 X4). *)
(* Defined. *)

(* Lemma rw_while_prt_util {Γ Δ} {e c}  {w : (Δ ++ Γ) |- e : BOOL} {w1 : Γ ;;; Δ ||- c : UNIT}  *)
(*       {w' : Γ ;;; Δ ||- While e c : UNIT} {ϕ} {ϕ'} {θ} {θ'} {ψ'}  {ψ : post} : *)
(*   w |- {{ϕ'}} e {{θ}} -> *)
(*        w1 ||- {{θ'}} c {{ψ'}} -> *)
(*        ((rw_to_ro_pre ϕ) ->> ϕ') -> *)
(*        (ro_to_rw_pre (θ true) ->> θ') ->  *)
(*        (ψ' ->>> (fun _ => ϕ)) ->  *)
(*        ((fun _ => ϕ /\\ ro_to_rw_pre (θ false)) ->>> ψ) -> *)
(*        w' ||- {{ϕ}} While e c {{ψ}}. *)
(* Proof. *)
(*   intros. *)
(*   pose proof (ro_imply_prt _ _ _ w w _ _ _ _ *)
(*                            H X (fun x h p => p) *)
(*              ). *)
(*   pose proof (rw_imply_prt _ _ _ _ w1 w1 _ _ _ _ *)
(*                            H0 X0 H1 *)
(*              ). *)
(*   pose proof (rw_while_prt _ _ _ _ _ _ w' _ _ X1 X2). *)
(*   exact (rw_imply_prt _ _ _ _ w' w' _ _ _ _ *)
(*                       (fun _ p => p) X3 H2 *)
(*         ). *)
(* Defined. *)

(* (* when we know where the limit converges to *) *)
Lemma ro_lim_prt_util {Γ} {e}
  {w : Γ |- Lim e : REAL}
  {ϕ} {ψ} (f : sem_ctx Γ -> R) :
   [(x, z) : INTEGER :: Γ ] |- (has_type_ro_Lim_inverse Γ e w)
        {{ϕ z}}
          e
          {{y : REAL| Rabs (y - f z) < pow2 (- x)}}ᵗ ->
        ((fun (x : sem_ctx Γ) y => ϕ x /\ y = f x) ->>> ψ) ->
        [x : Γ] |- w {{ϕ x}} Lim e {{y : REAL | ψ x y}}ᵖ.
Proof.
  intros.
  pose proof
       (ro_lim_prt _ _ _
                   ϕ (fun '((x, z) : sem_ctx (INTEGER :: Γ)) y =>  (Rabs (y - f z) < pow2 (- x)))
                   w
       (fun (x : sem_ctx Γ) y => ϕ x /\ y = f x)
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
   [(x, z) : INTEGER :: Γ ] |- (has_type_ro_Lim_inverse Γ e w)
        {{ϕ z}}
          e
          {{y : REAL| Rabs (y - f z) < pow2 (- x)}}ᵗ ->
        ((fun (x : sem_ctx Γ) y => ϕ x /\ y = f x) ->>> ψ) ->
        [x : Γ] |- w {{ϕ x}} Lim e {{y : REAL | ψ x y}}ᵗ.
Proof.
  intros.
  pose proof
       (ro_lim_tot _ _ _
                   ϕ (fun '((x, z) : sem_ctx (INTEGER :: Γ)) y =>  (Rabs (y - f z) < pow2 (- x)))
                   w
       (fun (x : sem_ctx Γ) y => ϕ x /\ y = f x)
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
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a H0 H);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.


(* Lemma ro_rw_prt_util {Γ } {e} {τ} {w : (Γ) |- e : τ} {ϕ} {ψ} : *)
(*   has_type_rw_ro Γ nil e τ w ||- *)
(*                  {{fun x => ϕ (snd x)}} *)
(*                  e *)
(*                  {{y | fun x => ψ y (snd x)}} -> *)
(*   w |- {{ϕ}} e {{ψ}}. *)
(* Proof. *)
(*   intro. *)
(*   pose proof (ro_rw_prt _ _ _ (has_type_rw_ro Γ nil e τ w) _ _ w X). *)
(*   apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X0); *)
(*     try (intros h1 h2; auto); try (intros h1 h2 h3; auto). *)
(* Defined. *)

(* Lemma ro_rw_tot_util {Γ} {e} {τ} {w : (Γ) |- e : τ} {ϕ} {ψ} : *)
(*   has_type_rw_ro Γ nil e τ w ||- *)
(*                  [{fun x => ϕ (snd x)}] *)
(*                  e *)
(*                  [{y | fun x => ψ y (snd x)}] -> *)
(*   w |- [{ϕ}] e [{ψ}]. *)
(* Proof. *)
(*   intro. *)
(*   pose proof (ro_rw_tot _ _ _ (has_type_rw_ro Γ nil e τ w) _ _ w X). *)
(*   apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X0); *)
(*     try (intros h1 h2; auto); try (intros h1 h2 h3; auto). *)
(* Defined. *)



Lemma pp_ro_rw_prt_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ ;;; _ : nil] ||- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ.
Proof.
  intros.
  pose proof (pp_ro_rw_prt
                (Γ := Γ) (c := e) (τ := τ) (ϕ := fun x _ => ϕ x) (ψ := fun x _ y => ψ x y)).
  simpl in X0.
  apply X0; auto.
Defined.


Lemma pp_ro_rw_tot_back {Γ} {e} {τ} {ϕ} {ψ} :
  [γ : Γ ;;; _ : nil] ||- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ.
Proof.
  intros.
  pose proof (pp_ro_rw_tot
                (Γ := Γ) (c := e) (τ := τ) (ϕ := fun x _ => ϕ x) (ψ := fun x _ y => ψ x y)).
  simpl in X0.
  apply X0; auto.
Defined.

Lemma pp_ro_var_prt_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ x (ro_access Γ k τ w x)) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ γ y}}ᵖ.
Proof.
  intros.
  pose proof (@pp_ro_var_prt Γ k τ ψ w).
  apply (pp_ro_imply_prt X).
  apply H.
  intro h; auto.
Defined.

Lemma pp_ro_var_tot_back {Γ} {k} {τ} {ϕ} {ψ} :
  forall w : Γ |- VAR k : τ, 
    ϕ ->> (fun x => ψ x (ro_access Γ k τ w x)) ->
    [γ : Γ] |- {{ϕ γ}} VAR k {{y : τ | ψ γ y}}ᵗ.
Proof.
  intros.
  pose proof (@pp_ro_var_tot Γ k τ ψ w).
  apply (pp_ro_imply_tot X).
  apply H.
  intro h; auto.
Defined.

Definition pre {A} := A -> Prop.
Lemma pp_ro_skip_prt_back {Γ} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ tt) -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ γ y}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_Skip Γ).
  pose proof (ro_skip_prt _  (has_type_ro_Skip Γ) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_skip_tot_back {Γ} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ tt) -> [γ : Γ] |- {{ϕ γ}} SKIP {{y : UNIT | ψ γ y}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_Skip Γ).
  pose proof (ro_skip_tot _  (has_type_ro_Skip Γ) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_true_prt_back {Γ} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ true) -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ γ y}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_True Γ).
  pose proof (ro_true_prt _  (has_type_ro_True Γ) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_true_tot_back {Γ} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ true) -> [γ : Γ] |- {{ϕ γ}} TRUE {{y : BOOL | ψ γ y}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_True Γ).
  pose proof (ro_true_tot _  (has_type_ro_True Γ) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_false_prt_back {Γ} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ false) -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ γ y}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_False Γ).
  pose proof (ro_false_prt _  (has_type_ro_False Γ) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_false_tot_back {Γ} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ false) -> [γ : Γ] |- {{ϕ γ}} FALSE {{y : BOOL | ψ γ y}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_False Γ).
  pose proof (ro_false_tot _  (has_type_ro_False Γ) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_int_prt_back {Γ} {k} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ k) -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ γ y}}ᵖ.
Proof.
  intros.
  exists (has_type_ro_Int Γ k).
  pose proof (ro_int_prt _ _ (has_type_ro_Int Γ k) ψ).
  apply (fun a => ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Lemma pp_ro_int_tot_back {Γ} {k} {ϕ : pre} {ψ : post} :
  (forall γ, ϕ γ -> ψ γ k) -> [γ : Γ] |- {{ϕ γ}} INT k {{y : INTEGER | ψ γ y}}ᵗ.
Proof.
  intros.
  exists (has_type_ro_Int Γ k).
  pose proof (ro_int_tot _ _ (has_type_ro_Int Γ k) ψ).
  apply (fun a => ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.


Lemma pp_ro_recip_prt_back {Γ} {e} {ϕ : pre} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ γ (/ y)}}ᵖ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ γ y}}ᵖ.
Proof.
  intros [w p].
  exists (has_type_ro_OpRrecip _ _ w).
  apply (ro_recip_prt _ _ w _ _ _ _ p).
  intros x h [j _]; auto.
Defined.

Lemma pp_ro_recip_tot_back {Γ} {e} {ϕ} {ψ} :
  [γ : Γ] |- {{ϕ γ}} e {{y : REAL | ψ  γ (/ y) /\ y <> 0 %R}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} ;/; e {{y : REAL | ψ γ y}}ᵗ.
Proof.
  intros [w p].
  exists (has_type_ro_OpRrecip _ _ w).
  apply (ro_recip_tot _ _ w _ _ _ _ p).
  intros x h [j jj]; auto.
Defined.

Lemma pp_ro_lim_prt_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(z, γ) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun (x : sem_ctx Γ) y => ϕ x /\ y = f x) ->>> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ γ y}}ᵖ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_Lim _ _ x).
  apply (ro_lim_prt_util f).
  
  apply (fun a => ro_imply_tot _ _ REAL _ _ _ _ _
                               (fun '((x0, z) : sem_ctx (INTEGER::Γ)) y =>  (Rabs (y - f z) < pow2 (- x0)))
                               a p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma pp_ro_lim_tot_util_known_limit {Γ} {e} {ϕ : sem_ctx Γ -> Prop} {ψ} (f : sem_ctx Γ -> R) :
  [(z, γ) : INTEGER :: Γ] |- {{ϕ γ}} e  {{y : REAL | Rabs (y - f γ) < pow2 (- z)}}ᵗ ->
  ((fun (x : sem_ctx Γ) y => ϕ x /\ y = f x) ->>> ψ) ->
  [γ : Γ] |- {{ϕ γ}} Lim e {{y : REAL | ψ γ y}}ᵗ.
Proof.
  intros.
  destruct X.
  exists (has_type_ro_Lim _ _ x).
  apply (ro_lim_tot_util f).
  
  apply (fun a => ro_imply_tot _ _ REAL _ _ _ _ _
                               (fun '((x0, z) : sem_ctx (INTEGER::Γ)) y =>  (Rabs (y - f z) < pow2 (- x0)))
                               a p);
    try (intros [h1 h1'] h2; auto); try (intros h1 [h2 h2'] h3; auto).
  exact H.
Defined.

Lemma pp_rw_ro_prt_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : τ | ψ (snd_app x) (fst_app x) y}}ᵖ -> 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵖ.
Proof.
  intros [w p].
  exists (has_type_rw_ro _ _ _ _ w).
  apply (rw_ro_prt _ _ _ _ w
                        _ _ (has_type_rw_ro Γ Δ e τ w)
             ) in p.
  apply (fun a => rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  rewrite tedious_equiv_fst, tedious_equiv_snd; auto.
  rewrite tedious_equiv_fst, tedious_equiv_snd; auto.
Defined.

Lemma pp_rw_ro_tot_back {Γ Δ} {e} {τ} {ϕ} {ψ} : 
  [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : τ | ψ (snd_app x) (fst_app x) y}}ᵗ -> 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵗ.
Proof.
  intros [w p].
  exists (has_type_rw_ro _ _ _ _ w).
  apply (rw_ro_tot _ _ _ _ w
                        _ _ (has_type_rw_ro Γ Δ e τ w)
             ) in p.
  apply (fun a => rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p);
    try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
  rewrite tedious_equiv_fst, tedious_equiv_snd; auto.
  rewrite tedious_equiv_fst, tedious_equiv_snd; auto.
Defined.

Lemma pp_ro_tot_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ γ y /\ θ γ) }}ᵗ.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_tot_pose_readonly _ _ _ _ _ _ _ p).
Defined.

Lemma pp_ro_prt_pose_readonly {Γ} {e} {τ} {ϕ} {ψ} θ : 
  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ -> [γ : Γ] |- {{(ϕ γ /\ θ γ)}} e {{y : τ | (ψ γ y /\ θ γ) }}ᵖ.
Proof.
  intros [w p].
  exists w.
  apply (admissible_ro_prt_pose_readonly _ _ _ _ _ _ _ p).
Defined.

Lemma pp_rw_while_tot_back {Γ Δ} {e c} ϕ θ ψ {ϕ' : rwpre} {ψ' : rwpost}:
    [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{θ (δ ; γ) true}} c {{y : UNIT | ϕ γ δ}}ᵗ ->  
    [γ' : (Γ ++ Δ) ;;; δ : Δ] ||- {{θ (δ; fst_app γ') true /\ δ = snd_app γ'}} c {{y : UNIT | ψ γ' δ  }}ᵗ -> 
    (forall δ γ,
        ϕ γ δ -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ (γ; f n) ( f (S n))))) -> 
    (forall x y, ϕ' x y -> ϕ x y) ->
    (forall x y z, ϕ x y /\ θ (y ; x) false -> ψ' x y z) ->    
    [γ : Γ ;;; δ : Δ] ||- {{ϕ' γ δ}} While e c {{y : UNIT | ψ' γ δ y }}ᵗ.
  Proof.
    intros p1 p2 p3 h h1 h2.
    apply (fun a => pp_rw_imply_tot a h1 h2).
    apply (pp_rw_while_tot
             (ψ := ψ))
           ; auto.
  Defined.
  


Lemma pp_ro_tot_prt {Γ} {e} {τ} {ϕ} {ψ} :  [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ -> [γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵖ.
Proof.
  intros [w h].
  exists w.
  apply admissible_ro_tot_prt.
  exact h.
Defined.

Lemma pp_rw_tot_prt {Γ Δ} {e} {τ} {ϕ} {ψ} : [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵗ ->[γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} e {{y : τ | ψ γ δ y}}ᵖ.
Proof.
Proof.
  intros [w h].
  exists w.
  apply admissible_rw_tot_prt.
  exact h.
Defined.


Lemma pp_rw_assign_tot_util {Γ Δ} {k} {e} τ {ϕ} {θ} {ψ : rwpost} :
  forall (a : assignable Δ τ k),
    [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : τ | θ x y}}ᵗ ->
    (forall x γ δ, ϕ γ δ -> θ (δ; γ) x -> ψ γ (update k x δ a) tt) ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} (LET k := e) {{y : UNIT | ψ γ δ y}}ᵗ.
Proof.
  intros.
  apply (pp_rw_assign_tot a
           (θ := fun x y => θ x y /\ ϕ(snd_app x) (fst_app x))).
  apply (pp_ro_tot_pose_readonly (fun x => ϕ(snd_app x) (fst_app x))) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  intro h; auto.
  intros h1 h2 h3 h4.
  destruct h4.
  reduce_tedious H1.
  auto.
 Defined.
  
Lemma pp_rw_new_var_tot_util2 {Γ Δ} {e c} {τ} σ {ϕ}
         θ
         {ψ : rwpost} :
  [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : σ | θ x y}}ᵗ ->
                  [γ : Γ ;;; (x, δ ) : σ :: Δ] ||- {{θ (δ; γ) x /\ ϕ γ δ }}
   c
   {{y : τ | ψ γ δ y}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} (NEWVAR e IN c) {{y : τ | ψ γ δ y}}ᵗ.
Proof.
  intros.
  apply (pp_rw_new_var_tot
           (σ := σ)
           (θ := fun x y => θ x y /\ ϕ (snd_app x) (fst_app x))).
  apply (pp_ro_tot_pose_readonly (fun x => ϕ (snd_app x) (fst_app x))) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  intros h1 h2; auto.
  apply (pp_rw_imply_tot X0).
  intros h1 [h2 h3] h4.
  reduce_tedious h4.
  auto.
  auto.
Defined.

Lemma pp_rw_cond_tot_util {Γ Δ} {τ} {e c1 c2} {ϕ} θ {ψ} :
  [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ /\ θ (δ ; γ) true}} c1 {{y : τ | ψ γ δ y}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ /\ θ (δ ; γ) false}} c2 {{y : τ | ψ γ δ y}}ᵗ ->
  [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ}} (IF e THEN c1 ELSE c2 END) {{y : τ | ψ γ δ y}}ᵗ.
Proof.
  intros.
  apply (pp_rw_cond_tot (θ := fun x y => ϕ (snd_app x) (fst_app x) /\ θ x y)) .
  apply (pp_ro_tot_pose_readonly (fun x => ϕ (snd_app x) (fst_app x))) in X.
  apply (pp_ro_imply_tot X).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; auto.
  apply (pp_rw_imply_tot X0).
  intros h1 h2 h3.
  reduce_tedious h3; auto.
  auto.
  apply (pp_rw_imply_tot X1).
  intros h1 h2 h3.
  reduce_tedious h3; auto.
  auto.
Defined.

Lemma pp_ro_real_comp_lt_tot_util {Γ} {e1 e2} {ϕ} ψ1 ψ2 {ψ} :
  [γ : Γ] |- {{ϕ γ}} e1 {{y : REAL | ψ1 γ y}}ᵗ ->
  [γ : Γ] |- {{ϕ γ}} e2 {{y : REAL | ψ2 γ y}}ᵗ ->
  (forall x y1 y2, (ϕ x /\ ψ1 x y1 /\ ψ2 x y2) -> (y1 <> y2 /\ ψ x (Rltb'' y1 y2))) ->
  [γ : Γ] |- {{ϕ γ}} e1 ;<; e2 {{y : BOOL | ψ γ y}}ᵗ.
Proof.
  intros.
  apply
    (pp_ro_real_comp_lt_tot
       ψ1
       (fun x  y=> ϕ x /\ ψ2 x y)).
  exact X.
  apply (pp_ro_tot_pose_readonly ϕ) in X0.
  apply (pp_ro_imply_tot X0).
  intros h1 h2; split; auto.
  intros h1 h2 [h3 h4]; auto.
  intros.
  apply H.
  repeat split; destruct H1 as [h1 h2]; auto.
Defined.


Lemma pp_rw_while_tot_back_util {Γ Δ} {e c} ϕ θ ψ {ϕ' : rwpre} {ψ' : rwpost}:
    [x : Δ ++ Γ] |- {{ϕ (snd_app x) (fst_app x)}} e {{y : BOOL | θ x y}}ᵗ ->
    [γ : Γ ;;; δ : Δ] ||- {{ϕ γ δ /\ θ (δ ; γ) true}} c {{y : UNIT | ϕ γ δ}}ᵗ ->  
    [γ' : (Γ ++ Δ) ;;; δ : Δ] ||- {{ϕ (fst_app γ') δ /\ θ (δ; fst_app γ') true /\ δ = snd_app γ'}} c {{y : UNIT | ψ γ' δ  }}ᵗ -> 
    (forall δ γ,
        ϕ γ δ -> ~ (exists f : nat -> sem_ctx Δ, f 0%nat = δ /\ (forall n : nat, ψ (γ; f n) ( f (S n))))) -> 
    (forall x y, ϕ' x y -> ϕ x y) ->
    (forall x y z, ϕ x y /\ θ (y ; x) false -> ψ' x y z) ->    
    [γ : Γ ;;; δ : Δ] ||- {{ϕ' γ δ}} While e c {{y : UNIT | ψ' γ δ y }}ᵗ.
  Proof.
    intros p1 p2 p3 h h1 h2.
    apply (pp_rw_while_tot_back ϕ (fun x y => θ x y /\ ϕ (snd_app x) (fst_app x)) ψ).
    
    
    apply (pp_ro_tot_pose_readonly (fun x => ϕ (snd_app x) (fst_app x))) in p1.
    apply (pp_ro_imply_tot p1).
    intros x1 x2; auto.
    intros x1 x2; auto.

    apply (pp_rw_imply_tot p2).
    intros.
    reduce_tedious H; auto.
    destruct H; auto.
    intros; auto.

    apply (pp_rw_imply_tot p3).
    intros.
    reduce_tedious H; auto.
    destruct H.
    destruct H.
    auto.
    intros; auto.
    intros; auto.
    intros; auto.
    intros; auto.
    apply h2; auto.
    destruct H; auto.
    destruct H0.
    split; auto.
  Defined.
