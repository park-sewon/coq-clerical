Require Import ZArith.
Require Import Reals.
Require Import List.
Require Import Coq.Program.Equality.
From Clerical.Preliminaries Require Import Preliminaries.
Require Import Powerdomain.Powerdomain.
Require Import Syntax.
Require Import Typing.
Require Import TypingProperties.

(* In this file, define the denotational semantics of Clerical expressions.
   For the purpose, we import the Powerdomain library which provides a moand
   pdom : Type -> Type. The file PowerdomainSemantics.v provides various
   semantic functions including

   - pdom_list_case {X : Type} : list (pdom bool * pdom X) -> pdom X
     which we use here to interpret CaseList : list (exp * exp) -> exp,
   - pdom_while {X : Type} : (X -> pdom bool) (X -> pdom X) : X -> pdom X
     defined using a Least Fixed-point Theorem in file PowerdomainFixedpointsv
     which we use here to interpret While b c.

   In The file PowerdomainSemantics2.v provides specific semantic functions
   such as limits, divisions, comparisons, etc using Coq standard libraries.
   (take a look!) *)

(* Denotation of data types *)
Definition sem_datatype (τ : datatype) : Type :=
  match τ with
  | DUnit => unit
  | DInteger => Z
  | DBoolean => bool
  | DReal => R
  end.

(* Denotation of contexts *)
Fixpoint sem_ctx (lst : ctx) : Type :=
  match lst with
  | nil => unit
  | cons t lst => sem_datatype t * sem_ctx lst
  end.


(* Updating states *)
Fixpoint update
  {τ : datatype} {Θ : ctx} (k : nat) (v : sem_datatype τ) (γ : sem_ctx Θ)
  (i : assignable Θ τ k) {struct i} : sem_ctx Θ.
Proof.
  induction i.

  (* is_writable_0 *)
  {
    exact (v, snd γ).
  }

  (* is_writable_S *)
  {
    split.
    - exact (fst γ).
    - apply (IHi v (snd γ)).
  }
Defined.

Definition assign_wty_assignable  Γ Δ k e τ (w : (Δ ++ Γ) |- e : τ) (w' : Γ ;;; Δ ||- Assign k e : DUnit) : assignable Δ τ k.
Proof.
  intros.
  inversion w'.
  contradiction (ro_assign_absurd _ _ _ H).
  assert (τ0 = τ) by apply (has_type_ro_unambiguous _ _ _ _ H4 w).
  induction H5.
  exact H3.
Defined.

Definition update' {Γ Δ} {k} {e} {τ} (w : (Δ ++ Γ) |- e : τ) (w' : Γ ;;; Δ ||- Assign k e : DUnit) : sem_ctx Δ -> sem_datatype τ -> sem_ctx Δ.
Proof.
  intros δ v.
  exact (update _ v δ (assign_wty_assignable _ _ _ _ _ w w')).
Defined.

Section TediousList.
  (* We use list for context and cartesian products dependent to it as its semantics.
   We often append lists and merge their states. Though in abstract level this operation
   seems very trivial, in formal level, they need some clerical tedious works.
   In the following section, before we define the semantics, let us define the operations
   and prove some obvious properties.
   When we have Γ, Δ, γ : sem_ctx Γ, and δ ∈ sem_ctx Δ, we define
   - (γ ; δ) : sem_ctx (Γ ++ Δ) 
   - fst_app : sem_ctx (Γ ++ Δ) -> sem_ctx Γ
   - snd_app : sem_ctx (Γ ++ Δ) -> sem_ctx Δ
   and prove their properties. *)
  
  Definition tedious_sem_app Γ Δ : sem_ctx (Γ ++ Δ) -> (sem_ctx Γ) * sem_ctx Δ.
  Proof.
    intro.
    induction Γ.
    simpl.
    simpl in X.
    exact (tt, X).
    simpl.
    simpl in X.
    destruct X.
    destruct (IHΓ s0).
    exact ((s, s1), s2).
  Defined.

  Definition tedious_prod_sem Γ Δ : (sem_ctx Γ) * sem_ctx Δ -> sem_ctx (Γ ++ Δ).
  Proof.
    intros.
    induction Γ.
    simpl.
    simpl in X.
    destruct X as [_ X]; exact X.
    simpl.
    destruct X.
    simpl in s.
    destruct s.
    split.
    exact s.
    exact (IHΓ (s1, s0)).
  Defined.
  
  Notation " ( γ ; δ ) " := (tedious_prod_sem _ _  (γ, δ)).

  Definition fst_app {Γ Δ} : sem_ctx (Γ ++ Δ) -> sem_ctx Γ.
  Proof.
    intro γδ.
    destruct (tedious_sem_app _ _ γδ) as [γ _].
    exact γ.
  Defined.

  Definition snd_app {Γ Δ} : sem_ctx (Γ ++ Δ) -> sem_ctx Δ.
  Proof.
    intro γδ.
    destruct (tedious_sem_app _ _ γδ) as [_ δ].
    exact δ.
  Defined.

  Definition pair_app {Γ Δ} : sem_ctx Γ -> sem_ctx Δ -> sem_ctx (Γ ++ Δ).
  Proof.
    intros γ δ.
    apply tedious_prod_sem.
    exact (γ, δ).
  Defined.

  Lemma tedious_equiv_1 : forall Δ Γ δ γ,  tedious_sem_app Δ Γ (tedious_prod_sem Δ Γ (δ, γ)) = (δ, γ).
  Proof.
    intros.
    induction Δ.
    simpl in δ.
    destruct δ.
    simpl.
    auto.
    simpl.
    simpl in δ.
    destruct δ.
    rewrite IHΔ.
    auto.
  Defined.

  Lemma tedious_equiv_2_snd : forall Δ Γ τ  (γ : sem_ctx ((τ :: Δ) ++ Γ)), snd_app γ = snd_app (snd γ).
  Proof.
    intros.
    unfold snd_app.
    simpl.
    destruct γ.
    simpl.
    destruct (tedious_sem_app Δ Γ s0); auto.
  Defined.

  Lemma tedious_equiv_2_fst : forall Δ Γ τ  (γ : sem_ctx ((τ :: Δ) ++  Γ)), fst_app γ = (fst γ, fst_app (snd γ)).
  Proof.
    intro.
    intros.
    unfold fst_app.
    simpl.
    destruct γ.
    simpl.  
    destruct (tedious_sem_app Δ Γ s0); auto.
  Defined.

  Lemma tedious_equiv_2 {Δ Γ} (γ : sem_ctx (Δ ++ Γ)) : γ = (fst_app γ; snd_app γ). 
  Proof.
    dependent induction Δ.
    simpl.
    auto.
    simpl.
    destruct γ.
    simpl.
    rewrite tedious_equiv_2_snd.
    simpl.
    rewrite tedious_equiv_2_fst.
    simpl.
    rewrite <- IHΔ.
    auto.
  Defined.

  

  Lemma tedious_equiv_3 : forall {Γ Δ} h, tedious_prod_sem Δ Γ (tedious_sem_app Δ Γ h) = h.
  Proof.
    intros.
    rewrite (tedious_equiv_2 h) at 1.
    rewrite (tedious_equiv_2 h) at 3.
    unfold fst_app, snd_app.
    destruct (tedious_sem_app Δ Γ h).
    rewrite  tedious_equiv_1.
    reflexivity.
  Defined.

  
  Lemma tedious_equiv_snd : forall Γ Δ (x : sem_ctx Γ) (y : sem_ctx Δ), snd_app (x; y) = y.
  Proof.
    intros.
    unfold snd_app.
    rewrite tedious_equiv_1.
    reflexivity.
  Defined.

  Lemma tedious_equiv_fst : forall Γ Δ (x : sem_ctx Γ) (y : sem_ctx Δ), fst_app (x; y) = x.
  Proof.
    intros.
    unfold fst_app.
    rewrite tedious_equiv_1.
    reflexivity.
  Defined.

  Lemma tedious_equiv_0 : forall Δ Γ x,  tedious_sem_app Δ Γ (tedious_prod_sem Δ Γ x) = x.
  Proof.
    intros.
    destruct x.
    apply tedious_equiv_1.
  Defined.
  
  Lemma tedious_equiv_4_fst : forall Δ x, @snd_app nil Δ x = x. 
  Proof.
    intros.
    simpl in x.
    unfold snd_app; simpl; auto.
  Defined.


  
End TediousList.
Notation " ( γ ; δ ) " := (tedious_prod_sem _ _  (γ, δ)).
  Ltac reduce_tedious_tactic h :=
    match type of h with
    | ltac_No_arg =>
        repeat (simpl; try rewrite <- tedious_equiv_2; try rewrite tedious_equiv_fst; try rewrite tedious_equiv_snd;
                try rewrite tedious_equiv_2_fst; try rewrite tedious_equiv_2_snd; try rewrite tedious_equiv_4_fst)
    | _ =>
        repeat (simpl in h; try rewrite <- tedious_equiv_2 in h; try rewrite tedious_equiv_fst in h; try rewrite tedious_equiv_snd in h; try rewrite tedious_equiv_2_fst in h; try rewrite tedious_equiv_2_snd in h; try rewrite tedious_equiv_4_fst in h)
    end.
Tactic Notation "reduce_tedious" constr(x1) :=
  reduce_tedious_tactic x1 .

Tactic Notation "reduce_tedious" :=
  reduce_tedious_tactic ltac_no_arg.

Section AccessState.
  Fixpoint ro_access  Γ k τ (w: Γ |- Var k : τ) : sem_ctx Γ -> sem_datatype τ.
  Proof.
    inversion w.
    inversion H.
    simpl in H7.
    exact (ro_access _ _ _ H3).
    intro.
    simpl in X.
    destruct X.
    exact s.
    intro.
    apply (ro_access _ _ _ H1).
    destruct X.
    exact s0.
  Defined.

  Fixpoint p_ro_access  Γ k τ (w : r_has_type_ro Γ (Var k) τ) : sem_ctx Γ -> sem_datatype τ.
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

  Fixpoint ro_access_Var_0 Γ τ (w : (τ :: Γ) |- Var 0 : τ) {struct w} : forall x (γ : sem_ctx Γ), ro_access (τ :: Γ) 0 τ w (x, γ) = x.
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

  Fixpoint ro_access_Var_S Γ k τ σ (w : (τ :: Γ) |- Var (S k) : σ) {struct w} : forall x (γ : sem_ctx Γ),
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
    easy_rewrite_uip.
    reflexivity.
    rewrite H0.
    apply ro_access_Var_S.
    simpl.
    easy_rewrite_uip.
    reflexivity.
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

  Fixpoint ro_access_app  Γ γ k τ w Δ δ w':
    ro_access Γ k τ w γ = ro_access (Γ ++ Δ) k τ w' (γ ; δ).
  Proof.
    intros.
    dependent induction w.
    dependent destruction h.
    easy_rewrite_uip.
    apply ro_access_app.
    simpl.
    easy_rewrite_uip.
    destruct γ.
    simpl in w'.
    rewrite ro_access_Var_0.
    reflexivity.
    easy_rewrite_uip.
    destruct γ.
    rewrite ro_access_Var_S.
    
    rewrite (ro_access_app Γ s0 k0 τ w Δ δ (has_type_ro_Var_S_inv (Γ ++ Δ) k0 σ τ w')).
    reflexivity.
  Qed.
End AccessState.

Fixpoint sem_ro_exp (Γ : ctx) (e : exp) (τ : datatype) (D : Γ |- e : τ) {struct D} :
  sem_ctx Γ -> pdom (sem_datatype τ)
with sem_rw_exp (Γ Δ : ctx) (c : exp) (τ : datatype) (D : Γ ;;; Δ ||- c : τ) {struct D} :
  sem_ctx Γ -> sem_ctx Δ -> pdom (sem_ctx Δ * sem_datatype τ).
Proof.
  - (* read only expressions *)
    induction D; intro γ.

    (* | has_type_ro_rw *)
    pose proof (sem_rw_exp _ _ _ _ h γ tt) as X.
    exact (pdom_lift snd X).

    (* | has_type_ro_Var_0 *)
    simpl in γ.
    exact (pdom_unit (fst γ)).

    (* | has_type_ro_Var_S *)
    simpl in γ.
    (* exact (IHD (snd γ)). *)
    exact (sem_ro_exp _ _ _ D (snd γ)).
    
    (* | has_type_ro_True *)
    exact (pdom_unit true).

    (* | has_type_ro_False *)
    exact (pdom_unit false).

    (* | has_type_ro_Skip *)
    exact (pdom_unit tt).
    
    (* | has_type_ro_Int *)
    exact (pdom_unit k).

    (* | has_type_ro_OpRrecip *)
    pose proof (sem_ro_exp _ _ _ D γ).
    exact (pdom_bind Rrecip X). 
    
    (* | has_type_ro_OpZRcoerce *)
    pose proof (sem_ro_exp _ _ _ D γ).
    exact (pdom_lift IZR X).
    
    (* | has_type_ro_OpZRexp *)
    pose proof (sem_ro_exp _ _ _ D γ).
    exact (pdom_lift (powerRZ 2) X).

    (* | has_type_ro_OpZplus *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zplus x y).
    
    (* | has_type_ro_OpZminus *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zminus x y).
    
    (* | has_type_ro_OpZmult *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zmult x y).
    
    (* | has_type_ro_OpZlt *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Z.ltb x y).

    (* | has_type_ro_OpZeq *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Z.eqb x y).

    (* | has_type_ro_OpRplus *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rplus x y).

    (* | has_type_ro_OpRminus *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rminus x y).

    (* | has_type_ro_OpRmult *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rmult x y).

    (* | has_type_ro_OpRlt *)
    pose proof (sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_bind2 Rltb x y).

    (* | has_type_ro_Lim *)
    exact (Rlim (fun x : Z => sem_ro_exp _ _ _ D (x, γ))). 


  - (* read write commands*)
    Require Import Coq.Program.Equality.
    dependent destruction D; intros γ δ.

    (* has_type_rw_ro *)
    exact (pdom_lift (fun x => (δ, x)) (sem_ro_exp _ _ _ h (δ; γ))).
    
    (* has_type_rw_Seq *)
    pose proof (sem_rw_exp _ _ _ _ D1 γ) as C1.
    pose proof (sem_rw_exp _ _ _ _ D2 γ) as C2.
    apply (pdom_bind C2).
    apply (pdom_lift (@fst _ (sem_datatype DUnit))).
    apply C1.
    exact δ.

    (* has_type_rw_Assign *)
    pose proof (pdom_lift (fun v => update k v δ a) (sem_ro_exp _ _ _ h (δ; γ))) as V.
    exact (pdom_lift (fun x => (x, tt)) V).
    
    (* has_type_rw_Newvar *)
    pose proof (sem_ro_exp _ _ _ h (δ; γ)) as V.
    pose proof (sem_rw_exp _ _ _ _ D γ) as f.
    pose proof (pdom_bind f (pdom_lift (fun v => (v, δ)) V)) as res.
    exact (pdom_lift (fun x => (snd (fst x), snd x)) res).

    (* has_type_rw_Cond *)
    pose proof (sem_ro_exp _ _ _ h (δ; γ)) as B.
    pose proof (sem_rw_exp _ _ _ _ D1 γ δ) as X.
    pose proof (sem_rw_exp _ _ _ _ D2 γ δ) as Y.
    exact (pdom_bind (fun b : bool => if b then X else Y) B).
    
    (* (* has_type_rw_Case *) *)
    (* pose proof (sem_ro_exp _ _ _ h (δ; γ)) as B1. *)
    (* pose proof (sem_ro_exp _ _ _ h0 (δ; γ)) as B2. *)
    (* pose proof (sem_rw_exp _ _ _ _ D1 γ δ) as X. *)
    (* pose proof (sem_rw_exp _ _ _ _ D2 γ δ) as Y. *)
    (* exact (Case2 B1 B2 X Y). *)

    (* has_type_rw_CaseList *)
    assert (list ((pdom bool) * (pdom (sem_ctx Δ * sem_datatype τ)))).
    clear l0.
    induction f.
    exact nil.
    destruct p.
    exact ((sem_ro_exp _ _ _ h (δ; γ), sem_rw_exp _ _ _ _ h0 γ δ) :: IHf ).
    exact (pdom_case_list X).
    
    (* has_type_rw_While *)
    pose proof (fun d => sem_ro_exp _ _ _ h (d; γ)) as B.
    pose proof (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ D γ d)) as C.
    exact (pdom_lift (fun x => (x, tt)) (pdom_while B C δ)).
Defined.
