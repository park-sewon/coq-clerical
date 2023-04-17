Require Import ZArith.
Require Import Reals.
Require Import Clerical.
Require Import Typing.
Require Import TypingProperties.
Require Import Powerdomain.
Require Import List.
Require Import Coq.Program.Equality.
Definition sem_datatype (τ : datatype) : Type :=
  match τ with
  | DUnit => unit
  | DInteger => Z
  | DBoolean => bool
  | DReal => R
  end.

Fixpoint sem_list_datatype (lst : ro_ctx) : Type :=
  match lst with
  | nil => unit
  | cons t lst => sem_datatype t * sem_list_datatype lst
  end.

Definition sem_ro_ctx := sem_list_datatype.

Definition tedious_sem_concat Γ Δ : sem_ro_ctx (Γ ++ Δ) -> (sem_ro_ctx Γ) * sem_ro_ctx Δ.
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

Definition tedious_prod_sem Γ Δ : (sem_ro_ctx Γ) * sem_ro_ctx Δ -> sem_ro_ctx (Γ ++ Δ).
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

Definition fst_concat {Γ Δ} : sem_ro_ctx (Γ ++ Δ) -> sem_ro_ctx Γ.
Proof.
  intro γδ.
  destruct (tedious_sem_concat _ _ γδ) as [γ _].
  exact γ.
Defined.

Definition snd_concat {Γ Δ} : sem_ro_ctx (Γ ++ Δ) -> sem_ro_ctx Δ.
Proof.
  intro γδ.
  destruct (tedious_sem_concat _ _ γδ) as [_ δ].
  exact δ.
Defined.

Definition pair_concat {Γ Δ} : sem_ro_ctx Γ -> sem_ro_ctx Δ -> sem_ro_ctx (Γ ++ Δ).
Proof.
  intros γ δ.
  apply tedious_prod_sem.
  exact (γ, δ).
Defined.


Lemma tedious_equiv_1 : forall Δ Γ δ γ,  tedious_sem_concat Δ Γ (tedious_prod_sem Δ Γ (δ, γ)) = (δ, γ).
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


Notation " ( γ ; δ ) " := (tedious_prod_sem _ _  (γ, δ)).


Lemma tedious_equiv_2_snd : forall Δ Γ τ  (γ : sem_ro_ctx ((τ :: Δ) ++ Γ)), snd_concat γ = snd_concat (snd γ).
Proof.
  intros.
  unfold snd_concat.
  simpl.
  destruct γ.
  simpl.
  destruct (tedious_sem_concat Δ Γ s0); auto.
Defined.

Lemma tedious_equiv_2_fst : forall Δ Γ τ  (γ : sem_ro_ctx ((τ :: Δ) ++  Γ)), fst_concat γ = (fst γ, fst_concat (snd γ)).
Proof.
  intro.
  intros.
  unfold fst_concat.
  simpl.
  destruct γ.
  simpl.  
  destruct (tedious_sem_concat Δ Γ s0); auto.
Defined.


Lemma tedious_equiv_2 {Δ Γ} (γ : sem_ro_ctx (Δ ++ Γ)) : γ = (fst_concat γ; snd_concat γ). 
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


Definition sem_rw_ctx : rw_ctx -> Type.
Proof.
  intros [Γ Δ].
  exact (sem_list_datatype Γ * sem_list_datatype Δ)%type.
Defined.
  
Fixpoint update
  {τ : datatype} {Θ : ro_ctx} (k : nat) (v : sem_datatype τ) (γ : sem_list_datatype Θ)
  (i : assignable Θ τ k) {struct i} : sem_list_datatype Θ.
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
  contradiction (ro_assign_absurd _ _ _ H3).
  assert (τ0 = τ) by apply (has_type_ro_unambiguous _ _ _ _ H4 w).
  induction H5.
  exact H2.
Defined.

Definition update' {Γ Δ} {k} {e} {τ} (w : (Δ ++ Γ) |- e : τ) (w' : Γ;;;Δ ||- Assign k e : DUnit) : sem_ro_ctx Δ -> sem_datatype τ -> sem_ro_ctx Δ.
Proof.
  intros δ v.
  exact (update _ v δ (assign_wty_assignable _ _ _ _ _ w w')).
Defined.

Definition Rrecip' : R -> flat R.
Proof.
  intro x.
  destruct (total_order_T x 0).
  destruct s.
  exact (total (/x))%R.
  exact (bot R).
  exact (total (/x))%R.
Defined.


Definition Rltb'' : R -> R -> bool.
Proof.
  intros x y.
  destruct (total_order_T x y).
  destruct s.
  exact (true)%R.
  exact (false).
  exact (false).
Defined.


Definition Rltb' : R -> R -> flat bool.
Proof.
  intros x y.
  destruct (total_order_T x y).
  destruct s.
  exact (total true)%R.
  exact (bot bool).
  exact (total false)%R.
Defined.

Definition Rrecip : R -> pdom R := fun x => flat_to_pdom (Rrecip' x).
  
Definition Rltb : R -> R -> pdom bool := fun x y => flat_to_pdom (Rltb' x y).

Definition Rlim_def (f : Z -> pdom R) : flat R -> Prop :=
  (fun y : flat R =>
     exists y' : R, y = total y' /\                            
                 forall x : Z,
                   ~ pdom_is_empty (f x) /\ 
                 forall z : flat R,
                   proj1_sig (f x) z ->
                   exists z' : R, z = total z' /\ Rabs (z' - y') < powerRZ 2 (- x))%R.


Section RealsFacts.
  Open Scope R_scope.
  Require Import Lra Lia.
  Definition pow2 : Z -> R := fun x => (powerRZ 2) x.
  
  Lemma archimed_pow2' : forall n, (0 < n)%nat -> pow2 (- Z.of_nat n) < 1 / INR n. 
  Proof.
    intros.
    induction n.
    contradict H; lia.
    destruct n.
    simpl.
    lra.
    destruct n.
    simpl.
    lra.
    replace (- Z.of_nat (S (S (S n))))%Z with (- Z.of_nat (S (S n)) - 1)%Z.
    replace (1 / INR (S (S (S n)))) with (1 / (INR (S (S n)) + 1)).
    assert (0 < S (S n))%nat by lia.
    apply IHn in H0.
    replace (pow2 (- Z.of_nat (S (S n)) - 1)) with
      (pow2 (- Z.of_nat (S (S n))) /2 ).
    assert (pow2 (- Z.of_nat (S (S n)))/2 < 1 / INR (S (S n)) /2).
    lra.
    assert (1 / INR (S (S n)) / 2 < 1 / (INR (S (S n)) + 1)).
    assert (forall x,2 <= x -> x + 1 < 2 * x).
    intros.
    lra.
    pose proof (H2 (INR (S (S n)))).
    assert (2 <= INR (S (S n))).
    replace 2 with (INR (S (S O))).
    apply le_INR.
    lia.
    auto.
    apply H3 in H4.
    assert (0 < INR (S (S n)) + 1).
    lra.
    assert (0<  2 * INR (S (S n))).
    lra.
    apply (Rmult_lt_compat_l _ _ _ (Rinv_0_lt_compat _ H5)) in H4.
    apply (Rmult_lt_compat_l _ _ _ (Rinv_0_lt_compat _ H6)) in H4.
    rewrite Rinv_l in H4.
    replace (/ (2 * INR (S (S n))) * (/ (INR (S (S n)) + 1) * (2 * INR (S (S n)))))
      with (/ (2 * INR (S (S n)))  * (2 * INR (S (S n))) * (/ (INR (S (S n)) + 1))) in H4 by ring.    
    rewrite Rinv_l in H4.
    unfold Rdiv.
    unfold Rdiv in H4.
    rewrite Rinv_mult in H4.
    replace (/ 2 * / INR (S (S n)) * 1) with (1 * / INR (S (S n)) * / 2) in H4 by ring.
    auto.
    lra.
    lra.
    lra.
    unfold Rdiv.
    assert (pow2 (- 1)%Z = / 2).
    simpl.
    lra.
    rewrite <- H1.
    unfold pow2.
    rewrite <- powerRZ_add.
    apply lp.
    lia.
    lra.
    simpl.
    auto.
    simpl.
    lia.
  Defined.
  
  Lemma archimed_pow2 :forall x : R, 0 < x -> exists k, pow2 k < x.
  Proof.
    intros.
    pose proof (archimed_cor1 _ H).
    destruct H0.
    exists (- Z.of_nat x0)%Z.
    destruct H0.
    pose proof (archimed_pow2' x0 H1).
    lra.
  Defined.
    
  Lemma Rlim_def_unique f : forall x y, Rlim_def f x -> Rlim_def f y -> x = y.
  Proof.
    intros x y H H0.
    destruct H as [x' [tx hx]].
    destruct H0 as [y' [ty hy]].
    rewrite tx, ty; apply lp.
    clear tx ty.

    destruct (lem (x' = y')); auto.
    destruct (Rdichotomy _ _ H).
    (* when x' < y' *)
    clear H.
    assert (0 < y' - x') by lra.
    pose proof (archimed_pow2 _ H).
    destruct H1 as [k o].

    pose proof (hx (- k + 1)%Z) as [xk hxk].
    pose proof (hy (- k + 1)%Z) as [yk hyk].
    apply pdom_neg_empty_exists in xk as [xk mx].
    (* apply pdom_neg_empty_exists in yk as [yk my]. *)
    pose proof (hxk _ mx) as [zx [p1 p2]].
    (* pose proof (hyk _ my) as [zy [q1 q2]]. *)
    pose proof (hyk _ mx) as [zy [q1 q2]].
    rewrite p1 in q1.
    apply total_is_injective in q1.
    induction q1.
    pose proof (Rplus_lt_compat _ _ _ _ p2 q2).
    rewrite <- Rabs_Ropp in H1 at 1.
    pose proof (Rle_lt_trans _ _ _ (Rabs_triang _ _) H1).
    replace (- (zx - x') + (zx - y')) with (x' - y') in H2 by ring.
    replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1))) with (pow2 k) in H2.
    rewrite Rabs_left in H2.
    replace ( - (x' - y')) with (y' - x') in H2 by ring.
    contradict (Rlt_asym _ _ H2 o).
    lra.
    replace (- (- k + 1))%Z with (k + - 1)%Z by ring.
    rewrite powerRZ_add.
    simpl.
    unfold pow2.
    lra.
    lra.

    (* when y' < x' *)
    clear H.
    assert (0 < x' - y') by lra.
    pose proof (archimed_pow2 _ H).
    destruct H1 as [k o].

    pose proof (hx (- k + 1)%Z) as [xk hxk].
    pose proof (hy (- k + 1)%Z) as [yk hyk].
    apply pdom_neg_empty_exists in xk as [xk mx].
    (* apply pdom_neg_empty_exists in yk as [yk my]. *)
    pose proof (hxk _ mx) as [zx [p1 p2]].
    (* pose proof (hyk _ my) as [zy [q1 q2]]. *)
    pose proof (hyk _ mx) as [zy [q1 q2]].
    rewrite p1 in q1.
    apply total_is_injective in q1.
    induction q1.
    pose proof (Rplus_lt_compat _ _ _ _ p2 q2).
    rewrite <- Rabs_Ropp in H1 at 1.
    pose proof (Rle_lt_trans _ _ _ (Rabs_triang _ _) H1).
    replace (- (zx - x') + (zx - y')) with (x' - y') in H2 by ring.
    replace (powerRZ 2 (- (- k + 1)) + powerRZ 2 (- (- k + 1))) with (pow2 k) in H2.
    rewrite Rabs_right in H2.
    contradict (Rlt_asym _ _ H2 o).
    lra.
    replace (- (- k + 1))%Z with (k + - 1)%Z by ring.
    rewrite powerRZ_add.
    simpl.
    unfold pow2.
    lra.
    lra.
  Defined.
  

  Lemma Rlim_def_never_bot : forall f, ~ (Rlim_def f (bot R)).
  Proof.
    intro.
    intro.
    destruct H.
    destruct H.
    contradict (flat_bot_neq_total _ H).
  Defined.
  
  Definition Rlim : (Z -> pdom R) -> pdom R.
  Proof.
    intro f.
    exists (Rlim_def f).
    intro H.
    apply pset_infinite_subset_infinite in H.
    contradict H.
    apply hprop_ninfinite.
    intros.
    destruct x, y.
    apply sig_eq.
    simpl.
    apply (Rlim_def_unique f); auto.
  Defined.

End RealsFacts.


(* Definition Case2' {X : Type} : flat bool -> flat bool -> pdom X -> pdom X -> pdom X. *)
(* Proof. *)
(*   intros b1 b2 c1 c2. *)
(*   destruct b1. *)
(*   (* when b1 = bot *) *)
(*   destruct b2. *)
(*   (* when b2 = bot *) *)
(*   exact (pdom_flat_unit (bot X)). *)
(*   destruct b. *)
(*   (* when b2 = true *) *)
(*   exact c2. *)
(*   (* when b2 = false *) *)
(*   exact (pdom_flat_unit (bot X)). *)
(*   destruct b. *)
(*   (* when b1 = true *) *)
(*   destruct b2. *)
(*   (* when b2 = bot *) *)
(*   exact c1. *)
(*   destruct b. *)
(*   (* when b2 = true *) *)
(*   exact (strict_union c1 c2). *)
(*   (* when b2 = false *) *)
(*   exact c1. *)
(*   (* when b1 = false *) *)
(*   destruct b2. *)
(*   (* when b2 = bot *) *)
(*   exact (pdom_flat_unit (bot X)). *)
(*   destruct b. *)
(*   (* when b2 = true *) *)
(*   exact c2. *)
(*   (* when b2 = false *) *)
(*   exact (pdom_flat_unit (bot X)). *)
(* Defined. *)

Definition Case2 {X : Type} : pdom bool -> pdom bool -> pdom X -> pdom X -> pdom X.
Proof.
  apply pdom_case2.
  (* intros b1 b2 c1 c2. *)
  (* exact (pdom_flat_bind2 (fun x y => Case2' x y c1 c2) b1 b2).  *)
Defined.
  
Fixpoint sem_ro_exp (Γ : ro_ctx) (e : exp) (τ : datatype) (D : Γ |- e : τ) {struct D} :
  sem_ro_ctx Γ -> pdom (sem_datatype τ)
with sem_rw_exp (Γ Δ : ro_ctx) (c : exp) (τ : datatype) (D : Γ ;;; Δ ||- c : τ) {struct D} :
  sem_ro_ctx Γ -> sem_ro_ctx Δ -> pdom (sem_ro_ctx Δ * sem_datatype τ).
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
    exact (pdom_lift (fun x => (δ, x)) (sem_ro_exp _ _ _ h (tedious_prod_sem _ _ (δ, γ)))).
  
    (* has_type_rw_Seq *)
    pose proof (sem_rw_exp _ _ _ _ D1 γ) as C1.
    pose proof (sem_rw_exp _ _ _ _ D2 γ) as C2.
    apply (pdom_bind C2).
    apply (pdom_lift (@fst _ (sem_datatype DUnit))).
    apply C1.
    exact δ.

    (* has_type_rw_Assign *)
    pose proof (pdom_lift (fun v => update k v δ a) (sem_ro_exp _ _ _ h (tedious_prod_sem _ _ (δ, γ)))) as V.
    exact (pdom_lift (fun x => (x, tt)) V).
    
    (* has_type_rw_Newvar *)
    pose proof (sem_ro_exp _ _ _ h (tedious_prod_sem _ _ (δ, γ))) as V.
    pose proof (sem_rw_exp _ _ _ _ D γ) as f.
    pose proof (pdom_bind f (pdom_lift (fun v => (v, δ)) V)) as res.
    exact (pdom_lift (fun x => (snd (fst x), snd x)) res).

    (* has_type_rw_Cond *)
    pose proof (sem_ro_exp _ _ _ h (tedious_prod_sem _ _ (δ, γ))) as B.
    pose proof (sem_rw_exp _ _ _ _ D1 γ δ) as X.
    pose proof (sem_rw_exp _ _ _ _ D2 γ δ) as Y.
    exact (pdom_bind (fun b : bool => if b then X else Y) B).
    
    (* has_type_rw_Case *)
    pose proof (sem_ro_exp _ _ _ h (tedious_prod_sem _ _ (δ, γ))) as B1.
    pose proof (sem_ro_exp _ _ _ h0 (tedious_prod_sem _ _ (δ, γ))) as B2.
    pose proof (sem_rw_exp _ _ _ _ D1 γ δ) as X.
    pose proof (sem_rw_exp _ _ _ _ D2 γ δ) as Y.
    exact (Case2 B1 B2 X Y).

    (* has_type_rw_CaseList *)
    assert (list ((pdom bool) * (pdom (sem_ro_ctx Δ * sem_datatype τ)))).
    clear l0.
    induction f.
    exact nil.
    destruct p.
    exact ((sem_ro_exp _ _ _ h (δ; γ), sem_rw_exp _ _ _ _ h0 γ δ) :: IHf ).
    exact (pdom_case_list X).
    
    (* has_type_rw_While *)
    pose proof (fun d => sem_ro_exp _ _ _ h (tedious_prod_sem _ _ (d, γ))) as B.
    pose proof (fun d => pdom_lift fst (sem_rw_exp _ _ _ _ D γ d)) as C.
    exact (pdom_lift (fun x => (x, tt)) (pdom_while B C δ)).
Defined.
