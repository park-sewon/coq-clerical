Require Import List.
Require Import Reals.
Require Import Coq.Program.Equality.

From Clerical.Preliminaries Require Import Preliminaries.
From Clerical.Powerdomain Require Import Powerdomain.
From Clerical Require Import Syntax.
From Clerical Require Import Typing.
From Clerical Require Import TypingProperties.
From Clerical Require Import Semantics.

(* In this file, we prove some properties of the semantics of Clerical.
   The main theorems here are that 1) the semantics is irrelevnet to the welltypedness
   and that 2) the semantics does not change for us adding auxiliary variables at the end of the readonly contexts.

   Putting it more formally,
   1) forall (w1 w2 : Γ |- e : τ), sem_ro_exp Γ e τ w1 = sem_ro_exp Γ e τ w2
   1') forall (w1 w2 : Γ ;;; Δ ||- e : τ), sem_rw_exp Γ Δ e τ w1 = sem_rw_exp Γ Δ e τ w2
   and
   2) forall Γ' (w1 : Γ ;;; Δ ||- e : τ) (w2 : (Γ ++ Γ') ;;; Δ ||- e : τ), forall γ δ γ', sem_rw_exp Γ Δ e τ w1 γ δ = sem_rw_exp (Γ ++ Γ') Δ e τ w2 (γ ; γ') δ

   To prove it, again we define a semantics to restricted typing rules, proving the properties on the restricted semantics and transfer the result back.
 *)
Fixpoint r_sem_ro_exp (Γ : ctx) (e : exp) (τ : datatype) (D : Γ |~ e : τ) {struct D} : sem_ctx Γ -> pdom (sem_datatype τ)
with r_sem_rw_exp (Γ Δ : ctx) (c : exp) (τ : datatype) (D : Γ ;;; Δ ||~ c : τ) {struct D} : sem_ctx Γ -> sem_ctx Δ -> pdom (sem_ctx Δ * sem_datatype τ).
Proof.
  - (* read only expressions *)
    induction D; intro γ.
    exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)).
    exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)).
    exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)).
    exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)).
    exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)).
    exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)).
    (* exact (pdom_lift snd (r_sem_rw_exp _ _ _ _ r γ tt)). *)

    (* | has_type_ro_Var_0 *)
    simpl in γ.
    exact (pdom_unit (fst γ)).

    (* | has_type_ro_Var_S *)
    simpl in γ.
    (* exact (IHD (snd γ)). *)
    exact (r_sem_ro_exp _ _ _ D (snd γ)).

    (* | has_type_ro_True *)
    exact (pdom_unit true).

    (* | has_type_ro_False *)
    exact (pdom_unit false).

    (* | has_type_ro_Skip *)
    exact (pdom_unit tt).
    
    (* | has_type_ro_Int *)
    exact (pdom_unit k).

    (* | has_type_ro_OpRrecip *)
    pose proof (r_sem_ro_exp _ _ _ D γ).
    exact (pdom_bind Rrecip X). 
    
    (* | has_type_ro_OpZRcoerce *)
    pose proof (r_sem_ro_exp _ _ _ D γ).
    exact (pdom_lift IZR X).
    
    (* | has_type_ro_OpZRexp *)
    pose proof (r_sem_ro_exp _ _ _ D γ).
    exact (pdom_lift (powerRZ 2) X).

    (* | has_type_ro_OpZplus *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zplus x y).
    
    (* | has_type_ro_OpZminus *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zminus x y).
    
    (* | has_type_ro_OpZmult *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zmult x y).
    
    (* | has_type_ro_OpZlt *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Z.ltb x y).

    (* | has_type_ro_OpZeq *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Z.eqb x y).

    (* | has_type_ro_OpRplus *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rplus x y).

    (* | has_type_ro_OpRminus *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rminus x y).

    (* | has_type_ro_OpRmult *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rmult x y).

    (* | has_type_ro_OpRlt *)
    pose proof (r_sem_ro_exp _ _ _ D1 γ) as x.
    pose proof (r_sem_ro_exp _ _ _ D2 γ) as y.
    exact (pdom_bind2 Rltb x y).

    (* | has_type_ro_Lim *)
    exact (Rlim (fun x : Z => r_sem_ro_exp _ _ _ D (x, γ))). 

  - (* read write commands *)
    dependent destruction D; intros γ δ.

    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (r_sem_ro_exp _ _ _ r (δ ; γ))).

    (* has_type_rw_Seq *)
    pose proof (r_sem_rw_exp _ _ _ _ D1 γ) as C1.
    pose proof (r_sem_rw_exp _ _ _ _ D2 γ) as C2.
    apply (pdom_bind C2).
    apply (pdom_lift (@fst _ (sem_datatype DUnit))).
    apply C1.
    exact δ.

    (* has_type_rw_Assign *)
    pose proof (pdom_lift (fun v => update k v δ a) (r_sem_ro_exp _ _ _ r (tedious_prod_sem _ _ (δ, γ)))) as V.
    exact (pdom_lift (fun x => (x, tt)) V).
    
    (* has_type_rw_Newvar *)
    pose proof (r_sem_ro_exp _ _ _ r (tedious_prod_sem _ _ (δ, γ))) as V.
    pose proof (r_sem_rw_exp _ _ _ _ D γ) as f.
    pose proof (pdom_bind f (pdom_lift (fun v => (v, δ)) V)) as res.
    exact (pdom_lift (fun x => (snd (fst x), snd x)) res).

    (* has_type_rw_Cond *)
    pose proof (r_sem_ro_exp _ _ _ r (tedious_prod_sem _ _ (δ, γ))) as B.
    pose proof (r_sem_rw_exp _ _ _ _ D1 γ δ) as X.
    pose proof (r_sem_rw_exp _ _ _ _ D2 γ δ) as Y.
    exact (pdom_bind (fun b : bool => if b then X else Y) B).
    
    (* (* has_type_rw_Case *) *)
    (* pose proof (r_sem_ro_exp _ _ _ r (tedious_prod_sem _ _ (δ, γ))) as B1. *)
    (* pose proof (r_sem_ro_exp _ _ _ r0 (tedious_prod_sem _ _ (δ, γ))) as B2. *)
    (* pose proof (r_sem_rw_exp _ _ _ _ D1 γ δ) as X. *)
    (* pose proof (r_sem_rw_exp _ _ _ _ D2 γ δ) as Y. *)
    (* exact (Case2 B1 B2 X Y). *)

    (* has_type_rw_CaseList *)
    assert (list ((pdom bool) * ( pdom (sem_ctx Δ * sem_datatype τ)))).
    clear l0.
    induction f.
    exact nil.
    destruct p.
    exact ((r_sem_ro_exp _ _ _ r (δ; γ), r_sem_rw_exp _ _ _ _ r0 γ δ) :: IHf). 
    exact (pdom_case_list X).

    
    (* has_type_rw_While *)
    pose proof (fun d => r_sem_ro_exp _ _ _ r (tedious_prod_sem _ _ (d, γ))) as B.
    pose proof (fun d => pdom_lift fst (r_sem_rw_exp _ _ _ _ D γ d)) as C.
    exact (pdom_lift (fun x => (x, tt)) (pdom_while B C δ)).
Defined.


Lemma r_sem_ro_Seq : forall Γ c1 c2 τ (w : Γ |~ (c1 ;; c2) : τ),
    r_sem_ro_exp Γ (c1;; c2) τ w =
      (fun γ : sem_ctx Γ =>
         pdom_lift snd (pdom_bind (r_sem_rw_exp Γ nil c2 τ (r_has_type_ro_inv_Seq_2 _ _ _ _ w) γ) (pdom_lift fst (r_sem_rw_exp Γ nil c1 UNIT (r_has_type_ro_inv_Seq_1 _ _ _ _ w) γ tt)))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction r.
  easy_rewrite_uip.
  auto.
Qed.


Lemma r_sem_ro_Newvar : forall Γ e c τ (w :  Γ |~ (NEWVAR e IN c) : τ), exists σ p p1,
    r_sem_ro_exp Γ (NEWVAR e IN c) τ w
    =
      (fun γ : sem_ctx Γ =>
         pdom_lift snd
           (pdom_lift (fun x : sem_datatype σ * unit * sem_datatype τ => (snd (fst x), snd x))
              (pdom_bind (r_sem_rw_exp Γ (σ :: nil) c τ p1 γ)
                 (pdom_lift (fun v : sem_datatype σ => (v, tt)) (r_sem_ro_exp Γ e σ p γ))))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction r.
  easy_rewrite_uip.
  exists σ, r, r1.
  auto.  
Qed.

Lemma r_sem_ro_Cond : forall Γ e c1 c2 τ (w : Γ |~ (IF e THEN c1 ELSE c2 END) : τ), exists p1 p2 p3,
    r_sem_ro_exp Γ (IF e THEN c1 ELSE c2 END) τ w =
      (fun γ : sem_ctx Γ =>
         pdom_lift snd
           (pdom_bind (fun b : bool => if b then r_sem_rw_exp Γ nil c1 τ p2 γ tt else r_sem_rw_exp Γ nil c2 τ p3 γ tt)
              (r_sem_ro_exp Γ e BOOL p1 γ))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction r.
  easy_rewrite_uip.
  exists r1, r2, r3.
  auto.  
Qed.

(* Lemma r_sem_ro_Case : forall Γ e1 e2 c1 c2 τ (w : Γ |~ (CASE e1 ==> c1 OR e2 ==> c2 END) : τ), exists p1 p2 p3 p4, *)
(*     r_sem_ro_exp Γ (CASE e1 ==> c1 OR e2 ==> c2 END) τ w *)
(*     =  (fun γ : sem_ctx Γ => *)
(*           pdom_lift snd *)
(*             (Case2 (r_sem_ro_exp Γ e1 BOOL p1 γ) (r_sem_ro_exp Γ e2 BOOL p3 γ) (r_sem_rw_exp Γ nil c1 τ p2 γ tt) *)
(*                (r_sem_rw_exp Γ nil c2 τ p4 γ tt))). *)
(* Proof. *)
(*   intros. *)
(*   dependent destruction w. *)
(*   dependent destruction r. *)
(*   easy_rewrite_uip. *)
(*   exists r1, r2, r3, r4. *)
(*   auto.   *)
(* Qed. *)

Lemma r_sem_ro_CaseList : forall Γ l τ (w : Γ |~ CaseList l : τ),
  exists f : ForallT (fun ec : exp * exp => ((Γ |~ fst ec : BOOL) * (Γ;;; nil ||~ snd ec : τ))%type) l,
    r_sem_ro_exp Γ (CaseList l) τ w
    = 


      (fun γ : sem_ctx Γ =>
         pdom_lift snd
           (pdom_case_list
              (ForallT_rect (exp * exp) (fun ec : exp * exp => ((Γ |~ fst ec : BOOL) * (Γ;;; nil ||~ snd ec : τ))%type)
                 (fun (l2 : list (exp * exp)) (_ : ForallT (fun ec : exp * exp => ((Γ |~ fst ec : BOOL) * (Γ;;; nil ||~ snd ec : τ))%type) l2) =>
                    list (pdom bool * pdom (unit * sem_datatype τ))) nil
                 (fun (x : exp * exp) (l2 : list (exp * exp)) (p : (Γ |~ fst x : BOOL) * (Γ;;; nil ||~ snd x : τ))
                      (_ : ForallT (fun ec : exp * exp => ((Γ |~ fst ec : BOOL) * (Γ;;; nil ||~ snd ec : τ))%type) l2)
                      (IHf : list (pdom bool * pdom (unit * sem_datatype τ))) =>
                    let (a, b) := p in (r_sem_ro_exp Γ (fst x) BOOL a γ, r_sem_rw_exp Γ nil (snd x) τ b γ tt) :: IHf) l f))).
  intros.
  dependent destruction w.
  dependent destruction r.
  easy_rewrite_uip.
  exists f.
  auto.
Qed.

Lemma r_sem_ro_While : forall Γ e c (w : Γ |~ (WHILE e DO c END) : UNIT), exists p p1,
    r_sem_ro_exp Γ (WHILE e DO c END) UNIT w =
      (fun γ : sem_ctx Γ =>
         pdom_lift snd
           (pdom_lift (fun x : unit => (x, tt))
              (pdom_while (fun _ : unit => r_sem_ro_exp Γ e BOOL p γ)
                 (fun d : unit => pdom_lift fst (r_sem_rw_exp Γ nil c UNIT p1 γ d)) tt))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction r.
  easy_rewrite_uip.
  exists r, r1.
  auto.  
Qed.


Definition dn_intro : forall X : Type, X -> (X -> False) -> False.
Proof.
  intro X.
  exact (fun x f => f x).
Defined.

Lemma r_sem_ctx_rewrite : forall Γ1 Γ2 e τ (w1 : Γ1 |~ e : τ) (w2 : Γ2 |~ e : τ) (p : Γ1 = Γ2) γ,
    r_sem_ro_exp _ _ _ w1 γ = r_sem_ro_exp _ _ _ w2 (tr (fun Γ => sem_ctx Γ) p γ).
Proof.
  intros.
  destruct p.
  simpl.
  rewrite (r_has_type_ro_unique _ _ _ w1 w2).
  auto.
Qed.

Lemma r_sem_rw_rw_ctx_rewrite : forall Γ Δ1 Δ2 e τ (w : Γ ;;; Δ1 ||~ e : τ) (p : Δ1 = Δ2) γ δ,
    r_sem_rw_exp _ _ _ _ w γ δ =
      pdom_lift (fun q => (tr (fun Δ => sem_ctx Δ) (eq_sym p) (fst q), (snd q)))
        (r_sem_rw_exp _ _ _ _ (tr (fun Δ => Γ ;;; Δ ||~ e : τ) p w) γ (tr (fun Δ => sem_ctx Δ) p δ)).
Proof.
  intros.
  destruct p.
  simpl.
  replace (fun q : sem_ctx Δ1 * sem_datatype τ => (fst q, snd q))
    with (fun q :sem_ctx Δ1 * sem_datatype τ => q).
  rewrite pdom_lift_id.
  reflexivity.
  apply dfun_ext.
  intros [a b]; simpl; reflexivity.
Qed.

Lemma r_sem_rw_ctx_rewrite : forall Γ1 Γ2 Δ e τ (w : Γ1 ;;; Δ ||~ e : τ) (p : Γ1 = Γ2) γ δ,
    r_sem_rw_exp _ _ _ _ w γ δ =
      (r_sem_rw_exp _ _ _ _ (tr (fun Γ => Γ ;;; Δ ||~ e : τ) p w) (tr (fun Δ => sem_ctx Δ) p γ) δ).
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Qed.

Definition app_assoc := 
  fun {A : Type} (l m n : list A) =>
    list_ind (fun l0 : list A => l0 ++ m ++ n = (l0 ++ m) ++ n)
      ((let H : n = n := eq_refl in
        (let H0 : m = m := eq_refl in
         (let H1 : A = A := eq_refl in (fun (_ : A = A) (_ : m = m) (_ : n = n) => eq_refl) H1) H0) H)
        :
        nil ++ m ++ n = (nil ++ m) ++ n)
      (fun (a : A) (l0 : list A) (IHl : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
         (let H : l0 ++ m ++ n = (l0 ++ m) ++ n := IHl in
          (let H0 : a = a := eq_refl in
           (let H1 : A = A := eq_refl in
            (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
               eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ m ++ n)) eq_refl) (f_equal (cons a) H4)) H1) H0) H)
         :
         (a :: l0) ++ m ++ n = ((a :: l0) ++ m) ++ n) l.

Lemma tr_f_equal : forall X Y (P : Y -> Type) (f : X -> Y) (x y : X) (p : x = y),
  forall t, tr P (f_equal f p) t = tr (fun x => P (f x)) p t.
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Defined.

Lemma eq_refl_left_unit : forall X (x z : X) (p : x = z), eq_trans (eq_refl x) p = p.
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Defined.

Lemma tr_constant_pair : forall X (P : X -> Type) C (x y : X) (p : x = y),
  forall c t, tr (fun x => C * P x)%type p (c, t) = (c, tr P p t).
Proof.
  intros.
  destruct p.
  simpl.
  reflexivity.
Defined.

Fixpoint app_assoc_tr (Γ1 Γ2 Γ3 : list datatype) : forall (γ1 : sem_ctx Γ1) (γ2 : sem_ctx Γ2) (γ3 : sem_ctx Γ3),
    tr _ (app_assoc Γ1 Γ2 Γ3) (γ1 ; (γ2 ; γ3)) = ((γ1 ; γ2) ; γ3).
Proof.
  intros.
  destruct Γ1.
  simpl.
  auto.
  simpl.
  destruct γ1.
  replace ((eq_trans eq_refl (f_equal (cons d) (app_assoc Γ1 Γ2 Γ3))))
    with (( (f_equal (cons d) (app_assoc Γ1 Γ2 Γ3)))).
  rewrite tr_f_equal.
  simpl.
  rewrite tr_constant_pair.
  apply lp.
  apply app_assoc_tr.
  rewrite eq_refl_left_unit.
  reflexivity.
Defined.

Lemma eq_sym_tr_inverse_left {X} (P : X -> Type) (x y : X) (e : x = y) :
  forall t, tr P (eq_sym e) (tr P e t) = t. 
Proof.
  intros.
  destruct e.
  simpl.
  reflexivity.
Defined.

Lemma eq_sym_tr_inverse_right {X} (P : X -> Type) (x y : X) (e : x = y) :
  forall t, tr P e (tr P (eq_sym e) t) = t. 
Proof.
  intros.
  destruct e.
  simpl.
  reflexivity.
Defined.


Lemma eq_sym_app_assoc_tr (Γ1 Γ2 Γ3 : list datatype) : forall (γ1 : sem_ctx Γ1) (γ2 : sem_ctx Γ2) (γ3 : sem_ctx Γ3), tr (fun Γ0 : list datatype => sem_ctx Γ0) (eq_sym (app_assoc Γ1 Γ2 Γ3)) ((γ1; γ2); γ3) = (γ1; (γ2; γ3)).
Proof.
  intros.
  pose proof (app_assoc_tr _ _ _ γ1 γ2 γ3).
  pose proof (lp _ _ (fun k => tr (fun Γ0 : list datatype => sem_ctx Γ0) (eq_sym (app_assoc Γ1 Γ2 Γ3)) k) _ _ H).
  simpl in H0.
  rewrite eq_sym_tr_inverse_left in H0.
  rewrite H0; reflexivity.
Defined.

Lemma pl : forall {X Y} (f g: X -> Y) (x : X), f = g -> f x = g x.
Proof.
  intros.
  rewrite H; auto.
Defined.

Lemma pdom_case_list_post_processing {X Y} (f : X -> Y) l :
  pdom_case_list (map (fun sc => (fst sc, pdom_lift f (snd sc))) l)
  = pdom_lift f (pdom_case_list l).
Proof.
  apply sig_eq.
  apply pred_ext; intros.
  +
    destruct a.
    

    ++
      (* when bot *)
      apply pdom_lift_bot_1.
      apply pdom_case_list_bot_1.
      intro.
      assert (pdom_is_empty (pdom_case_list (map (fun sc : pdom bool * pdom X => (fst sc, pdom_lift f (snd sc))) l))).
      apply pdom_case_list_empty_1.
      apply pdom_case_list_empty_2 in H0.
      apply Exists_exists in H0.
      apply Exists_exists.
      destruct H0.
      destruct x as [e c].
      exists (e, pdom_lift f c).
      simpl.
      split.
      apply in_map_iff.
      destruct H0.
      exists (e, c).
      simpl; split; auto.
      destruct H0.
      destruct H1.
      left; auto.
      simpl in H1; destruct H1.
      right; auto.
      split; auto.
      apply pdom_lift_empty_1; auto.
      apply (H1 _ H).

      apply pdom_case_list_bot_2 in H.
      destruct H.
      apply Exists_exists in H.
      left.
      apply Exists_exists.
      destruct H.
      destruct x.
      destruct H.
      apply in_map_iff in H.
      destruct H.
      exists x.
      destruct H; split; auto.
      injection H; intros.
      destruct H0.
      simpl in H0.
      rewrite <- H3 in H0; split; auto.
      simpl in H4.
      rewrite <- H2 in H4.
      apply pdom_lift_bot_2 in H4.
      auto.

      right.
      pose proof (Forall_to_forall _ _ H).
      clear H.
      apply Forall_forall.
      intros [e c].
      pose proof (H0 (e, (pdom_lift f c))).
      simpl in H.
      intro.
      assert (In (e, pdom_lift f c) (map (fun sc : pdom bool * pdom X => (fst sc, pdom_lift f (snd sc))) l)).
      apply in_map_iff.
      exists (e, c).
      simpl.
      split; auto.
      apply H in H2.
      simpl; auto.

    ++
      (* when total *)
      assert (~pdom_is_empty (pdom_case_list l)) as n.
      {
        intro.
        assert (pdom_is_empty (pdom_case_list (map (fun sc : pdom bool * pdom X => (fst sc, pdom_lift f (snd sc))) l))).
        apply pdom_case_list_empty_1.
        apply pdom_case_list_empty_2 in H0.
        apply Exists_exists in H0.
        apply Exists_exists.
        destruct H0.
        destruct x as [e c].
        exists (e, pdom_lift f c).
        simpl.
        split.
        apply in_map_iff.
        destruct H0.
        exists (e, c).
        simpl; split; auto.
        destruct H0.
        destruct H1.
        left; auto.
        simpl in H1; destruct H1.
        right; auto.
        split; auto.
        apply pdom_lift_empty_1; auto.
        apply (H1 _ H).
      }
      apply pdom_lift_total_1.
      apply pdom_case_list_total_2 in H.
      apply Exists_exists in H.
      destruct H.
      destruct H.
      apply in_map_iff in H.
      destruct H.
      destruct H.
      destruct x.
      destruct H0.
      injection H; intros.
      destruct x0.
      simpl in H, H0, H2, H3, H4.
      induction H4.
      rewrite <- H3 in H2.
      apply pdom_lift_total_2 in H2.
      destruct H2.
      exists x.
      split.
      apply pdom_case_list_total_1.
      auto.
      apply Exists_exists.
      exists (p, p0); split; auto.
      simpl; split; destruct H2; auto.
      destruct H2; auto.

  +
    assert (~ pdom_is_empty (pdom_case_list (map (fun sc : pdom bool * pdom X => (fst sc, pdom_lift f (snd sc))) l))).
    {
      intro.
      assert (pdom_is_empty (pdom_lift f (pdom_case_list l))).
      apply pdom_lift_empty_1.
      apply pdom_case_list_empty_1.
      apply pdom_case_list_empty_2 in H0.
      apply Exists_exists.
      apply Exists_exists in H0.
      destruct H0.
      destruct H0.
      apply in_map_iff in H0.
      destruct H0.
      exists x0.
      destruct H0.
      split; auto.
      destruct H1.
      rewrite <- H0 in H1.
      simpl in H1.
      left; auto.
      right.
      rewrite <- H0 in H1.
      simpl in H1.
      destruct H1; split; auto.
      apply pdom_lift_empty_2 in H3.
      auto.
      apply (H1 _ H).
    }
    
    destruct a.
    apply pdom_case_list_bot_1.
    auto.
    apply pdom_lift_bot_2 in H.
    apply pdom_case_list_bot_2 in H.
    destruct H.
    apply Exists_exists in H.
    left; apply Exists_exists.
    destruct H.
    destruct H.
    destruct H1.
    destruct x.
    exists (s, pdom_lift f s0).
    simpl; split; auto.
    apply in_map_iff.
    exists (s, s0); auto.
    split; auto.
    exists ⊥; auto.

    pose proof (Forall_to_forall _ _  H).
    right; apply Forall_forall.
    intros.
    apply in_map_iff in H2.
    destruct H2.
    pose proof (H1 x0).
    assert (In x0 l).
    destruct H2; auto.
    apply H3 in H4.
    destruct H2.
    destruct x.
    simpl.
    injection H2; intros.
    rewrite <- H7.
    auto.

    apply pdom_case_list_total_1.
    auto.
    apply pdom_lift_total_2 in H.
    destruct H.
    destruct H.
    apply Exists_exists.
    apply pdom_case_list_total_2 in H.
    apply Exists_exists in H.
    destruct H.

    destruct H.
    destruct H2.
    destruct x0.
    exists (s, pdom_lift f s0).
    simpl.
    split; auto.
    apply in_map_iff.
    exists (s, s0); auto.
    simpl in H2, H3.
    split; auto.
    exists (total x).
    split; auto.
    simpl.
    rewrite H1; auto.
Defined.


Lemma pdom_lifted_monotone {X Y} (f : X -> Y) : pdom_is_monotone (pdom_lift f).
Proof.
  intros x y o.
  destruct o.
  left.
  rewrite H; auto.
  destruct H.
  destruct H0.
  right; split; auto.
  apply pdom_lift_bot_1; auto.
  left; auto.
  apply pdom_lift_empty_1; auto.
  right; split; auto.
  apply pdom_lift_bot_1; auto.
  right; auto.
  intros z m.
  destruct z.
  right; auto.
  left.
  apply pdom_lift_total_2 in m.
  destruct m.
  destruct H1.
  pose proof (H0 _ H1).
  destruct H3.
  apply pdom_lift_total_1.
  exists x0; split; auto.
  contradict (flat_bot_neq_total _ H3).
Defined.

Lemma r_sem_move_readonly_while X Y Z (f : X -> Z) (g : Y -> Z) x y (b1 : X -> pdom bool) (c1 : X -> pdom X) (b2 : Y -> pdom bool) (c2 : Y -> pdom Y) :
  (forall n, 
      pdom_lift f (pdom_fun_bot_chain (pdom_W b1 c1) (pdom_W_monotone b1 c1) n x) = 
        pdom_lift g (pdom_fun_bot_chain (pdom_W b2 c2) (pdom_W_monotone b2 c2) n y)) ->
  pdom_lift f (pdom_while b1 c1 x) = pdom_lift g (pdom_while b2 c2 y).
Proof.
  intro.

  destruct (lem (pdom_is_empty  (pdom_while b1 c1 x)));
    destruct (lem (pdom_is_empty ((pdom_while b2 c2 y)))).
  assert (pdom_lift f (pdom_while b1 c1 x) = pdom_empty _ ).
  apply pdom_is_empty_is_empty.
  apply pdom_lift_empty_1; auto.
  assert (pdom_lift g (pdom_while b2 c2 y) = pdom_empty _ ).
  apply pdom_is_empty_is_empty.
  apply pdom_lift_empty_1; auto.
  rewrite H2, H3; auto.

  contradict H1.
  unfold pdom_while.
  unfold pdom_fun_lfp.
  apply pdom_fun_chain_empty_1.
  apply pdom_fun_chain_empty_2 in H0.
  destruct H0.
  pose proof (pdom_lift_empty_1 f _ H0).
  rewrite H in H1.
  apply pdom_lift_empty_2 in H1.
  exists x0; auto.

  contradict H0.
  unfold pdom_while.
  unfold pdom_fun_lfp.
  apply pdom_fun_chain_empty_1.
  apply pdom_fun_chain_empty_2 in H1.
  destruct H1.
  pose proof (pdom_lift_empty_1 g _ H0).
  rewrite <- H in H1.
  apply pdom_lift_empty_2 in H1.
  exists x0; auto.

  rename H0 into h1.
  rename H1 into h2.
  
  apply sig_eq.
  apply pred_ext; intros p m.
  +
    destruct p.
    apply pdom_lift_bot_2 in m.
    unfold pdom_while in m.
    apply pdom_lift_bot_1.
    unfold pdom_while.
    unfold pdom_fun_lfp.
    apply pdom_fun_chain_bot_1.
    intro.
    unfold pdom_while in m.
    unfold pdom_fun_lfp in m.
    pose proof (pdom_fun_chain_bot_2 _ _ _ m n).
    pose proof (H n).
    apply (pdom_lift_bot_2 g).
    rewrite <- H1.
    apply pdom_lift_bot_1.
    auto.
    apply pdom_lift_total_1.
    apply pdom_lift_total_2 in m.
    destruct m.
    destruct H0.
    unfold pdom_while in H0.
    unfold pdom_fun_lfp in H0.
    unfold pdom_fun_chain_sup in H0.
    apply pdom_chain_membership_2 in H0.
    destruct H0.
    assert (total z ∈ pdom_lift g (pdom_fun_bot_chain (pdom_W b2 c2) (pdom_W_monotone b2 c2) x1 y)).
    rewrite <- H.
    apply pdom_lift_total_1.
    exists x0; auto.
    apply pdom_lift_total_2 in H2.
    destruct H2.
    exists x2.
    split.
    unfold pdom_while.
    unfold pdom_fun_lfp.
    unfold pdom_fun_chain_sup.
    apply pdom_chain_membership_1.
    split.
    exact h2.
    exists x1.
    destruct H2; auto.
    destruct H2; auto.

  +
    destruct p.
    apply pdom_lift_bot_2 in m.
    unfold pdom_while in m.
    apply pdom_lift_bot_1.
    unfold pdom_while.
    unfold pdom_fun_lfp.
    apply pdom_fun_chain_bot_1.
    intro.
    unfold pdom_while in m.
    unfold pdom_fun_lfp in m.
    pose proof (pdom_fun_chain_bot_2 _ _ _ m n).
    pose proof (H n).
    apply (pdom_lift_bot_2 f).
    rewrite  H1.
    apply pdom_lift_bot_1.
    auto.
    apply pdom_lift_total_1.
    apply pdom_lift_total_2 in m.
    destruct m.
    destruct H0.
    unfold pdom_while in H0.
    unfold pdom_fun_lfp in H0.
    unfold pdom_fun_chain_sup in H0.
    apply pdom_chain_membership_2 in H0.
    destruct H0.
    assert (total z ∈ pdom_lift f (pdom_fun_bot_chain (pdom_W b1 c1) (pdom_W_monotone b1 c1) x1 x)).
    rewrite H.
    apply pdom_lift_total_1.
    exists x0; auto.
    apply pdom_lift_total_2 in H2.
    destruct H2.
    exists x2.
    split.
    unfold pdom_while.
    unfold pdom_fun_lfp.
    unfold pdom_fun_chain_sup.
    apply pdom_chain_membership_1.
    split.
    exact h1.
    exists x1.
    destruct H2; auto.
    destruct H2; auto.
Qed.

Lemma tedious_eq {Γ Δ} : forall (γ1 γ2 : sem_ctx Γ) (δ1 δ2 : sem_ctx Δ), γ1 = γ2 -> δ1 = δ2 -> (γ1 ; δ1) = (γ2 ; δ2).
Proof.
  intros.
  destruct H.
  destruct H0.
  reflexivity.
Defined.


Fixpoint assign_concat_fst' Δ Δ' τ k (a :assignable Δ τ k) x δ δ' {struct a} : 
  (update k x δ a ; δ') = (update k x (δ; δ') (assignable_push_back Δ Δ' τ k a)).
Proof.
  dependent destruction a.
  simpl.
  destruct δ.
  simpl.
  reflexivity.
  destruct δ.
  replace (tedious_prod_sem (@cons datatype σ Δ) Δ'
             (@pair (sem_ctx (@cons datatype σ Δ)) (sem_ctx Δ')
                (@update τ (@cons datatype σ Δ) (S k) x (@pair (sem_datatype σ) (sem_ctx Δ) s s0)
                   (assignable_S Δ τ σ k a)) δ'))
    with
    (s, (update k x s0 a; δ')).

  simpl.
  apply lp.
  rewrite assign_concat_fst'.
  destruct a; auto.
  simpl.
  destruct a; auto.
Defined.

Lemma assign_concat_fst : 
  forall Δ Δ' τ k (a0 :assignable Δ τ k) (a : assignable (Δ ++ Δ') τ k) a1 δ δ',
    (update k a1 δ a0 ; δ') = (update k a1 (δ; δ') a).
Proof.
  intros.
  rewrite (assign_concat_fst' Δ Δ' τ k a0).
  apply lp.
  apply assignable_unique. 
Defined.

Fixpoint r_sem_move_readonly  Γ Δ Δ' e τ (w1 : Γ ;;; (Δ ++ Δ') ||~ e : τ) (w2 : (Δ' ++ Γ) ;;; Δ ||~ e : τ) :
  forall γ δ δ', r_sem_rw_exp _ _ _ _ w1 γ (δ ; δ') =
                   pdom_lift (fun y => ((fst y; δ'), snd y)) (r_sem_rw_exp _ _ _ _ w2 (δ'; γ) δ).
Proof.
  intros.
  dependent destruction w1;
    dependent destruction w2;
    easy_rewrite_uip; try simpl in p0;
    try induction (r_has_type_ro_unique _ _ _ r r0);
    try (rewrite pdom_lift_comp; simpl; reflexivity);
    try (rewrite pdom_lift_comp;
         simpl;
         apply lp;
         rewrite (r_sem_ctx_rewrite _ _ _ _ r0 r (app_assoc Δ Δ' Γ));
         apply lp;
         apply eq_sym;
         apply app_assoc_tr).
  
  unfold pdom_bind.
  rewrite (r_sem_move_readonly _ _ _ _ _ w1_1 w2_1).
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  simpl.
  replace (fun y : sem_ctx Δ * unit => r_sem_rw_exp Γ (Δ ++ Δ') c2 τ w1_2 γ (fst y; δ'))
    with (fun y : sem_ctx Δ * unit =>
            pdom_lift (fun y => ((fst y; δ'), snd y)) (r_sem_rw_exp _ _ _ _ w2_2 (δ'; γ) (fst y))).
  simpl.
  rewrite <- pdom_lift_comp.
  rewrite pdom_mult_natural.
  apply lp.
  apply lp.
  apply lp.
  reflexivity.
  apply dfun_ext.
  intro.
  rewrite (r_sem_move_readonly _ _ _ _ _ w1_2 w2_2).
  reflexivity.

  assert (τ = τ0).
  assert ( (Δ ++ Δ' ++ Γ) |~ e : τ).
  rewrite app_assoc; auto.
  apply (r_has_type_ro_unambiguous _ _ _ _ H r0).
  induction H.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  simpl.
  replace (fun y : sem_datatype τ => (update k y (δ; δ') a, tt)) with
    (fun y : sem_datatype τ => ((update k y δ a0; δ'), tt)).
  apply lp.
  rewrite (r_sem_ctx_rewrite _ _ _ _ r0 r (app_assoc Δ Δ' Γ)).
  apply lp, eq_sym, app_assoc_tr.
  apply dfun_ext; intro.
  assert (((update k a1 δ a0; δ') = (update k a1 (δ; δ') a))).
  apply assign_concat_fst.

  rewrite H; reflexivity.

  

  
  rewrite pdom_lift_comp.
  simpl.
  unfold pdom_bind.
  rewrite pdom_lift_comp.
  simpl.
  rewrite pdom_lift_comp.
  simpl.
  assert (σ = σ0).
  assert ( (Δ ++ Δ' ++ Γ) |~ e : σ).
  rewrite app_assoc; auto.
  apply (r_has_type_ro_unambiguous _ _ _ _ H r0).
  induction H.
  rewrite (r_sem_ctx_rewrite _ _ _ _ r0 r (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ctx Γ0) (app_assoc Δ Δ' Γ) (δ; (δ'; γ)))
    with  ((δ; δ'); γ) by (apply eq_sym, app_assoc_tr).
  pose proof (r_sem_move_readonly Γ (σ::Δ) Δ' _ _ w1 w2 γ).

  replace (fun y : sem_datatype σ => r_sem_rw_exp Γ (σ :: Δ ++ Δ') c τ w1 γ (y, (δ; δ')))
    with ((fun y : sem_datatype σ =>
             pdom_lift (fun y : sem_ctx (σ :: Δ) * sem_datatype τ => ((fst y; δ'), snd y))
               (r_sem_rw_exp (Δ' ++ Γ) (σ :: Δ) c τ w2 (δ'; γ) (y, δ)))).
  rewrite <- pdom_lift_comp.
  rewrite pdom_mult_natural.
  rewrite pdom_lift_comp.
  simpl.
  rewrite app_assoc_tr.
  apply pl.
  apply lp.
  apply dfun_ext.
  intros [[a b] d].
  simpl.
  reflexivity.
  apply dfun_ext.
  intro.
  rewrite <- (H (a, δ) δ').
  simpl.
  reflexivity.

  unfold pdom_bind.

  rewrite (r_sem_ctx_rewrite _ _ _ _ r0 r (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ctx Γ0) (app_assoc Δ Δ' Γ) (δ; (δ'; γ)))
    with  ((δ; δ'); γ) by (apply eq_sym, app_assoc_tr).
  rewrite (r_sem_move_readonly Γ _ _ _ _ w1_1 w2_1 γ ).
  rewrite (r_sem_move_readonly Γ _ _ _ _ w1_2 w2_2 γ).
  replace
    ((fun b : bool =>
        if b
        then
          pdom_lift (fun y : sem_ctx Δ * sem_datatype τ => ((fst y; δ'), snd y))
            (r_sem_rw_exp (Δ' ++ Γ) Δ c1 τ w2_1 (δ'; γ) δ)
        else
          pdom_lift (fun y : sem_ctx Δ * sem_datatype τ => ((fst y; δ'), snd y))
            (r_sem_rw_exp (Δ' ++ Γ) Δ c2 τ w2_2 (δ'; γ) δ)))
    with
    
    ((fun b : bool =>
        pdom_lift (fun y : sem_ctx Δ * sem_datatype τ => ((fst y; δ'), snd y))
          (if b
           then
             
             (r_sem_rw_exp (Δ' ++ Γ) Δ c1 τ w2_1 (δ'; γ) δ)
           else
             (r_sem_rw_exp (Δ' ++ Γ) Δ c2 τ w2_2 (δ'; γ) δ)))).
  rewrite <- pdom_lift_comp.
  rewrite pdom_mult_natural.
  rewrite app_assoc_tr.
  reflexivity.
  apply dfun_ext; intros.
  destruct a; simpl; reflexivity.


  (* (* case *) *)
  (* rewrite (r_sem_ctx_rewrite _ _ _ _ r1 r (app_assoc Δ Δ' Γ)). *)
  (* rewrite (r_sem_ctx_rewrite _ _ _ _ r2 r0 (app_assoc Δ Δ' Γ)). *)
  (* replace  (tr (fun Γ0 : list datatype => sem_ctx Γ0) (app_assoc Δ Δ' Γ) (δ; (δ'; γ))) *)
  (*   with  ((δ; δ'); γ) by (apply eq_sym, app_assoc_tr). *)
  (* rewrite (r_sem_move_readonly Γ _ _ _ _ w1_1 w2_1 γ ). *)
  (* rewrite (r_sem_move_readonly Γ _ _ _ _ w1_2 w2_2 γ). *)
  (* rewrite app_assoc_tr. *)
  (* apply Case2_post_processing. *)

  {
    rewrite <- pdom_case_list_post_processing.
    apply lp.
    simpl.
    clear l0 l2.
    dependent induction f.
    simpl.
    dependent induction f0.
    simpl.
    reflexivity.
    simpl.
    destruct p.
    dependent destruction f0.
    simpl.
    destruct p.
    simpl.
    rewrite (IHf f0).
    apply pl.
    apply lp.
    rewrite (r_sem_move_readonly Γ _ _ _ _ r0 r2).
    rewrite (r_sem_ctx_rewrite _ _ _ _ r1 r (app_assoc Δ Δ' Γ)).
    rewrite app_assoc_tr.
    reflexivity.
  }

  
  
  
  rewrite pdom_lift_comp.
  simpl.
  apply r_sem_move_readonly_while.
  intros.
  generalize δ, δ'.
  induction n.
  intros.
  simpl.
  unfold pdom_fun_bot.
  apply sig_eq.
  simpl.
  apply pred_ext.
  intros.
  destruct H.
  destruct H.
  exists ⊥; split; auto.
  simpl.
  rewrite <- H in H0.
  simpl in H0.
  auto.
  intros.
  destruct H.
  destruct H.
  rewrite <- H in H0.
  simpl in H0.
  exists ⊥; split; simpl; auto.

  intros.
  simpl.
  simpl in IHn.
  unfold pdom_W at 1.
  unfold pdom_bind.
  rewrite <- pdom_mult_natural.
  rewrite pdom_lift_comp.
  assert (forall Y Z (f : Y -> Z) (g1 g2 :  Y),
             (fun b : bool => f (if b then g1 else g2)) = fun b : bool => if b then f g1 else f g2).
  {
    intros.
    apply dfun_ext; intro b; destruct b; auto.
  }
  rewrite H.
  rewrite <- pdom_mult_natural.
  rewrite pdom_lift_comp.

  unfold pdom_W at 2.
  unfold pdom_bind.
  rewrite <- pdom_mult_natural.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  rewrite H.
  rewrite <- pdom_mult_natural.
  rewrite pdom_lift_comp.
  apply lp.
  rewrite (r_sem_ctx_rewrite _ _ _ _ r0 r (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ctx Γ0) (app_assoc Δ Δ' Γ) (δ0; (δ'0; γ)))
    with  ((δ0; δ'0); γ) by (apply eq_sym, app_assoc_tr).
  rewrite app_assoc_tr.
  apply pl.
  apply lp.
  apply dfun_ext.
  intro.
  destruct a.
  apply lp.
  simpl.
  simpl in IHn.
  assert (
      (fun y : sem_ctx (Δ ++ Δ') * unit =>
         pdom_lift (fun x : sem_ctx (Δ ++ Δ') => (x, tt))
           (pdom_fun_bot_chain
              (pdom_W (fun d : sem_ctx (Δ ++ Δ') => r_sem_ro_exp ((Δ ++ Δ') ++ Γ) e BOOL r (d; γ))
                 (fun d : sem_ctx (Δ ++ Δ') => pdom_lift fst (r_sem_rw_exp Γ (Δ ++ Δ') c UNIT w1 γ d)))
              (pdom_W_monotone (fun d : sem_ctx (Δ ++ Δ') => r_sem_ro_exp ((Δ ++ Δ') ++ Γ) e BOOL r (d; γ))
                 (fun d : sem_ctx (Δ ++ Δ') => pdom_lift fst (r_sem_rw_exp Γ (Δ ++ Δ') c UNIT w1 γ d))) n
              (fst y))) =
        fun y : sem_ctx (Δ ++ Δ') * unit =>
          pdom_lift (fun y0 : sem_ctx Δ => ((y0; snd_app (fst y)), tt))
            (pdom_fun_bot_chain
               (pdom_W (fun d : sem_ctx Δ => r_sem_ro_exp (Δ ++ Δ' ++ Γ) e BOOL r0 (d; (snd_app (fst y); γ)))
                  (fun d : sem_ctx Δ => pdom_lift fst (r_sem_rw_exp (Δ' ++ Γ) Δ c UNIT w2 (snd_app (fst y); γ) d)))
               (pdom_W_monotone
                  (fun d : sem_ctx Δ => r_sem_ro_exp (Δ ++ Δ' ++ Γ) e BOOL r0 (d; (snd_app (fst y); γ)))
                  (fun d : sem_ctx Δ => pdom_lift fst (r_sem_rw_exp (Δ' ++ Γ) Δ c UNIT w2 (snd_app (fst y); γ) d))) n
               (fst_app (fst y)))).
  

  apply dfun_ext; intro y.
  pose proof (IHn (fst_app (fst y)) (snd_app (fst y))).
  rewrite <- tedious_equiv_2 in H0.
  simpl.
  auto.
  simpl.
  simpl in H0.
  rewrite H0.
  clear H0.
  rewrite (r_sem_move_readonly Γ _ _ _ _ w1 w2 γ).
  rewrite pdom_lift_comp.
  simpl.
  assert  ((fun y : sem_ctx Δ * unit =>
              pdom_lift (fun y0 : sem_ctx Δ => ((y0; snd_app (fst y; δ'0)), tt))
                (pdom_fun_bot_chain
                   (pdom_W (fun d : sem_ctx Δ => r_sem_ro_exp (Δ ++ Δ' ++ Γ) e BOOL r0 (d; (snd_app (fst y; δ'0); γ)))
                      (fun d : sem_ctx Δ =>
                         pdom_lift fst (r_sem_rw_exp (Δ' ++ Γ) Δ c UNIT w2 (snd_app (fst y; δ'0); γ) d)))
                   (pdom_W_monotone
                      (fun d : sem_ctx Δ => r_sem_ro_exp (Δ ++ Δ' ++ Γ) e BOOL r0 (d; (snd_app (fst y; δ'0); γ)))
                      (fun d : sem_ctx Δ =>
                         pdom_lift fst (r_sem_rw_exp (Δ' ++ Γ) Δ c UNIT w2 (snd_app (fst y; δ'0); γ) d))) n
                   (fst_app (fst y; δ'0)))) =
             (fun y : sem_ctx Δ * unit =>
                pdom_lift (fun y0 : sem_ctx Δ => ((y0;  δ'0), tt))
                  (pdom_fun_bot_chain
                     (pdom_W (fun d : sem_ctx Δ => r_sem_ro_exp (Δ ++ Δ' ++ Γ) e BOOL r0 (d; (δ'0; γ)))
                        (fun d : sem_ctx Δ =>
                           pdom_lift fst (r_sem_rw_exp (Δ' ++ Γ) Δ c UNIT w2 (δ'0; γ) d)))
                     (pdom_W_monotone
                        (fun d : sem_ctx Δ => r_sem_ro_exp (Δ ++ Δ' ++ Γ) e BOOL r0 (d; (δ'0; γ)))
                        (fun d : sem_ctx Δ =>
                           pdom_lift fst (r_sem_rw_exp (Δ' ++ Γ) Δ c UNIT w2 (δ'0; γ) d))) n
                     (fst y)))).

  apply dfun_ext.
  intros.
  unfold snd_app.
  rewrite tedious_equiv_1.
  unfold fst_app.
  rewrite tedious_equiv_1.
  auto.
  simpl in H0.
  simpl.
  rewrite H0.
  auto.

  rewrite pdom_unit_natural.
  rewrite pdom_unit_natural.
  auto.
Qed.


Fixpoint sem_ro_r_sem_ro Γ e τ (w1 : Γ |- e : τ) w2 {struct w1} : sem_ro_exp Γ e τ w1 = r_sem_ro_exp Γ e τ w2
with sem_rw_r_sem_rw Γ Δ e τ (w1 : Γ ;;; Δ ||- e : τ) w2 {struct w1}: sem_rw_exp Γ Δ e τ w1 = r_sem_rw_exp Γ Δ e τ w2.
Proof.
  +
    dependent destruction w1.
    dependent destruction h.
    simpl.
    easy_rewrite_uip.
    simpl in h.
    rewrite <- (sem_ro_r_sem_ro _ _ _ h w2). 
    apply dfun_ext; intro.
    rewrite pdom_lift_comp.
    simpl.
    rewrite pdom_lift_id.
    auto.

    rewrite r_sem_ro_Seq.    
    easy_rewrite_uip.
    rewrite (sem_rw_r_sem_rw _ _ _ _ h1 (r_has_type_ro_inv_Seq_1 Γ c1 c2 τ w2) ).
    rewrite (sem_rw_r_sem_rw _ _ _ _ h2 (r_has_type_ro_inv_Seq_2 Γ c1 c2 τ w2) ).
    auto.

    contradict (assignable_absurd _ _ a).

    destruct (r_sem_ro_Newvar _ _ _ _ w2) as [σ' [p [p1 eq]]].
    induction (has_type_ro_r_has_type_ro_unambiguous _ _ _ _ h p).
    rewrite eq.
    simpl in h.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ h p).
    rewrite (sem_rw_r_sem_rw _ _ _ _ h1 p1).
    reflexivity.

    destruct (r_sem_ro_Cond _ _ _ _ _ w2) as [p1 [p2 [p3 eq]]].
    rewrite eq.
    simpl in h1.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ h1 p1).
    rewrite (sem_rw_r_sem_rw _ _ _ _ h2 p2).
    rewrite (sem_rw_r_sem_rw _ _ _ _ h3 p3).
    reflexivity.


    (* destruct (r_sem_ro_Case _ _ _ _ _ _ w2) as [p1 [p2 [p3 [p4 eq]]]]. *)
    (* rewrite eq. *)
    (* simpl in h1, h3. *)
    (* easy_rewrite_uip. *)
    (* rewrite (sem_ro_r_sem_ro _ _ _ h1 p1). *)
    (* rewrite (sem_ro_r_sem_ro _ _ _ h3 p3). *)
    (* rewrite (sem_rw_r_sem_rw _ _ _ _ h2 p2). *)
    (* rewrite (sem_rw_r_sem_rw _ _ _ _ h4 p4). *)
    (* reflexivity. *)
    {
      destruct (r_sem_ro_CaseList _ _ _ w2) as [ff eq].
      rewrite eq.
      easy_rewrite_uip.
      apply dfun_ext; intro.
      apply lp.
      apply lp.
      clear eq.
      clear l0 w2.
      dependent induction f.
      dependent destruction ff.
      simpl. 
      reflexivity.    
      dependent destruction ff.
      simpl.
      simpl in p, p0.
      destruct p, p0; simpl.
      rewrite (IHf ff).
      apply pl.
      rewrite (sem_ro_r_sem_ro _ _ _ h r).
      rewrite (sem_rw_r_sem_rw _ _ _ _ h0 r0).
      reflexivity.
    }
    
    destruct (r_sem_ro_While _ _ _  w2) as [p [p1 eq]].
    rewrite eq.
    simpl in h. 
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ h p).
    rewrite (sem_rw_r_sem_rw _ _ _ _ h1 p1).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    auto.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1 w2).
    reflexivity.


    dependent destruction w2.
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.
    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_r_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ w1 w2).
    reflexivity.

  +
    dependent destruction w1.
    dependent destruction h.
    easy_rewrite_uip.
    apply dfun_ext; intros.
    apply dfun_ext; intros.
    pose proof (sem_rw_r_sem_rw _ _ _ _ h (has_type_rw_r_has_type_rw _ _ _ _ h)).
    rewrite H.
    rewrite pdom_lift_comp.
    pose proof (r_sem_move_readonly Γ nil Δ).
    simpl in H0.
    rewrite <- (H0 _ _ w2 (has_type_rw_r_has_type_rw (Δ ++ Γ) nil e τ h)).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h0 r).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h0 r).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h r).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h r).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h r).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h1 r1).
    rewrite (sem_ro_r_sem_ro  _ _ _ h2 r2).
    reflexivity.

    dependent destruction w2.
    dependent destruction r.    
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro  _ _ _ h r).
    reflexivity.

    
    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_rw_r_sem_rw _ _ _ _ w1_1 w2_1).
    rewrite (sem_rw_r_sem_rw _ _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    induction (has_type_ro_r_has_type_ro_unambiguous _ _ _ _ h r).
    rewrite (sem_ro_r_sem_ro _ _ _ h r).
    induction (assignable_unique _ _ _ a a0).
    reflexivity.

    dependent destruction w2.
    induction (has_type_ro_r_has_type_ro_unambiguous _ _ _ _ h r).
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ h r).
    rewrite (sem_rw_r_sem_rw _ _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ h r).
    rewrite (sem_rw_r_sem_rw _ _ _ _ w1_1 w2_1).
    rewrite (sem_rw_r_sem_rw _ _ _ _ w1_2 w2_2).
    reflexivity.

    (* dependent destruction w2. *)
    (* easy_rewrite_uip. *)
    (* rewrite (sem_ro_r_sem_ro _ _ _ h r). *)
    (* rewrite (sem_ro_r_sem_ro _ _ _ h0 r0). *)
    (* rewrite (sem_rw_r_sem_rw _ _ _ _ w1_1 w2_1). *)
    (* rewrite (sem_rw_r_sem_rw _ _ _ _ w1_2 w2_2). *)
    (* reflexivity. *)

    
    dependent destruction w2.
    easy_rewrite_uip.
    apply dfun_ext; intros.
    apply dfun_ext; intros.
    apply lp.
    clear l0 l2.
    dependent induction f.
    dependent destruction f0.
    simpl.
    reflexivity.
    dependent destruction f0.
    destruct p, p0.
    simpl.
    rewrite (IHf f0).
    apply pl.
    rewrite (sem_ro_r_sem_ro _ _ _ h r).
    rewrite (sem_rw_r_sem_rw _ _ _ _ h0 r0).
    reflexivity.
    
    
    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_r_sem_ro _ _ _ h r).
    rewrite (sem_rw_r_sem_rw _ _ _ _ w1 w2).
    reflexivity.
Qed.

(* semantics is unique *)
Lemma sem_ro_exp_unique Γ e τ (w1 w2 : Γ |- e : τ): sem_ro_exp Γ e τ w1 = sem_ro_exp Γ e τ w2.
Proof.
  rewrite (sem_ro_r_sem_ro _ _ _ w1 (has_type_ro_r_has_type_ro _ _ _ w1)).
  rewrite (sem_ro_r_sem_ro _ _ _ w2 (has_type_ro_r_has_type_ro _ _ _ w2)).
  apply lp.
  apply r_has_type_ro_unique.
Qed.


Lemma sem_rw_exp_unique Γ Δ e τ (w1 w2 : Γ ;;; Δ ||- e : τ) : sem_rw_exp Γ Δ e τ w1 = sem_rw_exp Γ Δ e τ w2.
Proof.
  rewrite (sem_rw_r_sem_rw _ _ _ _ w1 (has_type_rw_r_has_type_rw _ _ _ _ w1)).
  rewrite (sem_rw_r_sem_rw _ _ _ _ w2 (has_type_rw_r_has_type_rw _ _ _ _ w2)).
  apply lp.
  apply r_has_type_rw_unique.
Qed.

Fixpoint r_has_type_ro_add_auxiliaries Γ e τ (w : Γ |~ e : τ) : forall Γ', (Γ ++ Γ') |~ e : τ
with r_has_type_rw_add_auxiliaries Γ Δ e τ (w : Γ ;;; Δ ||~ e : τ) : forall Γ', (Γ ++ Γ') ;;; Δ ||~ e : τ.
Proof.
  +
    
    intros.
    dependent destruction w.

    (* commands *)
    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ').
    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ').
    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ').
    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ').
    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ').
    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ').
    (* constructor. *)
    (* exact (r_has_type_rw_add_auxiliaries _ _ _ _ r Γ'). *)

    (* variables *)
    constructor.

    simpl.
    pose proof (r_has_type_ro_add_auxiliaries _ _ _ w Γ').
    exact (r_has_type_ro_Var_S (Γ++ Γ') σ τ k H).

    (* constants *)
    constructor.
    constructor.
    constructor.
    constructor.

    (* unary *)
    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w Γ').
    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w Γ').
    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (r_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (r_has_type_ro_add_auxiliaries _ _ _ w Γ').
  +

    intros.
    dependent destruction w.
    
    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').

    constructor.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ w1 Γ').
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ w2 Γ').

    apply (r_has_type_rw_Assign _ _ _ τ).
    exact a.
    induction (eq_sym (app_assoc Δ Γ Γ')).     
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').
    

    apply (r_has_type_rw_Newvar _ _ _ _ σ).
    induction (eq_sym (app_assoc Δ Γ Γ')).     
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ w Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ w1 Γ').
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ w2 Γ').

    
    (* constructor. *)
    (* induction (eq_sym (app_assoc Δ Γ Γ')).  *)
    (* exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ'). *)
    (* exact (r_has_type_rw_add_auxiliaries _ _ _ _ w1 Γ'). *)
    (* induction (eq_sym (app_assoc Δ Γ Γ')).  *)
    (* exact (r_has_type_ro_add_auxiliaries _ _ _ r0 Γ'). *)
    (* exact (r_has_type_rw_add_auxiliaries _ _ _ _ w2 Γ'). *)

    constructor.
    apply l0.
    clear l0.
    dependent induction f.
    apply ForallT_nil.
    apply ForallT_cons.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    split.
    destruct p.
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').
    destruct p.
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ r0 Γ').
    exact (IHf Γ').

    
    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (r_has_type_ro_add_auxiliaries _ _ _ r Γ').
    exact (r_has_type_rw_add_auxiliaries _ _ _ _ w Γ').

Defined.

Fixpoint r_sem_ro_exp_auxiliary_ctx Γ Γ' e τ (w : Γ |~ e : τ) :
  forall γ γ', r_sem_ro_exp Γ e τ w γ = r_sem_ro_exp (Γ ++ Γ') e τ (r_has_type_ro_add_auxiliaries _ _ _ w Γ') (γ; γ')
with r_sem_rw_exp_auxiliary_ctx Γ Γ' Δ e τ (w : Γ ;;; Δ ||~ e : τ) :
  forall γ γ' δ, r_sem_rw_exp Γ Δ e τ w γ δ = r_sem_rw_exp (Γ ++ Γ') Δ e τ (r_has_type_rw_add_auxiliaries _ _ _ _ w Γ') (γ ; γ') δ.
Proof.
  +
    intros.
    dependent destruction w; easy_rewrite_uip;
      try (rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ r γ γ' tt); reflexivity);
      try (rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ w γ γ'); reflexivity);
      try (rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ w1 γ γ');
           rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ w2 γ γ'); reflexivity);
      try reflexivity.
    
    destruct γ.
    simpl; reflexivity.

    destruct γ.
    simpl.
    rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ w s0 γ'). 
    reflexivity.

    apply lp.
    apply dfun_ext; intro.
    rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ w (a, γ) γ'). 
    reflexivity.
    
  +
    intros.
    dependent destruction w; easy_rewrite_uip; try apply lp;
      try (rewrite <- eq_sym_app_assoc_tr;
           rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r Γ'));
           rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r _ γ');
           reflexivity).
    
    rewrite <- (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w1 _ γ').
    apply pl.
    apply lp.
    apply dfun_ext; intro d.
    rewrite <- (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w2 _ γ').
    reflexivity.

    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r Γ')).
    rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r _ γ').
    apply pl.
    apply lp.
    apply dfun_ext; intro.
    rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w _ γ' a).
    reflexivity.

    
    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r Γ')).
    rewrite (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r _ γ').
    apply pl.
    apply lp.
    apply dfun_ext; intro.
    rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w1 _ γ').
    rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w2 _ γ').
    reflexivity.

    (* rewrite <- eq_sym_app_assoc_tr. *)
    (* rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r Γ')). *)
    (* rewrite <- (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r _ γ'). *)
    (* rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r0 Γ')). *)
    (* rewrite <- (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r0 _ γ'). *)
    (* rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w1 _ γ'). *)
    (* rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w2 _ γ'). *)
    (* reflexivity. *)

    {
      clear l0.
      dependent induction f.
      simpl.
      auto.
      simpl in IHf.
      simpl.
      
      rewrite <- (IHf).
      simpl.
      destruct p.
      simpl.
      rewrite <- eq_sym_app_assoc_tr.
      assert (forall (A : Type) (x y: A) (P Q : A -> Set) (e : x = y) p q,
                 @eq_rec A x (fun a : A => (P a * Q a)%type) (p, q) y e =
                   (@eq_rec A x P p y e, @eq_rec A x Q q y e)).
      intros.
      destruct e.
      auto.
      rewrite H.
      simpl.
      rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r Γ')).
      rewrite <- (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r _ γ').
      assert (r_sem_rw_exp Γ Δ (snd x) τ r0 γ δ =
                r_sem_rw_exp (Γ ++ Γ') Δ (snd x) τ
                  (eq_rec ((Δ ++ Γ) ++ Γ') (fun _ : list datatype => (Γ ++ Γ');;; Δ ||~ snd x : τ) (r_has_type_rw_add_auxiliaries Γ Δ (snd x) τ r0 Γ') 
                     (Δ ++ Γ ++ Γ') (eq_sym (app_assoc Δ Γ Γ'))) (γ; γ') δ).
      
      rewrite  (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ r0 _ γ').
      assert (forall (A : Type) (x y: A) (P : Set) (e : x = y) p,
                 @eq_rec A x (fun a : A => (P )%type) p y e = p).
      intros.
      destruct e.
      simpl.
      auto.

      rewrite H0.
      reflexivity.
      rewrite H0.
      apply lp.
      reflexivity.
    }



    
    
    apply pl.

    assert (forall X Y Z (f : X -> Y -> Z) a b c d, a = b -> c = d -> f a c = f b d).
    intros.
    destruct H, H0; reflexivity.
    apply H.

    apply dfun_ext.
    intros.
    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (r_sem_ctx_rewrite _ _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ r Γ')).
    rewrite <- (r_sem_ro_exp_auxiliary_ctx _ _ _ _ r _ γ').
    reflexivity.

    apply dfun_ext.
    intros.
    rewrite (r_sem_rw_exp_auxiliary_ctx _ _ _ _ _ w _ γ').
    reflexivity.    
Qed.



Lemma sem_ro_exp_auxiliary_ctx :
  forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) γ γ', sem_ro_exp Γ e τ w γ = sem_ro_exp (Γ ++ Γ') e τ w' (γ; γ').
Proof.
  intros.
  rewrite (sem_ro_r_sem_ro _ _ _ _ (has_type_ro_r_has_type_ro _ _ _ w)).
  rewrite (sem_ro_r_sem_ro _ _ _ _ (has_type_ro_r_has_type_ro _ _ _ w')).
  rewrite <- (r_has_type_ro_unique _ _ _ (r_has_type_ro_add_auxiliaries _ _ _ (has_type_ro_r_has_type_ro Γ e τ w) Γ') (has_type_ro_r_has_type_ro (Γ ++ Γ') e τ w')).
  apply r_sem_ro_exp_auxiliary_ctx.
Defined.


Lemma sem_rw_exp_auxiliary_ctx : forall Γ Γ' Δ e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) γ γ' δ, sem_rw_exp Γ Δ e τ w γ δ = sem_rw_exp (Γ ++ Γ') Δ e τ w' (γ ; γ') δ.
Proof.
  intros.
  rewrite (sem_rw_r_sem_rw _ _ _ _ _ (has_type_rw_r_has_type_rw _ _ _ _ w)).
  rewrite (sem_rw_r_sem_rw _ _ _ _ _ (has_type_rw_r_has_type_rw _ _ _ _ w')).
  rewrite <- (r_has_type_rw_unique _ _ _ _ (r_has_type_rw_add_auxiliaries _ _ _ _ (has_type_rw_r_has_type_rw Γ Δ e τ w) Γ') (has_type_rw_r_has_type_rw (Γ ++ Γ') Δ e τ w')).
  apply r_sem_rw_exp_auxiliary_ctx.
Defined.


Lemma reduce_var_access_0 : forall Γ τ (w : (τ :: Γ) |- Var 0 : τ) x,
    var_access _ _ _ w x = fst x.
Proof.
  intros.
  rewrite (var_access_typing_irrl _ _ _ w (has_type_ro_Var_0 _ _)).
  destruct x; auto.
Defined.

Lemma reduce_var_access_S : forall Γ τ σ n (w : (σ :: Γ) |- Var (S n) : τ) x,
    var_access _ _ _ w x = var_access _ _ _ (has_type_ro_Var_S_inverse w) (snd x).
Proof.
  intros.
  rewrite (var_access_typing_irrl _ _ _ w (has_type_ro_Var_S _ _ _ _ (has_type_ro_Var_S_inverse w))).
  destruct x; auto.
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
      (@update τ (@cons datatype σ Δ) (S k) x (@pair (sem_datatype σ) (sem_ctx Δ) s s0) (assignable_S Δ τ σ k a1))
            = (s, update k x s0 a1)). 
  simpl.
  unfold update.
  unfold assignable_rect.
  destruct a1; auto.
  assert (
      (@update τ (@cons datatype σ Δ) (S k) x (@pair (sem_datatype σ) (sem_ctx Δ) s s0) (assignable_S Δ τ σ k a2))
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


Lemma reduce_update_0 : forall Δ τ (a : assignable (τ :: Δ) τ 0)
                                   (x y : sem_datatype τ) (δ : sem_ctx Δ),
    @update τ (τ::Δ) 0 x (y, δ) a = (x, δ).
Proof.
  intros.
  rewrite (update_assignable_irrl 0 _ _ _ _ a (assignable_0 _ _)).
  auto.
Defined.

Lemma update_assignable_S : forall Δ σ k (a : assignable Δ σ k) τ x δ y,
    @update σ (τ :: Δ) (S k) x (y, δ) (assignable_S _ σ τ _ a)
    = (y, @update σ Δ k x δ a).
Proof.
  intros.
  simpl.
  unfold update.
  apply lp.
  auto.
  simpl.
  destruct a.
  simpl.
  auto.
  simpl.
  apply lp.
  auto.
Defined.

Lemma reduce_update_S : forall Δ k τ σ (a : assignable (τ :: Δ) σ (S k)) x y
                               (δ : sem_ctx Δ),
    @update σ (τ :: Δ) (S k) x (y, δ) a
    = (y, @update σ Δ k x δ (assignable_S_inverse a)). 
Proof.
  intros.
  rewrite (update_assignable_irrl _ _ _ _ _ a
             (assignable_S _ _ _ _ ((assignable_S_inverse a)))).
  rewrite update_assignable_S.
  auto.
Defined.
