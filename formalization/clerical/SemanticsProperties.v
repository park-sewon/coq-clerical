Require Import List.
Require Import Reals.
Require Import Coq.Program.Equality.

Require Import Clerical.
Require Import Typing.
Require Import TypingProperties.
Require Import Powerdomain.
Require Import Semantics.


Fixpoint p_sem_ro_comp (Γ : ro_ctx) (e : comp) (τ : datatype) (D : Γ |~ e : τ) {struct D} :
  sem_ro_ctx Γ -> pdom (sem_datatype τ)
with p_sem_rw_comp (Γ Δ : ro_ctx) (c : comp) (τ : datatype) (D : Γ ;;; Δ ||~ c : τ) {struct D} :
  sem_ro_ctx Γ -> sem_ro_ctx Δ -> pdom (sem_ro_ctx Δ * sem_datatype τ).
Proof.
  - (* read only expressions *)
    induction D; intro γ.
    exact (pdom_lift snd (p_sem_rw_comp _ _ _ _ p γ tt)).
    exact (pdom_lift snd (p_sem_rw_comp _ _ _ _ p γ tt)).
    exact (pdom_lift snd (p_sem_rw_comp _ _ _ _ p γ tt)).
    exact (pdom_lift snd (p_sem_rw_comp _ _ _ _ p γ tt)).
    exact (pdom_lift snd (p_sem_rw_comp _ _ _ _ p γ tt)).
    exact (pdom_lift snd (p_sem_rw_comp _ _ _ _ p γ tt)).

    (* | has_type_ro_Var_0 *)
    simpl in γ.
    exact (pdom_unit (fst γ)).

    (* | has_type_ro_Var_S *)
    simpl in γ.
    (* exact (IHD (snd γ)). *)
    exact (p_sem_ro_comp _ _ _ D (snd γ)).


      (* | has_type_ro_True *)
    exact (pdom_unit true).

    (* | has_type_ro_False *)
    exact (pdom_unit false).

    (* | has_type_ro_Skip *)
    exact (pdom_unit tt).
    
    (* | has_type_ro_Int *)
    exact (pdom_unit k).

    (* | has_type_ro_OpRrecip *)
    pose proof (p_sem_ro_comp _ _ _ D γ).
    exact (pdom_bind Rrecip X). 
    
    (* | has_type_ro_OpZRcoerce *)
    pose proof (p_sem_ro_comp _ _ _ D γ).
    exact (pdom_lift IZR X).
    
    (* | has_type_ro_OpZRexp *)
    pose proof (p_sem_ro_comp _ _ _ D γ).
    exact (pdom_lift (powerRZ 2) X).

    (* | has_type_ro_OpZplus *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zplus x y).
    
    (* | has_type_ro_OpZminus *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zminus x y).
    
    (* | has_type_ro_OpZmult *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Zmult x y).
    
    (* | has_type_ro_OpZlt *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Z.ltb x y).

    (* | has_type_ro_OpZeq *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Z.eqb x y).

    (* | has_type_ro_OpRplus *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rplus x y).

    (* | has_type_ro_OpRminus *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rminus x y).

    (* | has_type_ro_OpRmult *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_lift2 Rmult x y).

    (* | has_type_ro_OpRlt *)
    pose proof (p_sem_ro_comp _ _ _ D1 γ) as x.
    pose proof (p_sem_ro_comp _ _ _ D2 γ) as y.
    exact (pdom_bind2 Rltb x y).

    (* | has_type_ro_Lim *)
    exact (Rlim (fun x : Z => p_sem_ro_comp _ _ _ D (x, γ))). 


  - (* read write commands*)
    dependent destruction D; intros γ δ.

    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).
    exact (pdom_lift (fun x => (δ, x)) (p_sem_ro_comp _ _ _ p (δ ; γ))).

    (* has_type_rw_Seq *)
    pose proof (p_sem_rw_comp _ _ _ _ D1 γ) as C1.
    pose proof (p_sem_rw_comp _ _ _ _ D2 γ) as C2.
    apply (pdom_bind C2).
    apply (pdom_lift (@fst _ (sem_datatype DUnit))).
    apply C1.
    exact δ.

    (* has_type_rw_Assign *)
    pose proof (pdom_lift (fun v => update k v δ a) (p_sem_ro_comp _ _ _ p (tedious_prod_sem _ _ (δ, γ)))) as V.
    exact (pdom_lift (fun x => (x, tt)) V).
    
    (* has_type_rw_Newvar *)
    pose proof (p_sem_ro_comp _ _ _ p (tedious_prod_sem _ _ (δ, γ))) as V.
    pose proof (p_sem_rw_comp _ _ _ _ D γ) as f.
    pose proof (pdom_bind f (pdom_lift (fun v => (v, δ)) V)) as res.
    exact (pdom_lift (fun x => (snd (fst x), snd x)) res).

    (* has_type_rw_Cond *)
    pose proof (p_sem_ro_comp _ _ _ p (tedious_prod_sem _ _ (δ, γ))) as B.
    pose proof (p_sem_rw_comp _ _ _ _ D1 γ δ) as X.
    pose proof (p_sem_rw_comp _ _ _ _ D2 γ δ) as Y.
    exact (pdom_bind (fun b : bool => if b then X else Y) B).
    
    (* has_type_rw_Case *)
    pose proof (p_sem_ro_comp _ _ _ p (tedious_prod_sem _ _ (δ, γ))) as B1.
    pose proof (p_sem_ro_comp _ _ _ p0 (tedious_prod_sem _ _ (δ, γ))) as B2.
    pose proof (p_sem_rw_comp _ _ _ _ D1 γ δ) as X.
    pose proof (p_sem_rw_comp _ _ _ _ D2 γ δ) as Y.
    exact (Case2 B1 B2 X Y).
    
    (* has_type_rw_While *)
    pose proof (fun d => p_sem_ro_comp _ _ _ p (tedious_prod_sem _ _ (d, γ))) as B.
    pose proof (fun d => pdom_lift fst (p_sem_rw_comp _ _ _ _ D γ d)) as C.
    exact (pdom_lift (fun x => (x, tt)) (pdom_while B C δ)).
Defined.

Ltac easy_rewrite_uip :=
  repeat (try unfold simplification_heq; try unfold solution_left; try unfold eq_rect_r; try rewrite (prop_irrl _ (eq_sym _) eq_refl); simpl).

Lemma has_type_ro_phas_type_ro_unambiguous : forall Γ e τ σ, Γ |- e : τ -> Γ |~ e : σ -> τ = σ.
Proof.
  intros.
  apply (has_type_ro_phas_type_ro) in H.
  apply (phas_type_ro_unambiguous _ _ _ _ H H0).
Qed.

Lemma has_type_rw_phas_type_rw_unambiguous : forall Γ Δ e τ σ, Γ ;;; Δ ||- e : τ -> Γ ;;; Δ ||~ e : σ -> τ = σ.
Proof.
  intros.
  apply (has_type_rw_phas_type_rw) in H.
  apply (phas_type_rw_unambiguous _ _ _ _ _ H H0).
Qed.

 
Lemma p_has_type_ro_inv_Seq_1 Γ c1 c2 τ (w : Γ |~ (c1 ;; c2) : τ) : Γ ;;; nil ||~ c1 : DUnit.
Proof.
  dependent destruction w.
  dependent destruction p.
  simpl in p1.
  exact p1.
Defined.

Lemma p_has_type_ro_inv_Seq_2 Γ c1 c2 τ (w : Γ |~ (c1 ;; c2) : τ) : Γ ;;; nil ||~ c2 : τ.
Proof.
  dependent destruction w.
  dependent destruction p.
  simpl in p2.
  exact p2.
Defined.
  

Lemma p_sem_ro_Seq : forall Γ c1 c2 τ (w : Γ |~ (c1 ;; c2) : τ),
    p_sem_ro_comp Γ (c1;; c2) τ w =
      (fun γ : sem_ro_ctx Γ =>
         pdom_lift snd (pdom_bind (p_sem_rw_comp Γ nil c2 τ (p_has_type_ro_inv_Seq_2 _ _ _ _ w) γ) (pdom_lift fst (p_sem_rw_comp Γ nil c1 UNIT (p_has_type_ro_inv_Seq_1 _ _ _ _ w) γ tt)))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction p.
  easy_rewrite_uip.
  auto.
Qed.


Lemma p_sem_ro_Newvar : forall Γ e c τ (w :  Γ |~ (NEWVAR e IN c) : τ), exists σ p p1,
    p_sem_ro_comp Γ (NEWVAR e IN c) τ w
    =
      (fun γ : sem_ro_ctx Γ =>
         pdom_lift snd
                   (pdom_lift (fun x : sem_datatype σ * unit * sem_datatype τ => (snd (fst x), snd x))
                              (pdom_bind (p_sem_rw_comp Γ (σ :: nil) c τ p1 γ)
                                         (pdom_lift (fun v : sem_datatype σ => (v, tt)) (p_sem_ro_comp Γ e σ p γ))))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction p.
  easy_rewrite_uip.
  exists σ, p, p1.
  auto.  
Qed.

Lemma p_sem_ro_Cond : forall Γ e c1 c2 τ (w : Γ |~ (IF e THEN c1 ELSE c2 END) : τ), exists p1 p2 p3,
    p_sem_ro_comp Γ (IF e THEN c1 ELSE c2 END) τ w =
      (fun γ : sem_ro_ctx Γ =>
   pdom_lift snd
     (pdom_bind (fun b : bool => if b then p_sem_rw_comp Γ nil c1 τ p2 γ tt else p_sem_rw_comp Γ nil c2 τ p3 γ tt)
        (p_sem_ro_comp Γ e BOOL p1 γ))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction p.
  easy_rewrite_uip.
  exists p1, p2, p3.
  auto.  
Qed.

Lemma p_sem_ro_Case : forall Γ e1 e2 c1 c2 τ (w : Γ |~ (CASE e1 ==> c1 OR e2 ==> c2 END) : τ), exists p1 p2 p3 p4,
    p_sem_ro_comp Γ (CASE e1 ==> c1 OR e2 ==> c2 END) τ w
    =  (fun γ : sem_ro_ctx Γ =>
   pdom_lift snd
     (Case2 (p_sem_ro_comp Γ e1 BOOL p1 γ) (p_sem_ro_comp Γ e2 BOOL p3 γ) (p_sem_rw_comp Γ nil c1 τ p2 γ tt)
        (p_sem_rw_comp Γ nil c2 τ p4 γ tt))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction p.
  easy_rewrite_uip.
  exists p1, p2, p3, p4.
  auto.  
Qed.

Lemma p_sem_ro_While : forall Γ e c (w : Γ |~ (WHILE e DO c END) : UNIT), exists p p1,
    p_sem_ro_comp Γ (WHILE e DO c END) UNIT w =
       (fun γ : sem_ro_ctx Γ =>
   pdom_lift snd
     (pdom_lift (fun x : unit => (x, tt))
        (pdom_while (fun _ : unit => p_sem_ro_comp Γ e BOOL p γ)
           (fun d : unit => pdom_lift fst (p_sem_rw_comp Γ nil c UNIT p1 γ d)) tt))).
Proof.
  intros.
  dependent destruction w.
  dependent destruction p.
  easy_rewrite_uip.
  exists p, p1.
  auto.  
Qed.

Fixpoint assignable_unique Δ τ n (a1 a2 : assignable Δ τ n) : a1 = a2.
Proof.
  dependent destruction a1;
    dependent destruction a2; try reflexivity.
  rewrite (assignable_unique _ _ _ a1 a2).
  reflexivity.
Qed.

  
  

Fixpoint p_has_type_ro_unique Γ e τ (w1 w2 : Γ |~ e : τ) {struct w1}: w1 = w2 
with p_has_type_rw_unique Γ Δ e τ (w1 w2 : Γ ;;; Δ ||~ e : τ) {struct w1}: w1 = w2.
Proof.
  dependent destruction w1;
    dependent destruction w2;
    try 
      (rewrite (p_has_type_rw_unique _ _ _ _ p p0); reflexivity);
    try 
      (rewrite (p_has_type_ro_unique _ _ _ w1 w2); reflexivity);
    try 
      (rewrite (p_has_type_ro_unique _ _ _ w1_1 w2_1); rewrite (p_has_type_ro_unique _ _ _ w1_2 w2_2); reflexivity);
      try reflexivity.
dependent destruction w1;
    dependent destruction w2;
    try 
      (rewrite (p_has_type_rw_unique _ _ _ _ p p0); reflexivity);
    try 
      (rewrite (p_has_type_ro_unique _ _ _ p p0); reflexivity);
    try 
      (rewrite (p_has_type_ro_unique _ _ _ w1_1 w2_1); rewrite (p_has_type_ro_unique _ _ _ w1_2 w2_2); reflexivity);
      try reflexivity.

  rewrite (p_has_type_rw_unique _ _ _ _ w1_1 w2_1);
    rewrite (p_has_type_rw_unique _ _ _ _ w1_2 w2_2); reflexivity.

  induction (phas_type_ro_unambiguous _ _ _ _ p p0).
  rewrite (assignable_unique _ _ _ a a0).
  rewrite (p_has_type_ro_unique _ _ _ p p0); reflexivity.
  
    induction (phas_type_ro_unambiguous _ _ _ _ p p0).

  rewrite (p_has_type_ro_unique _ _ _  p p0);
    rewrite (p_has_type_rw_unique _ _ _ _ w1 w2); reflexivity.
  
  rewrite (p_has_type_ro_unique _ _ _ p p0);
    rewrite (p_has_type_rw_unique _ _ _ _ w1_1 w2_1);
    rewrite (p_has_type_rw_unique _ _ _ _ w1_2 w2_2); reflexivity.

  rewrite (p_has_type_ro_unique _ _ _ p p1);
    rewrite (p_has_type_ro_unique _ _ _ p0 p2);
    rewrite (p_has_type_rw_unique _ _ _ _ w1_1 w2_1);
    rewrite (p_has_type_rw_unique _ _ _ _ w1_2 w2_2); reflexivity.

  rewrite (p_has_type_ro_unique _ _ _ p p0);
    rewrite (p_has_type_rw_unique _ _ _ _ w1 w2); reflexivity.
Qed.

Definition dn_intro : forall X : Type, X -> (X -> False) -> False.
Proof.
  intro X.
  exact (fun x f => f x).
Defined.
  


Lemma p_sem_ro_ctx_rewrite : forall Γ1 Γ2 e τ (w1 : Γ1 |~ e : τ) (w2 : Γ2 |~ e : τ) (p : Γ1 = Γ2) γ,
    p_sem_ro_comp _ _ _ w1 γ = p_sem_ro_comp _ _ _ w2 (tr (fun Γ => sem_ro_ctx Γ) p γ).
Proof.
  intros.
  destruct p.
  simpl.
  rewrite (p_has_type_ro_unique _ _ _ w1 w2).
  auto.
Qed.

Lemma p_sem_rw_rw_ctx_rewrite : forall Γ Δ1 Δ2 e τ (w : Γ ;;; Δ1 ||~ e : τ) (p : Δ1 = Δ2) γ δ,
    p_sem_rw_comp _ _ _ _ w γ δ =
      pdom_lift (fun q => (tr (fun Δ => sem_ro_ctx Δ) (eq_sym p) (fst q), (snd q)))
      (p_sem_rw_comp _ _ _ _ (tr (fun Δ => Γ ;;; Δ ||~ e : τ) p w) γ (tr (fun Δ => sem_ro_ctx Δ) p δ)).
Proof.
  intros.
  destruct p.
  simpl.
  replace (fun q : sem_ro_ctx Δ1 * sem_datatype τ => (fst q, snd q))
    with (fun q :sem_ro_ctx Δ1 * sem_datatype τ => q).
  rewrite pdom_lift_id.
  reflexivity.
  apply dfun_ext.
  intros [a b]; simpl; reflexivity.
Qed.

Lemma p_sem_rw_ro_ctx_rewrite : forall Γ1 Γ2 Δ e τ (w : Γ1 ;;; Δ ||~ e : τ) (p : Γ1 = Γ2) γ δ,
    p_sem_rw_comp _ _ _ _ w γ δ =
      (p_sem_rw_comp _ _ _ _ (tr (fun Γ => Γ ;;; Δ ||~ e : τ) p w) (tr (fun Δ => sem_ro_ctx Δ) p γ) δ).
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

Fixpoint app_assoc_tr (Γ1 Γ2 Γ3 : list datatype) : forall (γ1 : sem_ro_ctx Γ1) (γ2 : sem_ro_ctx Γ2) (γ3 : sem_ro_ctx Γ3),
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


Lemma eq_sym_app_assoc_tr (Γ1 Γ2 Γ3 : list datatype) : forall (γ1 : sem_ro_ctx Γ1) (γ2 : sem_ro_ctx Γ2) (γ3 : sem_ro_ctx Γ3), tr (fun Γ0 : list datatype => sem_ro_ctx Γ0) (eq_sym (app_assoc Γ1 Γ2 Γ3)) ((γ1; γ2); γ3) = (γ1; (γ2; γ3)).
Proof.
  intros.
  pose proof (app_assoc_tr _ _ _ γ1 γ2 γ3).
  pose proof (lp _ _ (fun k => tr (fun Γ0 : list datatype => sem_ro_ctx Γ0) (eq_sym (app_assoc Γ1 Γ2 Γ3)) k) _ _ H).
  simpl in H0.
  rewrite eq_sym_tr_inverse_left in H0.
  rewrite H0; reflexivity.
Defined.

Lemma pl : forall {X Y} (f g: X -> Y) (x : X), f = g -> f x = g x.
Proof.
  intros.
  rewrite H; auto.
Defined.

Lemma Case2_post_processing {X Y} (f : X -> Y) e1 e2 c1 c2 :
  Case2 e1 e2 (pdom_lift f c1) (pdom_lift f c2) = pdom_lift f (Case2 e1 e2 c1 c2). 
Proof.
  unfold Case2.
  destruct (lem (pdom_is_empty (pdom_case2 e1 e2 (pdom_lift f c1) (pdom_lift f c2)))).
  destruct (lem (pdom_is_empty (pdom_lift f (pdom_case2 e1 e2 c1 c2)))).
  rewrite (pdom_is_empty_is_empty _ H).
  rewrite (pdom_is_empty_is_empty _ H0).
  auto.
  contradict H0.
  apply pdom_case2_empty_2 in H.
  apply pdom_lift_empty_1.  
  apply pdom_case2_empty_1.
  repeat destruct H; auto.
  apply pdom_lift_empty_2 in H0.
  auto.
  apply pdom_lift_empty_2 in H0.
  auto.
  destruct (lem (pdom_is_empty (pdom_lift f (pdom_case2 e1 e2 c1 c2)))).
  contradict H.
  apply pdom_lift_empty_2 in H0.
  apply pdom_case2_empty_1.
  apply pdom_case2_empty_2 in H0.
  repeat destruct H0; auto.
  destruct H.
  auto.
  destruct H.
  right.
  right.
  left.
  destruct H; split; auto.
  apply pdom_lift_empty_1; auto.
  right.
  right.
  right.
  destruct H; split; auto.
  apply pdom_lift_empty_1; auto.

  (* when both hand sides are non empty *)
  assert (~ pdom_is_empty (pdom_case2 e1 e2 c1 c2)).
  intro.
  contradict H0.
  apply pdom_lift_empty_1.
  auto.
  
  apply sig_eq.
  apply pred_ext; intros.
  +
    
    destruct a.
    
    apply pdom_case2_bot_2 in H2.
    apply pdom_lift_bot_1.
    apply pdom_case2_bot_1; auto.
    repeat destruct H2; auto.
    apply pdom_lift_bot_2 in H3; left; split; auto.
    apply pdom_lift_bot_2 in H3; right; left; split; auto.
    apply pdom_case2_total_2 in H2.
    apply pdom_lift_total_1.
    destruct H2.
    destruct H2.
    apply pdom_lift_total_2 in H3.
    destruct H3.
    exists x.
    destruct H3; split; auto.
    apply pdom_case2_total_1; auto.
    destruct H2.
    apply pdom_lift_total_2 in H3.
    destruct H3.
    exists x.
    destruct H3; split; auto.
    apply pdom_case2_total_1; auto.
    
  +

    destruct a.
    apply pdom_lift_bot_2 in H2.
    apply pdom_case2_bot_1; auto.
    apply pdom_case2_bot_2 in H2.
    repeat destruct H2; auto.
    left; split; auto.
    apply pdom_lift_bot_1; auto.
    right; left; split; auto.
    apply pdom_lift_bot_1; auto.
    apply pdom_lift_total_2 in H2.
    destruct H2.
    destruct H2.
    apply pdom_case2_total_1; auto.
    apply pdom_case2_total_2 in H2.
    destruct H2.
    left; destruct H2; split; auto.
    apply pdom_lift_total_1.
    exists x; auto.
    right; destruct H2; split; auto.
    apply pdom_lift_total_1.
    exists x; auto.
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

(* Lemma pdom_lifted_continuous {X Y} (f : X -> Y) : pdom_is_continuous (pdom_lift f) (pdom_lifted_monotone f). *)
(* Admitted. *)

Lemma p_sem_move_readonly_while X Y Z (f : X -> Z) (g : Y -> Z) x y (b1 : X -> pdom bool) (c1 : X -> pdom X) (b2 : Y -> pdom bool) (c2 : Y -> pdom Y) :
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


Lemma assign_concat_fst : 
  forall Δ Δ' τ k (a0 :assignable Δ τ k) (a : assignable (Δ ++ Δ') τ k) a1 δ δ',
    (update k a1 δ a0 ; δ') = (update k a1 (δ; δ') a).
Admitted.

Fixpoint p_sem_move_readonly  Γ Δ Δ' e τ (w1 : Γ ;;; (Δ ++ Δ') ||~ e : τ) (w2 : (Δ' ++ Γ) ;;; Δ ||~ e : τ) :
  forall γ δ δ', p_sem_rw_comp _ _ _ _ w1 γ (δ ; δ') =
           pdom_lift (fun y => ((fst y; δ'), snd y)) (p_sem_rw_comp _ _ _ _ w2 (δ'; γ) δ).
Proof.
  intros.
  dependent destruction w1;
  dependent destruction w2;
    easy_rewrite_uip; try simpl in p0;
    try induction (p_has_type_ro_unique _ _ _ p p0);
    try (rewrite pdom_lift_comp; simpl; reflexivity);
    try (rewrite pdom_lift_comp;
         simpl;
         apply lp;
         rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p0 p (app_assoc Δ Δ' Γ));
         apply lp;
         apply eq_sym;
         apply app_assoc_tr).

  unfold pdom_bind.
  rewrite (p_sem_move_readonly _ _ _ _ _ w1_1 w2_1).
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  simpl.
  replace (fun y : sem_ro_ctx Δ * unit => p_sem_rw_comp Γ (Δ ++ Δ') c2 τ w1_2 γ (fst y; δ'))
    with (fun y : sem_ro_ctx Δ * unit =>
            pdom_lift (fun y => ((fst y; δ'), snd y)) (p_sem_rw_comp _ _ _ _ w2_2 (δ'; γ) (fst y))).
  simpl.
  rewrite <- pdom_lift_comp.
  rewrite pdom_mult_natural.
  apply lp.
  apply lp.
  apply lp.
  reflexivity.
  apply dfun_ext.
  intro.
  rewrite (p_sem_move_readonly _ _ _ _ _ w1_2 w2_2).
  reflexivity.

  assert (τ = τ0).
  assert ( (Δ ++ Δ' ++ Γ) |~ e : τ).
  rewrite app_assoc; auto.
  apply (phas_type_ro_unambiguous _ _ _ _ H p0).
  induction H.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  rewrite pdom_lift_comp.
  simpl.
  replace (fun y : sem_datatype τ => (update k y (δ; δ') a, tt)) with
    (fun y : sem_datatype τ => ((update k y δ a0; δ'), tt)).
  apply lp.
  rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p0 p (app_assoc Δ Δ' Γ)).
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
  apply (phas_type_ro_unambiguous _ _ _ _ H p0).
  induction H.
  rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p0 p (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ro_ctx Γ0) (app_assoc Δ Δ' Γ) (δ; (δ'; γ)))
    with  ((δ; δ'); γ) by (apply eq_sym, app_assoc_tr).
  pose proof (p_sem_move_readonly Γ (σ::Δ) Δ' _ _ w1 w2 γ).

  replace (fun y : sem_datatype σ => p_sem_rw_comp Γ (σ :: Δ ++ Δ') c τ w1 γ (y, (δ; δ')))
    with ((fun y : sem_datatype σ =>
             pdom_lift (fun y : sem_ro_ctx (σ :: Δ) * sem_datatype τ => ((fst y; δ'), snd y))
                       (p_sem_rw_comp (Δ' ++ Γ) (σ :: Δ) c τ w2 (δ'; γ) (y, δ)))).
  rewrite <- pdom_lift_comp.
  rewrite pdom_mult_natural.
  rewrite pdom_lift_comp.
  simpl.
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

  rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p0 p (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ro_ctx Γ0) (app_assoc Δ Δ' Γ) (δ; (δ'; γ)))
    with  ((δ; δ'); γ) by (apply eq_sym, app_assoc_tr).
  rewrite (p_sem_move_readonly Γ _ _ _ _ w1_1 w2_1 γ ).
  rewrite (p_sem_move_readonly Γ _ _ _ _ w1_2 w2_2 γ).
  replace
    ((fun b : bool =>
        if b
        then
          pdom_lift (fun y : sem_ro_ctx Δ * sem_datatype τ => ((fst y; δ'), snd y))
                    (p_sem_rw_comp (Δ' ++ Γ) Δ c1 τ w2_1 (δ'; γ) δ)
        else
          pdom_lift (fun y : sem_ro_ctx Δ * sem_datatype τ => ((fst y; δ'), snd y))
                    (p_sem_rw_comp (Δ' ++ Γ) Δ c2 τ w2_2 (δ'; γ) δ)))
    with
    
    ((fun b : bool =>
        pdom_lift (fun y : sem_ro_ctx Δ * sem_datatype τ => ((fst y; δ'), snd y))
        (if b
        then
         
           (p_sem_rw_comp (Δ' ++ Γ) Δ c1 τ w2_1 (δ'; γ) δ)
        else
           (p_sem_rw_comp (Δ' ++ Γ) Δ c2 τ w2_2 (δ'; γ) δ)))).
  rewrite <- pdom_lift_comp.
  rewrite pdom_mult_natural.
  reflexivity.
  apply dfun_ext; intros.
  destruct a; simpl; reflexivity.


  (* case *)
  rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p1 p (app_assoc Δ Δ' Γ)).
  rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p2 p0 (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ro_ctx Γ0) (app_assoc Δ Δ' Γ) (δ; (δ'; γ)))
    with  ((δ; δ'); γ) by (apply eq_sym, app_assoc_tr).
  rewrite (p_sem_move_readonly Γ _ _ _ _ w1_1 w2_1 γ ).
  rewrite (p_sem_move_readonly Γ _ _ _ _ w1_2 w2_2 γ).
  apply Case2_post_processing.


  
  rewrite pdom_lift_comp.
  simpl.
  apply p_sem_move_readonly_while.
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
  rewrite (p_sem_ro_ctx_rewrite _ _ _ _ p0 p (app_assoc Δ Δ' Γ)).
  replace  (tr (fun Γ0 : list datatype => sem_ro_ctx Γ0) (app_assoc Δ Δ' Γ) (δ0; (δ'0; γ)))
    with  ((δ0; δ'0); γ) by (apply eq_sym, app_assoc_tr).
  apply pl.
  apply lp.
  apply dfun_ext.
  intro.
  destruct a.
  apply lp.
  simpl.
  simpl in IHn.
  assert (
      (fun y : sem_ro_ctx (Δ ++ Δ') * unit =>
        pdom_lift (fun x : sem_ro_ctx (Δ ++ Δ') => (x, tt))
                  (pdom_fun_bot_chain
                     (pdom_W (fun d : sem_ro_ctx (Δ ++ Δ') => p_sem_ro_comp ((Δ ++ Δ') ++ Γ) e BOOL p (d; γ))
                             (fun d : sem_ro_ctx (Δ ++ Δ') => pdom_lift fst (p_sem_rw_comp Γ (Δ ++ Δ') c UNIT w1 γ d)))
                     (pdom_W_monotone (fun d : sem_ro_ctx (Δ ++ Δ') => p_sem_ro_comp ((Δ ++ Δ') ++ Γ) e BOOL p (d; γ))
                                      (fun d : sem_ro_ctx (Δ ++ Δ') => pdom_lift fst (p_sem_rw_comp Γ (Δ ++ Δ') c UNIT w1 γ d))) n
                     (fst y))) =
          fun y : sem_ro_ctx (Δ ++ Δ') * unit =>
            pdom_lift (fun y0 : sem_ro_ctx Δ => ((y0; snd_concat (fst y)), tt))
                      (pdom_fun_bot_chain
                         (pdom_W (fun d : sem_ro_ctx Δ => p_sem_ro_comp (Δ ++ Δ' ++ Γ) e BOOL p0 (d; (snd_concat (fst y); γ)))
                                 (fun d : sem_ro_ctx Δ => pdom_lift fst (p_sem_rw_comp (Δ' ++ Γ) Δ c UNIT w2 (snd_concat (fst y); γ) d)))
                         (pdom_W_monotone
                            (fun d : sem_ro_ctx Δ => p_sem_ro_comp (Δ ++ Δ' ++ Γ) e BOOL p0 (d; (snd_concat (fst y); γ)))
                            (fun d : sem_ro_ctx Δ => pdom_lift fst (p_sem_rw_comp (Δ' ++ Γ) Δ c UNIT w2 (snd_concat (fst y); γ) d))) n
                         (fst_concat (fst y)))).
  

  apply dfun_ext; intro y.
  pose proof (IHn (fst_concat (fst y)) (snd_concat (fst y))).
  rewrite <- tedious_equiv_2 in H0.
  simpl.
  auto.
  simpl.
  simpl in H0.
  rewrite H0.
  clear H0.
  rewrite (p_sem_move_readonly Γ _ _ _ _ w1 w2 γ).
  rewrite pdom_lift_comp.
  simpl.
 assert  ((fun y : sem_ro_ctx Δ * unit =>
     pdom_lift (fun y0 : sem_ro_ctx Δ => ((y0; snd_concat (fst y; δ'0)), tt))
       (pdom_fun_bot_chain
          (pdom_W (fun d : sem_ro_ctx Δ => p_sem_ro_comp (Δ ++ Δ' ++ Γ) e BOOL p0 (d; (snd_concat (fst y; δ'0); γ)))
             (fun d : sem_ro_ctx Δ =>
              pdom_lift fst (p_sem_rw_comp (Δ' ++ Γ) Δ c UNIT w2 (snd_concat (fst y; δ'0); γ) d)))
          (pdom_W_monotone
             (fun d : sem_ro_ctx Δ => p_sem_ro_comp (Δ ++ Δ' ++ Γ) e BOOL p0 (d; (snd_concat (fst y; δ'0); γ)))
             (fun d : sem_ro_ctx Δ =>
              pdom_lift fst (p_sem_rw_comp (Δ' ++ Γ) Δ c UNIT w2 (snd_concat (fst y; δ'0); γ) d))) n
          (fst_concat (fst y; δ'0)))) =
     (fun y : sem_ro_ctx Δ * unit =>
     pdom_lift (fun y0 : sem_ro_ctx Δ => ((y0;  δ'0), tt))
       (pdom_fun_bot_chain
          (pdom_W (fun d : sem_ro_ctx Δ => p_sem_ro_comp (Δ ++ Δ' ++ Γ) e BOOL p0 (d; (δ'0; γ)))
             (fun d : sem_ro_ctx Δ =>
              pdom_lift fst (p_sem_rw_comp (Δ' ++ Γ) Δ c UNIT w2 (δ'0; γ) d)))
          (pdom_W_monotone
             (fun d : sem_ro_ctx Δ => p_sem_ro_comp (Δ ++ Δ' ++ Γ) e BOOL p0 (d; (δ'0; γ)))
             (fun d : sem_ro_ctx Δ =>
              pdom_lift fst (p_sem_rw_comp (Δ' ++ Γ) Δ c UNIT w2 (δ'0; γ) d))) n
          (fst y)))).

  apply dfun_ext.
  intros.
  unfold snd_concat.
  rewrite tedious_equiv_1.
  unfold fst_concat.
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

 

(* Fixpoint p_sem_move_readonly  Γ Δ e τ (w1 : Γ ;;; Δ ||~ e : τ) (w2 : (Δ ++ Γ) ;;; nil ||~ e : τ) : *)
(*   forall γ δ, p_sem_rw_comp Γ Δ e τ w1 γ δ = *)
(*            pdom_lift (fun y => (δ, snd y)) (p_sem_rw_comp (Δ ++ Γ) nil e τ w2 (δ; γ) tt). *)
(* Proof. *)
(*   intros. *)
(*   dependent destruction w1; *)
(*   dependent destruction w2; *)
(*     easy_rewrite_uip; try simpl in p0; *)
(*     try induction (p_has_type_ro_unique _ _ _ p p0); *)
(*     try (rewrite pdom_lift_comp; simpl; reflexivity). *)

(*   unfold pdom_bind. *)

(*   rewrite (p_sem_move_readonly _ _ _ _ w1_1 w2_1). *)
(*   rewrite pdom_lift_comp. *)
(*   rewrite pdom_lift_comp. *)
(*   rewrite pdom_lift_comp. *)
(*   simpl. *)
(*   rewrite (p_sem_move_readonly _ _ _ _ w1_2 w2_2). *)
(*   simpl. *)
(*   rewrite <- pdom_lift_comp. *)
(*   rewrite pdom_mult_natural. *)
(*   replace (fun y : unit * unit => p_sem_rw_comp (Δ ++ Γ) nil c2 τ w2_2 (δ; γ) (fst y)) with *)
(*     (fun _ : unit * unit => p_sem_rw_comp (Δ ++ Γ) nil c2 τ w2_2 (δ; γ) tt). *)
(*   reflexivity. *)
(*   apply dfun_ext. *)
(*   intro. *)
(*   destruct a. *)
(*   destruct u; simpl; reflexivity. *)

(*   contradict (assignable_absurd _ _ a0). *)

  
(*   rewrite pdom_lift_comp. *)
(*   rewrite pdom_lift_comp. *)
  
  
(*   rewrite pdom_lift_comp. *)
(*   s *)
  
  
(*   rewrite (p_sem_move_readonly _ _ _ _ w1_2 w2_2). *)
  
  
(*   simpl in w2_1, w2_2. *)
  

  
  
(*   reflex *)
(*   rewrite (p_sem_move_readonly . *)
(*   apply lp.re *)
    

Fixpoint sem_ro_p_sem_ro Γ e τ (w1 : Γ |- e : τ) w2 {struct w1} : sem_ro_comp Γ e τ w1 = p_sem_ro_comp Γ e τ w2
with sem_rw_p_sem_rw Γ Δ e τ (w1 : Γ ;;; Δ ||- e : τ) w2 {struct w1}: sem_rw_comp Γ Δ e τ w1 = p_sem_rw_comp Γ Δ e τ w2.
Proof.
  +
    dependent destruction w1.
    dependent destruction h.
    simpl.
    easy_rewrite_uip.
    simpl in h.
    rewrite <- (sem_ro_p_sem_ro _ _ _ h w2). 
    apply dfun_ext; intro.
    rewrite pdom_lift_comp.
    simpl.
    rewrite pdom_lift_id.
    auto.

    rewrite p_sem_ro_Seq.    
    easy_rewrite_uip.
    rewrite (sem_rw_p_sem_rw _ _ _ _ h1 (p_has_type_ro_inv_Seq_1 Γ c1 c2 τ w2) ).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h2 (p_has_type_ro_inv_Seq_2 Γ c1 c2 τ w2) ).
    auto.

    contradict (assignable_absurd _ _ a).

    destruct (p_sem_ro_Newvar _ _ _ _ w2) as [σ' [p [p1 eq]]].
    induction (has_type_ro_phas_type_ro_unambiguous _ _ _ _ h p).
    rewrite eq.
    simpl in h.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h1 p1).
    reflexivity.

    destruct (p_sem_ro_Cond _ _ _ _ _ w2) as [p1 [p2 [p3 eq]]].
    rewrite eq.
    simpl in h1.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h1 p1).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h2 p2).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h3 p3).
    reflexivity.


    destruct (p_sem_ro_Case _ _ _ _ _ _ w2) as [p1 [p2 [p3 [p4 eq]]]].
    rewrite eq.
    simpl in h1, h3.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro _ _ _ h3 p3).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h2 p2).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h4 p4).
    reflexivity.

    destruct (p_sem_ro_While _ _ _  w2) as [p [p1 eq]].
    rewrite eq.
    simpl in h. 
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    rewrite (sem_rw_p_sem_rw _ _ _ _ h1 p1).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    auto.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1 w2).
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
    rewrite (sem_ro_p_sem_ro _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.
    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1_1 w2_1).
    rewrite (sem_ro_p_sem_ro _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ w1 w2).
    reflexivity.

  +
    dependent destruction w1.
    dependent destruction h.
     easy_rewrite_uip.
    apply dfun_ext; intros.
    apply dfun_ext; intros.
    pose proof (sem_rw_p_sem_rw _ _ _ _ h (has_type_rw_phas_type_rw _ _ _ _ h)).
    rewrite H.
    rewrite pdom_lift_comp.
    pose proof (p_sem_move_readonly Γ nil Δ).
    simpl in H0.
    rewrite <- (H0 _ _ w2 (has_type_rw_phas_type_rw (Δ ++ Γ) nil e τ h)).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h0 p).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h0 p).
    reflexivity.

    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    reflexivity.

    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h p).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h p).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h p).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.
    
        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.
    
    dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h1 p1).
    rewrite (sem_ro_p_sem_ro  _ _ _ h2 p2).
    reflexivity.

        dependent destruction w2.
    dependent destruction p.    
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro  _ _ _ h p).
    reflexivity.

    
    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1_1 w2_1).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    induction (has_type_ro_phas_type_ro_unambiguous _ _ _ _ h p).
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    induction (assignable_unique _ _ _ a a0).
    reflexivity.

    dependent destruction w2.
    induction (has_type_ro_phas_type_ro_unambiguous _ _ _ _ h p).
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1 w2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1_1 w2_1).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    rewrite (sem_ro_p_sem_ro _ _ _ h0 p0).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1_1 w2_1).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1_2 w2_2).
    reflexivity.

    dependent destruction w2.
    easy_rewrite_uip.
    rewrite (sem_ro_p_sem_ro _ _ _ h p).
    rewrite (sem_rw_p_sem_rw _ _ _ _ w1 w2).
    reflexivity.
Qed.


(* Lemma sem_ro_comp_unique_Seq Γ c1 c2 τ h1 h2 : *)
(*   sem_ro_comp Γ (c1;; c2) τ (has_type_ro_rw Γ (c1;; c2) τ (has_type_rw_Seq Γ nil c1 c2 τ h1 h2)) = *)
(*     sem_ro_comp Γ (c1;; c2) τ (has_type_ro_rw Γ (c1;; c2) τ (has_type_rw_Seq Γ nil c1 c2 τ h1 h2)). *)
(*   simpl. *)
(*   easy_rewrite_uip. *)

  
(* semantics is unique *)
Lemma sem_ro_comp_unique Γ e τ (w1 w2 : Γ |- e : τ): sem_ro_comp Γ e τ w1 = sem_ro_comp Γ e τ w2.
Proof.
  rewrite (sem_ro_p_sem_ro _ _ _ w1 (has_type_ro_phas_type_ro _ _ _ w1)).
  rewrite (sem_ro_p_sem_ro _ _ _ w2 (has_type_ro_phas_type_ro _ _ _ w2)).
  apply lp.
  apply p_has_type_ro_unique.
Qed.

  
Lemma sem_rw_comp_unique Γ Δ e τ (w1 w2 : Γ ;;; Δ ||- e : τ) : sem_rw_comp Γ Δ e τ w1 = sem_rw_comp Γ Δ e τ w2.
Proof.
  rewrite (sem_rw_p_sem_rw _ _ _ _ w1 (has_type_rw_phas_type_rw _ _ _ _ w1)).
  rewrite (sem_rw_p_sem_rw _ _ _ _ w2 (has_type_rw_phas_type_rw _ _ _ _ w2)).
  apply lp.
  apply p_has_type_rw_unique.
Qed.

Fixpoint p_has_type_ro_add_auxiliaries Γ e τ (w : Γ |~ e : τ) : forall Γ', (Γ ++ Γ') |~ e : τ
with p_has_type_rw_add_auxiliaries Γ Δ e τ (w : Γ ;;; Δ ||~ e : τ) : forall Γ', (Γ ++ Γ') ;;; Δ ||~ e : τ.
Proof.
  +
    
    intros.
    dependent destruction w.

    (* commands *)
    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ p Γ').
    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ p Γ').
    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ p Γ').
    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ p Γ').
    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ p Γ').
    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ p Γ').

    (* variables *)
    constructor.

    simpl.
    pose proof (p_has_type_ro_add_auxiliaries _ _ _ w Γ').
    exact (phas_type_ro_Var_S (Γ++ Γ') σ τ k H).

    (* constants *)
    constructor.
    constructor.
    constructor.
    constructor.

    (* unary *)
    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w Γ').
    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w Γ').
    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w1 Γ').
    exact (p_has_type_ro_add_auxiliaries _ _ _ w2 Γ').

    constructor.
    exact (p_has_type_ro_add_auxiliaries _ _ _ w Γ').
  +

    intros.
    dependent destruction w.
    
    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').

    constructor.
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w1 Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w2 Γ').

    apply (phas_type_rw_Assign _ _ _ τ).
    exact a.
    induction (eq_sym (app_assoc Δ Γ Γ')).     
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').
    

    apply (phas_type_rw_Newvar _ _ _ _ σ).
    induction (eq_sym (app_assoc Δ Γ Γ')).     
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w1 Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w2 Γ').

    
    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w1 Γ').
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p0 Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w2 Γ').

    constructor.
    induction (eq_sym (app_assoc Δ Γ Γ')). 
    exact (p_has_type_ro_add_auxiliaries _ _ _ p Γ').
    exact (p_has_type_rw_add_auxiliaries _ _ _ _ w Γ').

Defined.

Fixpoint p_sem_ro_comp_auxiliary_ctx Γ Γ' e τ (w : Γ |~ e : τ) :
forall γ γ', p_sem_ro_comp Γ e τ w γ = p_sem_ro_comp (Γ ++ Γ') e τ (p_has_type_ro_add_auxiliaries _ _ _ w Γ') (γ; γ')
with p_sem_rw_comp_auxiliary_ctx Γ Γ' Δ e τ (w : Γ ;;; Δ ||~ e : τ) :
  forall γ γ' δ, p_sem_rw_comp Γ Δ e τ w γ δ = p_sem_rw_comp (Γ ++ Γ') Δ e τ (p_has_type_rw_add_auxiliaries _ _ _ _ w Γ') (γ ; γ') δ.
Proof.
  +
    intros.
    dependent destruction w; easy_rewrite_uip;
      try (rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ p γ γ' tt); reflexivity);
      try (rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ w γ γ'); reflexivity);
      try (rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ w1 γ γ');
           rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ w2 γ γ'); reflexivity);
      try reflexivity.
    
    destruct γ.
    simpl; reflexivity.

    destruct γ.
    simpl.
    rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ w s0 γ'). 
    reflexivity.

    apply lp.
    apply dfun_ext; intro.
    rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ w (a, γ) γ'). 
    reflexivity.
   
  +
    intros.
    dependent destruction w; easy_rewrite_uip; try apply lp;
      try (rewrite <- eq_sym_app_assoc_tr;
           rewrite <- (p_sem_ro_ctx_rewrite _ _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ p Γ'));
           rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ p _ γ');
           reflexivity).
    
    rewrite <- (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w1 _ γ').
    apply pl.
    apply lp.
    apply dfun_ext; intro d.
    rewrite <- (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w2 _ γ').
    reflexivity.

    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (p_sem_ro_ctx_rewrite _ _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ p Γ')).
    rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ p _ γ').
    apply pl.
    apply lp.
    apply dfun_ext; intro.
    rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w _ γ' a).
    reflexivity.

    
    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (p_sem_ro_ctx_rewrite _ _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ p Γ')).
    rewrite (p_sem_ro_comp_auxiliary_ctx _ _ _ _ p _ γ').
    apply pl.
    apply lp.
    apply dfun_ext; intro.
    rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w1 _ γ').
    rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w2 _ γ').
    reflexivity.

    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (p_sem_ro_ctx_rewrite _ _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ p Γ')).
    rewrite <- (p_sem_ro_comp_auxiliary_ctx _ _ _ _ p _ γ').
    rewrite <- (p_sem_ro_ctx_rewrite _ _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ p0 Γ')).
    rewrite <- (p_sem_ro_comp_auxiliary_ctx _ _ _ _ p0 _ γ').
    rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w1 _ γ').
    rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w2 _ γ').
    reflexivity.

    apply pl.

    assert (forall X Y Z (f : X -> Y -> Z) a b c d, a = b -> c = d -> f a c = f b d).
    intros.
    destruct H, H0; reflexivity.
    apply H.

    apply dfun_ext.
    intros.
    rewrite <- eq_sym_app_assoc_tr.
    rewrite <- (p_sem_ro_ctx_rewrite _ _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ p Γ')).
    rewrite <- (p_sem_ro_comp_auxiliary_ctx _ _ _ _ p _ γ').
    reflexivity.

    apply dfun_ext.
    intros.
    rewrite (p_sem_rw_comp_auxiliary_ctx _ _ _ _ _ w _ γ').
    reflexivity.    
Qed.



Lemma sem_ro_comp_auxiliary_ctx :
  forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) γ γ', sem_ro_comp Γ e τ w γ = sem_ro_comp (Γ ++ Γ') e τ w' (γ; γ').
Proof.
  intros.
  rewrite (sem_ro_p_sem_ro _ _ _ _ (has_type_ro_phas_type_ro _ _ _ w)).
  rewrite (sem_ro_p_sem_ro _ _ _ _ (has_type_ro_phas_type_ro _ _ _ w')).
  rewrite <- (p_has_type_ro_unique _ _ _ (p_has_type_ro_add_auxiliaries _ _ _ (has_type_ro_phas_type_ro Γ e τ w) Γ') (has_type_ro_phas_type_ro (Γ ++ Γ') e τ w')).
  apply p_sem_ro_comp_auxiliary_ctx.
Defined.


Lemma sem_rw_comp_auxiliary_ctx : forall Γ Γ' Δ e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) γ γ' δ, sem_rw_comp Γ Δ e τ w γ δ = sem_rw_comp (Γ ++ Γ') Δ e τ w' (γ ; γ') δ.
Proof.
  intros.
  rewrite (sem_rw_p_sem_rw _ _ _ _ _ (has_type_rw_phas_type_rw _ _ _ _ w)).
  rewrite (sem_rw_p_sem_rw _ _ _ _ _ (has_type_rw_phas_type_rw _ _ _ _ w')).
  rewrite <- (p_has_type_rw_unique _ _ _ _ (p_has_type_rw_add_auxiliaries _ _ _ _ (has_type_rw_phas_type_rw Γ Δ e τ w) Γ') (has_type_rw_phas_type_rw (Γ ++ Γ') Δ e τ w')).
  apply p_sem_rw_comp_auxiliary_ctx.
Defined.
  
