(* about the base of our type theory allowing Prop to be classical and some other trivally derived stuffs *)
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.


Axiom lem : forall P : Prop, P \/ ~P.

Axiom dcchoice : forall (A : nat -> Type) (P : forall n, A n -> Prop), (forall n : nat, exists a : A n, P n a) -> exists f : forall n, A n, forall n, P n (f n).

Lemma cchoice : forall (A : Type) (P : nat -> A -> Prop), (forall n : nat, exists a : A, P n a) -> exists f : nat -> A, forall n, P n (f n).
Proof.
  intros.
  apply (dcchoice (fun _ => A) P H).
Defined.

Axiom dchoice : forall (P : nat -> Type) (R : forall n, P n -> P (S n ) -> Prop),
    P 0 -> (forall n x, exists y, R n x y) -> exists (f : forall n, P n), forall n, R n (f n) (f (S n)).  


Axiom prop_ext : forall (P Q : Prop), (P -> Q) -> (Q -> P) -> P = Q.
Axiom dfun_ext : forall A (P : A-> Type) (f g : forall a, P a), (forall a, f a = g a) -> f = g.
Lemma pred_ext : forall A (P Q : A -> Prop), (forall a, P a -> Q a) -> (forall a, Q a -> P a) -> P = Q.
Proof.
  intros.
  apply dfun_ext.
  intro.
  apply prop_ext.
  apply (H a).
  apply (H0 a).
Defined.



Lemma prop_irrl : forall (P : Prop) (p q : P), p = q.
Proof.
  intros.
  assert (True = P).
  apply prop_ext; intro; auto.
  induction H.
  destruct p.
  destruct q.
  auto.
Defined.

Lemma dn_elim : forall P : Prop, ~~P -> P.
Proof.
  intros.
  destruct (lem P); auto.
  contradiction (H H0).
Qed.  

Lemma neg_exists_forall_neg (A : Type) : forall P : A -> Prop, (~ exists a, P a) -> forall a, ~ P a.
Proof.
  intros.
  intro.
  contradict H.
  exists a; auto.
Qed.

(* this is classical *)
Lemma neg_forall_exists_neg (A : Type) : forall P : A -> Prop, (~ forall a, P a) -> (exists a, ~ P a).
Proof.
  intros.
  destruct (lem (exists a, ~ P a)); auto.
  contradict H.
  intro.
  destruct (lem (P a)); auto.
  contradict H0.
  exists a; auto.
Qed.

Lemma impl_disj (P Q : Prop) : (P -> Q) -> (~ P) \/ Q.
Proof.
  intro.
  destruct (lem P).
  right; exact (H H0).
  left; exact H0.
Defined.

Lemma neg_disj (P Q : Prop) : ~ (P \/ Q) -> (~ P) /\ (~Q).
Proof.
  intro.
  split.
  intro.
  contradict H.
  left; auto.
  intro.
  contradict H.
  right; auto.
Defined.

Lemma neg_conj (P Q : Prop) : ~ (P /\ Q) -> (~ P) \/ (~Q).
Proof.
  intros; destruct (lem P); auto.
Defined.

Lemma sig_eq {X} (P : X -> Prop) (x y : {a | P a}) :
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros.
  destruct x, y.
  simpl in H.
  induction H.
  rewrite (prop_irrl _ p p0).
  auto.
Defined.

Lemma cchoice_or : forall P Q, (forall n : nat, P n \/ Q n) -> exists f : nat -> bool, forall n, if (f n) then (P n) else (Q n).
Proof.
  intros.  
  assert (forall n, exists b : bool, if b then (P n) else (Q n)).
  intro n.
  destruct (H n).
  exists true; auto.
  exists false; auto.
  apply (cchoice _ _ ) in H0.
  simpl in H0.
  exact H0.
Defined.

Definition tr {A : Type} (P : A -> Type) a b : (a = b) -> P a -> P b.
  intros e y.
  induction e.
  exact y.
Defined.

Definition lp : forall S T (f : S -> T) (a b : S), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  exact (eq_refl _).
Defined.

(* dependent choice with starting position *)
Lemma dchoice_start : forall (P : nat -> Type) (R : forall n, P n -> P (S n) -> Prop) x,
    (forall n x, exists y', R n x y') -> exists (f : forall n, P n), f 0 = x /\forall n, R n (f n) (f (S n)).  
Proof.
  intros.
  pose proof (dchoice (fun n => ((n = 0) * {y' : P 0 | y' = x}) + ((n <> 0) * P n))%type (fun n a b =>
                                                                                            match a with
                                                                                              inl (e, t) => match b with
                                                                                                            | inl _ => False
                                                                                                            | inr (_, y) => R 0 x
                                                                                                                              (tr _ _ _ (lp _ _ S _ _ e) y)
                                                                                                            end
                                                                                            | inr (_, x') => match b with
                                                                                                             | inl _ => False
                                                                                                             | inr (_, y) => R n x' y
                                                                                                             end
                                                                                            end)
    ) as [f h].
  left; split; auto.
  exists x; auto.
  intros.
  
  destruct x0.
  destruct p.
  destruct (eq_sym e).
  assert (1 <> 0).
  auto.
  destruct (H 0 x).
  exists (inr (H0, x0)).
  rewrite (prop_irrl _ e eq_refl). 
  simpl.
  auto.
  destruct p.
  assert (S n <> 0).
  auto.
  destruct (H n p).
  exists (inr (H0, x0)).
  auto.
  assert (forall n, (n = 0) + (n <> 0)).
  auto.
  intro.
  destruct (lt_eq_lt_dec n 0).
  destruct s.
  right; auto.
  lia.
  left; auto.
  right; lia.
  exists (fun n => match (H0 n) with
                   | inl e => match f n with
                              | inl _ => (tr _ _ _ (eq_sym e) x)
                              | inr (ne, _) => False_rect _ (ne e)
                              end
                   | inr ne => match f n with
                               | inl (e, _) => False_rect _ (ne e)
                               | inr (_, y) => y
                               end
                   end
         ).
  split.
  destruct (H0 0).
  destruct (f 0).
  rewrite (prop_irrl _ (eq_sym e) eq_refl). 
  auto.
  destruct p.
  contradict n; auto.
  contradict n; auto.
  intros.
  destruct (H0 n).
  destruct (H0 (S n)).
  contradict (e0).
  auto.
  pose proof (h n).
  destruct (f n).
  destruct p.
  destruct (f (S n)).
  contradict H1.
  destruct p.
  destruct e.
  simpl.
  rewrite (prop_irrl _ (e0) eq_refl) in H1.
  simpl in H1; auto.
  destruct p.
  contradict n1; auto.
  destruct (H0 (S n)).
  contradict e.
  auto.
  pose proof (h n).
  destruct (f n).
  destruct p.
  contradict n0; auto.
  destruct p.
  destruct (f (S n)).
  contradict H1.
  destruct p0.
  auto.
Defined.


Lemma projT2_eq {A} {P : A -> Type} {a} {x y : P a} : @existT A P a x = @existT A P a y -> x = y.
Proof.
  intro.
  dependent destruction H.
  apply eq_refl.
Qed.



Ltac easy_rewrite_uip :=
  repeat (try unfold simplification_heq; try unfold solution_left; try unfold eq_rect_r; try rewrite (prop_irrl _ (eq_sym _) eq_refl); simpl).


Ltac use_eq_l id :=
  induction id; clear id.
Ltac use_eq_r id :=
  induction (eq_sym id); clear id.
Ltac unfold_existT id :=
  repeat apply projT2_eq in id.

Inductive ltac_No_arg : Set :=
  | ltac_no_arg : ltac_No_arg.
Ltac unfold_existT_mul x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 :=
  match type of x1 with 
  | ltac_No_arg => idtac "base case reached"
  | _ =>
      unfold_existT x1; 
      unfold_existT_mul x2 x3 x4 x5 x6 x7 x8 x9 x10 ltac_no_arg
  end.
Ltac unfold_existT_mul' x1 x2 x3 x4 :=
  match type of x1 with 
  | ltac_no_arg => idtac "base case reached"
  | _ =>
      unfold_existT x1; 
      unfold_existT_mul' x2 x3 x4 ltac_no_arg
  end.

Tactic Notation "unwind" constr(x1) :=
  unfold_existT_mul x1 ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2):=
  unfold_existT_mul x1 x2 ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3):=
  unfold_existT_mul x1 x2 x3 ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4):=
  unfold_existT_mul x1 x2 x3 x4 ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5):=
  unfold_existT_mul x1 x2 x3 x4 x5 ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6):=
  unfold_existT_mul x1 x2 x3 x4 x5 x6 ltac_no_arg ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7):=
  unfold_existT_mul x1 x2 x3 x4 x5 x6 x7 ltac_no_arg ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) constr(x8):=
  unfold_existT_mul x1 x2 x3 x4 x5 x6 x7 x8 ltac_no_arg ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9):=
  unfold_existT_mul x1 x2 x3 x4 x5 x6 x7 x8 x9 ltac_no_arg.
Tactic Notation "unwind" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9) constr(x10):=
  unfold_existT_mul x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
