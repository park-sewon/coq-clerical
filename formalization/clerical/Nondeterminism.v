(* classical treatment of our powerdomain ... maybe this makes some people upset :( *)
(* I also uses dependent destruction... what does it do really *)
Require Import Coq.Program.Equality.

(* random stuffs *)
Axiom lem : forall P : Prop, P \/ ~P.
Axiom cchoice : forall (A : Type) (P : nat -> A -> Prop), (forall n : nat, exists a : A, P n a) -> exists f : nat -> A, forall n, P n (f n).
Axiom prop_ext : forall (P Q : Prop), (P -> Q) -> (Q -> P) -> P = Q.

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

Definition lp : forall S T (f : S -> T) (a b : S), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  exact (eq_refl _).
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

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall a b, f a = f b -> a = b.

Lemma proj1_sig_injective :  forall {A : Type} (P : A -> Prop), injective (@proj1_sig A P).
Proof.
  intros A P x y e.
  destruct x.
  destruct y.
  simpl in e.
  induction e.
  induction (prop_irrl _ p p0).
  auto.
Defined.

Definition surjective {A B} (f : A -> B) : Prop :=
  forall b, exists a, f a = b.

Definition infinite (A : Type) : Prop :=
  exists f : nat -> A, injective f.

Definition ninfinite A := ~infinite A.

Definition nat_upper_bound (P : nat -> Prop) n : Prop := forall x, P x -> x <= n.
Definition nat_max (P : nat -> Prop) n : Prop :=
  nat_upper_bound P n /\ P n.

Require Import Coq.Arith.Compare_dec.
Lemma step_monotone_monotone : forall (f : nat -> nat), (forall n, f n < f (S n)) -> forall n m, n < m -> f n < f m.
Proof.
  intros.
  induction H0.
  exact (H n).
  exact (PeanoNat.Nat.lt_trans _ _ _ IHle (H m)).
Defined.

Lemma inc_seq_injective : forall (f : nat -> nat), (forall n, f n < f (S n)) -> injective f.
Proof.
  intros f H n m e.
  pose proof (step_monotone_monotone f H).
  destruct (lt_eq_lt_dec n m).
  destruct s.
  pose proof (H0 _ _ l).
  contradict H1.
  rewrite e; apply PeanoNat.Nat.lt_irrefl.
  exact e0.
  pose proof (H0 _ _ l).
  contradict H1.
  rewrite e; apply PeanoNat.Nat.lt_irrefl.
Defined.

Lemma finite_set_upper_bounded : forall (P : nat -> Prop), ninfinite {n | P n} -> exists n, nat_upper_bound P n.
Proof.
  intros.
  destruct (lem (exists n, nat_upper_bound P n)); auto.
  pose proof (neg_exists_forall_neg _ _ H0).
  assert (forall n : nat, exists m : nat, m > n /\ P m).
  {
    intro.
    pose proof (H1 n).
    apply neg_forall_exists_neg in H2.
    destruct H2.
    exists x.
    destruct (lem (x > n /\ P x)); auto.
    apply neg_conj in H3.
    contradict H2.
    intro.
    destruct H3.
    apply not_lt; auto.
    contradict (H3 H2).
  }
  apply (cchoice _) in H2.
  destruct H2.
  assert (infinite {n : nat | P n}).
  pose (fun n => nat_rec _  (x 0) (fun _ k => x k) n) as f.
  assert (forall n, P (f n)).
  intro.
  destruct n.
  simpl.
  destruct (H2 0); auto.
  simpl.
  destruct (H2 (f n)); auto.
  exists (fun n => exist _ (f n) (H3 n)).
  intros n m e.
  injection e.
  intro.
  assert (injective f) as ij.
  {
    apply inc_seq_injective.
    intro.
    simpl.
    destruct (H2 (f n0)); auto.
  }
  apply ij; auto.
  contradict (H H3).
Defined.

Require Import Coq.Arith.Wf_nat.
Lemma nat_wf : forall (P : nat -> Prop), (exists n, P n) -> exists m, P m /\ forall n, P n -> m <= n.
Proof.
  intros.
  pose proof (dec_inh_nat_subset_has_unique_least_element P (fun n => (lem (P n))) H).
  unfold has_unique_least_element in H0.
  destruct H0.
  exists x.
  destruct H0.
  exact H0.
Defined.


Lemma finite_set_max : forall (P : nat -> Prop), ninfinite {n | P n} -> (exists n, P n) -> exists n, nat_max P n.
Proof.
  intros.
  destruct (nat_wf (fun n => nat_upper_bound P n) (finite_set_upper_bounded P H)).
  assert (P x).
  destruct (lem (P x)); auto.
  destruct x.
  destruct H0.
  destruct x.
  contradict (H2 H0).
  destruct H1.
  pose proof (H1 _ H0).
  contradict H4.
  apply PeanoNat.Nat.nle_succ_0.
  destruct H1.
  assert (nat_upper_bound P x).
  intros m p.
  pose proof (H1 _ p).
  assert (m = S x \/ S m <= S x).
  destruct H4.
  left; auto.
  right; apply le_n_S; auto.
  destruct H5.
  rewrite H5 in p.
  contradict (H2 p).
  apply le_S_n; auto.
  apply H3 in H4.
  contradict (PeanoNat.Nat.nle_succ_diag_l _ H4).
  exists x.
  split; destruct H1; auto.
Defined.

  
Lemma Pigeon2' : forall {A} {P Q : A -> Prop},
    infinite {a | P a \/ Q a} -> infinite {a | P a} \/ infinite {a | Q a}.
Proof.
  intros A P Q [f h].
  destruct (lem (infinite {n | P (proj1_sig (f n))})).
  {
    left.
    destruct H as [g hh].
    exists (fun n => exist _ (proj1_sig (f (proj1_sig (g n)))) (proj2_sig (g n))).
    intros n m e.
    injection e; intros.
    apply proj1_sig_injective in H.
    apply h in H.
    apply proj1_sig_injective in H.
    apply hh in H; auto.
  }
  destruct (lem (infinite {n | Q (proj1_sig (f n))})).
  {
    right.
    destruct H0 as [g hh].
    exists (fun n => exist _ (proj1_sig (f (proj1_sig (g n)))) (proj2_sig (g n))).
    intros n m e.
    injection e; intros.
    apply proj1_sig_injective in H0.
    apply h in H0.
    apply proj1_sig_injective in H0.
    apply hh in H0; auto.
  }
  apply finite_set_upper_bounded in H.
  apply finite_set_upper_bounded in H0.
  destruct H as [x hx].
  destruct H0 as [y hy].
  pose proof (f (S (max x y))).
  assert (P (proj1_sig (f (S (max x y)))) \/ Q (proj1_sig (f (S (max x y)))))
    by (destruct (f (S (max x y))); simpl; auto).
  destruct H.
  {
    pose proof (hx (S (Nat.max x y)) H).
    pose proof (PeanoNat.Nat.le_max_l x y).
    apply le_n_S in H1.
    pose proof (PeanoNat.Nat.le_trans _ _ _ H1 H0).
    contradict H2.
    apply PeanoNat.Nat.nle_succ_diag_l.
  }
  {
    pose proof (hy (S (Nat.max x y)) H).
    pose proof (PeanoNat.Nat.le_max_r x y).
    apply le_n_S in H1.
    pose proof (PeanoNat.Nat.le_trans _ _ _ H1 H0).
    contradict H2.
    apply PeanoNat.Nat.nle_succ_diag_l.
  }
Defined.
  
Lemma tr {A} (B : A -> Type) {x y : A} (p : x = y) : B x -> B y.
Proof.
  destruct p.
  exact (fun x => x). 
Defined.

Definition apd {A} {B : A -> Type} (f : forall x, B x) {x y} (p : x = y) :
  (tr B p (f x)) = (f y).
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma Pigeon : forall {A : Type} (P : A -> Type),
    infinite {a : A & P a} ->
    infinite A \/ exists a : A, infinite (P a).
Proof.
  intros.
  destruct (lem (infinite A \/ exists a : A, infinite (P a))); auto.
  apply neg_disj in H0.
  destruct H0 as [p q']; pose proof (neg_exists_forall_neg _ _ q') as q; clear q'.
  destruct H as [f inj].
  pose (fun a : A => {n : nat | projT1 (f n) = a}) as fiber.
  assert (forall a, ninfinite (fiber a)).
  {
    intro.
    intro.
    assert (infinite (P a)).
    {
      unfold fiber in H.
      destruct H as [g h].
      exists (fun n => tr P (proj2_sig (g n)) (projT2 (f (proj1_sig (g n))))).
      intros i j e.
      case_eq (g i); intros.
      case_eq (g j); intros.
      rewrite H in e.
      rewrite H0 in e.
      simpl in e.
      destruct e0.
      simpl in e.
      assert (x = x0).
      {
        clear H H0.
        apply inj.
        destruct (f x).
        destruct (f x0).
        simpl in e1, e.
        destruct e1.
        simpl in e.
        destruct e.
        auto.
      }
      destruct H1.
      apply h.
      rewrite H, H0.
      clear H H0 e.
      rewrite (prop_irrl _ e1 eq_refl).
      auto.
    }
    exact (q _ H0).
  }
  pose ({n : nat | exists a, nat_max (fun m => projT1 (f m) = a) n}) as S.
  assert (ninfinite S).
  intros [g h].
  contradict p.
  exists (fun n => projT1 (f (proj1_sig (g n)))).
  intros i j e.
  apply h.
  destruct (g i), (g j); simpl in e.  
  unfold nat_max in e0, e1.
  assert (x = x0).
  {
    destruct e0 as [a [p pp]].
    destruct e1 as [c [r rr]].
    rewrite pp in e.
    rewrite rr in e.
    induction e.
    pose proof (p _ rr).
    pose proof (r _ pp).
    apply PeanoNat.Nat.le_antisymm; auto.
  }
  induction H0.
  rewrite (prop_irrl _ e0 e1); auto.
  (* now the real proof *)
  apply finite_set_upper_bounded in H0.
  destruct H0.

  assert (forall n, n <= x).
  intro n.
  case_eq (f n); intros.
  destruct (finite_set_max (fun n => projT1 (f n) = x0) (H x0)).
  exists n; rewrite  H1; simpl; auto.
  assert (n <= x1).
  apply H2.
  rewrite H1; auto.
  assert (x1 <= x).
  apply H0.
  exists x0.
  exact H2.
  apply (PeanoNat.Nat.le_trans _ _ _ H3 H4).
  clear S.
  pose proof (H1 (S x)).
  contradict H2.
  apply PeanoNat.Nat.nle_succ_diag_l.
Defined.

Lemma forall_or (A : Type) (P Q : A -> Prop) : (forall a, P a \/ Q a) -> (exists a, P a) \/ (forall a, Q a).
Proof.
  intros.
  destruct (lem (exists a, P a)).
  left; auto.
  right.
  pose proof (neg_exists_forall_neg _ _ H0).
  intro a.
  pose proof (H a).
  destruct H2; auto.
  contradict (H1 a H2).
Defined.

(* some more stuffs about infinity and non-infinity *)
Lemma surjection_infinite {A B} (f : A -> B) : surjective f -> infinite B -> infinite A.
Proof.
  intros s [e inj].
  assert (forall n, exists a, f a = (e n)) by (intro n; destruct (s (e n)) as [a h]; exists a; auto).
  apply cchoice in H.
  destruct H as [en h].
  exists en.
  intros n m hh.
  apply inj.
  rewrite <- h, <- h.
  rewrite hh; auto.
Defined.

Lemma surjection_infinite2 {A B} : (exists f : A -> B, surjective f) -> infinite B -> infinite A.
Proof.
  intros [f s] h.
  apply (surjection_infinite f s h).
Defined.




Lemma hprop_ninfinite A : (forall x y : A, x = y) -> ninfinite A.
Proof.
  intros e [f u].
  pose proof (u 0 1 (e (f 0) (f 1))).
  contradict H; auto.
Defined.

Lemma bool_ninfinite : ninfinite bool.
Proof.
  unfold ninfinite; unfold infinite.
  intros [f H].
  contradict H.
  intro.  
  case_eq (f 0); intro; case_eq (f 1); intro.
  assert (0 = 1) by (apply H; induction H0; auto).
  contradict H2; auto.
  case_eq (f 2); intro.
  assert (0 = 2) by (apply H; induction H0; auto).
  contradict H3; auto.
  assert (1 = 2) by (apply H; induction H2; auto).
  contradict H3; auto.
  case_eq (f 2); intro.
  assert (1 = 2) by (apply H; induction H2; auto).
  contradict H3; auto.
  assert (0 = 2) by (apply H; induction H0; auto).
  contradict H3; auto.
  assert (0 = 1) by (apply H; induction H1; auto).
  contradict H2; auto.
Defined.

Lemma Pigeon2 : forall {A B : Type}, infinite (A + B) -> infinite A \/ infinite B.
Proof.
  intros.
  assert (infinite {b : bool & if b then A else B}).
  destruct H as [f e].
  exists (fun n =>
            match f n with
            | inl x => existT (fun b : bool => if b then A else B) true x
            | inr y => existT (fun b : bool => if b then A else B) false y
            end).
  intros i j eq.
  case_eq (f i).
  case_eq (f j).
  intros.
  rewrite H in eq.
  rewrite H0 in eq.
  dependent destruction eq.
  apply e; rewrite H, H0; auto.
  intros.
  rewrite H in eq; rewrite H0 in eq.
  dependent destruction eq.
  intros.
  case_eq (f j); intros.
  rewrite H in eq; rewrite H0 in eq.
  dependent destruction eq.
  rewrite H in eq; rewrite H0 in eq.
  dependent destruction eq.
  apply e; rewrite H, H0; auto.
  apply Pigeon in H0.
  destruct H0.
  contradict (bool_ninfinite H0).
  destruct H0.
  destruct x.
  left; auto.
  right; auto.
Defined.


Lemma sum_ninfinite A B : ninfinite A -> ninfinite B -> ninfinite (A + B).
Proof.
  intros f g i.
  destruct (Pigeon2 i).
  exact (f H).
  exact (g H).
Defined.

Lemma injection_ninfinite {A B} (f : A -> B) : injective f -> ninfinite B -> ninfinite A.
Proof.
  intros i y [s q].
  assert (infinite B).
  exists (fun n => (f (s n))).
  intros n m e.
  apply i in e.
  apply q in e.
  exact e.
  exact (y H).
Defined.

Lemma subset_ninfinte A (P : A -> Prop) : ninfinite A -> ninfinite {a | P a}.
Proof.
  apply (injection_ninfinite (@proj1_sig A P)).
  intros [x p] [y q] e.
  simpl in e.
  induction e.
  induction (prop_irrl _ p q).
  auto.
Defined.

Lemma inl_neq_inr {X Y} {x : X} {y : Y} : inl x <> inr y.
Proof.
  pose (fun z : X+ Y => match z with inl _ => 0 | inr _ => 1 end). 
  intro.
  pose proof (lp _ _ n _ _ H).
  simpl in H0.
  contradict H0; auto.
Defined.

Lemma inr_neq_inl {X Y} {x : X} {y : Y} : inr x <> inl y.
Proof.
  apply not_eq_sym, inl_neq_inr.
Defined.
  
(* Flat domain *)
Inductive flat (A : Type) :=
  bot : flat A
| total : A -> flat A.
Arguments total {_}.

Lemma flat_ninfinite A : ninfinite A -> ninfinite (flat A).
Proof.
  intros.
  assert (ninfinite (A + unit)).
  apply sum_ninfinite; auto.
  apply hprop_ninfinite; intros; auto.
  destruct x, y; auto.
  apply (injection_ninfinite (fun x => match x with total a => inl a | bot _ => inr tt end)).
  intros x y.
  destruct x, y; intros; auto.
  contradict (inr_neq_inl H1).
  contradict (inl_neq_inr H1).
  injection H1.
  intro e; rewrite e; auto.
  exact H0.
Defined.

Definition pset (A : Type) := A -> Prop.

Definition pset_infinite {A} (S : pset A) :=
  exists f : nat -> A, injective f /\ forall n, (S (f n)). 

Lemma pset_infinite_subset_infinite {A} {S : pset A} : pset_infinite S -> infinite {a | S a}.
Proof.
  intros [f [i j]].
  exists (fun n => exist (fun b => S b) (f n) (j n)).
  intros n m e.
  injection e.
  intro.
  apply i; auto.
Defined.

Lemma subset_infinite_pset_infinite {A} {S : pset A} : infinite {a | S a} -> pset_infinite S.
Proof.
  intros [f i]. 
  exists (fun n =>  (proj1_sig (f n))).
  split.
  intros n m e.
  apply proj1_sig_injective in e.
  apply i in e.
  exact e.
  intro n; destruct (f n); auto.
Defined.

Definition pdom (A : Type)
  := {S : pset (flat A) | pset_infinite S -> S (bot A)}.

Definition pdom_char {A} : pdom A -> pset (flat A).
Proof.
  intros [f _].
  exact f.
Defined.

Lemma pdom_infinite_bot {A} (S : pdom A) : pset_infinite (pdom_char S) -> pdom_char S (bot A).
Proof.
  destruct S; simpl; auto.
Defined.
  
Definition pdom_nempty {A : Type} : pdom A -> Prop := fun S => exists a, pdom_char S a.

(* powerdomain is a monad *)
Definition pdom_unit {A : Type} : A -> pdom A.
Proof.
  intro a.
  exists (fun b => total a = b).
  intro.
  assert (ninfinite {a0 | total a = a0}).
  apply hprop_ninfinite.
  intros.
  destruct x, y.
  assert (x = x0) by (rewrite <-e, <- e0; auto).
  induction H0.
  rewrite (prop_irrl _ e e0).
  auto.
  contradict (H0 (pset_infinite_subset_infinite H)).
Defined.

Definition pdom_lift' {A B : Type} (f : A -> B) : flat A -> flat B.
Proof.
  intro.
  destruct X.
  exact (bot B).
  exact (total (f a)).
Defined.

Definition pdom_lift {A B : Type} (f : A -> B) : pdom A -> pdom B.
Proof.
  intro.
  exists (fun b => exists a : flat A, pdom_char X a /\ pdom_lift' f a = b).
  intro.
  assert (infinite {a | pdom_char X a}).
  {
    apply pset_infinite_subset_infinite in H.
    apply (fun h => surjection_infinite2 h H).
    exists (fun x => match x with exist _ a p => exist _ (pdom_lift' f a) (ex_intro _ a (conj p eq_refl)) end). 
    intros [b [a [h1 h2]]].
    exists (exist _ a h1).
    rewrite <- h2.
    auto.
  }
  pose proof (pdom_infinite_bot X (subset_infinite_pset_infinite H0)).
  exists (bot A); unfold pdom_lift'; auto.
Defined.

Definition pdom_mult {A : Type} : pdom (pdom A) -> pdom A.
Proof.
  intros X.
  exists (fun a =>
            (* X is not empty *)
            pdom_nempty X /\
              (* all subsets are not empty *)
              (forall S : pdom A, pdom_char X (total S) -> pdom_nempty S) /\
              (* a can be bot if X contains bot *)
              (a = bot A /\ (pdom_char X (bot (pdom A)))
               (* otherwise, there exists S \in X such that a is in S *)
               \/ exists S, pdom_char S a /\ pdom_char X (total S))).
  intro.

  destruct H as [f [a b]].
  repeat split.
  destruct (b 0) as [t1 [t2 t3]]; auto.
  destruct (b 0) as [t1 [t2 t3]]; auto.
  assert (forall n : nat,
             (f n = bot A /\ pdom_char X (bot (pdom A)) \/ (exists S : pdom A, pdom_char S (f n) /\ pdom_char X (total S)))).
  intro.
  destruct (b n) as [_ [_ p]]; auto.
  clear b.
  destruct (forall_or _ _ _ H).
  destruct H0.
  left; destruct H0; split; auto.
  clear H.
  destruct (cchoice _ _ H0).
  pose (fun a : {aa : pdom A | pdom_char X (total aa)} => {x : flat A | pdom_char (proj1_sig a) x}) as T.
  pose (fun n => @existT _ T (exist _ (x n) (proj2 (H n))) (@exist (flat A) (fun y => pdom_char (x n) y) (f n) (proj1 (H n)))) as s.
  assert (injective s) as H1.
  {  
    unfold s.
    intros n m e.
    injection e.
    intros.
    exact (a n m H1).
  }
  pose proof (Pigeon _ (ex_intro _ s H1)).
  
  clear H1.
  destruct H2.
  {
    (* when index set is infinite *)
    destruct H1.
    assert (pset_infinite (pdom_char X)).
    exists (fun n => total (proj1_sig (x0 n))).
    split.
    intros i j e.
    injection e.
    intro.
    apply proj1_sig_injective in H2.
    apply H1 in H2.
    exact H2.
    intro.
    destruct (x0 n).
    simpl.
    exact p.
    left.
    split; auto.
    destruct X.
    simpl in H2.
    simpl.
    exact (p H2).
  }
  
  {
    (* when there is infinite fiber *)
    right.
    destruct H1.
    destruct x0.
    exists x0.
    split; auto.
    assert (pset_infinite (pdom_char x0)).
    destruct H1.
    exists (fun n => proj1_sig (x1 n)).
    split.
    intros n m e.
    apply proj1_sig_injective in e.
    apply H1 in e.
    auto.
    intro .
    destruct (x1 n); simpl.
    simpl in p0.
    exact p0.
    destruct x0 as [z y].
    pose proof (y H2).
    simpl.
    exact H3.
  }
Defined.

Definition pdom_bind {A B : Type} (f : A -> pdom B) : pdom A -> pdom B := fun S => pdom_mult (pdom_lift f S).

Definition flat_to_pdom {A : Type} : flat A -> pdom A.
Proof.
  intro x.
  exists (fun y => x = y).
  intro i.
  contradict i.
  intro.
  destruct H as [f [i j]].
  pose proof (i 0 1).
  assert (0 = 1).
  apply H; rewrite <- j; rewrite <- j; auto.
  contradict H0; auto.
Defined.  

Definition pdom_prod {A B : Type} :  (pdom A) -> (pdom B) -> pdom (A * B).
Proof.
  intro.
  apply pdom_bind.
  intro b.
  apply (pdom_lift (fun a => (a, b)) X).
Defined.

Definition pdom_lift2 {A B C : Type} : (A -> B -> C) -> pdom A -> pdom B -> pdom C.
Proof.
  intros f X Y.
  exact (pdom_lift (fun ab => f (fst ab) (snd ab)) (pdom_prod X Y)).
Defined.

Definition pdom_bind2 {A B C : Type} : (A -> B -> pdom C) -> pdom A -> pdom B -> pdom C.
Proof.
  intros f X Y.
  exact (pdom_bind (fun ab => f (fst ab) (snd ab)) (pdom_prod X Y)).
Defined.

(* Lemma bool_is_not_infinite : forall f : nat -> bool, injective f -> False. *)
(* Proof. *)
(*   intros. *)
(*   contradict H. *)
(*   intro.   *)

(*   case_eq (f 0); intro. *)
(*   case_eq (f 1); intro. *)
(*   assert (0 = 1). *)
(*   apply H. *)
(*   induction H0. *)
(*   auto. *)
(*   contradict H2; auto. *)
(*   case_eq (f 2); intro. *)
(*   assert (0 = 2). *)
(*   apply H. *)
(*   induction H0. *)
(*   auto. *)
(*   contradict H3; auto. *)
(*   assert (1 = 2). *)
(*   apply H. *)
(*   induction H2. *)
(*   auto. *)
(*   contradict H3; auto. *)
(*   case_eq (f 1); intro. *)
(*   case_eq (f 2); intro. *)
(*   assert (1 = 2). *)
(*   apply H. *)
(*   induction H2. *)
(*   auto. *)
(*   contradict H3; auto. *)
(*   assert (0 = 2). *)
(*   apply H. *)
(*   induction H0. *)
(*   auto. *)
(*   contradict H3; auto. *)
(*   assert (0 = 1). *)
(*   apply H. *)
(*   induction H1. *)
(*   auto. *)
(*   contradict H2; auto. *)
(* Defined. *)


(* Definition strict_union {X : Type} : pdom X -> pdom X -> pdom X. *)
(* Proof. *)
(*   intros S T. *)
(*   pose (pdom_bind (fun b : bool => if b then S else T)). *)
(*   assert (pdom bool). *)
(*   { *)
(*     (* construct {true, false} as pdom *) *)
(*     exists (fun b => b = total true \/ b = total false). *)
(*     intro. *)
(*     contradict H. *)
(*     intro. *)
(*     destruct H. *)
(*     destruct H. *)
(*     destruct (H0 0). *)
(*     destruct (H0 1). *)
(*     assert (0 = 1). *)
(*     apply H. *)
(*     induction H1. *)
(*     auto. *)
(*     contradict H3; auto. *)
(*     destruct (H0 2). *)
(*     assert (0 = 2). *)
(*     apply H. *)
(*     induction H1. *)
(*     auto. *)
(*     contradict H4; auto. *)
(*     assert (1 = 2). *)
(*     apply H. *)
(*     induction H2. *)
(*     auto. *)
(*     contradict H4; auto. *)
(*     destruct (H0 1). *)
(*     destruct (H0 2). *)
(*     assert (1 = 2). *)
(*     apply H. *)
(*     induction H2. *)
(*     auto. *)
(*     contradict H4; auto. *)
(*     assert (0 = 2). *)
(*     apply H. *)
(*     induction H1. *)
(*     auto. *)
(*     contradict H4; auto. *)
(*     assert (0 = 1). *)
(*     apply H. *)
(*     induction H1. *)
(*     auto. *)
(*     contradict H3; auto. *)
(*   } *)
(*   exact (p X0). *)
(* Defined. *)

Definition pdom_flat_unit {X : Type} : flat X -> pdom X.
Proof.
  intro x.
  exists (fun y => x = y).
  intro.
  contradict H.
  intro.
  destruct H as [f [a b]].
  assert (0 = 1).
  apply (a 0 1).
  rewrite <- b.
  rewrite <- b.
  auto.
  contradict H; auto.
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
     
  
Definition pdom_case2' (X : Type)
  (b1 b2 : pdom bool)
  (c1 c2 : pdom X)
  (x : nat -> flat X)
  (H : injective x)
  (f : nat -> bool)
  (u : forall n : nat, if f n then pdom_char b1 (total true) /\ pdom_char c1 (x n) else pdom_char b2 (total true) /\ pdom_char c2 (x n))
  : nat ->
         {b : bool &
         if b then {j : flat X | pdom_char b1 (total true) /\ pdom_char c1 j} else {j : flat X | pdom_char b2 (total true) /\ pdom_char c2 j}}.
Proof.
  intro n.
  exists (f n).
  case_eq (f n).
  intro.
  pose proof (u n).
  rewrite H0 in H1.
  exists (x n); auto.
  intro.
  pose proof (u n).
  rewrite H0 in H1.
  exists (x n); auto.
Defined.


Definition pdom_case2 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) : pdom X.
Proof.
  exists
    (
      fun x =>
        (* empty condition *)
        (pdom_nempty b1 /\ pdom_nempty b2)
        /\
          (pdom_char b1 (total true) -> pdom_nempty c1)
        /\
          (pdom_char b2 (total true) -> pdom_nempty c2)
        /\
          (* values *)
          (
            (pdom_char b1 (total true) /\ pdom_char c1 x)
            \/
              (pdom_char b2 (total true) /\ pdom_char c2 x)
            \/
              (pdom_char b1 (bot bool) /\ pdom_char b2 (bot bool) /\ x = bot X)
          )
    ).
  (* when the result is infinte *)
  (* (1) the result is non empty *)
  intro.
  destruct H.
  destruct H.
  split.
  destruct (H0 0); auto.
  split.
  destruct (H0 0).
  destruct H2; auto.
  split.
  destruct (H0 0).
  destruct H2.
  destruct H3; auto.

  (* now clean the assumption to the cases *)
  assert (forall n : nat,
              (pdom_char b1 (bot bool) /\ pdom_char b2 (bot bool) /\ x n = bot X) \/
                (pdom_char b1 (total true) /\ pdom_char c1 (x n) \/
                   pdom_char b2 (total true) /\ pdom_char c2 (x n))).
  intro n.
  destruct (H0 n) as [a [b [c d]]].
  destruct d; auto.
  destruct H1; auto.  
  clear H0.
  destruct (forall_or _ _ _ H1).
  destruct H0.
  right.
  right.
  destruct H0 as [a [b c]]; split; auto.
  clear H1.

  (* decide which branch is infinite *)
  assert (infinite {a : flat X | pdom_char b1 (total true) /\ pdom_char c1 a} \/ infinite {a : flat X | pdom_char b2 (total true) /\ pdom_char c2 a}).
  {
    apply Pigeon2'.
    exists (fun n => exist _ (x n) (H0 n)); auto.
    intros n m e.
    injection e; intro.
    apply H; auto.
  }
  destruct H1.
  {
    (* when c1 is infinite *)
    left.
    destruct H1 as [f h]; destruct (f 0) as [a [b c]].
    split; auto.
    apply pdom_infinite_bot.
    exists (fun n => proj1_sig (f n)).
    split; auto.
    intros n m e.
    apply proj1_sig_injective in e.
    apply h in e; auto.
    intro; destruct (f n) as [j [jj jjj]]; simpl; auto.
  }
  {
    (* when c2 is infinite *)
    right; left.
    destruct H1 as [f h]; destruct (f 0) as [a [b c]].
    split; auto.
    apply pdom_infinite_bot.
    exists (fun n => proj1_sig (f n)).
    split; auto.
    intros n m e.
    apply proj1_sig_injective in e.
    apply h in e; auto.
    intro; destruct (f n) as [j [jj jjj]]; simpl; auto.
  }
Defined.

Definition pdom_W {X : Type} (b : X -> pdom bool) (c : X -> pdom X) : (X -> pdom X) -> X -> pdom X.
Proof.
Admitted.


Definition pdom_while {X : Type} : (X -> pdom bool) -> (X -> pdom X) -> X -> pdom X.
Proof.
  intros B C.
Admitted.

