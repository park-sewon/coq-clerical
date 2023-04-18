Require Import PowerdomainBase.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Equality.

(* things about infinite types *)
Section Infinity.
  
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

  
End Infinity.
