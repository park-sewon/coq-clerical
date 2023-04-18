Require Import Coq.Arith.Compare_dec.
Require Import Lia.

Require Import PowerdomainBase.
Require Import PowerdomainInfinite.
Require Import PowerdomainMonad.
Require Import PowerdomainProperties.

Section PartialOrder.
  Definition pdom_incl {X : Type} (S T : pdom X) :=
    forall x : flat X, proj1_sig S x -> proj1_sig T x.

  Definition pdom_le {X : Type} (S T : pdom X) :=
    S = T \/ (proj1_sig S (bot X) /\ (pdom_is_empty T \/ pdom_incl S (pdom_add_elem T (bot X)))).

  Infix "⊑" := (pdom_le) (at level 80).

  Lemma pdom_le_refl {X : Type} : forall (S : pdom X), S ⊑ S.
  Proof.
    intros.
    left; auto.
  Defined.

  Lemma pdom_is_empty_le_is_empty {X : Type} : forall (S T : pdom X), S ⊑ T -> pdom_is_empty S -> pdom_is_empty T.
  Proof.
    intros.
    destruct H.
    rewrite <- H; auto.
    destruct H.
    contradict H.
    intro.
    exact (H0 _ H).
  Defined.

  Lemma pdom_le_trans {X : Type} : forall (S T R : pdom X), S ⊑ T -> T ⊑ R -> S ⊑ R.
  Proof.
    intros.
    case_eq H; intros.
    case_eq H0; intros.
    left; rewrite e, e0; auto.
    clear H1; induction e; right; auto.
    case_eq H0; intros.
    clear H2; induction e; right; auto.
    clear H1 H2.
    destruct a, a0.
    right.
    split; auto.
    destruct H4.
    left; auto.
    destruct H2.
    left.
    apply (pdom_is_empty_le_is_empty _ _ H0 H2).
    right.
    intros n e.
    pose proof (H2 n e).
    destruct n.
    auto.
    apply H4.
    destruct T.
    simpl.
    simpl in H5.
    destruct H5; auto.
    contradict H5.
    apply flat_bot_neq_total.
  Defined.

  Lemma pdom_le_asym {X : Type} : forall (x y : pdom X), x ⊑ y -> y ⊑ x -> x = y.
  Proof.
    intros.
    case_eq H; intros; auto.
    case_eq H0; intros; auto.
    destruct a.
    destruct o.
    pose proof (pdom_is_empty_le_is_empty _ _ H0 p0).
    rewrite (pdom_is_empty_is_empty _ p0).
    rewrite (pdom_is_empty_is_empty _ H3).
    auto.
    destruct a0.
    destruct o.
    pose proof (pdom_is_empty_le_is_empty _ _ H p2).
    rewrite (pdom_is_empty_is_empty _ p2).
    rewrite (pdom_is_empty_is_empty _ H3).
    auto.
    clear H1 H2.
    apply sig_eq.
    destruct x, y.
    simpl; simpl in p1, p2, p, p0.
    apply pred_ext.
    intros.
    destruct a; auto.
    pose proof (p0 _ H1).
    simpl in H2.
    destruct H2; auto.
    contradict (flat_bot_neq_total _ H2).
    intros.
    destruct a; auto.
    pose proof (p2 _ H1).
    simpl in H2.
    destruct H2; auto.
    contradict (flat_bot_neq_total _ H2).
  Qed.

End PartialOrder.
Infix "⊑" := (pdom_le) (at level 80).

Section Completeness.
  Definition pdom_bot {X : Type} : pdom X := pdom_flat_unit (bot X).
  Lemma pdom_bot_is_bot {X : Type} : forall (S : pdom X), pdom_bot ⊑ S.
  Proof.
    intros.
    right.
    split.
    unfold pdom_bot.
    unfold proj1_sig.
    unfold pdom_flat_unit.
    auto.
    right.
    intros x e.
    unfold proj1_sig in e.
    simpl in e.
    rewrite <- e.
    unfold proj1_sig.
    unfold pdom_add_elem.
    right; auto.
  Defined.

  Definition pdom_is_chain {X : Type} (f : nat -> pdom X) := forall n m, n <= m -> f n ⊑ f m.

  Definition pdom_indexed_subset_is_sup {X I: Type} (f : I -> pdom X) (T : pdom X) :=
    (forall i, (f i) ⊑ T) /\ forall T', (forall i, (f i) ⊑ T') -> T ⊑ T'.

  Definition pdom_indexed_union_when_bot {X I : Type} (f : I -> pdom X) : (exists i, proj1_sig (f i) (bot X)) -> pdom X.
  Proof.
    intros.
    exists (fun x => exists i, proj1_sig (f i) x).
    intros.
    exact H.
  Defined
  .

  Definition pdom_chain_sup {X : Type} (f : nat -> pdom X) : pdom_is_chain f -> pdom X.
  Proof.
    intros H.
    exists (fun x =>
              (* when there is emptyset, it is emptyset *)
              ((exists n, pdom_is_empty (f n)) -> False)
              /\
                ((forall n, proj1_sig (f n) (bot X)) -> exists i, proj1_sig (f i) x)
              /\
                ((exists n, ~ proj1_sig (f n) (bot X)) -> (exists n, ~ proj1_sig (f n) (bot X) /\ proj1_sig (f n) x))).
    intro.
    destruct H0 as [g [h hh]].
    split.
    destruct (hh 0); auto.
    split.
    intro.
    exists 0; apply H0; auto.
    intro.
    assert (forall n : nat,
             exists n0 : nat, ~ proj1_sig (f n0) (bot X) /\ proj1_sig (f n0) (g n)).
    intros.
    destruct (hh n) as [a [b c]]; apply c; auto.
    clear hh.
    destruct H0.
    assert (forall n, proj1_sig (f x) (g n)).
    intro n.
    destruct (H1 n).
    destruct H2.
    destruct (PeanoNat.Nat.le_ge_cases x x0).
    pose proof (H _ _ H4).
    destruct H5.
    rewrite H5; auto.
    destruct H5.
    contradict (H0 H5).
    pose proof (H _ _ H4).
    destruct H5.
    rewrite <- H5; auto.
    destruct H5.
    contradict (H2 H5).
    contradict H0.
    apply pdom_infinite_bot.
    exists g; auto.
  Defined.

  Lemma pdom_omega_complete {X : Type} (f : nat -> pdom X) (H : pdom_is_chain f) :
    pdom_indexed_subset_is_sup f (pdom_chain_sup f H).
  Proof.
    destruct (lem (exists n, pdom_is_empty (f n))).
    {
      assert (pdom_chain_sup f H = pdom_empty X) as rw.
      {
        apply pdom_is_empty_is_empty.
        unfold pdom_chain_sup, pdom_is_empty; simpl.
        intros x [a [b c]].
        apply a.
        exact H0.
      }
      rewrite rw.
      (* when there is emptyset *)
      destruct H0 as [i h].
      
      split.
      intro j.
      destruct (le_ge_dec i j).
      pose proof (H i j l).
      pose proof (pdom_is_empty_le_is_empty _ _ H0 h).
      rewrite  (pdom_is_empty_is_empty _ H1).
      
      apply pdom_le_refl.
      assert (j <= i) by auto.
      pose proof (H j i H0).
      assert (f i ⊑ pdom_empty X).
      rewrite  (pdom_is_empty_is_empty _ h).
      apply pdom_le_refl.
      apply (pdom_le_trans _ _ _ H1 H2).
      intros.
      pose proof (pdom_is_empty_le_is_empty _ _ (H0 i) h).
      rewrite  (pdom_is_empty_is_empty _ H1).
      apply pdom_le_refl.
    }

    destruct (lem (forall n, proj1_sig (f n) (bot X))).
    {
      assert (pdom_chain_sup f H =  (pdom_indexed_union_when_bot f (ex_intro _ 0 (H1 0)))) as rw.
      {
        apply proj1_sig_injective.
        simpl.
        apply pred_ext.
        intros x [a [b c]].
        exact (b H1).
        intros; repeat split.
        exact H0.
        intro.
        exact H2.
        intro.
        destruct H3.
        contradict (H3 (H1 x)).        
      }
      rewrite rw.
      
      (* when all chain contains bot *)
      split.
      intros.
      right.
      split.
      exact (H1 i ).
      right.
      intros x e.
      simpl.
      left.
      exists i; auto.
      (* now proving least *)
      intros.
      destruct (lem (pdom_is_empty T')).
      right.
      split; simpl.
      exists 0; auto.
      left; auto.
      
      right.
      split.
      simpl.
      exists 0; auto.
      right.
      intros x e.
      simpl.
      simpl in e.
      destruct e.
      destruct (H2 x0).
      left; rewrite <- H5; auto.
      destruct H5.
      destruct H6.
      contradict (H3 H6).
      destruct x.
      right; auto.
      left.
      apply H6 in H4.
      simpl in H4.
      destruct H4; auto.
      contradict H4; apply flat_bot_neq_total.
    }

    {
      
      (* when bot disappear *)
      apply (neg_forall_exists_neg) in H1.
      
      destruct H1.
      assert ( (pdom_chain_sup f H) = f x) as rw.
      {
        apply proj1_sig_injective.
        simpl.
        apply pred_ext.
        intros y [a [b c]].
        pose proof (c (ex_intro _ x H1)).
        clear a b c.
        destruct H2.
        assert (f x = f x0).
        destruct (PeanoNat.Nat.le_ge_cases x x0).
        apply H in H3.
        destruct H3.
        auto.
        destruct H3.
        contradict (H1 H3).
        apply H in H3.
        destruct H3.
        auto.
        destruct H3.
        destruct H2.
        contradict (H2 H3).
        rewrite H3; destruct H2; auto.
        intros; repeat split.
        exact H0.
        intro.
        contradict (H1 (H3 x)).
        intro.
        exists x; auto.
      }
      rewrite rw.      
      split.
      intro.
      destruct (PeanoNat.Nat.le_ge_cases i x).
      apply (H _ _ H2).
      pose proof (H _ _ H2).
      destruct H3.
      rewrite H3; apply pdom_le_refl.
      destruct H3.
      contradict (H1 H3).
      (* minimality *)
      intros.
      pose proof (H2 x).
      exact H3.
    }
  Defined.

End Completeness.


Section PointwiseOrderingCompleteness.
  Definition pdom_fun_le {X Y : Type} (f g : X -> pdom Y) := forall a, f a ⊑ g a.

  Infix "≤" := (pdom_fun_le) (at level 80).

  Lemma pdom_fun_le_refl {X Y} (f : X -> pdom Y) : f ≤ f.
  Proof.
    intro x; apply pdom_le_refl; auto.
  Defined.

  Lemma pdom_fun_le_trans {X Y} (f g h: X -> pdom Y) : f ≤ g -> g ≤ h -> f ≤ h.
  Proof.
    intros h1 h2 x; apply (pdom_le_trans _ _ _ (h1 x) (h2 x)).
  Defined.

  Lemma pdom_fun_le_asym {X Y} (f g: X -> pdom Y) : f ≤ g -> g ≤ f -> f = g.
  Proof.
    intros.
    apply dfun_ext; intros.
    apply pdom_le_asym; try apply H; try apply H0.
  Qed.

  Definition pdom_fun_is_monotone {X Y : Type} (f : (X -> pdom Y) -> (X -> pdom Y)) :=
    forall x y, x ≤ y -> f x ≤ f y.

  Definition pdom_fun_bot {X Y : Type} : X -> pdom Y := fun _ => pdom_bot.

  Definition pdom_fun_bot_is_bot {X Y : Type} : forall (f :X -> pdom Y), pdom_fun_bot ≤ f.
  Proof.
    intros f e; apply pdom_bot_is_bot; auto.
  Defined.
 
  Definition pdom_fun_is_chain {X Y : Type} (s : nat -> (X -> pdom Y)) := forall n m, n <= m -> s n ≤ s m.
  
  Definition pdom_fun_chain_sup {X Y: Type} (f : nat -> (X -> pdom Y)) : pdom_fun_is_chain f -> X -> pdom Y.
  Proof.
    intro.
    pose (fun x : X => fun n => f n x) as g. 
    assert (forall x, pdom_is_chain (g x)).
    intros x i j o.
    exact (H i j o x).
    intro x.
    exact (pdom_chain_sup (g x) (H0 x)).
  Defined.

  Definition pdom_fun_indexed_subset_is_sup {X Y I: Type} (f : I -> (X -> pdom Y)) (T : X -> pdom Y) :=
    (forall i, (f i) ≤ T) /\ forall T', (forall i, (f i) ≤ T') -> T ≤ T'.

  Lemma pdom_fun_omega_complete {X Y : Type} (f : nat -> (X -> pdom Y)) (H : pdom_fun_is_chain f) :
    pdom_fun_indexed_subset_is_sup f (pdom_fun_chain_sup f H).
  Proof.
    split.
    intro.
    intro x.
    unfold pdom_fun_chain_sup.
    apply (pdom_omega_complete (fun n => f n x)).
    intros.
    intro x.
    apply (pdom_omega_complete (fun n => f n x)).
    intro i.
    exact (H0 i x).
  Defined.    
End PointwiseOrderingCompleteness.

Infix "⊑" := (pdom_le) (at level 80).

Infix "≤" := (pdom_fun_le) (at level 80).
