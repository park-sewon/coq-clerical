Require Import PowerdomainBase.
Require Import PowerdomainInfinite.
Require Import PowerdomainMonad.
Require Import PowerdomainProperties.
Require Import PowerdomainCompleteness.
Require Import Lia.

Lemma pdom_chain_empty_1 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  (exists n, pdom_is_empty (s n)) -> pdom_is_empty (pdom_chain_sup s c).
Proof.
  intros [n emp] x [p _].
  apply p; exists n; apply emp.
Defined.

Lemma pdom_chain_empty_2 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  pdom_is_empty (pdom_chain_sup s c) -> exists n, pdom_is_empty (s n).
Proof.
  intros.
  destruct (lem (exists n : nat, pdom_is_empty (s n))); auto.
  pose proof (neg_exists_forall_neg _ _ H0); clear H0.
  contradict H.
  destruct (lem (exists n, ~ ((bot _) ∈ s n))).
  destruct H as [i p].
  pose (H1 i).
  simpl in n.
  unfold pdom_is_empty in n.
  apply neg_forall_exists_neg in n.
  destruct n.
  apply dn_elim in H.
  apply (pdom_is_neg_empty_by_evidence _ x).
  simpl.
  split.
  intros [n k].
  apply (H1 n k).
  split.
  intro.
  exists i; auto.
  intros _. 
  exists i; split; auto.
  apply (pdom_is_neg_empty_by_evidence _ (bot _)).
  split.
  intros [n k].
  apply (H1 n k).
  split.
  intros.
  exists 0; apply H0; auto.
  intro.
  contradict (H H0).
Defined.

Lemma forall_or_exists_neg {X : Type} (P : X -> Prop) : (forall x, P x) \/ (exists x, ~ P x).
Proof.
  destruct (lem (forall x, P x)); auto.
  apply neg_forall_exists_neg in H; auto.
Defined.

Lemma pdom_chain_bot_1 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  (forall n, (bot X) ∈ s n) ->  (bot X) ∈ (pdom_chain_sup s c).
Proof.
  intros.
  repeat split; intros.
  destruct H0.
  apply (H0 (bot X) (H x)).
  exists 0; apply H.
  destruct H0 as [j k]; contradict (k (H j)).
Defined.

Lemma pdom_chain_bot_2 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  (bot X) ∈ (pdom_chain_sup s c) -> forall n, (bot X) ∈ s n.
Proof.
  intros h n.
  destruct h as [p [q r]].
  destruct (forall_or_exists_neg (fun n => bot X ∈ s n)).
  apply H.
  apply r in H.
  destruct H as [i [j k]].
  contradict (j k).
Defined.

Lemma pdom_fun_chain_empty_1 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
  forall x, (exists n, pdom_is_empty (s n x)) ->  pdom_is_empty (pdom_fun_chain_sup s c x).
Proof.
  intros x [n h] y [p _]. 
  apply p.
  exists n; auto.
Defined.

Lemma pdom_fun_chain_empty_2 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
  forall x, pdom_is_empty (pdom_fun_chain_sup s c x) -> exists n, pdom_is_empty (s n x).
Proof.
  intros x e.
  unfold pdom_fun_chain_sup in e.
  apply pdom_chain_empty_2 in e.
  exact e.
Defined.

Lemma pdom_fun_chain_bot_1 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
  forall x, (forall n, (bot Y) ∈ (s n x)) -> (bot Y) ∈ (pdom_fun_chain_sup s c x) .
Proof.
  intros.
  unfold pdom_fun_chain_sup.
  apply pdom_chain_bot_1.
  exact H.
Defined.

Lemma pdom_fun_chain_bot_2 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
  forall x, (bot Y) ∈ (pdom_fun_chain_sup s c x) -> forall n, (bot Y) ∈ (s n x).
Proof.
  intros.
  unfold pdom_fun_chain_sup in H.
  pose proof (pdom_chain_bot_2 _ _ H).
  apply H0.
Defined.

Lemma pdom_chain_membership_1 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  forall x, (~ pdom_is_empty (pdom_chain_sup s c) /\ exists n, total x ∈ s n) -> total x ∈ pdom_chain_sup s c.
Proof.
  intros x [p q].
  repeat split; intros.
  contradict p.
  apply pdom_chain_empty_1.
  exact H.
  exact q.
  destruct H.
  destruct q.
  assert (H' : x1 <= x0 \/ x0 <= x1) by lia; destruct H'.
  (* when x1 <= x0, x is in x0 because x0 is not empty *)
  exists x0; split; auto.
  apply c in H1.
  destruct H1.
  rewrite <- H1; auto.
  destruct H1.
  destruct H2.
  contradict p.
  apply pdom_chain_empty_1.
  exists x0; auto.
  apply H2 in H0.
  destruct H0.
  exact H0.
  contradict (flat_bot_neq_total _ H0).
  (* when x0 <= x1 *)
  exists x1; split; auto.
  intro.
  contradict H.
  destruct (c _ _ H1).
  rewrite H; auto.
  destruct H.
  exact H.
Qed.

Lemma pdom_chain_membership_2 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  forall x, x ∈ pdom_chain_sup s c -> exists n, x ∈ s n.
Proof.
  intros x [p [q r]].
  destruct (forall_or_exists_neg  (fun n : nat => bot X ∈ s n)).
  exact (q H).
  destruct (r H).
  exists x0; destruct H0; auto.
Qed.

Lemma pdom_chain_sup_flat {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
  ~ (bot X ∈ pdom_chain_sup s c) -> exists n, forall m, n <= m -> s m = pdom_chain_sup s c.
Proof.
  intros.
  assert (exists n, ~ (bot X ∈ s n)).
  destruct (forall_or_exists_neg (fun n => bot X ∈ s n)); auto.
  contradict H.
  apply pdom_chain_bot_1.
  exact H0.
  destruct H0.
  exists x.
  intros.
  destruct (c _ _ H1).
  assert (s m ⊑ pdom_chain_sup s c).
  apply pdom_omega_complete.
  destruct H3.
  rewrite  H3; auto.
  destruct H3 as [H3 _].
  rewrite H2 in H0.
  contradict (H0 H3).
  destruct H2.
  contradict (H0 H2).
Qed.

Lemma pdom_bind_agree_aux {X Y : Type} (f g : X -> pdom Y) (S : pdom X) :
  (forall x, total x ∈ S -> f x = g x) -> forall x, proj1_sig (pdom_bind f S) x -> proj1_sig (pdom_bind g S) x.
Proof.
  intros.
  destruct x.
  {
    (* when a is bot *)
    pose proof (pdom_bind_bot_2 _ _ H0).
    apply pdom_bind_bot_1.
    (* first, prove that pdom_bind g S is not empty *)
    intro.
    apply pdom_bind_empty_2 in H2.
    assert (pdom_is_empty (pdom_bind f S)).
    {
      apply pdom_bind_empty_1.
      destruct H2.
      left; auto.
      destruct H2 as [a [b c]].
      right.
      exists a; split; auto.
      rewrite (H _ b); auto.
    }
    apply (H3 _ H0).
    destruct H1.
    left; auto.
    destruct H1 as [a [b c]].
    right.
    exists a; rewrite<- (H _ b); auto.
  }
  {
    (* when a is total *)
    apply pdom_bind_total_1.
    split.
    intro.
    apply pdom_bind_empty_2 in H1.
    assert (pdom_is_empty (pdom_bind f S)).
    {
      apply pdom_bind_empty_1.
      destruct H1.
      left; auto.
      destruct H1 as [a [b c]].
      right.
      exists a; split; auto.
      rewrite (H _ b); auto.
    }
    apply (H2 _ H0).
    apply pdom_bind_total_2 in H0.
    destruct H0 as [_ [a [b c]]].
    exists a.
    rewrite <- (H _ b); auto.
  }
Defined.

Lemma pdom_bind_agree {X Y : Type} (f g : X -> pdom Y) (S : pdom X) :
  (forall x, total x ∈ S -> f x = g x) -> pdom_bind f S = pdom_bind g S.
Proof.
  intros.
  apply sig_eq.
  apply pred_ext; apply pdom_bind_agree_aux; auto.
  intros.
  rewrite (H x H0); auto.
Defined.

