Require Import PowerdomainBase.
Require Import PowerdomainInfinite.
Require Import PowerdomainMonad.


Definition pdom_empty (X : Type) : pdom X.
Proof.
  exists (fun _ => False).
  intro x.
  apply pset_infinite_subset_infinite in x.
  apply hprop_ninfinite in x; auto.
  intros.
  destruct x0.
  contradict f; auto.
Defined.


Lemma pdom_is_neg_empty_by_evidence {X : Type} (S : pdom X) :
  forall x, x ∈ S -> pdom_neg_is_empty S.
Proof.
  intros x i.
  intro.
  unfold pdom_is_empty in H.
  apply (H x i).
Qed.




Lemma pdom_neg_empty_exists {X : Type} (x : pdom X) : ~ pdom_is_empty x -> exists y, y ∈ x.
Proof.
  intros.
  apply neg_forall_exists_neg in H.
  destruct H.
  exists x0.
  apply dn_elim; auto.
Defined.

Lemma flat_to_pdom_neg_empty : forall X (x : flat X), pdom_neg_is_empty (flat_to_pdom x).
Proof.
  intros.
  destruct x.
  apply (pdom_is_neg_empty_by_evidence _ (bot X)).
  simpl; auto.
  apply (pdom_is_neg_empty_by_evidence _ (total x)).
  simpl; auto.
Qed.

Lemma total_is_injective : forall {X} {x y : X}, total x = total y -> x = y.
Proof.
  intros.
  injection H; auto.
Defined.

Lemma pdom_unit_neg_is_empty {X} : forall x :X, pdom_neg_is_empty (pdom_unit x).
Proof.
  intros x.
  apply (pdom_is_neg_empty_by_evidence _ (total x)).
  simpl; auto.
Qed.

  
Definition pdom_add_elem {X : Type} (S : pdom X) (x : flat X) : pdom X.
Proof.
  exists (fun y => proj1_sig S y \/ x = y).
  intros.
  apply pset_infinite_subset_infinite in H.
  apply Pigeon2' in H.
  destruct H.
  left.
  apply subset_infinite_pset_infinite in H.
  apply (pdom_infinite_bot _ H).
  contradict H.
  apply hprop_ninfinite.
  intros.
  destruct x0, y.
  rewrite <-  e, <- e0.
  auto.
Defined.


Definition pdom_add_tot {X : Type} (S : pdom X) (x : X) : pdom X.
Proof.
  exists (fun y => proj1_sig S y \/ total x = y).
  intros.
  apply pset_infinite_subset_infinite in H.
  apply Pigeon2' in H.
  destruct H.
  left.
  apply subset_infinite_pset_infinite in H.
  apply (pdom_infinite_bot _ H).
  contradict H.
  apply hprop_ninfinite.
  intros.
  destruct x0, y.
  rewrite <-  e, <- e0.
  auto.
Defined.

Lemma pdom_empty_is_empty {X : Type} : pdom_is_empty (pdom_empty X).
Proof.
  intro x.
  unfold pdom_empty.
  simpl.
  auto.
Defined.

Lemma pdom_is_empty_is_empty {X : Type} : forall S, pdom_is_empty S -> S = pdom_empty X.
Proof.
  intros.
  apply sig_eq.
  simpl.
  apply pred_ext.
  intros.
  exact (H a H0).
  intros.
  contradict H0.
Defined.

(*
    various small lemmas about pdom and pdom_fun
    naming conventions are for example: 
    pdom : prefix
    bind : operation
    membership : it is about membership
    1 : forward reasoning: if membership in original, then membership in bind
    2 : backward reasoning: if membership in bind, then membership in original
 *)
Lemma pdom_lift_non_empty_1 {X Y : Type} (f : X -> Y) (S : pdom X) :
  (~ pdom_is_empty S) -> ~ pdom_is_empty (pdom_lift f S).
Proof.
  intros.
  intro.
  contradict H.
  intros x h.
  destruct x.
  pose proof (H0 (bot Y)).
  contradict H.
  simpl.
  exists (bot X); split; auto.
  pose proof (H0 (total (f x))).
  contradict H.
  simpl.
  exists (total x); split; auto.
Defined.

Lemma pdom_lift_empty_1 {X Y : Type} (f : X -> Y) (S : pdom X) :
  (pdom_is_empty S) -> pdom_is_empty (pdom_lift f S).
Proof.
  intros p x e.
  unfold pdom_is_empty in p.
  destruct e.
  destruct H.
  apply (p _ H).
Defined.


Lemma pdom_lift_total_1 {X Y : Type} (f : X -> Y) (S : pdom X) :
  forall y, (exists x, total x ∈ S /\ y = f x) -> total y ∈ pdom_lift f S.
Proof.
  intros.
  destruct H.
  destruct H.
  rewrite H0.
  simpl.
  exists (total x).
  simpl; auto.
Defined.

Lemma pdom_lift_total_2 {X Y : Type} (f : X -> Y) (S : pdom X) :
  forall y,  total y ∈ pdom_lift f S -> (exists x, total x ∈ S /\ y = f x) .
Proof.
  intros.
  simpl in H.
  destruct H.
  destruct x.
  destruct H.

  simpl in H0.
  contradict (flat_bot_neq_total _ H0).
  exists x.
  simpl in H.
  destruct H; split; auto.
  injection H0; intro; auto.
Defined.

Lemma pdom_lift_bot_1 {X Y : Type} (f : X -> Y) (S : pdom X) :
  (bot X ∈ S) -> bot Y ∈ pdom_lift f S.
Proof.
  intros.
  simpl.
  exists (bot X); split; simpl; auto.
Defined.

Lemma pdom_lift_bot_2 {X Y : Type} (f : X -> Y) (S : pdom X) :
  bot Y ∈ pdom_lift f S -> (bot X ∈ S) .
Proof.
  intros.
  destruct H.
  destruct H.
  simpl in H0.
  destruct x; auto.
  simpl in H0.
  contradict (flat_total_neq_bot _ H0).
Defined.  

Lemma pdom_lift_empty_2 {X Y : Type} (f : X -> Y) (S : pdom X) :
  pdom_is_empty (pdom_lift f S) -> (pdom_is_empty S).
Proof.
  intros p x e.
  destruct x.
  pose proof (p (bot Y)).
  contradict H; apply pdom_lift_bot_1; auto.
  pose proof (p (total (f x))).
  contradict H.
  apply pdom_lift_total_1; exists x; auto.
Defined.

Lemma pdom_bind_total_1 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  forall x, (~ pdom_is_empty (pdom_bind f S) /\ exists s, (total s) ∈ S /\ x ∈ f s) -> x ∈ pdom_bind f S.
Proof.
  intros x [ne [s [t m]]].
  split.
  apply pdom_lift_non_empty_1.
  intro.
  apply (H _ t).
  split.
  intros.
  
  intro.
  
  contradict ne.
  intros y h.
  destruct h as [_ [h2 _]].
  pose proof (h2 _ H).
  apply (H1 H0).
  right.
  exists (f s).
  split; auto.
  simpl.
  exists (total s); auto.
Defined.

Lemma pdom_bind_total_2 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  forall x, total x ∈ pdom_bind f S -> (~ pdom_is_empty (pdom_bind f S) /\ exists s, (total s) ∈ S /\ total x ∈ f s).
Proof.
  intros.
  split.
  intro.
  apply (H0 _ H).
  destruct H as [h [h1 h2]].
  destruct h2.
  destruct H as [a b].
  contradict (flat_total_neq_bot _ a).
  destruct H as [a [b c]].
  destruct c.
  destruct H.
  destruct x0.
  simpl in H0.
  contradict (flat_bot_neq_total _ H0).
  exists x0.
  simpl in H0.
  split; auto.
  injection H0; intro.
  rewrite H1.
  exact b.
Defined.    

Lemma pdom_bind_empty_1 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  pdom_is_empty S \/ (exists x, (total x) ∈ S /\ pdom_is_empty (f x)) -> pdom_is_empty (pdom_bind f S).
Proof.
  intros.
  destruct H.
  intros x e.
  destruct e.
  apply H0, pdom_lift_empty_1, H.
  intros x e.
  destruct e as [a [b c]].
  destruct H.
  pose proof (b (f x0)).
  assert (total (f x0) ∈ pdom_lift f S).
  simpl.
  exists (total x0); destruct H; split; auto.
  apply H0 in H1.
  destruct H; apply H1; auto.
Defined.

Lemma pdom_bind_empty_2 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  pdom_is_empty (pdom_bind f S) ->
  pdom_is_empty S \/ (exists x, (total x) ∈ S /\ pdom_is_empty (f x)).
Proof.
  intros.
  destruct (lem (exists x : X, (total x ∈ S) /\ pdom_is_empty (f x))); auto.
  left.
  intros x e.
  assert (pdom_neg_is_empty (pdom_bind f S)).
  destruct x.
  apply (pdom_is_neg_empty_by_evidence _ (bot Y)).
  simpl.
  split.
  apply pdom_lift_non_empty_1.
  intro.
  apply (H1 _ e).
  split.
  intros.
  destruct H1.
  destruct (lem (pdom_neg_is_empty S0)); auto.
  contradict H0.
  destruct x.
  destruct H1.
  simpl in H1.
  contradict (flat_bot_neq_total _ H1).
  exists x; split; destruct H1; auto.
  simpl in H1.
  injection H1; intro.
  rewrite H3.
  intros i j.
  contradict H2.
  apply (pdom_is_neg_empty_by_evidence _ i j).
  left.
  split; auto.
  exists (bot X); auto.

  {
    assert (exists y, y ∈ f x).
    destruct (lem (exists y, y ∈ f x)); auto.
    contradict H0.
    exists x; split; auto.
    intros i j.
    contradict H1.
    exists i; auto.
    destruct H1.
    apply (pdom_is_neg_empty_by_evidence _ x0).
    simpl.
    split.
    apply pdom_lift_non_empty_1.
    intro.
    apply (H2 _ e).
    split.
    intros.
    destruct H2.
    destruct (lem (pdom_neg_is_empty S0)); auto.
    contradict H0.
    destruct H2.
    destruct x1.
    simpl in H2.
    contradict (flat_bot_neq_total _ H2).
    exists x1; split; auto.
    
    simpl in H2.
    injection H2; intro.
    rewrite H4.
    intros i j.
    contradict H3.
    apply (pdom_is_neg_empty_by_evidence _ i j); auto.
    right.
    exists (f x).
    split; auto.
    exists (total x); auto.
  }
  
  apply H1, H.
Defined.


Lemma pdom_bind_bot_1 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  ~ pdom_is_empty (pdom_bind f S) ->
  (bot X ∈ S \/ exists x, total x ∈ S /\ bot Y ∈ f x) ->  
  (bot Y) ∈ (pdom_bind f S).
Proof.
  intros.
  destruct H0.
  split.
  apply pdom_lift_non_empty_1.
  intro.
  apply H.
  apply pdom_bind_empty_1.
  left; auto.
  split.
  intros.
  intro.
  apply H.
  apply pdom_bind_empty_1.
  right; auto.
  pose proof (pdom_lift_total_2 _ _ _ H1).
  destruct H3 as [a [b c]].
  exists a; split; auto.
  rewrite <- c.
  exact H2.
  left.
  split; auto.
  simpl.
  exists (bot X); split; simpl; auto.

  destruct H0.
  destruct H0.
  simpl.
  split.
  apply pdom_lift_non_empty_1.
  intro.
  apply H.
  apply pdom_bind_empty_1.
  left; auto.
  split.
  intros.
  intro.
  contradict H.
  apply pdom_bind_empty_1.
  right.
  destruct H2.
  destruct H.
  destruct x0.
  simpl in H2.
  contradict (flat_bot_neq_total _ H2).
  simpl in H2.
  exists x0.
  split; auto.
  injection H2; intro e; rewrite e; auto.
  right.
  exists (f x).
  split; auto.
  exists (total x); auto.
Defined.

Lemma pdom_bind_bot_2 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  (bot Y) ∈ (pdom_bind f S) -> bot X ∈ S \/ exists x, total x ∈ S /\ bot Y ∈ f x.
Proof.
  intros.
  destruct H as [a [b c]].
  destruct c.
  destruct H.
  left.
  apply pdom_lift_bot_2 in H0; auto.
  destruct H.
  destruct H.
  
  right.
  apply pdom_lift_total_2 in H0.
  destruct H0 as [p [q r]]; exists p; split; auto.
  rewrite <- r; auto.
Defined.

Lemma pdom_bind_not_contain_bot {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
  ~ pdom_is_empty (pdom_bind f S) ->
  ~ ((bot Y) ∈ pdom_bind f S) -> forall s, total s ∈ S -> ~ (bot Y ∈ f s).
Proof.
  intros.
  intro.
  contradict H0.
  apply pdom_bind_bot_1.
  intro.
  contradict (H H0).
  right.
  exists s; auto.
Defined.

Lemma pdom_is_in_add_element_is_in {X : Type} (p : pdom X) (x y : flat X) : x ∈ p -> x ∈ pdom_add_elem p y.
Proof.
  intros; simpl; left; auto.
Defined.
