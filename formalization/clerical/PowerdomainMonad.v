(* classical treatment of our powerdomain ... maybe this makes some people upset :( *)
(* I also uses dependent destruction... what does it do really *)
Require Import Lia.
Require Import Coq.Arith.Compare_dec.

Require Import PowerdomainBase.
Require Import PowerdomainInfinite.


Section Flatdomain.
  
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

  Lemma flat_total_neq_bot {X : Type} : forall x, total x <> bot X.
  Proof.
    intros.
    pose (fun (x : flat X) => match x with total _ => 0 | bot _ => 1 end). 
    intro.
    pose proof (lp _ _ n _ _ H).
    simpl in H0.
    contradict H0; auto.
  Defined.

  Lemma flat_bot_neq_total {X : Type} : forall x, bot X <> total x.
  Proof.
    intros x e.
    apply (flat_total_neq_bot x).
    rewrite e; auto.
  Defined.

End Flatdomain.
Arguments total {_}.


Section Powerdomain.
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

  Lemma pdom_infinite_bot {A} (S : pdom A) : pset_infinite (proj1_sig S) -> proj1_sig S (bot A).
  Proof.
    destruct S; simpl; auto.
  Defined.
  
  Definition pdom_is_empty {X : Type} (S : pdom X) := forall x, ~ proj1_sig S x.

  Definition pdom_neg_is_empty {A : Type} : pdom A -> Prop := fun S => ~ pdom_is_empty S.
  
  (* Powerdomain is a monad *)
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
    exists (fun b => exists a : flat A, proj1_sig X a /\ pdom_lift' f a = b).
    intro.
    assert (infinite {a | proj1_sig X a}).
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
              pdom_neg_is_empty X /\
                (* all subsets are not empty *)
                (forall S : pdom A, proj1_sig X (total S) -> pdom_neg_is_empty S) /\
                (* a can be bot if X contains bot *)
                (a = bot A /\ (proj1_sig X (bot (pdom A)))
                 (* otherwise, there exists S \in X such that a is in S *)
                 \/ exists S, proj1_sig S a /\ proj1_sig X (total S))).
    intro.

    destruct H as [f [a b]].
    repeat split.
    destruct (b 0) as [t1 [t2 t3]]; auto.
    destruct (b 0) as [t1 [t2 t3]]; auto.
    assert (forall n : nat,
               (f n = bot A /\ proj1_sig X (bot (pdom A)) \/ (exists S : pdom A, proj1_sig S (f n) /\ proj1_sig X (total S)))).
    intro.
    destruct (b n) as [_ [_ p]]; auto.
    clear b.
    destruct (forall_or _ _ _ H).
    destruct H0.
    left; destruct H0; split; auto.
    clear H.
    destruct (cchoice _ _ H0).
    pose (fun a : {aa : pdom A | proj1_sig X (total aa)} => {x : flat A | proj1_sig (proj1_sig a) x}) as T.
    pose (fun n => @existT _ T (exist _ (x n) (proj2 (H n))) (@exist (flat A) (fun y => proj1_sig (x n) y) (f n) (proj1 (H n)))) as s.
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
      assert (pset_infinite (proj1_sig X)).
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
      assert (pset_infinite (proj1_sig x0)).
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
End Powerdomain.

Notation "x ∈ S" := (proj1_sig S x) (at level 80).
Notation "x ∉ S" := (~proj1_sig S x) (at level 85).
Notation "⊥" := (bot _).
