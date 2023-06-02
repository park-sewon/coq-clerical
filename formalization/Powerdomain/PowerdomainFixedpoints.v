From Clerical Require Import Preliminaries.BaseAxioms.

Require Import PowerdomainInfinite.
Require Import PowerdomainMonad.
Require Import PowerdomainProperties.
Require Import PowerdomainCompleteness.
Require Import PowerdomainOrderProperties.
Require Import Lia.


Section FixpointTheorem.  
  Definition pdom_is_monotone {X Y : Type} (f : pdom X -> pdom Y) := forall S T, S ⊑ T -> f S ⊑ f T.

  Lemma pdom_chain_monotone_chain {X Y : Type} (f : pdom X -> pdom Y) :
    forall (s : nat -> pdom X), pdom_is_chain s -> pdom_is_monotone f -> pdom_is_chain (fun n => f (s n)).
  Proof.
    intros.
    intros n m o.
    apply H0.
    apply H.
    exact o.
  Defined.

  Lemma pdom_is_step_chain_is_chain {X : Type} (s : nat -> pdom X) :
    (forall n, s n ⊑ s (S n)) -> pdom_is_chain s.
  Proof.
    intros sc i j o.
    induction o.
    apply pdom_le_refl.
    apply (pdom_le_trans _ _ _ IHo (sc m)).
  Defined.
  
  Definition pdom_is_continuous {X Y : Type} (f : pdom X -> pdom Y) (m : pdom_is_monotone f) :=
      forall (s : nat -> pdom X) (c : pdom_is_chain s),
        f (pdom_chain_sup s c) = pdom_chain_sup (fun n => f (s n)) (pdom_chain_monotone_chain f s c m).  


  Definition pdom_bot_chain {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) : nat -> pdom X.
  Proof.
    exact (fun n => nat_rect (fun _ => pdom X) (pdom_bot) (fun _ k => f k) n).
  Defined.

  Lemma pdom_bot_chain_is_chain {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) :
    pdom_is_chain (pdom_bot_chain f m).
  Proof.
    apply pdom_is_step_chain_is_chain.
    intro.
    simpl.
    induction n.
    simpl.
    apply pdom_bot_is_bot.
    simpl.
    apply m.
    exact IHn.
  Defined.
  
  Definition pdom_lfp {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) : pdom X.
  Proof.
    exact (pdom_chain_sup (pdom_bot_chain f m) (pdom_bot_chain_is_chain f m)).
  Defined.

  Lemma pdom_index_surjective_sup {X : Type} {I J : Type} (f : I -> pdom X) (g : J -> pdom X) (supf supg : pdom X) :
    pdom_indexed_subset_is_sup f supf -> pdom_indexed_subset_is_sup g supg -> (forall i, exists j, f i ⊑ g j) -> supf ⊑ supg.
  Proof.
    intros.
    apply H.
    intro.
    destruct H0.
    destruct (H1 i) as [j h].
    pose proof (H0 j).
    apply (pdom_le_trans _ _ _ h H3).
  Defined.
  
  Lemma pdom_lfp_prop {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) :
    pdom_is_continuous f m ->
    f (pdom_lfp f m) = (pdom_lfp f m) /\
      forall x, f x = x -> (pdom_lfp f m) ⊑ x.
  Proof.
    intros.
    split.
    unfold pdom_lfp.    
    pose proof (H (pdom_bot_chain f m) (pdom_bot_chain_is_chain f m)).
    rewrite H0.
    apply pdom_le_asym.
    apply (pdom_index_surjective_sup _ _ _ _ (pdom_omega_complete _ _) (pdom_omega_complete _ _)).
    intro n; exists (S n).
    simpl.
    apply pdom_le_refl.
    apply (pdom_index_surjective_sup _ _ _ _ (pdom_omega_complete _ _) (pdom_omega_complete _ _)).
    intro n; exists n.
    induction n.
    simpl.
    apply pdom_bot_is_bot.
    simpl.
    apply m; auto.
    (* least element *)
    {
    intros.
    assert (forall n, (pdom_bot_chain f m n) ⊑ x).
    {
      intro.
      induction n.
      simpl.
      apply pdom_bot_is_bot.
      simpl.
      rewrite <- H0; apply m; auto.
    }
    pose proof (pdom_omega_complete (pdom_bot_chain f m) (pdom_bot_chain_is_chain f m)).
    destruct H2.
    apply H3.
    exact H1.
    }
  Defined.
End FixpointTheorem.


Infix "≤" := (pdom_fun_le) (at level 80).

Section PointwiseOrderingFixpointTheorem.
  Lemma pdom_fun_is_step_chain_is_chain {X Y: Type} (s : nat -> X -> pdom Y) :
    (forall n, s n ≤ s (S n)) -> pdom_fun_is_chain s.
  Proof.
    intros sc i j o.
    induction o.
    apply pdom_fun_le_refl.
    apply (pdom_fun_le_trans _ _ _ IHo (sc m)).
  Defined.

  Lemma pdom_fun_chain_monotone_chain {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) :
    forall (s : nat -> X -> pdom Y), pdom_fun_is_chain s -> pdom_fun_is_monotone f -> pdom_fun_is_chain (fun n => f (s n)).
  Proof.
    intros.
    intros n m o.
    apply H0.
    apply H.
    exact o.
  Defined.
  
  Definition pdom_fun_is_continuous {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) (m : pdom_fun_is_monotone f) :=
      forall (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s),
        f (pdom_fun_chain_sup s c) = pdom_fun_chain_sup (fun n => f (s n)) (pdom_fun_chain_monotone_chain f s c m).  

  Definition pdom_fun_bot_chain {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) (m : pdom_fun_is_monotone f) : nat -> X -> pdom Y.
  Proof.
    exact (fun n => nat_rect (fun _ => X -> pdom Y) (pdom_fun_bot) (fun _ k => f k) n).
  Defined.

  Lemma pdom_fun_bot_chain_is_chain {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) (m : pdom_fun_is_monotone f) :
    pdom_fun_is_chain (pdom_fun_bot_chain f m).
  Proof.
    apply pdom_fun_is_step_chain_is_chain.
    intro.
    simpl.
    induction n.
    simpl.
    apply pdom_fun_bot_is_bot.
    simpl.
    apply m.
    exact IHn.
  Defined.
  
  Definition pdom_fun_lfp {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) (m : pdom_fun_is_monotone f) : X -> pdom Y.
  Proof.
    exact (pdom_fun_chain_sup (pdom_fun_bot_chain f m) (pdom_fun_bot_chain_is_chain f m)).
  Defined.

  Lemma pdom_fun_index_surjective_sup {X Y: Type} {I J : Type} (f : I -> X -> pdom Y) (g : J -> X -> pdom Y) (supf supg : X -> pdom Y) :
    pdom_fun_indexed_subset_is_sup f supf -> pdom_fun_indexed_subset_is_sup g supg -> (forall i, exists j, f i ≤ g j) -> supf ≤ supg.
  Proof.
    intros.
    apply H.
    intro.
    destruct H0.
    destruct (H1 i) as [j h].
    pose proof (H0 j).
    apply (pdom_fun_le_trans _ _ _ h H3).
  Defined.
    
  Lemma pdom_fun_lfp_prop {X Y: Type} (f : (X -> pdom Y) -> (X -> pdom Y)) (m : pdom_fun_is_monotone f) :
    pdom_fun_is_continuous f m ->
    f (pdom_fun_lfp f m) = (pdom_fun_lfp f m) /\
      forall x, f x = x -> (pdom_fun_lfp f m) ≤ x.
  Proof.
    intros.
    split.
    unfold pdom_fun_lfp.    
    pose proof (H (pdom_fun_bot_chain f m) (pdom_fun_bot_chain_is_chain f m)).
    rewrite H0.
    apply pdom_fun_le_asym.
    apply (pdom_fun_index_surjective_sup _ _ _ _ (pdom_fun_omega_complete _ _) (pdom_fun_omega_complete _ _)).
    intro n; exists (S n).
    simpl.
    apply pdom_fun_le_refl.
    apply (pdom_fun_index_surjective_sup _ _ _ _ (pdom_fun_omega_complete _ _) (pdom_fun_omega_complete _ _)).
    intro n; exists n.
    induction n.
    simpl.
    apply pdom_fun_bot_is_bot.
    simpl.
    apply m; auto.
    (* least element *)
    {
    intros.
    assert (forall n, (pdom_fun_bot_chain f m n) ≤ x).
    {
      intro.
      induction n.
      simpl.
      apply pdom_fun_bot_is_bot.
      simpl.
      rewrite <- H0; apply m; auto.
    }
    pose proof (pdom_fun_omega_complete (pdom_fun_bot_chain f m) (pdom_fun_bot_chain_is_chain f m)).
    destruct H2.
    apply H3.
    exact H1.
    }
  Defined.

  End PointwiseOrderingFixpointTheorem.



 


