From Clerical Require Import Preliminaries.BaseAxioms.

Require Import PowerdomainInfinite.
Require Import PowerdomainMonad.
Require Import PowerdomainProperties.
Require Import PowerdomainCompleteness.
Require Import PowerdomainOrderProperties.
Require Import PowerdomainFixedpoints.

Require Import Lia.
Require Import List.

Section BinaryCase.
  (* this is a section for binary case.
     this can be removed in any near future
     replaced with the more genearl CaseList.
     The section for CaseList can be found below. *)
  Definition pdom_case2' (X : Type)
    (b1 b2 : pdom bool)
    (c1 c2 : pdom X)
    (x : nat -> flat X)
    (H : injective x)
    (f : nat -> bool)
    (u : forall n : nat, if f n then proj1_sig b1 (total true) /\ proj1_sig c1 (x n) else proj1_sig b2 (total true) /\ proj1_sig c2 (x n))
    : nat ->
      {b : bool &
             if b then {j : flat X | proj1_sig b1 (total true) /\ proj1_sig c1 j} else {j : flat X | proj1_sig b2 (total true) /\ proj1_sig c2 j}}.
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
          (pdom_neg_is_empty b1 /\ pdom_neg_is_empty b2)
          /\
            (total true ∈ b1 -> pdom_neg_is_empty c1)
          /\
            (total true ∈ b2 -> pdom_neg_is_empty c2)
          /\
            (* values *)
            (
              (total true ∈ b1 /\ x ∈ c1)
              \/
                (total true ∈ b2 /\ x ∈ c2)
              \/
                ((bot bool ∈ b1 \/ total false ∈ b1) /\ (bot bool ∈ b2 \/ total false ∈ b2) /\ x = bot X)
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
               (* values *)
               (
                 ((bot bool ∈ b1 \/ total false ∈ b1) /\ (bot bool ∈ b2 \/ total false ∈ b2) /\ x n = bot X)
                 \/
                   (total true ∈ b1 /\ x n ∈ c1)
                 \/
                   (total true ∈ b2 /\ x n ∈ c2)
                     
           )).
    intro n.
    destruct (H0 n) as [a [b [c d]]].
    destruct d as [d|[d|d]]; auto.
    clear H0.
    destruct (forall_or _ _ _ H1).
    destruct H0.
    right.
    right.
    destruct H0 as [a [b c]]; split; auto.
    clear H1.

    (* decide which branch is infinite *)
    assert (infinite {a : flat X | proj1_sig b1 (total true) /\ proj1_sig c1 a} \/ infinite {a : flat X | proj1_sig b2 (total true) /\ proj1_sig c2 a}).
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


  Definition pdom_case2_empty_1 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) :
    pdom_is_empty b1 \/ pdom_is_empty b2 \/ (total true ∈ b1 /\ pdom_is_empty c1) \/ (total true ∈ b2 /\ pdom_is_empty c2) -> pdom_is_empty (pdom_case2 b1 b2 c1 c2).
  Proof.
    intros H x e.
    destruct e as [[h1 h2] [h3 [h4 _]]].
    repeat destruct H; auto.
    apply h3 in H; auto.
    apply h4 in H; auto.
  Defined.


  Definition pdom_case2_empty_2 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) :
    pdom_is_empty (pdom_case2 b1 b2 c1 c2) -> pdom_is_empty b1 \/ pdom_is_empty b2 \/ (total true ∈ b1 /\ pdom_is_empty c1) \/ (total true ∈ b2 /\ pdom_is_empty c2).
  Proof.
    intros.
    destruct (lem (pdom_is_empty b1)); auto.
    destruct (lem (pdom_is_empty b2)); auto.
    destruct (lem ((total true ∈ b1) /\ pdom_is_empty c1)); auto.
    destruct (lem ((total true ∈ b2) /\ pdom_is_empty c2)); auto.
    contradict H.
    apply neg_conj in H2.
    apply neg_conj in H3.
    destruct (lem (total true ∈ b1)).
    destruct H2.
    contradict (H2 H).
    apply pdom_neg_empty_exists in H2 as [x  h].
    apply (pdom_is_neg_empty_by_evidence _ x).
    repeat split; auto.
    intro.
    apply (pdom_is_neg_empty_by_evidence _ x); auto.
    intro.
    destruct H3; auto.
    contradict (H3 H2).
    destruct (lem (total true ∈ b2)).
    destruct H3.
    contradict (H3 H4).
    apply pdom_neg_empty_exists in H3 as [x  h].
    apply (pdom_is_neg_empty_by_evidence _ x).
    repeat split; auto.
    intro.
    contradict (H H3).
    intro.
    apply (pdom_is_neg_empty_by_evidence _ x); auto.
    apply (pdom_is_neg_empty_by_evidence _ (bot _)); auto.
    repeat split; auto.
    intro.
    contradict (H H5).
    intro.
    contradict (H4 H5).
    right.
    right.
    repeat split; auto.
    apply pdom_neg_empty_exists in H0 as [b  h].
    destruct b.
    left; auto.
    destruct b.
    contradict (H h).
    right; auto.
    apply pdom_neg_empty_exists in H1 as [b  h].
    destruct b.
    left; auto.
    destruct b.
    contradict (H4 h).
    right; auto.
  Defined.
  
  Lemma pdom_case2_total_1 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) x :
    ~ (pdom_is_empty (pdom_case2 b1 b2 c1 c2)) ->
    (total true ∈ b1 /\ total x ∈ c1) \/ (total true ∈ b2 /\ total x ∈ c2) ->
    total x ∈ pdom_case2 b1 b2 c1 c2.
  Proof.
    intros.
    repeat split.
    intro.
    contradict H.
    apply pdom_case2_empty_1; auto.
    intro.
    contradict H.
    apply pdom_case2_empty_1; auto.
    intros h1 h2.
    contradict H.
    apply pdom_case2_empty_1; auto.
    intros h1 h2.
    contradict H.
    apply pdom_case2_empty_1; auto.
    destruct H0.
    left; auto.
    right; left; auto.
  Defined.

  Lemma cpos : forall (P Q : Prop), (P -> Q) -> (~ Q -> ~ P).
  Proof.
    intros.
    intro.
    apply H0.
    apply H.
    apply H1.
  Defined.
  

  Lemma pdom_case2_total_2 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) x :
    total x ∈ pdom_case2 b1 b2 c1 c2 ->
    (total true ∈ b1 /\ total x ∈ c1) \/ (total true ∈ b2 /\ total x ∈ c2).
  Proof.
    intros.
    destruct H as [h1 [h2 [h3 h4]]].
    destruct h4.
    left; auto.
    destruct H.
    right; auto.
    destruct H as [_ [_ h]].
    contradict (flat_total_neq_bot _ h).
  Defined.

  Lemma pdom_case2_bot_1 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) :
    ~ (pdom_is_empty (pdom_case2 b1 b2 c1 c2)) ->
    (total true ∈ b1 /\ bot _ ∈ c1) \/ (total true ∈ b2 /\ bot _ ∈ c2)
    \/  ((bot bool ∈ b1 \/ total false ∈ b1) /\ (bot bool ∈ b2 \/ total false ∈ b2))
    -> bot X ∈ pdom_case2 b1 b2 c1 c2.
  Proof.
    intros.
    repeat split.
    intro.
    contradict H.
    apply pdom_case2_empty_1; auto.
    intro.
    contradict H.
    apply pdom_case2_empty_1; auto.
    intros h1 h2.
    contradict H.
    apply pdom_case2_empty_1; auto.
    intros h1 h2.
    contradict H.
    apply pdom_case2_empty_1; auto.
    destruct H0.
    left; auto.
    destruct H0.
    right; left; auto.
    right; right; destruct H0; repeat split; auto.
  Defined.

  Lemma pdom_case2_bot_2 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) :
    bot X ∈ pdom_case2 b1 b2 c1 c2 ->
    (total true ∈ b1 /\ bot _ ∈ c1) \/ (total true ∈ b2 /\ bot _ ∈ c2)
    \/  ((bot bool ∈ b1 \/ total false ∈ b1) /\ (bot bool ∈ b2 \/ total false ∈ b2)).
  Proof.
    intros.
    destruct H as [h1 [h2 [h3 h4]]].
    destruct h4.
    left; auto.
    destruct H.
    right; left; auto.
    right; right; destruct H.
    destruct H0; auto.
  Defined.


End BinaryCase.


Section CaseList.
  Fixpoint list_is_finite {X : Type} (l : list X) : infinite {x : X | In x l} -> False.
  Proof.
    destruct l.
    intro.
    destruct H.
    destruct (x 0).
    destruct (x 1).
    destruct i.
    intro.
    assert (infinite {x0 : X | In x0 l \/ x = x0}).
    apply subset_infinite_pset_infinite in H.
    apply pset_infinite_subset_infinite.
    destruct H.
    exists x0.
    destruct H; split; auto.
    intros.
    pose proof (H0 n).
    simpl in H1.
    destruct H1; auto.
    apply Pigeon2' in H0.
    destruct H0.
    exact (list_is_finite _ _ H0).
    apply hprop_ninfinite in H0; auto.
    intros.
    destruct x0, y.
    apply sig_eq; auto.
    simpl.
    rewrite <- e, <- e0; auto.
  Defined.
  
  Definition pdom_case_list {X : Type} (l : list ((pdom bool) * (pdom X))) : pdom X.
  Proof.
    exists
      (fun x =>
         (* define possible results in predicate form. *)
         (* (non)emptiness condition comes first:
            it is nonempty if and only if
            for all guard - computation pair, guard is nonempty, and if the guard contains true, computation is nonempty*)
         (Forall (fun ec => (~ pdom_is_empty (fst ec)) /\ (total true ∈ (fst ec) -> ~ pdom_is_empty (snd ec))) l)
         (* membership condition. Note that this case can include ⊥ *)
         /\ ((Exists (fun ec => total true ∈ (fst ec) /\ x ∈ (snd ec)) l)
             (* bottom condition from nonselectable guard. Note that this isnt iff condition for bot *)
             \/ (x = ⊥ /\ Forall (fun ec => total false ∈ (fst ec) \/ ⊥ ∈ (fst ec)) l))).
    

    (* now proving infinity -> contains bot *)
    intro.
    split.
    (* to prove containing bot, we first need to prove that it is nonempty *)
    {
      destruct H.
      destruct H.
      pose proof (H0 0).
      destruct H1 as [H1 _].
      auto.
    }
    
    (* now we prove that if there is infinitely many elements, there is bot  *)
    destruct H.
    destruct H.
    assert ( forall n : nat,

               (x n = ⊥ /\ Forall (fun ec : {S : flat bool -> Prop | pset_infinite S -> S ⊥} * pdom X => total false ∈ fst ec \/ ⊥ ∈ fst ec) l)
               \/ (Exists
                     (fun ec : {S : flat bool -> Prop | pset_infinite S -> S ⊥} * {S : flat X -> Prop | pset_infinite S -> S ⊥} =>
                        (total true ∈ fst ec) /\ x n ∈ snd ec) l
                     
           )).
    intro n; destruct (H0 n); destruct H2; auto.
    clear H0.
    destruct (forall_or _ _ _ H1).

    (* when one of the infinitely many elemnts happens to be ⊥ because of unselectable guard, then we are done *)
    destruct H0.
    right.
    destruct H0; split; auto.
    
    (* otherwise, the space {e : guard containing true & {x | x ∈ command gaurded by e} is infinite *)
    assert (infinite {ec' : {ec | In ec l /\ total true ∈ fst ec} &  {x | (proj1_sig (snd (proj1_sig ec')) x) } })%type.
    {
      clear H1.
      assert (forall a : nat,
               exists ec, 
                 (total true ∈ fst ec) /\ x a ∈ snd ec /\ In ec l).
      intro n.
      pose proof (H0 n).
      apply Exists_exists in H1.
      destruct H1.
      exists x0.
      destruct H1.
      destruct H2.
      auto.

      apply cchoice in H1.
      destruct H1.
      assert (forall n : nat, In (x0 n) l /\ total true ∈ fst (x0 n)).
      intro n; destruct (H1 n); auto.
      destruct H3; auto.
      assert (forall n, (x n ∈ snd (x0 n))).
      intro n; destruct (H1 n); auto.
      destruct H4; auto.
      exists (fun n => (existT _ (exist _ (x0 n) (H2 n)) (exist _ (x n) (H3 n)))).
      intros i j e.
      injection e; intros.
      apply H; auto.
    }
    clear  H H0 H1; rename x into H; rename H2 into H0. 

    (* by the infinity Pigeonhold principle, there is either
       (1) infintely many guards containing true or (2) one gaurd containing true whose guarded command has infintely many elements *)
    apply Pigeon in H0.
    destruct H0.
    {
      (* however, we only have finite list. Hence the first condition contradicts *)
      contradict H0.
      intro.
      assert (infinite {ec : pdom bool * pdom X | In ec l}).
      apply subset_infinite_pset_infinite in H0.
      apply pset_infinite_subset_infinite.
      destruct H0.
      exists x.
      destruct H0; split; auto.
      intro n; destruct (H1 n); auto.
      exact (list_is_finite _ H1).
    }

    (* when there is a guard containing true whose command contains infintely many elements,
       since the guarded command is pdom, it contaisn bot. and the bot is in the overall case operation. *)
    left.    
    apply Exists_exists.
    destruct H0.
    destruct x.
    exists x.
    destruct a; repeat split; auto.
    destruct x.
    simpl in H0.
    destruct p0.
    simpl in H0.
    simpl.
    destruct p1.
    simpl in H0.
    apply subset_infinite_pset_infinite in H0.
    pose proof (p1 H0).
    simpl.
    exact H1.
  Defined.

  Lemma Forall_to_forall {A} P (l:list A):
      Forall P l -> (forall x, In x l -> P x).
  Proof.
    apply Forall_forall.
  Defined.
  
  
  Lemma pdom_case_list_empty_1 {X} : forall (l : list ((pdom bool) * (pdom X))),
      (Exists (fun ec => pdom_is_empty (fst ec) \/ (total true ∈ fst ec /\ pdom_is_empty (snd ec)))) l ->
        pdom_is_empty (pdom_case_list l).
  Proof.
    intros.
    intros x [m _].
    apply Exists_exists in H.
    pose proof (Forall_to_forall _ _ m).
    clear m.
    destruct H as [h1 [h2 h3]].
    pose proof (H0 h1 h2).
    simpl in H.
    destruct H; destruct h3.
    auto.
    destruct H2.
    apply H1; auto.
  Defined.
  
      
  Lemma pdom_case_list_empty_2 {X} : forall (l : list ((pdom bool) * (pdom X))),
      pdom_is_empty (pdom_case_list l) ->
      (Exists (fun ec => pdom_is_empty (fst ec) \/ (total true ∈ fst ec /\ pdom_is_empty (snd ec)))) l.
  Proof.
    intros.
    apply Exists_exists.
    destruct (lem (exists x : pdom bool * pdom X, In x l /\ (pdom_is_empty (fst x) \/ (total true ∈ fst x) /\ pdom_is_empty (snd x)))); auto.
    pose proof (neg_exists_forall_neg _ _ H0).
    clear H0.
    contradict H.

    destruct (lem (Exists (fun ec => total true ∈ fst ec) l)).
    {
      (* when there is true *)
      apply Exists_exists in H.
      destruct H.
      pose proof (H1 x).
      simpl in H0.
      destruct H.
      apply neg_conj in H0.
      destruct H0.
      auto.
      apply neg_disj in H0.
      destruct H0.
      apply neg_conj in H3.
      destruct H3.
      auto.
      apply pdom_neg_empty_exists in H3.
      destruct H3.
      apply (pdom_is_neg_empty_by_evidence _ x0).
      simpl.
      split.
      {
        simpl.
        apply Forall_forall.
        intros.
        pose proof (H1 x1).
        simpl in H5.
        apply neg_conj in H5.
        destruct H5.
        auto.
        apply neg_disj in H5.
        destruct H5.
        split; auto.
      }
      left.
      apply Exists_exists.
      exists x.
      split; auto.
    }

    {
    (* when there is no true *)
      
      apply (pdom_is_neg_empty_by_evidence _ ⊥).
      simpl.
      split.
      {
        simpl.
        apply Forall_forall.
        intros.
        pose proof (H1 x).
        simpl in H2.
        apply neg_conj in H2.
        destruct H2.
        auto.
        apply neg_disj in H2.
        destruct H2.
        split; auto.
      }
      right.
      split; auto.
      apply Forall_forall.
      intros.
      apply Forall_Exists_neg in H.
      pose proof (Forall_to_forall _ _ H x H0).
      simpl in H2.
      pose proof (H1 x).
      simpl in H3.
      apply neg_conj in H3.
      destruct H3.
      contradict (H3 H0).
      apply neg_disj in H3.
      destruct H3 as [H3 _].
      apply pdom_neg_empty_exists in H3.
      destruct H3.
      destruct x0.
      right; auto.
      destruct b.
      contradict (H2 H3).
      left; auto.
    }
  Defined.
  
  Lemma pdom_case_list_total_1 {X} : forall (l : list ((pdom bool) * (pdom X))) x,
      (~ pdom_is_empty (pdom_case_list l)) ->
      (Exists (fun ec => total true ∈ fst ec /\ total x ∈ snd ec) l) ->
      total x ∈ pdom_case_list l.
  Proof.
    intros.
    simpl.
    split.
    apply pdom_neg_empty_exists in H.
    destruct H.
    simpl in H.
    destruct H; auto.

    left.
    apply Exists_exists.
    apply Exists_exists in H0.
    destruct H0.
    exists x0.
    auto.
  Defined.
  
  Lemma pdom_case_list_total_2 {X} : forall (l : list ((pdom bool) * (pdom X))) x,
      total x ∈ pdom_case_list l ->
      (Exists (fun ec => total true ∈ fst ec /\ total x ∈ snd ec) l).
  Proof.
    intros.
    simpl.
    destruct H.
    destruct H0.
    auto.
    destruct H0.
    contradict (flat_total_neq_bot _ H0).
  Defined.
 
  Lemma pdom_case_list_bot_1 {X} : forall (l : list ((pdom bool) * (pdom X))),
      (~ pdom_is_empty (pdom_case_list l)) ->
      (Exists (fun ec => total true ∈ fst ec /\ ⊥ ∈ snd ec) l) \/
        (Forall (fun ec => total false ∈ (fst ec) \/ ⊥ ∈ (fst ec)) l) ->
      ⊥ ∈ pdom_case_list l.
  Proof.
    intros.
    simpl.
    split.
    apply pdom_neg_empty_exists in H.
    destruct H.
    simpl in H.
    destruct H; auto.
    destruct H0.
    auto.
    right.
    auto.
  Defined.
  
  Lemma pdom_case_list_bot_2 {X} : forall (l : list ((pdom bool) * (pdom X))),
      ⊥ ∈ pdom_case_list l ->
      (Exists (fun ec => total true ∈ fst ec /\ ⊥ ∈ snd ec) l) \/
        (Forall (fun ec => total false ∈ (fst ec) \/ ⊥ ∈ (fst ec)) l).     
  Proof.
    intros.
    simpl in H.
    destruct H.
    destruct H0; auto.
    destruct H0.
    right; auto.
  Defined.
 
  
End CaseList.


Section While.
  (* this section defines the sematnic function for while loop.
     This section includes proofs of the continuity of bind operation and the continuity of if-then-else operation.
     At the end of this section, we prove that the semantic function for while loop is conintuous. *)
  Lemma pdom_bind_fst_monotone {X Y : Type} (f g: X -> pdom Y) (S : pdom X) :
    f ≤ g -> pdom_bind f S ⊑ pdom_bind g S.
  Proof.    
    intros.
    destruct (lem (proj1_sig (pdom_bind f S) (bot Y))).
    {
      (* when ⊥ is in f^†(S)  *)
      right; split; auto.
      destruct (lem (pdom_is_empty (pdom_bind g S))); auto.
      right.
      assert (forall x', proj1_sig (pdom_bind f S) (total x') -> proj1_sig (pdom_bind g S) (total x')).
      {
        intros.
        assert (exists x : X, proj1_sig S (total x) /\ proj1_sig (f x) (total x')).
        {
          destruct H2 as [a [b c]].
          destruct c.
          destruct H2.
          contradict (flat_total_neq_bot _ H2).
          destruct H2.
          destruct H2.
          unfold pdom_lift in H3.
          simpl in H3.
          destruct H3.
          destruct H3.
          destruct x0.
          simpl in H4.
          contradict (flat_bot_neq_total _ H4).
          exists x0.
          simpl in H4.
          injection H4; intro.
          rewrite H5; auto.
        }
        apply pdom_bind_total_1.
        split; auto.
        destruct H3 as [x [p q]].
        exists x.
        split; auto.
        destruct (H x).
        rewrite <- H3; auto.
        destruct H3.
        destruct H4.
        contradict (H1  (pdom_bind_empty_1 _ _ (or_intror (ex_intro _ x (conj p H4))))).
        pose proof (H4 (total x') q).
        simpl in H5.
        destruct H5; auto.
        contradict (flat_bot_neq_total _ H5).
      }
      intros x p.
      destruct x.
      simpl; right; auto.
      apply H2 in p.
      simpl; left; auto.
    }
    {
      (* when ⊥ is not in f^† S *)
      destruct (lem (pdom_is_empty (pdom_bind f S))).
      {
        left.
        rewrite (pdom_is_empty_is_empty _ H1).
        apply eq_sym, pdom_is_empty_is_empty.
        apply pdom_bind_empty_1.
        destruct (pdom_bind_empty_2 _ _ H1).
        left; auto.
        right.
        destruct H2 as [a [b c]].
        exists a; split; auto.
        destruct (H a).
        rewrite <- H2; auto.
        destruct H2.
        contradict (c _ H2).
      }
      {      
        pose proof (pdom_bind_not_contain_bot _ _ H1 H0).
        assert (forall a, total a ∈ S -> f a = g a) as jj.
        {
          intros.
          destruct (H a); auto.
          destruct H4.
          contradict (H2 _ H3 H4).
        }      
        left.
        apply pdom_bind_agree; auto.
      }

    }
  Defined.

  Lemma pdom_fun_chain_bind_chain {X Y : Type} (S : pdom X) :
    forall (s : nat -> (X -> pdom Y)) (c : pdom_fun_is_chain s), pdom_is_chain (fun n => pdom_bind (s n) S).
  Proof.
    intros.
    intros n m o.
    apply pdom_bind_fst_monotone.
    apply c.
    exact o.
  Defined.


  Lemma nat_injective_unbounded : forall n, forall (f : nat -> nat), injective f -> exists m, n <= f m.
  Proof.
    intro n.
    induction n.
    intros.
    exists 0.
    apply le_0_n.
    intros.
    destruct (IHn f H).
    destruct (Lt.le_lt_or_eq_stt _ _ H0).
    exists x.
    auto.
    clear H0.
    assert (injective (fun m => f (x + m + 1))).
    intros i j e.
    apply H in e.
    lia.
    destruct (IHn _ H0).
    destruct (Lt.le_lt_or_eq_stt _ _ H2).
    exists (x + x0 + 1).
    auto.
    rewrite H3 in H1.
    apply H in H1.
    contradict H1.
    lia.
  Defined.



  Lemma pdom_chain_infinite_bot_bot {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
    infinite {n | (bot X) ∈ s n} -> (bot X) ∈ pdom_chain_sup s c.
  Proof.
    intro i.
    apply pdom_chain_bot_1.
    intro n.
    destruct i.
    pose proof (nat_injective_unbounded n (fun n => proj1_sig (x n))).  
    assert ( injective (fun n : nat => proj1_sig (x n)) ).
    intros i j e.
    apply proj1_sig_injective, H in e; auto.
    apply H0 in H1.
    destruct H1.
    clear H0.
    destruct (x x0).
    simpl in H1.
    destruct (lem (bot X ∈ s n)); auto.
    destruct (c _ _ H1); auto.
    rewrite H2; auto.
    destruct H2.
    contradict (H0 H2).
  Defined.

  Lemma pdom_bind_fst_continuous {X Y : Type} (S : pdom X) :
    forall (s : nat -> (X -> pdom Y)) (c : pdom_fun_is_chain s),
      pdom_bind (pdom_fun_chain_sup s c) S = pdom_chain_sup (fun n => pdom_bind (s n) S) (pdom_fun_chain_bind_chain S s c).
  Proof.
    intros.
    apply pdom_le_asym.
    {

      destruct (lem (pdom_is_empty (  pdom_bind (pdom_fun_chain_sup s c) S))).      
      {
        (* when lhs is empty *)
        left.
        rewrite (pdom_is_empty_is_empty _ H).
        apply eq_sym.
        apply pdom_is_empty_is_empty.
        apply pdom_chain_empty_1.
        apply pdom_bind_empty_2 in H.
        destruct H.
        exists 0.
        apply pdom_bind_empty_1.
        left; auto.
        destruct H.
        destruct H.
        apply pdom_fun_chain_empty_2 in H0.
        destruct H0.
        exists x0.
        apply pdom_bind_empty_1.
        right.
        exists x; auto.
      }

      (* when lhs is not empty *)
      {
        assert (~ pdom_is_empty S) as nempty2.
        {
          intros.
          intro.
          assert (pdom_is_empty ( pdom_bind (pdom_fun_chain_sup s c) S)).
          apply pdom_bind_empty_1.
          left; auto.
          apply (H H1).
        }
        assert (forall n x, (total x ∈ S) -> ~ pdom_is_empty (s n x)) as nempty1.
        {
          intros.
          intro.
          assert (pdom_is_empty ( pdom_bind (pdom_fun_chain_sup s c) S)).
          apply pdom_bind_empty_1.
          right.
          exists x.
          split; auto.
          apply pdom_fun_chain_empty_1.
          exists n.
          auto.
          apply (H H2).
        }
        assert (forall n, ~ pdom_is_empty (pdom_bind (s n) S)) as nempty3.
        {
          intros n e.
          apply pdom_bind_empty_2 in e.
          destruct e.
          exact (nempty2 H0).
          destruct H0 as [a [b d]].
          exact (nempty1 n a b d).
        }
        rename H into H'.

        destruct (lem ((bot Y) ∈ pdom_bind (pdom_fun_chain_sup s c) S)).
        {
          (* when there is bot all the time *)
          right; split; auto.
          right.
          intros y h.
          apply pdom_is_in_add_element_is_in.
          split.
          intros [n e]; exact (nempty3 n e).
          split.
          intro.
          {
            (* when y is bot *)
            destruct y.
            exists 0.
            exact (H0 0).
            (* when y is total *)
            
            
            apply pdom_bind_total_2 in h.
            destruct h.
            destruct H2.
            destruct H2.
            destruct H3.
            destruct H4.
            destruct (lem (exists n : nat, ~ (bot Y ∈ s n x))).
            apply H5 in H6.
            destruct H6.
            exists x0.
            destruct H6.
            apply pdom_bind_total_1.
            split.
            apply nempty3.
            exists x; auto.
            assert ((forall n : nat, bot Y ∈ s n x)).
            destruct (lem ( forall n : nat, bot Y ∈ s n x)); auto.
            contradict H6.
            apply neg_forall_exists_neg in H7.
            exact H7.
            apply H4 in H7.
            destruct H7.
            exists x0.
            apply pdom_bind_total_1.
            split.
            apply nempty3.
            exists x; auto.
          }
          intro.
          (* this is contradiction *)
          assert (forall n, bot Y ∈ pdom_bind (s n) S).
          destruct (pdom_bind_bot_2 _ _  H).
          intros.
          apply pdom_bind_bot_1; auto.
          destruct H1 as [a [b d]].
          intro n;
            pose proof (pdom_fun_chain_bot_2 _ c _ d n).
          apply pdom_bind_bot_1; auto.
          right; exists a; auto.
          destruct H0.
          contradict (H0 (H1 x)).
        }
        
        {
          (* when bot is not in the sup *)
          (* when lhs is non empty *)

          left.
          assert (forall x, (total x) ∈ S ->  ~ ((bot Y) ∈ (pdom_fun_chain_sup s c x))) as fiber_nbot.
          {
            intros x e.
            contradict H.
            apply pdom_bind_total_1.          
            split; auto.
            exists x; split; auto.
          }
          apply proj1_sig_injective.
          apply pred_ext; intros.
          {
            destruct a.
            contradict (H H0).
            pose proof (pdom_bind_total_2 _ _ _ H0) as [_ [x [p1 p2]]].
            unfold pdom_fun_chain_sup in p2.
            apply pdom_chain_membership_2 in p2.
            destruct p2.
            assert (total y ∈ pdom_bind (s x0) S).
            apply pdom_bind_total_1.
            split; auto.
            exists x; auto.
            apply pdom_chain_membership_1.
            split; auto.
            intro.
            apply pdom_chain_empty_2 in H3.
            destruct H3.
            contradict (nempty3 x1 H3).
            exists x0; auto.
          }
          {
            destruct a.
            {
              (* test index set contains bot *)
              destruct (lem (bot X ∈ S)).
              {
                (* when the index set contains bot, then both sides contain bot anyway *)
                apply pdom_bind_bot_1; auto.              
              }
              {
                (* when the index set does not contain bot, things become complicated..
                   first, show that the index set is finite, and use Pigeon to select
                   an index x ∈ S where f on it contains bot indefinitely. *)
                assert (~ pset_infinite (proj1_sig S)).
                intro.
                apply (H1 (pdom_infinite_bot S H2)).
                (* first prove that for each n, there exists an index x
                 where f x contains bot *)
                assert (forall n, exists x, total x ∈ S /\ (bot Y) ∈ s n x) as fe.
                {
                  intro n.
                  pose proof (pdom_chain_bot_2 _ _ H0 n).
                  
                  apply pdom_bind_bot_2 in H3.
                  destruct H3.
                  contradict (H1 H3).
                  destruct H3.
                  exists x; destruct H3; auto.
                }
                apply cchoice in fe.
                destruct fe as [choice p].
                pose (fun x : {y | total y ∈ S} => {n : nat | (total (proj1_sig x) ∈ S) /\ bot Y ∈ s n (proj1_sig x)}) as P.
                pose proof (Pigeon P).
                assert (infinite { a & P a}).
                exists (fun n => existT _ (exist _ (choice n) (proj1 (p n))) (exist _ n (p n))).                
                intros i j e.
                injection e.
                intros.
                auto.
                apply H3 in H4; clear H3.
                destruct H4.
                contradict H2.
                apply subset_infinite_pset_infinite in H3.
                destruct H3.
                exists (fun n => total (x n)).
                split; destruct H2; auto.
                intros i j e.
                apply H2; injection e; auto.

                (* m : x ∈ S is the index where i say ⊥ appears infinitely often in f x *)
                destruct H3 as [[x m] i].
                apply pdom_bind_bot_1; auto.
                right.
                exists x.
                split; auto.
                apply pdom_chain_infinite_bot_bot.
                destruct i.
                apply pset_infinite_subset_infinite.
                
                exists (fun n => proj1_sig  (x0 n)).
                split.
                intros i j e.
                apply H3; apply proj1_sig_injective in e; auto.
                intro.
                destruct (x0 n).
                simpl.
                simpl in a.
                destruct a; auto.              
              }
            }
            
            {
              (* when a is a total element *)
              
              apply pdom_chain_membership_2 in H0.
              destruct H0.
              apply pdom_bind_total_1.
              split; auto.
              
              apply pdom_bind_total_2 in H0.
              destruct H0 as [_ [p1 [p2 p3]]].
              exists p1; split; auto.
              unfold pdom_fun_chain_sup.
              
              apply pdom_chain_membership_1.
              split; auto.
              unfold pdom_fun_chain_sup in H.
              intro.
              apply pdom_chain_empty_2 in H0.
              destruct H0.
              contradict (nempty1 x0 p1 p2 H0).
              exists x; auto.              
            }
          }        
        }
      }
    }
    { 
      apply pdom_omega_complete.
      intros.
      apply pdom_bind_fst_monotone.
      apply pdom_fun_omega_complete.
    }
  Defined.

  Lemma pdom_ite_fst_monotone {X : Type} (S T R : pdom X) :
    S ⊑ T -> (fun b : bool => if b then S else R) ≤ (fun b => if b then T else R).
  Proof.
    intros o b.
    destruct b; auto.
    left; auto.
  Defined.

  Lemma pdom_chain_ite_fun_chain {X : Type} (S : pdom X) (s : nat -> pdom X) (c : pdom_is_chain s) :
    pdom_fun_is_chain (fun n => (fun b : bool => if b then s n else S)).
  Proof.
    intros i j o b.
    apply pdom_ite_fst_monotone.
    apply c, o.
  Defined.


  Lemma pdom_is_chain_irrl {X : Type} (c : nat -> pdom X) (p q : pdom_is_chain c) : p = q.
  Proof.
    apply prop_irrl.
  Defined.

  Lemma pdom_ite_fst_continuous {X : Type} (S : pdom X) (s : nat -> pdom X) (c : pdom_is_chain s) :
    (fun b : bool => if b then pdom_chain_sup s c else S) = pdom_fun_chain_sup _ (pdom_chain_ite_fun_chain S s c).
  Proof.
    intros.
    unfold pdom_fun_chain_sup.
    apply dfun_ext.
    intro.
    destruct a.
    rewrite (pdom_is_chain_irrl
               _
               c
               (fun (i j : nat) (o : i <= j) => pdom_chain_ite_fun_chain S s c i j o true)
            )
    .
    auto.
    pose proof (pdom_omega_complete (fun _ => S) (fun (i j : nat) (o : i <= j) => pdom_chain_ite_fun_chain S s c i j o false)).
    apply pdom_le_asym.
    apply H.
    exact 0.
    apply H.
    intro; apply pdom_le_refl.
  Defined.        

  Definition pdom_W {X : Type} (b : X -> pdom bool) (c : X -> pdom X) : (X -> pdom X) -> X -> pdom X.
  Proof.
    intros f.
    intro x.
    exact (pdom_bind (fun (b : bool) => if b then (pdom_bind f) (c x) else pdom_unit x) (b x)). 
  Defined.

  Lemma pdom_W_monotone {X : Type} (b : X -> pdom bool) (c : X -> pdom X) : pdom_fun_is_monotone (pdom_W b c).
  Proof.
    unfold pdom_W.
    intros f g o x.
    apply pdom_bind_fst_monotone.
    intro y.
    destruct y.
    apply pdom_bind_fst_monotone.
    apply o.
    left; auto.
  Defined.


  Lemma pdom_W_continuous {X : Type} (b : X -> pdom bool) (c : X -> pdom X) : pdom_fun_is_continuous (pdom_W b c) (pdom_W_monotone b c).
  Proof.
    unfold pdom_W.
    intros s o.
    apply dfun_ext.
    intros.
    rewrite (pdom_bind_fst_continuous _ s o).
    rewrite (pdom_ite_fst_continuous).
    rewrite pdom_bind_fst_continuous.
    auto.
  Defined.

  Definition pdom_while {X : Type} : (X -> pdom bool) -> (X -> pdom X) -> X -> pdom X.
  Proof.
    intros b c.
    exact (pdom_fun_lfp (pdom_W b c) (pdom_W_monotone b c)).
  Defined.


End While.
