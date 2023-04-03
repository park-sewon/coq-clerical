(* classical treatment of our powerdomain ... maybe this makes some people upset :( *)
(* I also uses dependent destruction... what does it do really *)
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Compare_dec.

(* about the base of our type theory allowing Prop to be classical and some other trivally derived stuffs *)
Section Base.
  Axiom lem : forall P : Prop, P \/ ~P.
  Axiom cchoice : forall (A : Type) (P : nat -> A -> Prop), (forall n : nat, exists a : A, P n a) -> exists f : nat -> A, forall n, P n (f n).
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
  
End Base.

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

Section Powerdomain.
  
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

  (* Definition proj1_sig {A} : pdom A -> pset (flat A). *)
  (* Proof. *)
  (*   intros [f _]. *)
  (*   exact f. *)
  (* Defined. *)

  Lemma pdom_infinite_bot {A} (S : pdom A) : pset_infinite (proj1_sig S) -> proj1_sig S (bot A).
  Proof.
    destruct S; simpl; auto.
  Defined.
  
  Definition pdom_nempty {A : Type} : pdom A -> Prop := fun S => exists a, proj1_sig S a.

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
              pdom_nempty X /\
                (* all subsets are not empty *)
                (forall S : pdom A, proj1_sig X (total S) -> pdom_nempty S) /\
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
          (pdom_nempty b1 /\ pdom_nempty b2)
          /\
            (proj1_sig b1 (total true) -> pdom_nempty c1)
          /\
            (proj1_sig b2 (total true) -> pdom_nempty c2)
          /\
            (* values *)
            (
              (proj1_sig b1 (total true) /\ proj1_sig c1 x)
              \/
                (proj1_sig b2 (total true) /\ proj1_sig c2 x)
              \/
                (proj1_sig b1 (bot bool) /\ proj1_sig b2 (bot bool) /\ x = bot X)
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
               (proj1_sig b1 (bot bool) /\ proj1_sig b2 (bot bool) /\ x n = bot X) \/
                 (proj1_sig b1 (total true) /\ proj1_sig c1 (x n) \/
                    proj1_sig b2 (total true) /\ proj1_sig c2 (x n))).
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
End Powerdomain.
Arguments total {_}.


Section PowerdomainContinuity.

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

  Definition pdom_incl {X : Type} (S T : pdom X) :=
    forall x : flat X, proj1_sig S x -> proj1_sig T x.

  Definition pdom_is_empty {X : Type} (S : pdom X) := forall x, ~ proj1_sig S x.

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
    
  Definition pdom_le {X : Type} (S T : pdom X) :=
    S = T \/ (proj1_sig S (bot X) /\ (pdom_is_empty T \/ pdom_incl S (pdom_add_elem T (bot X)))).

  Infix "⊑" := (pdom_le) (at level 80).
  
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
  
  Lemma pdom_le_refl {X : Type} : forall (S : pdom X), S ⊑ S.
  Proof.
    intros.
    left; auto.
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
    pose proof (p2).
  Admitted.
  
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

  
  Definition pdom_is_monotone {X : Type} (f : pdom X -> pdom X) := forall S T, S ⊑ T -> f S ⊑ f T.

  Lemma pdom_chain_monotone_chain {X : Type} (f : pdom X -> pdom X) :
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
  
  Definition pdom_is_continuous {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) :=
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

  Definition pdom_fun_le {X Y : Type} (f g : X -> pdom Y) := forall a, f a ⊑ g a.

  Infix "≤" := (pdom_fun_le) (at level 80).
  
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

  Lemma pdom_fun_le_refl {X Y} (f : X -> pdom Y) : f ≤ f.
  Proof.
    intro x; apply pdom_le_refl; auto.
  Defined.

  Lemma pdom_fun_le_trans {X Y} (f g h: X -> pdom Y) : f ≤ g -> g ≤ h -> f ≤ h.
  Proof.
    intros h1 h2 x; apply (pdom_le_trans _ _ _ (h1 x) (h2 x)).
  Defined.

  Lemma pdom_fun_le_asym {X Y} (f g: X -> pdom Y) : f ≤ g -> g ≤ f -> f = g.
  Admitted.
    
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

  Notation "x ∈ S" := (proj1_sig S x) (at level 80).
  
  Lemma pdom_bind_membership {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
    forall x, (~ pdom_is_empty (pdom_bind f S) /\ exists s, (total s) ∈ S /\ x ∈ f s) -> x ∈ pdom_bind f S.
  Proof.
    intros.
  Admitted.

  Lemma pdom_bind_membership_2 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
    forall x, x ∈ pdom_bind f S -> (~ pdom_is_empty (pdom_bind f S) /\ exists s, (total s) ∈ S /\ x ∈ f s).
  Proof.
  Admitted.
  
  Lemma pdom_bind_not_contain_bot {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
    ~ ((bot Y) ∈ pdom_bind f S) -> forall s, total s ∈ S -> ~ (bot Y ∈ f s).
  Proof.
  Admitted.
  
  Lemma pdom_bind_empty_1 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
    pdom_is_empty S \/ (exists x, (total x) ∈ S /\ pdom_is_empty (f x)) -> pdom_is_empty (pdom_bind f S).
  Proof.
    intros.
  Admitted.

  Lemma pdom_bind_empty_2 {X Y : Type} (f : X -> pdom Y) (S : pdom X) :
    pdom_is_empty (pdom_bind f S) ->
    pdom_is_empty S \/ (exists x, (total x) ∈ S /\ pdom_is_empty (f x)).
  Proof.
    intros.
  Admitted.

  Lemma pdom_bind_agree {X Y : Type} (f g : X -> pdom Y) (S : pdom X) :
    (forall x, total x ∈ S -> f x = g x) -> pdom_bind f S = pdom_bind g S.
  Proof.
    intros.
    apply sig_eq.
    apply pred_ext.
    intros.
    apply pdom_bind_membership.
    split.
    intro.
    apply pdom_bind_empty_2 in H1.
    destruct H1.
    unfold pdom_is_empty in H1.
    pose proof (pdom_bind_empty_1 f _ (or_introl H1)). 
    contradict (H2 a H0).
    destruct H1.
    destruct H1.
    rewrite <- (H x H1) in H2.
    pose proof (pdom_bind_empty_1 f _ (or_intror (ex_intro _ x (conj H1 H2)))). 
    contradict (H3 a H0).
    apply pdom_bind_membership_2 in H0.
    destruct H0.
    destruct H1.
    exists x.
    destruct H1.
    rewrite (H x H1) in H2; auto.

    intros.
    apply pdom_bind_membership.
    split.
    intro.
    apply pdom_bind_empty_2 in H1.
    destruct H1.
    unfold pdom_is_empty in H1.
    pose proof (pdom_bind_empty_1 g _ (or_introl H1)). 
    contradict (H2 a H0).
    destruct H1.
    destruct H1.
    rewrite  (H x H1) in H2.
    pose proof (pdom_bind_empty_1 g _ (or_intror (ex_intro _ x (conj H1 H2)))). 
    contradict (H3 a H0).
    apply pdom_bind_membership_2 in H0.
    destruct H0.
    destruct H1.
    exists x.
    destruct H1.
    rewrite <- (H x H1) in H2; auto.
  Defined.
   
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
        apply pdom_bind_membership.
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
      pose proof (pdom_bind_not_contain_bot _ _ H0).
      assert (forall a, total a ∈ S -> f a = g a) as jj.
      {
        intros.
        destruct (H a); auto.
        destruct H3.
        contradict (H1 _ H2 H3).
      }      
      left.
      apply pdom_bind_agree; auto.
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

  Lemma pdom_is_in_add_element_is_in {X : Type} (p : pdom X) (x y : flat X) : x ∈ p -> x ∈ pdom_add_elem p y.
  Proof.
  Admitted.

  Lemma pdom_chain_empty_1 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
    pdom_is_empty (pdom_chain_sup s c) -> exists n, pdom_is_empty (s n).

  Proof.
  Admitted.

  Lemma pdom_chain_bot_1 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
    (bot X) ∈ (pdom_chain_sup s c) -> forall n, (bot X) ∈ s n.
  Proof.
  Admitted.

  Lemma pdom_chain_bot_2 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
    (forall n, (bot X) ∈ s n) ->  (bot X) ∈ (pdom_chain_sup s c).
  Proof.
  Admitted.
    
  Lemma pdom_chain_empty_2 {X : Type} (s : nat -> pdom X) (c : pdom_is_chain s) :
    (exists n, pdom_is_empty (s n)) -> pdom_is_empty (pdom_chain_sup s c).

  Proof.
  Admitted.
  
  Lemma pdom_fun_chain_empty_1 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
    forall x, pdom_is_empty (pdom_fun_chain_sup s c x) -> exists n, pdom_is_empty (s n x).

  Proof.
  Admitted.

  Lemma pdom_fun_chain_empty_2 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
    forall x, (exists n, pdom_is_empty (s n x)) ->  pdom_is_empty (pdom_fun_chain_sup s c x).

  Proof.
  Admitted.

  Lemma pdom_fun_chain_bot_1 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
    forall x, (bot Y) ∈ (pdom_fun_chain_sup s c x) -> forall n, (bot Y) ∈ (s n x).

  Proof.
  Admitted.

  Lemma pdom_fun_chain_bot_2 {X Y : Type} (s : nat -> X -> pdom Y) (c : pdom_fun_is_chain s) :
    forall x, (forall n, (bot Y) ∈ (s n x)) -> (bot Y) ∈ (pdom_fun_chain_sup s c x) .

  Proof.
  Admitted.

  
  Lemma pdom_bind_fst_continuous {X Y : Type} (S : pdom X) :
    forall (s : nat -> (X -> pdom Y)) (c : pdom_fun_is_chain s),
      pdom_bind (pdom_fun_chain_sup s c) S = pdom_chain_sup (fun n => pdom_bind (s n) S) (pdom_fun_chain_bind_chain S s c).
  Proof.
    intros.
    apply pdom_le_asym.
    {
      destruct (lem ((bot Y) ∈ pdom_bind (pdom_fun_chain_sup s c) S)).
      {
        (* when there is bot all the time *)
        right; split; auto.
        right.
        assert (forall n x, (total x ∈ S) -> ~ pdom_is_empty (s n x)) as nempty1.
        {
          intros.
          intro.
          assert (pdom_is_empty ( pdom_bind (pdom_fun_chain_sup s c) S)).
          apply pdom_bind_empty_1.
          right.
          exists x.
          split; auto.
          apply pdom_fun_chain_empty_2.
          exists n.
          auto.
          apply (H2 _ H).
        }
        assert (~ pdom_is_empty S) as nempty2.
        {
          intros.
          intro.
          assert (pdom_is_empty ( pdom_bind (pdom_fun_chain_sup s c) S)).
          apply pdom_bind_empty_1.
          left; auto.
          apply (H1 _ H).
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
        
        intros y h.
        apply pdom_is_in_add_element_is_in.
        split.
        intros [n e]; exact (nempty3 n e).
        split.
        intro.
        apply pdom_bind_membership_2 in h.
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
        apply pdom_bind_membership.
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
        apply pdom_bind_membership.
        split.
        apply nempty3.
        exists x; auto.
        intro.
        destruct H0.
        contradict H0.
        apply pdom_bind_membership.
        split.
        apply nempty3.
        apply pdom_bind_membership_2 in H.
        destruct H.
        destruct H0.
        exists x0.
        destruct H0; split; auto.
        exact (pdom_fun_chain_bot_1 s c x0 H1 x).
      }
 
      {
        (* when bot is not in the sup *)
        (* when lhs is empty *)
        destruct (lem (pdom_is_empty (  pdom_bind (pdom_fun_chain_sup s c) S))).
        {
          admit.
        }

        (* when lhs is non empty *)
        {
          assert (~ pdom_is_empty S) as nempty2.
          {
            intros.
            intro.
            assert (pdom_is_empty ( pdom_bind (pdom_fun_chain_sup s c) S)).
            apply pdom_bind_empty_1.
            left; auto.
            apply (H0 H2).
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
            apply pdom_fun_chain_empty_2.
            exists n.
            auto.
            apply (H0 H3).
          }
          assert (forall n, ~ pdom_is_empty (pdom_bind (s n) S)) as nempty3.
          {
            intros n e.
            apply pdom_bind_empty_2 in e.
            destruct e.
            exact (nempty2 H1).
            destruct H1 as [a [b d]].
            exact (nempty1 n a b d).
          }

          left.
          assert (forall x, (total x) ∈ S ->  ~ ((bot Y) ∈ (pdom_fun_chain_sup s c x))).
          intros x e.
          contradict H.
          apply pdom_bind_membership.          
          split; auto.
          exists x; split; auto.
          
          admit.
        }
        
      }
    }
    {
      apply pdom_omega_complete.
      intros.
      apply pdom_bind_fst_monotone.
      apply pdom_fun_omega_complete.
    }
    
  Admitted.
  
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
  Print pdom_W.
  
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
  
End PowerdomainContinuity.
