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

  
End Base.
