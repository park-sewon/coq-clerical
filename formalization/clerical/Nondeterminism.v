(* classical treatment of our powerdomain ... maybe this makes some people upset :( *)

Axiom lem : forall P : Prop, P \/ ~P.
Axiom cchoice : forall (A : Type) (P : nat -> A -> Prop), (forall n : nat, exists a : A, P n a) -> exists f : nat -> A, forall n, P n (f n).

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
  
Inductive flat (A : Type) :=
  bot : flat A
| total : A -> flat A.
Arguments total {_}.

Definition pset (A : Type) := A -> Prop.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall a b, f a = f b -> a = b.

Definition infinite {A : Type} (S : pset A) : Prop :=
  exists f : nat -> A, injective f /\ forall n, S (f n). 

Definition pdom (A : Type)
  := {S : pset (flat A) | infinite S -> S (bot A)}.

Definition pdom_char {A} : pdom A -> pset (flat A).
Proof.
  intros [f _].
  exact f.
Defined.

Definition pdom_nempty {A : Type} : pdom A -> Prop := fun S => exists a, pdom_char S a.

(* powerdomain is a monad *)
Definition pdom_unit {A : Type} : A -> pdom A.
Proof.
  intro a.
  exists (fun b => total a = b).
  intro.
  unfold infinite in H.
  contradict H.
  intro.
  destruct H as [f [i e]].
  pose proof (i 0 1).
  assert (f 0 = f 1) by (rewrite <- e; auto).
  pose proof (H H0).
  contradict H1.
  auto.
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
  assert (infinite (pdom_char X)).
  destruct H as [j [inj e]].
  destruct (cchoice _ _ e) as [i p].
  exists i.
  split.
  intros n m eq.
  destruct (p n) as [_ P].
  destruct (p m) as [_ Q].
  induction eq.
  rewrite P in Q.
  exact (inj _ _ Q).
  intro n.
  destruct (p n); auto.
  destruct X as [X inf].
  unfold pdom_char in H, H0.
  exists (bot A).
  simpl.
  pose proof (inf H0); split; auto.
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

  repeat split; try (destruct H as [f [a b]]).
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
  right.
  clear H.
Admitted.

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

Definition pdom_lift2 {A B C : Type} : (A -> B -> C) -> pdom A -> pdom B -> pdom C.
Admitted.

Definition pdom_bind2 {A B C : Type} : (A -> B -> pdom C) -> pdom A -> pdom B -> pdom C.
Admitted.

Definition strict_union {X : Type} : pdom X -> pdom X -> pdom X.
Proof.
  intros S T.
  exists (fun x => pdom_nempty S /\ pdom_nempty T /\ (pdom_char S x  \/ pdom_char T x)).
  intro.
  destruct H as [f [a b]].
  assert (forall n, (pdom_char S (f n) \/ pdom_char T (f n))).
  intro n; destruct (b n) as [_ [_ c]]; auto.
Admitted.

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

Definition pdom_flat_bind {X Y : Type} (f : flat X -> pdom Y) : pdom X -> pdom Y.
Admitted.

Definition pdom_flat_bind2 {X Y Z : Type} (f : flat X -> flat Y -> pdom Z) : pdom X -> pdom Y -> pdom Z.
Admitted.

Definition pdom_while {X : Type} : (X -> pdom bool) -> (X -> pdom X) -> X -> pdom X.
Proof.
  intros B C.
Admitted.

