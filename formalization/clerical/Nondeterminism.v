(* classical treatment of our powerdomain ... maybe this makes some people upset :( *)

(* random stuffs *)
Axiom lem : forall P : Prop, P \/ ~P.
Axiom cchoice : forall (A : Type) (P : nat -> A -> Prop), (forall n : nat, exists a : A, P n a) -> exists f : nat -> A, forall n, P n (f n).
Axiom prop_ext : forall (P Q : Prop), (P -> Q) -> (Q -> P) -> P = Q.

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

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall a b, f a = f b -> a = b.

Axiom Pigeon : forall {A : Type} (P : A -> Type) (f : nat -> {a : A & P a}), 
    injective f -> 
    (exists g : nat -> A, injective g) \/ (exists a : A, exists g : nat -> P a, injective g).
 
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
  
(* flat domain *)
Inductive flat (A : Type) :=
  bot : flat A
| total : A -> flat A.
Arguments total {_}.

Definition pset (A : Type) := A -> Prop.



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

Definition projP1 {A : Type} {P : A -> Prop} : {a : A | P a} -> A.
Proof.
  intro X. 
  destruct X as [a _].
  exact a.
Defined.

Lemma projP1_injective :  forall {A : Type} (P : A -> Prop), injective (@projP1 A P).
Proof.
  intros A P x y e.
  destruct x.
  destruct y.
  simpl in e.
  induction e.
  induction (prop_irrl _ p p0).
  auto.
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
  clear H.
  destruct (cchoice _ _ H0).
  pose (fun a : {aa : pdom A | pdom_char X (total aa)} => {x : flat A | pdom_char (projP1 a) x}) as T.
  pose (fun n => @existT _ T (exist _ (x n) (proj2 (H n))) (@exist (flat A) (fun y => pdom_char (x n) y) (f n) (proj1 (H n)))) as s.
  pose proof (Pigeon _ s).
  assert (injective s).
  {  
    unfold s.
    clear H1 s.
    intros n m e.
    injection e.
    intros.
    exact (a n m H1).
  }
  apply H1 in H2.
  clear H1.
  destruct H2.
  {
    (* when index set is infinite *)
    destruct H1.
    assert (infinite (pdom_char X)).
    exists (fun n => total (projP1 (x0 n))).
    split.
    intros i j e.
    injection e.
    intro.
    apply projP1_injective in H2.
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
    assert (infinite (pdom_char x0)).
    destruct H1.
    exists (fun n => projP1 (x1 n)).
    split.
    intros n m e.
    apply projP1_injective in e.
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

Lemma bool_is_not_infinite : forall f : nat -> bool, injective f -> False.
Proof.
  intros.
  contradict H.
  intro.  

  case_eq (f 0); intro.
  case_eq (f 1); intro.
  assert (0 = 1).
  apply H.
  induction H0.
  auto.
  contradict H2; auto.
  case_eq (f 2); intro.
  assert (0 = 2).
  apply H.
  induction H0.
  auto.
  contradict H3; auto.
  assert (1 = 2).
  apply H.
  induction H2.
  auto.
  contradict H3; auto.
  case_eq (f 1); intro.
  case_eq (f 2); intro.
  assert (1 = 2).
  apply H.
  induction H2.
  auto.
  contradict H3; auto.
  assert (0 = 2).
  apply H.
  induction H0.
  auto.
  contradict H3; auto.
  assert (0 = 1).
  apply H.
  induction H1.
  auto.
  contradict H2; auto.
Defined.


Definition strict_union {X : Type} : pdom X -> pdom X -> pdom X.
Proof.
  intros S T.
  pose (pdom_bind (fun b : bool => if b then S else T)).
  assert (pdom bool).
  {
    (* construct {true, false} as pdom *)
    exists (fun b => b = total true \/ b = total false).
    intro.
    contradict H.
    intro.
    destruct H.
    destruct H.
    destruct (H0 0).
    destruct (H0 1).
    assert (0 = 1).
    apply H.
    induction H1.
    auto.
    contradict H3; auto.
    destruct (H0 2).
    assert (0 = 2).
    apply H.
    induction H1.
    auto.
    contradict H4; auto.
    assert (1 = 2).
    apply H.
    induction H2.
    auto.
    contradict H4; auto.
    destruct (H0 1).
    destruct (H0 2).
    assert (1 = 2).
    apply H.
    induction H2.
    auto.
    contradict H4; auto.
    assert (0 = 2).
    apply H.
    induction H1.
    auto.
    contradict H4; auto.
    assert (0 = 1).
    apply H.
    induction H1.
    auto.
    contradict H3; auto.
  }
  exact (p X0).
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

Definition pdom_case2' (X : Type)
  (b1 b2 : pdom bool)
  (c1 c2 : pdom X)
  (x : nat -> flat X)
  (H : injective x)
  (f : nat -> bool)
  (u : forall n : nat, if f n then pdom_char b1 (total true) /\ pdom_char c1 (x n) else pdom_char b2 (total true) /\ pdom_char c2 (x n))
  : nat ->
         {b : bool &
         if b then {j : flat X | pdom_char b1 (total true) /\ pdom_char c1 j} else {j : flat X | pdom_char b2 (total true) /\ pdom_char c2 j}}.
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
Definition lp : forall S T (f : S -> T) (a b : S), a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  exact (eq_refl _).
Defined.


Definition pdom_case2 {X : Type} (b1 b2 : pdom bool) (c1 c2 : pdom X) : pdom X.
Proof.
  exists
    (
      fun x =>
        (* empty condition *)
        (pdom_nempty b1 /\ pdom_nempty b2)
        /\
          (pdom_char b1 (total true) -> pdom_nempty c1)
        /\
          (pdom_char b2 (total true) -> pdom_nempty c2)
        /\
          (* values *)
          (
            (pdom_char b1 (total true) /\ pdom_char c1 x)
            \/
              (pdom_char b2 (total true) /\ pdom_char c2 x)
            \/
              (pdom_char b1 (bot bool) /\ pdom_char b2 (bot bool) /\ x = bot X)
          )
    ).

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
  assert (forall n : nat,
              (pdom_char b1 (bot bool) /\ pdom_char b2 (bot bool) /\ x n = bot X) \/
                (pdom_char b1 (total true) /\ pdom_char c1 (x n) \/
                   pdom_char b2 (total true) /\ pdom_char c2 (x n))).
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
  
  assert (forall a : nat,
           exists b : bool, if b then  pdom_char b1 (total true) /\ pdom_char c1 (x a) else  pdom_char b2 (total true) /\ pdom_char c2 (x a)).
  intro a.
  destruct (H0 a).
  exists true; auto.
  exists false; auto.
  clear H0.
  apply cchoice in H1.
  destruct H1 as [f u].
  
  pose (fun b : bool => if b then {j | pdom_char b1 (total true) /\ pdom_char c1 j} else {j | pdom_char b2 (total true) /\ pdom_char c2 j}) as T.
  assert (exists f : nat -> {b & T b}, injective f).
  {
    (* detour *)
    unfold T.
    clear T.
    exists (pdom_case2' X b1 b2 c1 c2 x H f u).
    intros i j e.
    unfold pdom_case2' in e.
    Check projT1.
    Check (@projT1 bool (fun b : bool => if b then {j : flat X | pdom_char b1 (total true) /\ pdom_char c1 j} else {j : flat X | pdom_char b2 (total true) /\ pdom_char c2 j}) ).
    pose proof (lp _ _ (@projT1 bool (fun b : bool => if b then {j : flat X | pdom_char b1 (total true) /\ pdom_char c1 j} else {j : flat X | pdom_char b2 (total true) /\ pdom_char c2 j})) _ _ e).
    simpl in H0.
    apply H; auto.
    admit.
  }

  destruct H0.
  destruct (Pigeon _ x0 H0).
  destruct H1.
  
  contradict (bool_is_not_infinite x1 H1).
  destruct H1.
  destruct x1.
  {
    (* when left gaurd *)
    left.
    unfold T in H1.
    destruct c1.
    simpl in H1.
    assert (infinite x1).
    destruct H1.
    unfold infinite.
    exists (fun n => projP1 (x2 n)).
    split.
    intros i j e.
    apply projP1_injective in e.
    apply H1 in e.
    auto.
    intro n.
    destruct (x2 n).
    simpl.
    destruct a; auto.
    simpl.
    split; pose proof (p H2); auto.
    destruct H1 .
    destruct (x2 0).
    destruct a; auto.
  }
  {
    (* when right gaurd *)
    right; left.    
    unfold T in H1.
    destruct c2.
    simpl in H1.
    assert (infinite x1).
    destruct H1.
    unfold infinite.
    exists (fun n => projP1 (x2 n)).
    split.
    intros i j e.
    apply projP1_injective in e.
    apply H1 in e.
    auto.
    intro n.
    destruct (x2 n).
    simpl.
    destruct a; auto.
    simpl.
    split; pose proof (p H2); auto.
    destruct H1 .
    destruct (x2 0).
    destruct a; auto.
  }
Admitted.

Definition pdom_W {X : Type} (b : X -> pdom bool) (c : X -> pdom X) : (X -> pdom X) -> X -> pdom X.
Proof.
Admitted.


Definition pdom_while {X : Type} : (X -> pdom bool) -> (X -> pdom X) -> X -> pdom X.
Proof.
  intros B C.
Admitted.

