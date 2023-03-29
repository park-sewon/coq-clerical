(* classical treatment of our powerdomain ... maybe this makes some people upset :( *)

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

(* powerdomain is a monad *)
Definition unit (A : Type) : A -> pdom A.
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

Definition lift {A B : Type}
