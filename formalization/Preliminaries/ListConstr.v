Require Import Coq.Program.Equality.
Require Import List.

(* List forall in type level; cf. the Forall in List library is for Prop-level type families *)
Inductive ForallT {A} (P : A -> Type): list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons : forall x l, P x -> ForallT P l -> ForallT P (x::l).

(* CaseList has list of computations l and we want to annotate each of them.
   For that, we use the previously defined list forall ForallT.
   For example, a list of welltypedness wty_l and  postcondition for the readonly guards θ are of types
   wty_l : ForallT (fun ec => Δ ++ Γ |- fst ec : BOOL * Γ ;;; Δ snd ec : τ) l and 
   θ : ForallT (fun _ => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l.
   Then, we want to make a list of specifications where the two lists dependent on l combined.
   The following definitions are for this purpose. *)
Fixpoint ForallT_disj {A} (P : A -> Type) (Q : forall a, P a -> Prop) l (t : ForallT P l) : Prop.
Proof.
  dependent destruction t.
  exact False.
  exact (Q x p \/ ForallT_disj A P Q l t).
Defined.

Inductive ForallT1 {A} (P : A -> Type) (R : forall a, P a -> Type) : forall l, ForallT P l -> Type :=
  ForallT1_nil : ForallT1 P R nil (ForallT_nil P)
| ForallT1_cons : forall l a t1 p,  ForallT1 P R l t1 -> R a p -> ForallT1 P R (a :: l) (ForallT_cons P a l p t1).

Inductive ForallT2 {A} (P Q: A -> Type) (R : forall a, P a -> Q a -> Type) : forall l, ForallT P l -> ForallT Q l -> Type :=
  ForallT2_nil : ForallT2 P Q R nil (ForallT_nil P) (ForallT_nil Q)
| ForallT2_cons :forall l a t1 t2 p q,  ForallT2 P Q R l t1 t2 -> R a p q -> ForallT2 P Q R (a :: l) (ForallT_cons P a l p t1) (ForallT_cons Q a l q t2).

Inductive ForallT3 {A} (P Q R: A -> Type) (J : forall a, P a -> Q a -> R a -> Type) : forall l, ForallT P l -> ForallT Q l -> ForallT R l -> Type :=
  ForallT3_nil : ForallT3 P Q R J nil (ForallT_nil P) (ForallT_nil Q) (ForallT_nil R)
| ForallT3_cons :forall l a t1 t2 t3 p q r,  ForallT3 P Q R J l t1 t2 t3 -> J a p q r -> ForallT3 P Q R J (a :: l) (ForallT_cons P a l p t1) (ForallT_cons Q a l q t2) (ForallT_cons R a l r t3).  

