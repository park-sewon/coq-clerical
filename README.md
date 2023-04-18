# Clerical Coq Formalization
This repository provides a full formalization of the imperative programming lagnauge Clerical. The Coq project is structured as follows:

## Syntax and Typing
The formal syntax of Clerical can be found in [Clerical.v](./Clerical.v). There, the type `comp` is defined which is for Clerical expressions. For variables, De De Bruijn index is used. 

In [Typing.v](./Typing.v), the typing rules of Clerical are defined as mutually inductive types: `has_ro_type` for read-only expressions and `has_rw_type` for read-write expressions. The file introduces notations 
```coq
Notation "Gamma |- e : tau" := (has_ro_type Gamma e tau).
Notation "Gamma ;;; Delta |- e : tau" := (has_rw_type Gamma Delta e tau).
```
Here, `Gamma` and `Delta` are `list datatypes` standing for contexts.

In [TypingProperties.v](./TypingProperties.v), various properties of the typing rules are proven (/ assumed) including that the typing rules are not ambiguous.

## Powerdomain
One main part of the formalization is formalzing the powerdomain of Clerical which later used in the denotational semantics. The files with prefix `Powerdomain` do this.

- The file [Powerdomain.v](./Powerdomain.v) is the main file that exports everything.
- The file [PowerdomainBase.v](./PowerdomainBase.v) defines the setting. There, we assume Prop-level LEM, Prop-level countable choice, functional extensionality and Prop-positional extensionality. I.e., we assume `Prop` being a universe of classical propositions.
```coq
  Axiom lem : forall P : Prop, P \/ ~P.
  Axiom cchoice : forall (A : Type) (P : nat -> A -> Prop), (forall n : nat, exists a : A, P n a) -> exists f : nat -> A, forall n, P n (f n).
  Axiom prop_ext : forall (P Q : Prop), (P -> Q) -> (Q -> P) -> P = Q.
  Axiom dfun_ext : forall A (P : A-> Type) (f g : forall a, P a), (forall a, f a = g a) -> f = g.
```
* The file [PowerdomainInfinite.v](./PowerdomainInfinite.v) defines a type `X` being infinite by the classical existence of a injective mapping from `nat`. And, we defien various facts about infinte and n(ot)infinite types.

* The file [PowerdomainMonad.v](./PowerdomainMonad.v) is where the powerdomain is defined. For a type `X`, we first define `flat X` for the flat domain inductively by 
```coq
total {X} : X -> flat X 
bot {X} : flat X
```
For the bottom element, we introduce a notation `⊥`.

For the type `X`, a powerdomain `S : pdom X` is a dependent pair of a classical predicate `P : X -> Prop` and a proof of `infinite {x :  X | P x} -> P (bot X)` that when `P` accepts infinitely many `x : X`, it contians `bot`.
In this file, the monadic structure of `pdom : Type -> Type` is specified:
```coq
pdom_unit {X : Type} : X -> pdom X
pdom_mult {X : Type} : pdom (pdom X) -> pdom X
pdom_lift {X Y : Type} : (X -> Y) -> pdom X -> pdom Y
pdom_bind {X Y : Type} : (X -> pdom Y) -> pdom X -> pdom Y
```

* The file [PowerdomainProperties.v](./PowerdomainProperties.v) is where we prove various properties of the `pdom`'s moandic actions. 
For example, there, we prove that `(pdom_bind f S) : pdom Y` where `f : X -> pdom Y` and `S : pdom X` is empty iff `S` is empty or there exists `total x` in `S` such that `f x` is empty. 

* The file [PowerdomainCompleteness.v](./PowerdomainCompleteness.v) is where we prove that `pdom X` and `X -> pdom Y` are ω-complete. 
Here, we define the orders:
```coq
pdom_le {X : Type} : pdom X -> pdom X -> Prop
Notation "S ⊑ T" := (pdom_le S T)
pdom_fun_le {X Y : Type} : (X -> pdom Y) -> (X -> pdom Y) -> Prop
Notation "S ≤ T" := (pdom_fun_le S T)
```
The partial order ≤ on the function space is defined by the point-wise ordering of ⊑.

Then we define what it means sequences being chains
```coq
pdom_is_chain {X : Type} (s : nat -> pdom X) : Prop
pdom_fun_is_chain {X Y : Type} (s : nat -> X ->pdom Y) : Prop
```
define chians' supremums
```coq 
pdom_chain_sup {X : Type} (s : nat -> pdom X) : is_chain s ->  pdom X
pdom_fun_chain_sup {X Y : Type} (s : nat -> X -> pdom Y) : is_fun_chain s ->  X -> pdom Y
```
and prove that they are indeed supremums:
```coq
pdom_omega_complete {X : Type} (f : nat -> pdom X) (H : pdom_is_chain f) :
    pdom_indexed_subset_is_sup f (pdom_chain_sup f H).
pdom_fun_omega_complete {X Y : Type} (f : nat -> (X -> pdom Y)) (H : pdom_fun_is_chain f) :
    pdom_fun_indexed_subset_is_sup f (pdom_fun_chain_sup f H).
```
Here, `pdom_indexed_subset_is_sup {X I : Type} (f : I -> pdom X) (x : pdom X) : Prop` is a proposition saying that `x : pdom X` is a supremum of indexed powerdomains `f`.
Similarly. `pdom_fun_indexed_subset_is_sup {X Y I : Type} (f : I -> X -> pdom Y) (x : X -> pdom Y) : Prop` is a proposition saying that `x : X -> pdom Y` is a supremum of indexed functions to powerdomains `f`.

* The file [PowerdomainOrderProperties.v](./PowerdomainOrderProperties.v) is where we prove some useful facts about the orders of powerdomains.

* In the file [PowerdomainFixedpoints.v](./PowerdomainFixedpoints.v), we monotonicity and continuity:
```coq
pdom_is_monotone {X : Type} (f : pdom X -> pdom X) : Prop 
pdom_is_continuous {X : Type} (f : pdom X -> pdom X) : pdom_is_monotone f -> Prop 
pdom_fun_is_monotone {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) : Prop 
pdom_fun_is_continuous {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) : pdom_fun_is_monotone -> Prop 
```

Then, we define least fixed points
```coq
pdom_lfp {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) : pdom X.
pdom_fun_lfp {X Y : Type} (f : (X -> pdom Y) -> X -> pdom Y) (m : pdom_fun_is_monotone f) : X -> pdom Y.
```
as the supremums of bottom chains and prove their correctness:
```coq
pdom_lfp_prop {X : Type} (f : pdom X -> pdom X) (m : pdom_is_monotone f) :
    pdom_is_continuous f m ->
    f (pdom_lfp f m) = (pdom_lfp f m) /\
      forall x, f x = x -> (pdom_lfp f m) ⊑ x.

pdom_fun_lfp_prop {X Y: Type} (f : (X -> pdom Y) -> (X -> pdom Y)) (m : pdom_fun_is_monotone f) :
    pdom_fun_is_continuous f m ->
    f (pdom_fun_lfp f m) = (pdom_fun_lfp f m) /\
      forall x, f x = x -> (pdom_fun_lfp f m) ≤ x.
```


* In the file [PowerdomainSemantics.v](./PowerdomainSemantics.v), we define the sematnic functions. First, we define `pdom_case2 {X : Type} : pdom bool -> pdom bool -> pdom X -> pdom X -> pdom X` for the semantic function of guarded (binary) nondeterminism.

Then, we prove the ω-continuity of if-then-else operations and `pdom_bind` operator on its first function argument. To be precise, for any chain `s : nat -> X -> pdom Y`,
```coq
forall S : pdom X, pdom_bind (pdom_fun_chain_sup s) S = pdom_chain_sup (fun n => (pdom_bind (s n) S) 
```
Then, we define the semantic function for loops `pdom_while {X : Type} (b : X -> pdom bool) (f : X -> pdom X) : X -> pdom X` 
as the least fixed point of the operator:
```coq
pdom_W {X : Type} (b : X -> pdom bool) (f : X -> pdom X) : (X -> pdom X) -> (X -> pdom X) :=
    fun (f : X -> pdom X) (x : X) =>
    (pdom_bind (fun (b' : bool) => if b' then (pdom_bind f) (c x) else pdom_unit x) (b x)). 
```
The continuity of `pdom_W` is derived from the continutiy of if-then-else and `pdom_bind`.


## Denotational Semantics
The denotational semantics is defined in the file [Semantics.v](./Semantics.v):
```coq
Fixpoint sem_ro_comp (Γ : ro_ctx) (e : comp) (τ : datatype) (D : Γ |- e : τ) {struct D} :
  sem_ro_ctx Γ -> pdom (sem_datatype τ)
with sem_rw_comp (Γ Δ : ro_ctx) (c : comp) (τ : datatype) (D : Γ ;;; Δ ||- c : τ) {struct D} :
  sem_ro_ctx Γ -> sem_ro_ctx Δ -> pdom (sem_ro_ctx Δ * sem_datatype τ).
```
There, we define the denotations of datatypes `sem_datatype`.

## Specificaion Logic
