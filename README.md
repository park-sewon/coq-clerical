# Clerical Coq Formalization
This repository provides a full formalization of the imperative programming lagnauge Clerical. 
It includes the syntax, type system, denotational semantics, specifications, reasoning rules, and their soundness proofs. 
This project is structured as follows.

* Before defining the language, in [Clerical.Powerdomain](./formalization/Powerdomain/Powerdomain.v), we define a powerdomain as a monad `pdom : Type -> Type` 
and prove various properties including ω-completeness.
There, we also define various functions that are used later in the semantic construction.

* In [Clerical.Syntax.v](./formalization/Syntax.v), we define the Syntax of Clerical expressions and their typing rules are defined in [Clerical.Typing.v](./formalization/Typing.v).

* In [Clerical.Semantics.v](./formalization/Semantics.v), we define the denotational semantics of Clerical expressions using the aforementioned powerdomain. 

* In [Clerical.ReasoningRules.v](./formalization/ReasoningRules.v), we define the proof rules of correctness Hoare-style triples. The defintion of triples and their meanings can be found in [Clerical.Specification.v](./formalization/Specification.v).
The soundness of the proof rules w.r.t. the denotational semantics is proved in [Clerical.ReasoningSoundness.v](./formalization/ReasoningSoundness.v).

Now let us explain each parts in more detail.

## Base setting of the underlying type theory

We use Coq with considering Prop to be a classical set of classical propositions.
We assume some axioms that are considered valid under this interpretation in 
[Clerical.Powerdomain.PowerdomainBase](./formalization/Powerdomain/PowerdomainBase.v).
They are (1) Prop-level law of excluded middle, (2) Prop-level (dependently)countable choice, 
(3) Prop-level dependent choice and (4) Prop-propositional extensionality.
We also frequently use `dependent induction` and `dependent destruction` tactics which assumes UIP which is derivable by the 
additionally assumed axioms. Furthermore, we assume (dependent)function extensionality.

## Powerdomain
The Powerdomain sublibrary consists of several different source files. 
The file [Clerical.Powerdomain.Powerdomain](./formalization/Powerdomain/Powerdomain.v) is the main file that exports everything.

The powerdomain we use is a variant of the Plotkin powerdomain.
That means, we have to deal with something being _infinite_ very often.
In file [Clerical.Powerdomain.PowerdomainInfinite](./formalization/Powerdomain/PowerdomainInfinite.v),
we define a Prop-level definition of a type being infinite and prove various properties.
We define a type `A` being infinte by the classical existence of a injective mapping from `nat`. 
By classical reasonings, we prove useful choice lemmas. 
The most important lemma proved there that is later used often is
```coq
Lemma Pigeon : forall {A : Type} (P : A -> Type),
	infinite {a : A & P a} ->
		infinite A \/ exists a : A, infinite (P a).
```
a version of Pigeon hole principle, which says when a dependent pair type is infinite, 
(clasically) either the index type is infinite or there is a fiber that is infinite.


Based on the definition of infinite types, we define our powerdomain 
as a type-level mapping in [Clerical.Powerdomain.PowerdomainMonad](./formalization/Powerdomain/PowerdomainMonad.v)
and prove its monadic structure. They are
```coq
pdom : Type -> Type
pdom_lift {X Y : Type} : (X -> Y) -> (pdom X -> pdom Y)
pdom_bind {X Y : Type} : (X -> pdom Y) -> (pdom X -> pdom Y)
pdom_unit {X : Type} : X -> pdom X
pdom_mult {X : Type} : pdom (pdom X) -> pdom X
```
There, we also define the flat domain `flat : Type -> Type` inductively defined by 
the two constructors `⊥ {X : Type} : flat X` and `total {X : Type} : X -> flat X`.
The powerdomain `pdom X` is defined as a sigma type `{S : flat X -> Prop | infinite {x |S x } -> S ⊥}`.
In [Clerical.Powerdomain.PowerdomainProperties](./formalization/Powerdomain/PowerdomainProperties.v)
we prove various useful properties about the monadic actions; e.g., `pdom_bind_empty_1` is a 
lemma for a sufficient condition the result of a binding operation yielding the empty set.
In contrast, `pdom_bind_empty_2` is a lemma for a necessary condition.
For a powerdomain operation `ops` and a property `P`, 
the library provdies lemmas which are used to reason their behaviours: 
* `pdom_ops_P_1`: a sufficient condition the result of `ops` satisfies `P`
* `pdom_ops_P_2`: a necessary condition the result of `ops` satisfies `P`
We consider the three properties: `P = empty` the result is empty, `P = bot` the result contains ⊥, and `P = total` the result 
contains `total a` for any `a`.

In [Clerical.Powerdomain.PowerdomainCompleteness](./formalization/Powerdomain/PowerdomainCompleteness.v),
we define partial orders on powerdomains
```coq
pdom_le {X : Type} : pdom X -> pdom X -> Prop
Infix "⊑" := (pdom_le) (at level 80).
```
and on the mappings to powerdomains
```coq
pdom_fun_le {X Y : Type} : (X -> pdom Y) -> (X -> pdom Y) -> Prop
Infix "≤" := (pdom_fun_le) (at level 80).
```
where the later is defined as the point-wise ordering of the first.
In the file, we prove that both `pdom X` and `X -> pdom Y` for any `X` and `Y` are
ω-complete. 
We first define `pdom_chain_sup` as a general operation on countable chains 
and prove that for any coutnable chains, the subset generated by `pdom_chain_sup`
is indeed the least upper bound of the chain. We do similarly to the function types.
In [Clerical.Powerdomain.PowerdomainOrderProperties](./formalization/Powerdomain/PowerdomainOrderProperties.v)
we use various useful lemmas about supremums in the above fashion.
(E.g., `pdom_chain_bot_2` is a lemma stating a necessary condition for a 
supremum of a countable chain containing ⊥.)

Finally, in 
[Clerical.Powerdomain.PowerdomainFixedpoints](./formalization/Powerdomain/PowerdomainFixedpoints.v)
we prove the Least Fixed-point theorem for powerdomains and function types to a powerdomain.
Again, we define general operations on monotone endofunctions, which are to obtain 
the supremums of the bottom chains, and prove that when the endofunctions are continuous, 
the supreumums are indeed the least fixed-points.

In [Clerical.Powerdomain.PowerdomainSemantics](./formalization/Powerdomain/PowerdomainSemantics.v)
we define powerdomain functions that are later used in the denotational semantics.
Here, we define `pdom_case_list {X : Type} : (list ((pdom bool) * (pdom X))) -> pdom X` for 
our nondeterministic construction.
Again, its properties are proven in the file. 
(E.g., `pdom_case_list_total_1` gives us a sufficient condition for `pdom_case_list (e1, c1) :: (e2, c2) :: ... ::nil` 
contains `total x`.)

Then, the continuity of `pdom_bind` is proven. 
More precisely, we prove that `pdom_bind` is continuous on its first 
function argument by the lemma `pdom_bind_fst_continuous`:
```coq
  Lemma pdom_bind_fst_continuous {X Y : Type} (S : pdom X) :
    forall (s : nat -> (X -> pdom Y)) (c : pdom_fun_is_chain s),
      pdom_bind (pdom_fun_chain_sup s c) S = pdom_chain_sup (fun n => pdom_bind (s n) S) (pdom_fun_chain_bind_chain S s c).
```
The lemma and another lemma stating that `if-then-else {X : Type} : bool -> pdom X -> pdom X -> pdom X` operation 
is continuous on its first branch argument 
```coq
  Lemma pdom_ite_fst_continuous {X : Type} (S : pdom X) (s : nat -> pdom X) (c : pdom_is_chain s) :
    (fun b : bool => if b then pdom_chain_sup s c else S) = pdom_fun_chain_sup _ (pdom_chain_ite_fun_chain S s c).
```
plays the key role in proving the continutiy of `W` operator generating the loops' recurrence equation
```coq
Definition pdom_W {X : Type} (b : X -> pdom bool) (c : X -> pdom X) : (X -> pdom X) -> X -> pdom X.
Proof.
    intros f.
    intro x.
    exact (pdom_bind (fun (b : bool) => if b then (pdom_bind f) (c x) else pdom_unit x) (b x)). 
Defined.
```
Then, we define `pdom_while {X : Type} : (X -> pdom bool) -> (X -> pdom X) -> X -> pdom X.` 
as the least fixed-point of the `pdom_W` operator.

In [Clerical.Powerdomain.PowerdomainSemantics2](./formalization/Powerdomain/PowerdomainSemantics2.v)
we prepare various real number and integer operations using `pdom`. 
For example, there we define the limit operator using `pdom` and Coq's standard real number library.

## Syntax and Typing

The formal syntax of Clerical is defined in 
[Clerical.Syntax](./formalization/Syntax.v).
The expressions are defined as an inductive type `exp`.
The nondeterministic case expression is supposed to have a list of pairs of expressions:
```coq
| CaseList : list (exp * exp) -> exp
```

In [Clerical.Typing](./formalization/Typing.v), 
we define typing rules inductively. 
There, we define two type judgements: `has_type_ro` and `has_type_rw`. 
We use the notations `Γ |- c : τ` for the first and 
`Γ ;;; Δ |- c : τ` for the later. 

For a case expression `CaseList l` to be well-typed, we require `l` to have length greater than 0.
Since a well-typedness of an expression is `Type` not `Prop`, 
we introduce an inductive type
```coq
Inductive ForallT {A : Type} (P : A -> Type): list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons : forall x l, P x -> ForallT P l -> ForallT P (x::l).
```
where we use in the rule for ` Γ ;;; Δ ||- CaseList l : τ` when we require
`ForallT (fun ec : exp * exp => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ ;;; Δ ||- snd ec : τ)) l` in its premise.

In [Clerical.TypingProperties](./formalization/TypingProperties.v),
we prove various properties about our type system. 
The main theorem there is that our typing rules are unambiguous in the sense that 
when `Γ |- e : τ` and `Γ |- e : σ` we have `τ = σ`
and when `Γ ;;; Δ ||- e : τ` and `Γ ;;; Δ ||- e : σ` we have `τ = σ`.

such as that

We take a Prop-level definition of a type being infinite 

## Denotational Semantics

We define the denotational semantics of Clerical expressions in [Clerical.Semantics](./formalization/Semantics.v).
It is defined inductively on the well-typedness.
It uses the powerdomain `pdom` and the functions defined there.

In [Clerical.SemanticsProperties](./formalization/SemanticsProperties.v), we prove important properties about our semantics.
The main theorems there are that (1) the semantics is irrelevent to the well-typedness
and that (2) the semantics does not change when we add auxiliary variables at the end of the readonly contexts.

Formally, we prove the statments:
```coq
Lemma sem_ro_exp_unique Γ e τ (w1 w2 : Γ |- e : τ): sem_ro_exp Γ e τ w1 = sem_ro_exp Γ e τ w2.
Lemma sem_rw_exp_unique Γ Δ e τ (w1 w2 : Γ ;;; Δ ||- e : τ) : sem_rw_exp Γ Δ e τ w1 = sem_rw_exp Γ Δ e τ w2.
Lemma sem_ro_exp_auxiliary_ctx : forall Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) γ γ', sem_ro_exp Γ e τ w γ = sem_ro_exp (Γ ++ Γ') e τ w' (γ; γ').
Lemma sem_rw_exp_auxiliary_ctx : forall Γ Γ' Δ e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) γ γ' δ, sem_rw_exp Γ Δ e τ w γ δ = sem_rw_exp (Γ ++ Γ') Δ e τ w' (γ ; γ') δ.

```

## Specification logic

In [Clerical.Specification](./formalization/Specification.v), we define Hoare-stle correctness triples:

* When `w : Γ |- e : τ`, the triple `w |- {{ϕ}} e {{ψ}}` is a partial correctness triple, 
* When `w : Γ |- e : τ`, the triple `w |- [{ϕ}] e [{[ψ}]` is a total correctness triple, 
* When `w : Γ ;;; Δ ||- c : τ`, the triple `w ||- {{ϕ}} e {{ψ}}` is a partial correctness triple, and 
* When `w : Γ ;;; Δ ||- c : τ`, the triple `w ||- [{ϕ}] e [{ψ}]` is a total correctness triple.
Here, `ϕ` and `ψ` are predicates to `Prop` from the semantics of contexts.

In this file, we define their semantics (as intended) and define the notations:
* `w |- {{ϕ}} e {{ψ}}` denotes `w |= {{ϕ}} e {{ψ}}`, 
* `w |- [{ϕ}] e [{ψ}]` denotes `w |= [{ϕ}] e [{ψ}]`, 
* `w ||- {{ϕ}} e {{ψ}}` denotes `w ||= {{ϕ}} e {{ψ}}`, and 
* `w ||- [{ϕ}] e [{ψ}]` denotes `w |= [{ϕ}] e [{ψ}]`.

In [Clerical.ReasoningRules](./formalization/ReasoningRules.v), we define 
the proof rules.
To write down the prove rule of case expression, 
for a list `l : list (exp * exp)`, 
we require `l` dependent list of well-typednesses using the `ForallT`:
```coq
wty_l : ForallT (fun ec => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;;Δ ||- snd ec : τ)) l
```
also a `l` dependent list of postconditions 
```
θ : ForallT (fun ec => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l
```
and a list of premise specifications which is a list dependent on `wty_l` and `θ`
which are `l` dependent lists. To express this we define the inductive type:
```coq
Inductive ForallT2 {A} (P Q: A -> Type) (R : forall a, P a -> Q a -> Type) : forall l, ForallT P l -> ForallT Q l -> Type :=
  ForallT2_nil : ForallT2 P Q R nil (ForallT_nil P) (ForallT_nil Q)
| ForallT2_cons :forall l a t1 t2 p q,  ForallT2 P Q R l t1 t2 -> R a p q -> ForallT2 P Q R (a :: l) (ForallT_cons P a l p t1) (ForallT_cons Q a l q t2).
```
We write
```coq
ForallT2 _ _ 
    (fun ec wty_l θ  =>
    (fst (wty_l) |- {{rw_to_ro_pre ϕ}} fst ec {{θ}}) *
    (snd (wty_l) ||- {{ro_to_rw_pre (θ true)}} snd ec {{ψ}}))%type l wty_l θ ->
```
as the premise.

In [Clerical.ReasoningAdmissible](./formalization/ReasoningAdmissible.v), we prove admissible rules
and in [Clerical.ReasoningSoundness](./formalization/ReasoningSoundness.v), we prove the soundness of our proof rules:
```coq
Lemma proves_ro_prt_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- {{ϕ}} e {{ψ}} -> w |= {{ϕ}} e {{ψ}}
with proves_ro_tot_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- [{ϕ}] e [{ψ}] -> w |= [{ϕ}] e [{ψ}]
with proves_rw_prt_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- {{ϕ}} e {{ψ}} -> w ||= {{ϕ}} e {{ψ}}
with proves_rw_tot_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- [{ϕ}] e [{ψ}] -> w ||= [{ϕ}] e [{ψ}].
```


