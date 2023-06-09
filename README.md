# Clerical Coq Formalization
This repository provides a full formalization of the imperative programming language Clerical in Coq. 
It includes syntax, type system, denotational semantics, specifications, reasoning rules, soundness proofs, and some examples.

## Installation
It is checked to compile by coq_makefile under the Coq Proof Assistant version 8.16.1 (compiled with OCaml 4.14.1).
To compile the formalization part of this project, do `make` at `clerical` directory. 
To compile the examples part of this project, do `make` at `clerical/examples` directory.

## Overview of the project
### Examples

The `examples` directory contains example programs and their proofs.
For example, in [Examples.ProgAbs](./examples/ProgAbs.v), a clerical expression is parametrically defined 
```coq
Definition clerical_abs k :=
  Lim
    (CASE
       VAR (S k) ;<; EXP ( :-: (VAR 0) :-: (INT 1)) ==> ;-; VAR (S k)
     | ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k) ==> VAR (S k)
     END).
```
Here, `VAR k` denotes a variable with its De Bruijn index `k`.
Mathematical symbols surrounded by `: :` denote integer operations 
and those surrounded by `; ;` denote real operations.
The definition `clerical_abs k` for each natural number `k` is a clerical expression 
that computes the absolute value of the variable `k`.

Using our prove rules, we prove the correctness of the expression:
```coq
Lemma clerical_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    Γ |--
      [{fun _ => True}]
      clerical_abs k 
      [{y : REAL | fun x => y = Rabs (ro_access Γ k REAL w x) }].	  
```
Here, `ro_access Γ k REAL w x` means the variable `k` in a state `x`.

In [Examples.ProgLogic](./examples/ProgLogic.v), we define and prove Boolean negation,
in [Examples.ProgBounded](./examples/ProgBounded.v), we define and prove the soft boundedness test,
in [Examples.ProgSine](./examples/ProgSine.v), we define and prove the sine function, and 
in [Examples.ProgPi](./examples/ProgPi.v), we define and prove a closed expression computing `π`:
```coq
Lemma clerical_pi_correct :
  nil |--
    [{fun _ => True}]
    clerical_pi
    [{y : REAL | fun _ => y = PI}].
```
Here, `PI` is the constant `π` that we import from Coq's standard library.
However, the theory isn't enough to prove our program. 
For example, the proof of our program required the irrationality of `π`.
The _mathematical knowledge_ required in program proofs are partially proved 
or admitted in [Examples.Mathematics](./examples/Mathematics.v).


### Formalization
The formalization is in the `formalization` directory that corresponds to the `Clerical` logical path. 
The `formalization` directory consists of the subdirectories: `Preliminaries`, `Powerdomain`, and `Utils`. 
The base axioms of our type theory including what makes `Prop` classical, some preliminary mathematical facts and some basic tactics are declared or defined in the `Preliminaries`.
Based on that, in the `Powerdomain`, we define a powerdomain as a monad `pdom : Type -> Type` and prove various properties including its ω-completeness. There, we also define various functions that are used later in the semantic construction.
In `Utils` we define various tactics that are to be used by the users later. 

Files in the `formalization` directory formalize Clerical:

* In [Clerical.Syntax](./formalization/Syntax.v), we define the Syntax of Clerical expressions and their typing rules are defined in [Clerical.Typing.v](./formalization/Typing.v). Both are defined inductively.

There, the notations
```coq
Γ |- e : τ 
Γ ;;; Δ ||- e : τ
```
are defined. `Γ |- e : τ` means that a Clerical expression `e` has type `τ` under a read-only context `Γ` and `Γ ;;; Δ ||- e : τ` means that a Clerical expression `e` has type `τ` under a read-only context `Γ` and a read-write context `Δ`.

In [Clerical.TypingProperties](./formalization/TypingProperties.v), various properties of our type system are proven including that our typing rules are unambiguous.

* In [Clerical.Semantics](./formalization/Semantics.v), we define the denotational semantics of Clerical expressions using the aforementioned powerdomain recursively on well-typedness.
```coq
sem_exp_ro Γ e τ (w : Γ |- e : τ) : sem_ctx Γ -> pdom (sem_datatype τ)
sem_exp_rw Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) :  sem_ctx Γ -> sem_ctx Δ -> pdom (sem_ctx Δ * sem_datatype τ)
``` 

In [Clerical.SemanticsProperties](./formalization/SemanticsProperties.v), various properties of our semantics are proven including that they are irrelevant to specific type derivations. For example when we have two type derivations `w1 : Γ |- e : τ` and `w2 : Γ |- e : τ`, we 
have that their semantics are equal: `sem_exp_ro Γ e τ w1 γ = sem_exp_ro Γ e τ w1 γ` for all `γ`.



* In [Clerical.Specification](./formalization/Specification.v), we define specifications. 
For a well-typed read-only expression `w : Γ |- e : τ`, a pre-condition `ϕ : sem_ctx Γ -> Prop`, and a post-condition 
`ψ : sem_datatype τ -> sem_ctx Γ -> Prop`, `w |= {{ϕ}} e {{ψ}}` denotes its partial correctness
and `w |= [{ϕ}] e [{ψ}]` denotes its total correctness.
Specifications of read-write expressions are defined similarly: 
for a well-typed read-write expression `w : Γ ;;; Δ ||- e : τ`, a pre-condition `ϕ : sem_ctx Δ * sem_ctx Γ -> Prop`, and a post-condition 
`ψ : sem_datatype τ -> sem_ctx Δ * sem_ctx Γ -> Prop`, `w ||= {{ϕ}} e {{ψ}}` denotes its partial correctness
and `w ||= [{ϕ}] e [{ψ}]` denotes its total correctness.

In [Clerical.ReasoningRules](./formalization/ReasoningRules.v), we define the verification calculus inductively: 
for a well-typed read-only expression `w : Γ |- e : τ`, a pre-condition `ϕ`, and a post-condition 
`ψ`, `w |- {{ϕ}} e {{ψ}}` denotes that calculus proves the partial correctness and 
`w |- [{ϕ}] e [{ψ}]` denotes that calculus proves the total correctness of the read-only expression.
Similarly, for a well-typed read-write expression `w : Γ ;;; Δ ||- e : τ`, 
`w ||- {{ϕ}} e {{ψ}}` denotes that calculus proves the partial correctness and 
`w ||- [{ϕ}] e [{ψ}]` denotes that calculus proves the total correctness of the read-write expression.

The soundness of the proof rules is proved in [Clerical.ReasoningSoundness](./formalization/ReasoningSoundness.v).
```coq
Lemma proves_ro_prt_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- {{ϕ}} e {{ψ}} -> w |= {{ϕ}} e {{ψ}}
with proves_ro_tot_sound : forall Γ e τ (w : Γ |- e : τ) ϕ ψ, w |- [{ϕ}] e [{ψ}] -> w |= [{ϕ}] e [{ψ}]
with proves_rw_prt_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- {{ϕ}} e {{ψ}} -> w ||= {{ϕ}} e {{ψ}}
with proves_rw_tot_sound : forall Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ, w ||- [{ϕ}] e [{ψ}] -> w ||= [{ϕ}] e [{ψ}].
```

In [Clerical.ReasoningAdmissible](./formalization/ReasoningAdmissible.v) proves some admissible rules.

* Based on the specifications and proof rules on well-typedness, in [Clerical.ReasoningPrettyprinting](./formalization/ReasoningPrettyprinting.v),
well-typedness irrelevant specifications and rules are introduced:
```coq
Γ |-- {{ϕ}} e {{y : τ | ψ}}
```
says `e` has type `τ` under `Γ` and the well-typed read-only expression is partially correct w.r.t. the precondition `ϕ` and the postcondition `ψ`.
Formally, it is defined as a sigma-type: `{w : Γ |- e : τ & w |- {{ϕ}} e {{ψ}} }`.
Other judgements are defined similarly:
```coq
Γ |-- [{ϕ}] e [{y : τ | ψ}]
Γ ;;; Δ |-- {{ϕ}} e {{y : τ | ψ}}
Γ ;;; Δ |-- [{ϕ}] e [{y : τ | ψ}]
```
In the file, the original proof rules and the admissible rules are translated so that the users can use only these better-looking judgements.

* In [Clerical.ReasoningUtils](./formalization/ReasoningUtils.v), various utility functions in applying proof rules are defined.

## Base setting of the underlying type theory

We use Coq considering `Prop` to be a classical set of classical propositions.
We assume some axioms that are considered valid under this interpretation.
The axioms are declared in 
[Clerical.Preliminaries.BaseAxioms](./formalization/Preliminaries/BaseAxioms.v).
They are (1) Prop-level law of excluded middle, (2) Prop-level (dependently)countable choice, 
(3) Prop-level dependent choice and (4) Prop-propositional extensionality.
We also frequently use `dependent induction` and `dependent destruction` tactics which assume UIP which is derivable by the 
additionally assumed axioms. Furthermore, we assume (dependent)function extensionality.

One possible danger to this interpretation is our use of Coq's standard library of real numbers.
Using their axioms, we use `Rltb'' : R -> R -> bool` as the exact comparison function. 
The presence of this function is not feasible when we suppose `bool : Set` is constructive.

In the future, the unrealizable function `Rltb'' : R -> R -> bool` can be replaced.
(It should be feasible to replace.)

## Powerdomain
The `Powerdomain` project consists of several different source files. 
The file [Clerical.Powerdomain.Powerdomain](./formalization/Powerdomain/Powerdomain.v) is the main file that exports everything.

The powerdomain we use is a variant of the Plotkin powerdomain.
That means we have to deal with something being _infinite_ very often.
In the file [Clerical.Powerdomain.PowerdomainInfinite](./formalization/Powerdomain/PowerdomainInfinite.v),
we define a Prop-level definition of a type being infinite and prove various properties.
We define a type `A` as being infinite by the classical existence of an injective mapping from `nat`. 
By classical reasonings, we prove useful choice lemmas. 
The most important lemma proved there that is later used often is
```coq
Lemma Pigeon : forall {A : Type} (P : A -> Type),
	infinite {a : A & P a} ->
		infinite A \/ exists a : A, infinite (P a).
```
a version of Pigeon hole principle, which says when a dependent pair type is infinite, 
(classically) either the index type is infinite or there is a fiber that is infinite.


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
the library provides lemmas which are used to reason their behaviours: 
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
and prove that for any countable chains, the subset generated by `pdom_chain_sup`
is indeed the least upper bound of the chain. We do similarly to the function types.
In [Clerical.Powerdomain.PowerdomainOrderProperties](./formalization/Powerdomain/PowerdomainOrderProperties.v)
we use various useful lemmas about supremum in the above fashion.
(E.g., `pdom_chain_bot_2` is a lemma stating a necessary condition for a 
supremum of a countable chain containing ⊥.)

Finally, in 
[Clerical.Powerdomain.PowerdomainFixedpoints](./formalization/Powerdomain/PowerdomainFixedpoints.v)
we prove the Least Fixed-point theorem for powerdomains and function types to a powerdomain.
Again, we define general operations on monotone endofunctions, which are to obtain 
the supremum of the bottom chains, and prove that when the endofunctions are continuous, 
the supremum is indeed a least fixed-point.

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
plays the key role in proving the continuity of `W` operator generating the loops' recurrence equation
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
we prepare various real numbers and integer operations using `pdom`. 
For example, there we define the limit operator using `pdom` and Coq's standard real number library.

## Finite Dependent Types for Case

The formal syntax of Clerical is defined in 
[Clerical.Syntax](./formalization/Syntax.v).
The expressions are defined as an inductive type `exp`.
The nondeterministic case expression is supposed to have a list of pairs of expressions:
```coq
| CaseList : list (exp * exp) -> exp
```
An expression of the form `CaseList (e1, c1) :: (e2, c2) :: ... :: (en, cn) :: nil` is 
supposed to mean `case e1 => c1 | ... | en => cn end`.

In [Clerical.Typing](./formalization/Typing.v) when we define the well-typedness of a case expression 
`case e1 => c1 | ... | en => cn end` we want to make sure that each `ei` and `ci` are well-typed.
To state this for an arbitrary `l` in `CaseList l`, we use the following inductive type
```coq
Inductive ForallT {A : Type} (P : A -> Type): list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons : forall x l, P x -> ForallT P l -> ForallT P (x::l).
```
and write `ForallT (fun ec : exp * exp => ((Δ ++ Γ) |- fst ec : BOOL) * (Γ ;;; Δ ||- snd ec : τ)) l` in 
the premise of the typing rule of `CaseList l`.

In [Clerical.ReasoningRules](./formalization/ReasoningRules.v), to write down the proof rule of case expression, 
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

The list-dependent types are defined in [Clerical.Preliminaries.ListConstr](./formalization/Preliminaries/ListCosntr.v).

The library provides binary case expressions separately. It will be removed and replaced by the general case expression soon.

## Concatenated States

We often concatenate states.
Given `γ : sem_ctx Γ` and `δ : sem_ctx Δ`,
to feed the states into a read-only expression's semantics, we need to merge them 
to be `sem_ctx (Δ ++ Γ)`. The concatenation is recursively defined 
and we denote it by `(δ; γ) : sem_ctx (Γ ++ Δ)`.
Also, we have to often split the merged states. 
They are also defined recursively and denoted by `fst_add : sem_ctx (Γ ++ Δ) -> sem_ctx Γ` and  
`snd_add : sem_ctx (Γ ++ Δ) -> sem_ctx Δ`.
Now, there are very tedious equalities such as
`(fst_app x ; snd_app x) = x`, or `fst_app (x ; y) = x`.
They are defined in the `TediousList` section of [Clerical.Semantics](./formalization/Semantics.v).
