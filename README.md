# Clerical Coq Formalization
This repository provides a full formalization of the imperative programming language [Clerical](https://github.com/andrejbauer/clerical) in Coq.
It includes syntax, type system, denotational semantics, specifications and their proof rules, soundness proofs of the rules, and some examples and their proofs.

## Installation
It is checked to compile by `coq_makefile` under the Coq Proof Assistant version 8.18 and 8.19. 
To compile the formalization part of this project, run `make` in the `clerical` directory. 
To compile the examples part of this project, run `make` in the `clerical/examples` directory.

## Examples

The `clerical/examples` directory contains example programs and their proofs.
For example, in [Examples.ProgAbs](./examples/ProgAbs.v), a clerical expression defined parametically on `k`
that computes the absolute value of the real number that the variable `k` stores:
```coq
Definition clerical_abs (k : nat) :=
  Lim
    (CASE
       VAR (S k) ;<; EXP ( :-: (VAR 0) :-: (INT 1)) ==> ;-; VAR (S k)
     | ;-; EXP ( :-: (Var 0) :-: (INT 1)) ;<; Var (S k) ==> VAR (S k)
     END).
```
Here, `VAR k` denotes a variable with its De Bruijn index `k`.
Mathematical symbols surrounded by `: :` denote integer operations 
and those surrounded by `; ;` denote real operations.
Though in this example only binary nondeterministim is used, 
our formalization provides arbitrarily many guarded expressions using the grammar 
`CASE e1 ==> c1 | .. | en ==> cn END`.

Using our prove rules, in the same file, we prove the correctness specification:
```coq
Lemma clerical_abs_correct :
  forall Γ k (w : Γ |- VAR k : REAL),
    [γ : Γ] |-  {{True}} clerical_abs k {{y : REAL | y = Rabs (var_access Γ k REAL w γ) }}ᵗ.	  
```
Here, `var_access Γ k REAL w γ` denotes accessing the variable `k` of a state `γ : sem_ctx Γ`.
The triple denotes the total correctness of `clerical_abs k` in the sense that for any state `γ` satisfying `True`,
the expression `clerical_abs k` always terminates yielding a value `y : REAL` such that 
`y = Rabs (var_access Γ k REAL w γ)`. 

There are other examples as well. In [Examples.ProgSine](./examples/ProgSine.v), 
we define and prove the sine function. 
In [Examples.ProgPi](./examples/ProgPi.v), we define and prove a closed expression computing `π`:
```coq
Lemma clerical_pi_correct :
  [_ : nil] |- {{True}} clerical_pi  {{y : REAL | y = PI}}.
```
Here, `PI` is the constant `π` that we import from Coq's standard library.
However, the theory isn't enough to prove our program. 
For example, the proof of our program requires the irrationality of `π`.
The mathematical knowledge required in our program proofs is partially proved 
or admitted in [Examples.Mathematics](./examples/Mathematics.v).


## Formalization
The formalization is in the `formalization` directory that corresponds to the `Clerical` logical path. 
The `formalization` directory consists of the subdirectories: `Preliminaries` and `Powerdomain`. 
The base axioms of our type theory including what makes `Prop` classical, some preliminary mathematical facts and some basic tactics are declared or defined in `Preliminaries`.
Based on that, in `Powerdomain`, we define a powerdomain as a monad `pdom : Type -> Type` and prove various properties including its ω-completeness. There, we also define various functions that are used later in the semantic construction.

Files in the `formalization` directory formalize Clerical:

### Syntax and Typing
In [Syntax](./formalization/Syntax.v), we define the Syntax of Clerical expressions and their typing rules are defined in [Typing](./formalization/Typing.v). Both are defined inductively.

There, the notations
```coq
Γ |- e : τ 
Γ ;;; Δ ||- e : τ
```
are defined. `Γ |- e : τ` means that a Clerical expression `e` has type `τ` under a read-only context `Γ` and `Γ ;;; Δ ||- e : τ` means that a Clerical expression `e` has type `τ` under a read-write context `Γ ;;; Δ` where `Γ` is for read-only variabes
and `Δ` is for read-write variables.

Since Coq's standard list notation adds elements from the left: `x :: l`.
Since we want to add elements from the right, we define and use the new notations:
```coq
Notation "a ::: b" := (cons b a) (at level 60, left associativity).
Notation "a +++ b" := (app b a) (right associativity, at level 60).
```
They are in [Preliminaries.ListConstr](./formalization/Preliminaries/ListConstr.v).
Thanks to the new notation, we have more intuitive typing rules. For example, we have
```coq
 (Γ +++ Δ) |- e : BOOL -> 
 Γ ;;; Δ ||- c1 : τ -> 
 Γ ;;; Δ ||- c2 : τ -> 
 (*——————————-——————————*) 
 Γ ;;; Δ ||- IF e THEN c1 ELSE c2 END : τ
```
instead of having `Δ ++ Γ`.

In [TypingProperties](./formalization/TypingProperties.v), various properties of our type system are proven including that our typing rules are unambiguous.

### Semantics
In [Semantics](./formalization/Semantics.v), we define the denotational semantics of Clerical datatypes, contexts, and expressions.
The datatypes denotes the standard types:
```coq
sem_datatype : datatype -> Type
```

The semantics of contexts is defined recursively as
```coq
sem_ctx Γ := match Γ with 
  | nil => unit
  | Γ' ::: τ => sem_ctx Γ' * sem_datatype τ
  end.
```

Using the powerdomain, recursively on well-typedness of expressions, we define the denotational semantics of well-typed expressions.
```coq
sem_exp_ro Γ e τ (w : Γ |- e : τ) : sem_ctx Γ -> pdom (sem_datatype τ)
sem_exp_rw Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) :  sem_ctx Γ -> sem_ctx Δ -> pdom (sem_ctx Δ * sem_datatype τ)
``` 

In [SemanticsProperties](./formalization/SemanticsProperties.v), various properties of our semantics are proven including that they are irrelevant to specific type derivations. For example when we have two type derivations `w1 : Γ |- e : τ` and `w2 : Γ |- e : τ`, we 
have that their semantics are equal: `sem_exp_ro Γ e τ w1 γ = sem_exp_ro Γ e τ w1 γ` for all `γ`.


### Specifications
In [Specification](./formalization/Specification.v), we define specifications. 
For an expression `e`, a pre-condition `ϕ : sem_ctx Γ -> Prop`, and a post-condition 
`ψ : sem_ctx Γ *  sem_datatype τ -> Prop`, 
- partial correctness
  ```coq
  [| γ : Γ |]  |= {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ 
  ```
  denotes that there exists a witness of well-typedness `w : Γ |- e : τ` where for any `γ : sem_ctx Γ` such that `ϕ γ` holds,
`sem_exp_ro Γ e τ w γ` is non-empty and for any `total v ∈ sem_exp_ro Γ e τ w γ`, the post-condition `ψ (γ, v)` holds. 

- total correctness
  ```coq
  [| γ : Γ |] |= {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ
  ```
  denotes the same and that `⊥` is not in the semantics. 

Specifications of read-write expressions are defined similarly.  
For an expression `e`, a pre-condition 
`ϕ : sem_ctx Γ * sem_ctx Δ  -> Prop`, and a post-condition 
`ψ : sem_ctx Γ * (sem_ctx Δ  * sem_datatype τ) -> Prop`, 
- partial correctness
  ```coq
  [| γ : Γ ;;; δ : Δ |] ||= w {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ
  ```
  denotes that there exists a witness `w : Γ ;;; Δ  ||- e : τ` where for any `γ : sem_ctx Γ` and `δ : sem_ctx Δ` such that `ϕ (γ, δ)` holds,
`sem_exp_rw Γ Δ e τ w γ` is non-empty and for any `total (δ', v) ∈ sem_exp_ro Γ e τ w γ`, the post-condition `ψ (γ, (δ' v))` holds. 
- total correctness
  ```coq
  [| γ : Γ ;;; δ : Δ |] ||= w {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ
  ```
  denotes the same and that `⊥` is not in the semantics.

Furthermore in the same file assertions' notations are defined:
- `[γ : Γ] |- {{ϕ}}` denotes `fun γ : sem_ctx Γ => ϕ`,
- `[γ : Γ] |- {{y : τ | ϕ}}` denotes `fun '((γ, y) : sem_ctx Γ * sem_datatype τ) => ϕ`, 
- `[γ : Γ ;;; δ : Δ] ||- {{ϕ}}` denotes  `fun '((γ, y) : sem_ctx Γ * δ : sem_ctx Δ) => ϕ`, 
- and `[γ : Γ ;;; δ : Δ] ||- {{y : τ | ϕ}}` denotes `fun '((γ, (δ, y)) : sem_ctx Γ * (sem_ctx Δ * sem_datatype τ)) => ϕ`.


### Reasoning Rules
In [ReasoningRules](./formalization/ReasoningRules.v), we define our verification calculus inductively: 
for a context `Gamma`, an  expression `e`, a data type `τ`,  a pre-condition `ϕ`, and a post-condition 
`ψ`, 
- `[γ : Γ]  |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ` denotes that the calculus proves the partial correctness and 
- `[γ : Γ]  |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ` denotes that the calculus proves the total correctness
assuming that `e` is a read-only expression.

Similarly, 
- `[γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ` denotes that the calculus proves the partial correctness and 
- `[γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ` denotes that the calculus proves the total correctness
assuming that `e` is a read-write expression.

Note that here we do not require `e` to be well-typed. Instead, we prove that
all correctness triples derived from our calculus are well-typed implicitly in the soundness theorem.

The soundness of the proof rules is proved in [ReasoningSoundness](./formalization/ReasoningSoundness.v).
```coq
Lemma proves_ro_prt_sound : forall Γ e τ ϕ ψ, 
  [γ : Γ]  |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ -> [γ : Γ]  |= w {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵖ.
  
with proves_ro_tot_sound : forall Γ e τ ϕ ψ, 
  [γ : Γ]  |- {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ -> [γ : Γ]  |= w {{ϕ γ}} e {{y : τ | ψ (γ, y)}}ᵗ.
  
with proves_rw_prt_sound : forall Γ Δ e τ ϕ ψ, 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ -> [γ : Γ ;;; δ : Δ] ||= {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵖ.
  
with proves_rw_tot_sound : forall Γ Δ e τ ϕ ψ, 
  [γ : Γ ;;; δ : Δ] ||- {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ -> [γ : Γ ;;; δ : Δ] ||= {{ϕ (γ, δ)}} e {{y : τ | ψ (γ, (δ, y))}}ᵗ.
```

In [ReasoningAdmissible](./formalization/ReasoningAdmissible.v), we prove some admissible rules.

In [ReasoningUtils](./formalization/ReasoningUtils.v), various utility functions in applying proof rules are defined. 

To use the rules, when the pre or post-conditions that we use are in the form of functions on patterns, 
Coq's inference engine often fails.
For example, when we have `fun '(γ, δ) => γ = δ` as a pre-condition, in some case, applying a rule may 
complain that it cannot infer it. In the case, use `patf` as a placeholder to teach Coq engine that the 
argument is supposed to be a function of the form `fun '(?, ?) => ?`. 
Similarly,  use `pattf` for `fun '(?, (?, ?)) => ?`.
They are Coq notatations defined in [ReasoningRules](./formalization/ReasoningRules.v).

## Base setting of the underlying type theory

We use Coq considering `Prop` to be a classical set of classical propositions.
We assume some axioms that are considered valid under this interpretation.
The axioms are declared in 
[Preliminaries.BaseAxioms](./formalization/Preliminaries/BaseAxioms.v).
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
The file [Powerdomain.Powerdomain](./formalization/Powerdomain/Powerdomain.v) is the main file that exports everything.

The powerdomain we use is a variant of the Plotkin powerdomain.
That means we have to deal with something being _infinite_ very often.
In the file [Powerdomain.PowerdomainInfinite](./formalization/Powerdomain/PowerdomainInfinite.v),
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
as a type-level mapping in [Powerdomain.PowerdomainMonad](./formalization/Powerdomain/PowerdomainMonad.v)
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
In [Powerdomain.PowerdomainProperties](./formalization/Powerdomain/PowerdomainProperties.v)
we prove various useful properties about the monadic actions; e.g., `pdom_bind_empty_1` is a 
lemma for a sufficient condition the result of a binding operation yielding the empty set.
In contrast, `pdom_bind_empty_2` is a lemma for a necessary condition.
For a powerdomain operation `ops` and a property `P`, 
the library provides lemmas which are used to reason their behaviours: 
* `pdom_ops_P_1`: a sufficient condition the result of `ops` satisfies `P`
* `pdom_ops_P_2`: a necessary condition the result of `ops` satisfies `P`
We consider the three properties: `P = empty` the result is empty, `P = bot` the result contains ⊥, and `P = total` the result 
contains `total a` for any `a`.

In [Powerdomain.PowerdomainCompleteness](./formalization/Powerdomain/PowerdomainCompleteness.v),
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
where the latter is defined as the point-wise ordering of the first.
In the file, we prove that both `pdom X` and `X -> pdom Y` for any `X` and `Y` are
ω-complete. 
We first define `pdom_chain_sup` as a general operation on countable chains 
and prove that for any countable chains, the subset generated by `pdom_chain_sup`
is indeed the least upper bound of the chain. We do similarly to the function types.
In [Powerdomain.PowerdomainOrderProperties](./formalization/Powerdomain/PowerdomainOrderProperties.v)
we use various useful lemmas about supremum in the above fashion.
(E.g., `pdom_chain_bot_2` is a lemma stating a necessary condition for a 
supremum of a countable chain containing ⊥.)

Finally, in 
[Powerdomain.PowerdomainFixedpoints](./formalization/Powerdomain/PowerdomainFixedpoints.v)
we prove the Least Fixed-point theorem for powerdomains and function types to a powerdomain.
Again, we define general operations on monotone endofunctions, which are to obtain 
the supremum of the bottom chains, and prove that when the endofunctions are continuous, 
the supremum is indeed a least fixed point.

In [Powerdomain.PowerdomainSemantics](./formalization/Powerdomain/PowerdomainSemantics.v)
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

In [Powerdomain.PowerdomainSemantics2](./formalization/Powerdomain/PowerdomainSemantics2.v)
we prepare various real numbers and integer operations using `pdom`. 
For example, there we define the limit operator using `pdom` and Coq's standard real number library.

## Concatenated States

We often concatenate states.
Given `γ : sem_ctx Γ` and `δ : sem_ctx Δ`,
to feed the states into a read-only expression's semantics, we need to merge them 
to be `sem_ctx (Γ +++ Δ)`. 
The concatenation is recursively defined 
and we denote it by `(γ ; δ) : sem_ctx (Γ +++ Δ)`.
Also, we have to often split the merged states. 
They are also defined recursively and denoted by 
`fst_app : sem_ctx (Γ +++ Δ) -> sem_ctx Γ` and  
`snd_app : sem_ctx (Γ +++ Δ) -> sem_ctx Δ`.
Now, there are very tedious equalities such as
`(fst_app x ; snd_app x) = x`, or `fst_app (x ; y) = x`.
They are defined in the `TediousList` section of [Semantics](./formalization/Semantics.v).

Without proof, the tactics `reduce_tedious` and `reduce_tedious ident` reduce almost every expression.

## Finitely Dependent Types for Case

The formal syntax of Clerical is defined in 
[Syntax](./formalization/Syntax.v).
The expressions are defined as an inductive type `exp`.
The nondeterministic case expression is supposed to have a list of pairs of expressions:
```coq
| CaseList : list (exp * exp) -> exp
```
An expression of the form `CaseList (e1, c1) :: (e2, c2) :: ... :: (en, cn) :: nil` denotes
`CASE e1 ==> c1 | ... | en ==> cn END`.

In [Typing](./formalization/Typing.v) when we define the well-typedness of a case expression 
`case e1 => c1 | ... | en => cn end` we want to make sure that each `ei` and `ci` are well-typed.
To state this for an arbitrary `l` in `CaseList l`, we use the following inductive type
```coq
Inductive ForallT {A : Type} (P : A -> Type): list A -> Type :=
| ForallT_nil : ForallT P nil
| ForallT_cons : forall x l, P x -> ForallT P l -> ForallT P (x::l).
```
and write `ForallT (fun ec : exp * exp => ((Γ +++ Δ) |- fst ec : BOOL) * (Γ ;;; Δ ||- snd ec : τ)) l` in 
the premise of the typing rule of `CaseList l`.

In [ReasoningRules](./formalization/ReasoningRules.v), to write down the proof rule of case expression, 
for a list `l : list (exp * exp)`, 
we require `l` dependent list of well-typednesses using the `ForallT`:
```coq
wty_l : ForallT (fun ec => ((Γ +++ Δ) |- fst ec : BOOL) * (Γ ;;; Δ ||- snd ec : τ)) l
```
also a `l` dependent list of postconditions 
```
θ : ForallT (fun ec => sem_ro_ctx (Γ +++ Δ) * bool -> Prop) l
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
    ([x : Δ ++ Γ] |- {{ϕ (fst_app x, snd_app x)}} fst ec {{y : BOOL | θ x y}}ᵖ) *
    ([γ : Γ ;;; δ : Δ] ||- {{θ ((γ; δ), true)}} snd ec {{y : τ | ψ (γ, (δ, y))}}ᵖ)) l θ
```
as the premise. 

The list-dependent types are defined in [Preliminaries.ListConstr](./formalization/Preliminaries/ListCosntr.v).

The library provides binary case expressions separately. It will be removed and replaced by the general case expression soon.


## Arithmetical Expressions
There are proof rules for each construct of expressions. 
For example, to prove something about `42 + 42 + 42`, we need to apply
proof rules for each `42` and the additions. 

A Clerical expression is called arithmetical when it is arithmetical... 
See  [Utils.Arith](./formalization/Utils/Arith.v).
In the file, we prove that when an expression `e` is arithmetical, and if it is well-typed
`w : Γ |- e : τ`, there (constructively) exists a function 
`f : sem_ctx Γ -> sem_datatype τ` such that

```coq
[γ : Γ] |- {{True}} e {{y : τ | y = f γ}}ᵖ
```
holds.

Again constructively, there is a predicate `P : sem_ctx Γ -> Prop` 
such that 
```coq
[γ : Γ] |- {{P γ}} e {{y : τ | y = f γ}}ᵗ
```
holds. The safety predicate `P` tracks division-by-zero and real number comparisons in `e`.

We prove that it is decidable if an expression is arithmetical or not.

Using the constructions of the predicates, functions and correctness lemmas, 
in [Utils.ArithProver](./formalization/Utils/ArithProver.v),
we define a tactic `prove_arith` that derives a correctness triple of an arithmetical expression and 
automatically applies IMPLY rule.
For example, when we face a goal of type 
`[γ : Γ] |- {{ϕ γ}} e {{y : τ | ψ γ y}}ᵗ`
the tactic first judges if `e` is arithmetical. 
If it is, it derives the correctness triple
`[γ : Γ] |- {{P γ}} e {{y : τ | y = f γ}}ᵗ`.
Then, the tactic applies the admissible rule for posing additional conditions on a read-only context to get
`[γ : Γ] |- {{P γ /\ ϕ γ}} e {{y : τ | y = f γ /\ ϕ γ}}ᵗ`.
Applying the IMPLY rule, the tactic reduces the original triple to implications.

This tactic works also for partial correctness goals.

A similar tactic `prove_assign_arith τ` is defined to prove a triple for 
assigning an arithmetical expression of type `τ` to a variable. It calls `prove_arith` internally.



## Tactics

## Important Lemmas and constructions
