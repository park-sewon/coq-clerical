Require Import List.
Require Import Coq.Program.Equality.
Require Import Reals.
Require Import ZArith.
Require Import Clerical.Powerdomain.Powerdomain.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.
Require Import Clerical.TypingProperties.
Require Import Clerical.Semantics.
Require Import Clerical.SemanticsProperties.
Require Import Clerical.Specification.
Require Import Clerical.ReasoningRules.

Open Scope detail_scope.
Lemma proves_admissible_ro_prt_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- {{ϕ}} e {{ψ}}) :
  ψ ->>> θ -> w |- {{ϕ}} e {{θ}}.
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma proves_admissible_ro_prt_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- {{ϕ}} e {{ψ}}) :
  θ ->> ϕ -> w |- {{θ}} e {{ψ}}.
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (ro_imply_prt _ _ _ _ _ _ _ _ _ H X H0).
Defined.

Lemma proves_admissible_ro_tot_post_weaken {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- [{ϕ}] e [{ψ}]) :
  ψ ->>> θ -> w |- [{ϕ}] e [{θ}].
Proof.
  intros.
  assert (ϕ ->> ϕ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ H0 X H).
Defined.

Lemma proves_admissible_ro_tot_pre_strengthen {Γ} {e} {τ} {w : Γ |- e : τ} {ϕ} {ψ} {θ} (X : w |- [{ϕ}] e [{ψ}]) :
  θ ->> ϕ -> w |- [{θ}] e [{ψ}].
Proof.
  intros.
  assert (ψ ->>> ψ).
  intros a b; auto.
  apply (ro_imply_tot _ _ _ _ _ _ _ _ _ H X H0).
Defined.


Fixpoint admissible_ro_prt_proj Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ
         (X : w' |- {{ϕ}} e {{ψ}}) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w |- {{fun γ => exists γ', ϕ (γ ; γ')}} e {{y | fun γ => exists γ', ψ y (γ ; γ')}}

with admissible_ro_tot_proj Γ Γ' e τ (w : Γ |- e : τ) (w' : (Γ ++ Γ') |- e : τ) ϕ ψ
                                   (X : w' |- [{ϕ}] e [{ψ}]) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w |- [{fun γ => exists γ', ϕ (γ ; γ')}] e [{y | fun γ => exists γ', ψ y (γ ; γ')}]

with admissible_rw_prt_proj Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ
                                   (X : w' ||- {{ϕ}} e {{ψ}}) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w ||- {{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}} e {{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}}

with admissible_rw_tot_proj Γ Δ Γ' e τ (w : Γ ;;; Δ ||- e : τ) (w' : (Γ ++ Γ') ;;; Δ ||- e : τ) ϕ ψ
                                   (X : w' ||- [{ϕ}] e [{ψ}]) :
  (*——————————-——————————-——————————-——————————-——————————-*)
  w ||- [{fun δγ => exists γ', ϕ (fst δγ, (snd δγ ; γ'))}] e [{y | fun δγ => exists γ', ψ y (fst δγ, (snd δγ ; γ'))}].
Proof.
Admitted.



Fixpoint admissible_ro_prt_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |- {{ϕ}} e {{ψ}}) {struct X} :
  w |- {{ϕ /\\ θ}} e {{ψ /\\\ fun _ => θ}}
with admissible_ro_tot_pose_readonly Γ e τ (w : Γ |- e : τ) ϕ ψ θ (X : w |- [{ϕ}] e [{ψ}]) {struct X} :
  w |- [{ϕ /\\ θ}] e [{ψ /\\\ fun _ => θ}]
with admissible_rw_prt_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||- {{ϕ}} e {{ψ}}) {struct X} :
  w ||- {{ϕ /\\ fun δγ => θ (snd δγ) }} e {{ψ /\\\ fun _ δγ => θ (snd δγ)}}
with admissible_rw_tot_pose_readonly Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ θ (X : w ||- [{ϕ}] e [{ψ}]) {struct X} :
  w ||- [{ϕ /\\ fun δγ => θ (snd δγ)}] e [{ψ /\\\ fun _ δγ => θ (snd δγ)}].
Admitted.





Fixpoint admissible_ro_tot_prt Γ e τ (w : Γ |- e : τ) ϕ ψ (X : w |- [{ϕ}] e [{ψ}]) {struct X} : w |- {{ϕ}} e {{ψ}}
with admissible_rw_tot_prt Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) ϕ ψ (X : w ||- [{ϕ}] e [{ψ}]) {struct X} : w ||- {{ϕ}} e {{ψ}}.
Proof.
Admitted.
