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
Require Import Clerical.ReasoningSoundness.
Require Import Clerical.ReasoningAdmissibleRes0.
Require Import Clerical.ReasoningAdmissibleRes1.
Require Import Clerical.ReasoningAdmissibleRes2.


Fixpoint r_ro_var_prt_inv {Γ} {k} {τ} {w : Γ |- Var k : τ} {ϕ} {ψ} (p : w |~ {{ϕ}} (Var k) {{ψ}}) {struct p}:
  ϕ ->> (fun γ : sem_ro_ctx Γ => ψ (ro_access Γ k τ w γ) γ)
  with r_rw_var_prt_inv Γ Δ k τ (w : (Δ ++ Γ) |- Var k : τ) (w' : Γ ;;; Δ ||- Var k : τ) ϕ ψ (p : w' ||~ {{ϕ}} (Var k) {{ψ}}) {struct p} :  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ (ro_access _ k τ w γ) (tedious_sem_app _ _ γ)).
Proof.
  inversion p.
  repeat apply projT2_eq in H;
    repeat apply projT2_eq in H0;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H6.
    

  pose proof (r_ro_var_prt_inv _ _ _ _ _ _ X).
  intros γ m.
  induction H6.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  apply H7, H8.
  induction H4.
  apply H5.
  exact m.

  repeat apply projT2_eq in H3;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6.
  induction H5.
  induction H3.
  intros h1 h2.
  induction H6.
  exact h2.

  repeat apply projT2_eq in H3;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6.

  induction H5.
  induction H6.
  apply (r_rw_var_prt_inv _ nil _ _ w w0 _ _ X).

  inversion p.
  repeat apply projT2_eq in H;
    repeat apply projT2_eq in H0;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H7.
  
  pose proof (r_rw_var_prt_inv _ _ _ _ w _ _ _ X).
  intros γ m.
  induction H7.
  apply H8.
  apply H9.
  apply H6.
  induction H5.
  exact m.
  
  repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6;
    repeat apply projT2_eq in H7.
  induction H7.
  intros γ m.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  induction H6.
  rewrite tedious_equiv_3.
  rewrite tedious_equiv_3 in m.  
  apply (r_ro_var_prt_inv _ _ _ _ _ _ X γ m).
Defined.  

Fixpoint r_ro_var_tot_inv {Γ} {k} {τ} {w : Γ |- Var k : τ} {ϕ} {ψ} (p : w |~ [{ϕ}] (Var k) [{ψ}]) {struct p}:
  ϕ ->> (fun γ : sem_ro_ctx Γ => ψ (ro_access Γ k τ w γ) γ)
  with r_rw_var_tot_inv Γ Δ k τ (w : (Δ ++ Γ) |- Var k : τ) (w' : Γ ;;; Δ ||- Var k : τ) ϕ ψ (p : w' ||~ [{ϕ}] (Var k) [{ψ}]) {struct p} :  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ (ro_access _ k τ w γ) (tedious_sem_app _ _ γ)).
Proof.
  inversion p.
  repeat apply projT2_eq in H;
    repeat apply projT2_eq in H0;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H6.
    

  pose proof (r_ro_var_tot_inv _ _ _ _ _ _ X).
  intros γ m.
  induction H6.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  apply H7, H8.
  induction H4.
  apply H5.
  exact m.

  repeat apply projT2_eq in H3;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6.
  induction H5.
  induction H3.
  intros h1 h2.
  induction H6.
  exact h2.

  repeat apply projT2_eq in H3;
    repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6.

  induction H5.
  induction H6.
  apply (r_rw_var_tot_inv _ nil _ _ w w0 _ _ X).

  inversion p.
  repeat apply projT2_eq in H;
    repeat apply projT2_eq in H0;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H7.
  
  pose proof (r_rw_var_tot_inv _ _ _ _ w _ _ _ X).
  intros γ m.
  induction H7.
  apply H8.
  apply H9.
  apply H6.
  induction H5.
  exact m.
  
  repeat apply projT2_eq in H4;
    repeat apply projT2_eq in H5;
    repeat apply projT2_eq in H6;
    repeat apply projT2_eq in H7.
  induction H7.
  intros γ m.
  rewrite (ro_access_typing_irrl _ _ _ w w0).  
  induction H6.
  rewrite tedious_equiv_3.
  rewrite tedious_equiv_3 in m.
  apply (r_ro_var_tot_inv _ _ _ _ _ _ X γ m).
Defined.  

Fixpoint r_ro_skip_prt_inv {Γ} {w : Γ |- SKIP : UNIT} {ϕ} {ψ} (p : w |~ {{ϕ}} (SKIP) {{ψ}}) {struct p}:
  ϕ ->> (ψ tt)
with r_rw_skip_prt_inv Γ Δ (w : (Δ ++ Γ) |- SKIP : UNIT) (w' : Γ ;;; Δ ||- SKIP : UNIT) ϕ ψ (p : w' ||~ {{ϕ}} (SKIP) {{ψ}}) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ tt (tedious_sem_app _ _ γ)).
Proof.  
  dependent induction p.
  pose proof (r_ro_skip_prt_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_skip_prt_inv _ nil w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_skip_prt_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ m.
  rewrite tedious_equiv_3.
  rewrite tedious_equiv_3 in m.
  apply (r_ro_skip_prt_inv _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_skip_tot_inv {Γ} {w : Γ |- SKIP : UNIT} {ϕ} {ψ} (p : w |~ [{ϕ}] (SKIP) [{ψ}]) {struct p}:
  ϕ ->> (ψ tt)
with r_rw_skip_tot_inv Γ Δ (w : (Δ ++ Γ) |- SKIP : UNIT) (w' : Γ ;;; Δ ||- SKIP : UNIT) ϕ ψ (p : w' ||~ [{ϕ}] (SKIP) [{ψ}]) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ tt (tedious_sem_app _ _ γ)).
Proof.  
  dependent induction p.
  pose proof (r_ro_skip_tot_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_skip_tot_inv _ nil w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_skip_tot_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ;   rewrite tedious_equiv_3; intro m.
  apply (r_ro_skip_tot_inv _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_true_prt_inv {Γ} {w : Γ |- TRUE : BOOL} {ϕ} {ψ} (p : w |~ {{ϕ}} (TRUE) {{ψ}}) {struct p}:
  ϕ ->> (ψ true)
with r_rw_true_prt_inv Γ Δ (w : (Δ ++ Γ) |- TRUE : BOOL) (w' : Γ ;;; Δ ||- TRUE : BOOL) ϕ ψ (p : w' ||~ {{ϕ}} (TRUE) {{ψ}}) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _  γ)) ->> (fun γ => ψ true (tedious_sem_app _ _  γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_true_prt_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_true_prt_inv _ nil w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_true_prt_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intro γ; rewrite tedious_equiv_3; intro m.
  apply (r_ro_true_prt_inv _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_true_tot_inv {Γ} {w : Γ |- TRUE : BOOL} {ϕ} {ψ} (p : w |~ [{ϕ}] (TRUE) [{ψ}]) {struct p}:
  ϕ ->> (ψ true)
with r_rw_true_tot_inv Γ Δ (w : (Δ ++ Γ) |- TRUE : BOOL) (w' : Γ ;;; Δ ||- TRUE : BOOL) ϕ ψ (p : w' ||~ [{ϕ}] (TRUE) [{ψ}]) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _  γ)) ->> (fun γ => ψ true (tedious_sem_app _ _  γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_true_tot_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_true_tot_inv _ nil w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_true_tot_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intro γ; rewrite tedious_equiv_3; intro m.
  apply (r_ro_true_tot_inv _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_false_prt_inv {Γ} {w : Γ |- FALSE : BOOL} {ϕ} {ψ} (p : w |~ {{ϕ}} (FALSE) {{ψ}}) {struct p}:
  ϕ ->> (ψ false)
with r_rw_false_prt_inv Γ Δ (w : (Δ ++ Γ) |- FALSE : BOOL) (w' : Γ ;;; Δ ||- FALSE : BOOL) ϕ ψ (p : w' ||~ {{ϕ}} (FALSE) {{ψ}}) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ false (tedious_sem_app _ _ γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_false_prt_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_false_prt_inv _ nil w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_false_prt_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ; rewrite tedious_equiv_3; intro m.
  apply (r_ro_false_prt_inv _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_false_tot_inv {Γ} {w : Γ |- FALSE : BOOL} {ϕ} {ψ} (p : w |~ [{ϕ}] (FALSE) [{ψ}]) {struct p}:
  ϕ ->> (ψ false)
with r_rw_false_tot_inv Γ Δ (w : (Δ ++ Γ) |- FALSE : BOOL) (w' : Γ ;;; Δ ||- FALSE : BOOL) ϕ ψ (p : w' ||~ [{ϕ}] (FALSE) [{ψ}]) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ false (tedious_sem_app _ _ γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_false_tot_inv _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_false_tot_inv _ nil w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_false_tot_inv _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ; rewrite tedious_equiv_3; intro m.
  apply (r_ro_false_tot_inv _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_int_prt_inv {Γ} {k} {w : Γ |- (INT k) : INTEGER} {ϕ} {ψ} (p : w |~ {{ϕ}} (INT k) {{ψ}}) {struct p}:
  ϕ ->> (ψ k)
with r_rw_int_prt_inv Γ Δ k (w : (Δ ++ Γ) |- (INT k) : INTEGER) (w' : Γ ;;; Δ ||- (INT k) : INTEGER) ϕ ψ (p : w' ||~ {{ϕ}} (INT k) {{ψ}}) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ k (tedious_sem_app _ _ γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_int_prt_inv _ _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_int_prt_inv _ nil _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_int_prt_inv _ _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ; rewrite tedious_equiv_3; intro m.
  apply (r_ro_int_prt_inv _ _ _ _ _  r γ m).
Defined.

Fixpoint r_ro_int_tot_inv {Γ} {k} {w : Γ |- (INT k) : INTEGER} {ϕ} {ψ} (p : w |~ [{ϕ}] (INT k) [{ψ}]) {struct p}:
  ϕ ->> (ψ k)
with r_rw_int_tot_inv Γ Δ k (w : (Δ ++ Γ) |- (INT k) : INTEGER) (w' : Γ ;;; Δ ||- (INT k) : INTEGER) ϕ ψ (p : w' ||~ [{ϕ}] (INT k) [{ψ}]) {struct p} :
  (fun γ => ϕ (tedious_sem_app _ _ γ)) ->> (fun γ => ψ k (tedious_sem_app _ _ γ)).
Proof.
  dependent induction p.
  pose proof (r_ro_int_tot_inv _ _ _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  intros h1 h2; auto.
  apply (r_rw_int_tot_inv _ nil _ w w0).
  exact r.
  dependent induction p.
  pose proof (r_rw_int_tot_inv _ _ _ w _ _ _ p).
  intros γ m.
  apply a0.
  apply H.
  apply a.
  apply m.
  simpl in w0.
  intros γ; rewrite tedious_equiv_3; intro m.
  apply (r_ro_int_tot_inv _ _ _ _ _  r γ m).
Defined.



Fixpoint r_ro_int_op_plus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :+: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :+: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%Z γ)} }%type
with r_rw_int_op_plus_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :+: e2) : INTEGER}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :+: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_op_plus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_op_plus_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_op_plus_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_op_plus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_op_plus_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 :+: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 :+: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%Z γ)} }%type
with r_rw_int_op_plus_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :+: e2) : INTEGER}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 :+: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_op_plus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_op_plus_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_op_plus_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_op_plus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_op_minus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :-: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :-: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%Z γ)} }%type
with r_rw_int_op_minus_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :-: e2) : INTEGER}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :-: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_op_minus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_op_minus_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_op_minus_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_op_minus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_op_minus_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 :-: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 :-: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%Z γ)} }%type
with r_rw_int_op_minus_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :-: e2) : INTEGER}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 :-: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_op_minus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_op_minus_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_op_minus_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_op_minus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_op_mult_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :*: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :*: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%Z γ)} }%type
with r_rw_int_op_mult_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :*: e2) : INTEGER}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :*: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_op_mult_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_op_mult_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_op_mult_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_op_mult_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_op_mult_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 :*: e2) : INTEGER}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 :*: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%Z γ)} }%type
with r_rw_int_op_mult_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :*: e2) : INTEGER}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 :*: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_op_mult_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_op_mult_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_op_mult_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_op_mult_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_comp_lt_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :<: e2) : BOOL}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :<: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 <? y2)%Z γ)} }%type
with r_rw_int_comp_lt_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :<: e2) : BOOL}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :<: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 <? y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_comp_lt_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_comp_lt_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_comp_lt_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_comp_lt_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_comp_lt_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 :<: e2) : BOOL}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 :<: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 <? y2)%Z γ)} }%type
with r_rw_int_comp_lt_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :<: e2) : BOOL}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 :<: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 <? y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_comp_lt_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_comp_lt_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_comp_lt_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_comp_lt_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_comp_eq_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 :=: e2) : BOOL}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 :=: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 =? y2)%Z γ)} }%type
with r_rw_int_comp_eq_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :=: e2) : BOOL}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 :=: e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 =? y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_comp_eq_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_comp_eq_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_comp_eq_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_comp_eq_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_int_comp_eq_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 :=: e2) : BOOL}
  (w1 : Γ |- e1 : INTEGER)
  (w2 : Γ |- e2 : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 :=: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype INTEGER) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 =? y2)%Z γ)} }%type
with r_rw_int_comp_eq_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 :=: e2) : BOOL}
  {w1 : (Δ ++ Γ) |- e1 : INTEGER}
  {w2 : (Δ ++ Γ) |- e2 : INTEGER}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 :=: e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 =? y2)%Z (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_int_comp_eq_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_int_comp_eq_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_int_comp_eq_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_int_comp_eq_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_op_plus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;+; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;+; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%R γ)} }%type
with r_rw_real_op_plus_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;+; e2) : REAL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;+; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%R (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_real_op_plus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_real_op_plus_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_real_op_plus_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_real_op_plus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_op_plus_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 ;+; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 ;+; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%R γ)} }%type
with r_rw_real_op_plus_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;+; e2) : REAL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 ;+; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 + y2)%R (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_real_op_plus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_real_op_plus_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_real_op_plus_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_real_op_plus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_op_minus_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;-; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;-; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%R γ)} }%type
with r_rw_real_op_minus_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;-; e2) : REAL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;-; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%R (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_real_op_minus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_real_op_minus_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_real_op_minus_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_real_op_minus_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_op_minus_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 ;-; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 ;-; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%R γ)} }%type
with r_rw_real_op_minus_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;-; e2) : REAL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 ;-; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 - y2)%R (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_real_op_minus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_real_op_minus_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_real_op_minus_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_real_op_minus_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_op_mult_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;*; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;*; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%R γ)} }%type
with r_rw_real_op_mult_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;*; e2) : REAL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;*; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%R (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_real_op_mult_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_real_op_mult_prt_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_prt_typing_irrl X).
      apply (r_proves_ro_prt_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_real_op_mult_prt_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_real_op_mult_prt_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_op_mult_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 ;*; e2) : REAL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 ;*; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%R γ)} }%type
with r_rw_real_op_mult_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;*; e2) : REAL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 ;*; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> ψ (y1 * y2)%R (tedious_sem_app _ _ γ)))%type} }.
Proof.
  +
    simple inversion p; try (contradict H0; discriminate); intros.
    {
      induction H1, (eq_sym H2), (eq_sym H3).
      repeat apply projT2_eq in H4.
      induction H4.    
      repeat apply projT2_eq in H5.
      injection H5; intros.
      clear H2 H3 H5.
      
      pose proof (r_ro_real_op_mult_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      split.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H4.
      apply H.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H.
      induction H4.
      exact h2.
      intros.
      induction H1.
      apply H0.    
      apply m3; auto.
    }
    {
      use_eq_r H0.
      use_eq_r H.
      use_eq_r H1.
      unfold_existT H2.
      use_eq_r H2.
      unfold_existT H3.
      injection H3; intros; clear H3.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_real_op_mult_tot_inv _ nil _ _ w0 w1 w2 _ _ X).
    }
    {
      inversion H1.
      use_eq_r H6.
      use_eq_r H7.
      clear H1.
      use_eq_r H0.
      unfold_existT H3.
      use_eq_r H3.
      unfold_existT H4.
      injection H4; intros; clear H4.
      induction H0, H1.
      exists ψ1.
      exists ψ2.
      repeat split.
      apply (r_proves_ro_tot_typing_irrl X).
      apply (r_proves_ro_tot_typing_irrl X0).
      apply H.
    }
  +
    inversion p.
    {
      unfold_existT H.
      unfold_existT H0.
      unfold_existT H5.
      unfold_existT H7.
      pose proof (r_rw_real_op_mult_tot_inv _ _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[m1 m2] m3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H5.
      apply H6.
      exact h2.
      intros.
      induction H7.
      apply H8.
      apply m3.
      exact H9.
      exact H10.
    }
    {
      unfold_existT H4.
      unfold_existT H5.
      unfold_existT H6.
      unfold_existT H7.
      induction H6, H7.
      pose proof (r_ro_real_op_mult_tot_inv _ _ _ _ w1 w2 _ _ X) as [ψ1' [ψ2' [[h1 h2] h3]]].
      exists ψ1'.
      exists ψ2'.
      repeat split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
      rewrite tedious_equiv_3 in y.
      exact y.
      intros.
      rewrite tedious_equiv_3.
      apply h3; auto.
    }
Defined.

Fixpoint r_ro_real_lt_prt_inv {Γ} {e1 e2} {w : Γ |- (e1 ;<; e2) : BOOL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (e1 ;<; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ {{ϕ}} e1 {{ψ1}}) * (w2 |~ {{ϕ}} e2 {{ψ2}}) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) γ)} }%type
with r_rw_real_lt_prt_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;<; e2) : BOOL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ {{ϕ}} (e1 ;<; e2) {{ψ}}) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e1 {{y | ψ1 y}}) *
              (w2 |~ {{(fun γ => ϕ (tedious_sem_app _ _  γ))}} e2 {{y | ψ2 y}}) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 -> ψ (Rltb'' y1 y2) (tedious_sem_app _ _ γ)) )%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_real_lt_prt_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    apply (r_rw_real_lt_prt_inv _ nil _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_prt_typing_irrl p1).
    apply (r_proves_ro_prt_typing_irrl p2).
    apply ψ0.

  +
    dependent induction p.
    pose proof (r_rw_real_lt_prt_inv _ _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    apply a0.
    apply m3; auto.
    pose proof (r_ro_real_lt_prt_inv _ _ _ _ w1 w2 _ _ r) as [ψ1 [ψ2 [[h1 h2] h3]]].
    exists ψ1.
    exists ψ2.
    repeat split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    intros.
    rewrite tedious_equiv_3.
    apply h3; auto.
Defined.

Fixpoint r_ro_real_lt_tot_inv {Γ} {e1 e2} {w : Γ |- (e1 ;<; e2) : BOOL}
  (w1 : Γ |- e1 : REAL)
  (w2 : Γ |- e2 : REAL)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (e1 ;<; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2 &
           (w1 |~ [{ϕ}] e1 [{ψ1}]) * (w2 |~ [{ϕ}] e2 [{ψ2}]) * (forall (y1 y2 : sem_datatype REAL) (γ : sem_ro_ctx Γ), ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 /\ ψ (Rltb'' y1 y2) γ)} }%type
with r_rw_real_lt_tot_inv {Γ Δ} {e1 e2} {w0 : Γ;;; Δ ||- (e1 ;<; e2) : BOOL}
  {w1 : (Δ ++ Γ) |- e1 : REAL}
  {w2 : (Δ ++ Γ) |- e2 : REAL}
  {ϕ} {ψ} (p : w0 ||~ [{ϕ}] (e1 ;<; e2) [{ψ}]) {struct p}:
  {ψ1 & {ψ2  &
           ((w1 |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e1 [{y | ψ1 y}]) *
              (w2 |~ [{(fun γ => ϕ (tedious_sem_app _ _  γ))}] e2 [{y | ψ2 y}]) *
              (forall y1 y2 γ, ψ1 y1 γ -> ψ2 y2 γ -> y1 <> y2 /\ ψ (Rltb'' y1 y2) (tedious_sem_app _ _ γ)) )%type} }.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_real_lt_tot_inv _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    split.
    apply (m3 _ _ _ H H0).
    apply a0.
    apply m3; auto.
    apply (r_rw_real_lt_tot_inv _ nil _ _ _ _ _ _ _ r).

    exists ψ1.
    exists ψ2.
    split.
    split.
    apply (r_proves_ro_tot_typing_irrl p1).
    apply (r_proves_ro_tot_typing_irrl p2).
    apply a.

  +
    dependent induction p.
    pose proof (r_rw_real_lt_tot_inv _ _ _ _ _ w1 w2 _ _ p) as [ψ1' [ψ2' [[m1 m2] m3]]].
    exists ψ1'.
    exists ψ2'.
    split.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros.
    split.
    apply (m3 _ _ _ H H0).
    apply a0.
    apply m3; auto.

    pose proof (r_ro_real_lt_tot_inv _ _ _ _ w1 w2 _ _ r) as [ψ1 [ψ2 [[h1 h2] h3]]].
    exists ψ1.
    exists ψ2.
    repeat split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h2);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    intros.
    apply (h3 _ _ _ H H0).
    rewrite tedious_equiv_3.
    apply h3; auto.
Defined.

Fixpoint r_ro_recip_prt_inv {Γ} {e} {w : Γ |- (;/; e) : REAL}
  (w' : Γ |- e : REAL)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (;/; e) {{ψ}}) {struct p}:
  {θ & (w' |~ {{ϕ}} e {{θ}}) *   ((θ /\\\ (fun (x : sem_datatype REAL) (_ : sem_ro_ctx Γ) => x <> 0%R)) ->>> (fun x : sem_datatype REAL => ψ (/ x)%R))}%type
with r_rw_recip_prt_inv {Γ Δ} {e} {w : Γ;;; Δ ||- (;/; e) : REAL}
  {w' : (Δ ++ Γ) |- e : REAL}
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (;/; e) {{ψ}}) {struct p}:
  {θ & (w' |~ {{(fun γ => ϕ (tedious_sem_app _ _ γ))}} e {{y | θ y}}) *
         ((θ /\\\ (fun (x : sem_datatype REAL) _ => x <> 0%R)) ->>> (fun x γ => ψ (/ x)%R (tedious_sem_app _ _ γ)))}%type.
Proof.
    dependent induction p.
    pose proof (r_ro_recip_prt_inv _ _ _  w' _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    intros y γ.
    intro.
    apply a0.
    apply m2.
    exact H.
    apply (r_rw_recip_prt_inv _ nil _ _ _ _ _ r).

    exists θ.
    split.
    apply (r_proves_ro_prt_typing_irrl p).
    apply a.

  +
    dependent induction p.
    pose proof (r_rw_recip_prt_inv _ _ _ _  w' _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros y γ h.
    apply a0.
    apply m2.
    exact h.    
    pose proof (r_ro_recip_prt_inv _ _ _ w' _ _ r) as [θ [h1 h2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    intros x y z.
    rewrite tedious_equiv_3.
    apply h2; auto.    
Defined.

Fixpoint r_ro_recip_tot_inv {Γ} {e} {w : Γ |- (;/; e) : REAL}
  (w' : Γ |- e : REAL)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (;/; e) [{ψ}]) {struct p}:
  {θ & (w' |~ [{ϕ}] e [{θ}]) *   (θ ->>> ((fun (x : R) (_ : sem_ro_ctx Γ) => x <> 0%R) /\\\ (fun x : R => ψ (/ x))))%R}%type
with r_rw_recip_tot_inv {Γ Δ} {e} {w : Γ;;; Δ ||- (;/; e) : REAL}
  {w' : (Δ ++ Γ) |- e : REAL}
  {ϕ} {ψ} (p : w ||~ [{ϕ}] (;/; e) [{ψ}]) {struct p}:
  {θ & (w' |~ [{(fun γ => ϕ (tedious_sem_app _ _ γ))}] e [{y | θ y}]) *
         ((θ ->>> ((fun (x : sem_datatype REAL) _ => x <> 0%R) /\\\ (fun x γ => ψ (/ x)%R (tedious_sem_app _ _ γ)))))}%type.
Proof.
    dependent induction p.
    pose proof (r_ro_recip_tot_inv _ _ _  w' _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    intros y γ.
    intro.
    split.
    apply (m2 _ _ H).
    apply a0.
    apply m2.
    exact H.
    apply (r_rw_recip_tot_inv _ nil _ _ _ _ _ r).

    exists θ.
    split.
    apply (r_proves_ro_tot_typing_irrl p).
    apply a.

  +
    dependent induction p.
    pose proof (r_rw_recip_tot_inv _ _ _ _  w' _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    intros y γ h.
    split.
    apply (m2 _ _ h).
    apply a0.
    apply m2.
    exact h.    
    pose proof (r_ro_recip_tot_inv _ _ _ w' _ _ r) as [θ [h1 h2]].
    exists θ.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a h1);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    intros x y z.
    split.
    apply (h2 _ _ z).
    rewrite tedious_equiv_3.
    apply h2; auto.    
Defined.
 
Fixpoint r_ro_coerce_prt_inv {Γ} {e} {w : Γ |- (RE e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (RE e) {{ψ}}) {struct p}:
  w' |~ {{ϕ}} e {{y | ψ (IZR y)}}
with r_rw_coerce_prt_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (RE e) : REAL}
  (w' : (Δ ++ Γ) |- e : INTEGER)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (RE e) {{ψ}}) {struct p}:
  w' |~ {{fun γ => ϕ (tedious_sem_app _ _ γ)}} e {{y | fun γ => ψ (IZR y) (tedious_sem_app _ _ γ)}}.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_coerce_prt_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_rw_coerce_prt_inv _ nil _ w0); auto.
    apply (r_proves_ro_prt_typing_irrl p).
  +
    dependent induction p.
    pose proof (r_rw_coerce_prt_inv _ _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_coerce_prt_inv _ _ _  w' _ _ r).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    rewrite tedious_equiv_3.
    auto.
Defined.
 
Fixpoint r_ro_coerce_tot_inv {Γ} {e} {w : Γ |- (RE e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (RE e) [{ψ}]) {struct p}:
  w' |~ [{ϕ}] e [{y | ψ (IZR y)}]
with r_rw_coerce_tot_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (RE e) : REAL}
  (w' : (Δ ++ Γ) |- e : INTEGER)
  {ϕ} {ψ} (p : w ||~ [{ϕ}] (RE e) [{ψ}]) {struct p}:
  w' |~ [{fun γ => ϕ (tedious_sem_app _ _ γ)}] e [{y | fun γ => ψ (IZR y) (tedious_sem_app _ _ γ)}].
Proof.
  +
    dependent induction p.
    pose proof (r_ro_coerce_tot_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_rw_coerce_tot_inv _ nil _ w0); auto.
    apply (r_proves_ro_tot_typing_irrl p).
  +
    dependent induction p.
    pose proof (r_rw_coerce_tot_inv _ _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_coerce_tot_inv _ _ _  w' _ _ r).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    rewrite tedious_equiv_3.
    auto.
Defined.

Fixpoint r_ro_exp_prt_inv {Γ} {e} {w : Γ |- (EXP e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (EXP e) {{ψ}}) {struct p}:
  w' |~ {{ϕ}} e {{y | ψ (powerRZ 2 y)}}
with r_rw_exp_prt_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (EXP e) : REAL}
  (w' : (Δ ++ Γ) |- e : INTEGER)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (EXP e) {{ψ}}) {struct p}:
  w' |~ {{fun γ => ϕ (tedious_sem_app _ _ γ)}} e {{y | fun γ => ψ (powerRZ 2 y) (tedious_sem_app _ _ γ)}}.
Proof.
  +
    dependent induction p.
    pose proof (r_ro_exp_prt_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_rw_exp_prt_inv _ nil _ w0); auto.
    apply (r_proves_ro_prt_typing_irrl p).
  +
    dependent induction p.
    pose proof (r_rw_exp_prt_inv _ _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_exp_prt_inv _ _ _  w' _ _ r).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    rewrite tedious_equiv_3.
    auto.
Defined.

Fixpoint r_ro_exp_tot_inv {Γ} {e} {w : Γ |- (EXP e) : REAL}
  (w' : Γ |- e : INTEGER)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (EXP e) [{ψ}]) {struct p}:
  w' |~ [{ϕ}] e [{y | ψ (powerRZ 2 y)}]
with r_rw_exp_tot_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (EXP e) : REAL}
  (w' : (Δ ++ Γ) |- e : INTEGER)
  {ϕ} {ψ} (p : w ||~ [{ϕ}] (EXP e) [{ψ}]) {struct p}:
  w' |~ [{fun γ => ϕ (tedious_sem_app _ _ γ)}] e [{y | fun γ => ψ (powerRZ 2 y) (tedious_sem_app _ _ γ)}].
Proof.
  +
    dependent induction p.
    pose proof (r_ro_exp_tot_inv _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_rw_exp_tot_inv _ nil _ w0); auto.
    apply (r_proves_ro_tot_typing_irrl p).
  +
    dependent induction p.
    pose proof (r_rw_exp_tot_inv _ _ _ _  w' _ _ p). 
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_exp_tot_inv _ _ _  w' _ _ r).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
      try (intros x y; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_3 in y.
    exact y.
    rewrite tedious_equiv_3.
    auto.
Defined.




(* Lemma has_type_ro_Seq_rw  *)
Fixpoint r_rw_sequence_prt_inv {Γ Δ} {c1 c2} {τ} {w : Γ ;;; Δ ||- (c1 ;; c2) : τ}
  (w1 : Γ ;;; Δ ||- c1 : UNIT)
  (w2 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (c1 ;; c2) {{ψ}}) {struct p}:
  {θ & (w1 ||~ {{ϕ}} c1 {{θ}}) * (w2 ||~ {{θ tt}} c2 {{ψ}})}%type
with r_ro_sequence_prt_inv {Γ Δ} {c1 c2} {τ} {w : (Δ ++ Γ) |- (c1 ;; c2) : τ}
  (w1 : Γ ;;; Δ ||- c1 : UNIT)
  (w2 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (c1 ;; c2) {{ψ}}) {struct p}:
  {θ & (w1 ||~ {{fun x => ϕ (fst x; snd x)}} c1 {{θ}}) * (w2 ||~ {{θ tt}} c2 {{fun y x => ψ y (fst x; snd x)}})}%type.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_sequence_prt_inv _ _ _ _ _ _ w1 w2 _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_sequence_prt_inv _ _ _ _ _ _ w1 w2 _ _ r) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl; auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl; auto.
    exists θ.
    split; auto.
    apply (r_proves_rw_prt_typing_irrl p1).
    apply (r_proves_rw_prt_typing_irrl p2).
  +
    dependent induction p.
    pose proof (r_ro_sequence_prt_inv _ _ _ _ _ w0 w1 w2 _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w0) as [r1 r2].
    pose proof (r_rw_sequence_prt_inv _ _ _ _ _ w0 r1 r2 _ _ r) as [θ [m1 m2]].
    exists (fun _ x => θ tt (tt, (fst x; snd x))).
    split.
    apply r_admissible_move_rw_prt in m1.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1, h2.
    simpl in s.
    unfold fst_app, snd_app; simpl.
    auto.
    apply r_admissible_move_rw_prt in m2.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Fixpoint r_rw_sequence_tot_inv {Γ Δ} {c1 c2} {τ} {w : Γ ;;; Δ ||- (c1 ;; c2) : τ}
  (w1 : Γ ;;; Δ ||- c1 : UNIT)
  (w2 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w ||~ [{ϕ}] (c1 ;; c2) [{ψ}]) {struct p}:
  {θ & (w1 ||~ [{ϕ}] c1 [{θ}]) * (w2 ||~ [{θ tt}] c2 [{ψ}])}%type
with r_ro_sequence_tot_inv {Γ Δ} {c1 c2} {τ} {w : (Δ ++ Γ) |- (c1 ;; c2) : τ}
  (w1 : Γ ;;; Δ ||- c1 : UNIT)
  (w2 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (c1 ;; c2) [{ψ}]) {struct p}:
  {θ & (w1 ||~ [{fun x => ϕ (fst x; snd x)}] c1 [{θ}]) * (w2 ||~ [{θ tt}] c2 [{fun y x => ψ y (fst x; snd x)}])}%type.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_sequence_tot_inv _ _ _ _ _ _ w1 w2 _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (r_ro_sequence_tot_inv _ _ _ _ _ _ w1 w2 _ _ r) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl; auto.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl; auto.
    exists θ.
    split; auto.
    apply (r_proves_rw_tot_typing_irrl p1).
    apply (r_proves_rw_tot_typing_irrl p2).
  +
    dependent induction p.
    pose proof (r_ro_sequence_tot_inv _ _ _ _ _ w0 w1 w2 _ _ p) as [θ [m1 m2]].
    exists θ.
    split.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (has_type_rw_Seq_inverse _ _ _ _ _ w0) as [r1 r2].
    pose proof (r_rw_sequence_tot_inv _ _ _ _ _ w0 r1 r2 _ _ r) as [θ [m1 m2]].
    exists (fun _ x => θ tt (tt, (fst x; snd x))).
    split.
    apply r_admissible_move_rw_tot in m1.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1, h2.
    simpl in s.
    unfold fst_app, snd_app; simpl.
    auto.
    apply r_admissible_move_rw_tot in m2.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
Defined.

Fixpoint r_rw_cond_prt_inv {Γ Δ} {e c1 c2} {τ} {w : Γ ;;; Δ ||- (IF e THEN c1 ELSE c2 END) : τ}
  (w1 : (Δ ++ Γ) |- e : BOOL)
  (w2 : Γ ;;; Δ ||- c1 : τ)
  (w3 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (IF e THEN c1 ELSE c2 END) {{ψ}}) {struct p}:
  {θ & (w1 |~ {{fun x => ϕ (fst_app x, snd_app x)}} e {{θ}}) * (w2 ||~ {{ro_to_rw_pre (θ true)}} c1 {{ψ}}) * (w3 ||~ {{ro_to_rw_pre (θ false)}} c2 {{ψ}})}%type
with r_ro_cond_prt_inv {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- (IF e THEN c1 ELSE c2 END) : τ}
  (w1 : (Δ ++ Γ) |- e : BOOL)
  (w2 : Γ ;;; Δ ||- c1 : τ)
  (w3 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w |~ {{ϕ}} (IF e THEN c1 ELSE c2 END) {{ψ}}) {struct p}:
  {θ & (w1 |~ {{ϕ}} e {{θ}}) * (w2 ||~ {{ro_to_rw_pre (θ true)}} c1 {{fun y x => ψ y (fst x; snd x)}}) * (w3 ||~ {{ro_to_rw_pre (θ false)}} c2 {{fun y x => ψ y (fst x; snd x)}})}%type.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_cond_prt_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ p) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    pose proof (r_ro_cond_prt_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ r) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_2.
    exact h2.

    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl.
    auto.
    
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl.
    auto.
    
    exists θ.
    split; auto.
    split.
    assert (w4 |~ {{(fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (fst_app x, snd_app x))}} e {{y | θ y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre.
    unfold fst_app, snd_app in h2.
    destruct (tedious_sem_app Δ Γ h1); auto.
    apply (r_proves_ro_prt_typing_irrl X).
    apply (r_proves_rw_prt_typing_irrl p1).
    apply (r_proves_rw_prt_typing_irrl p2).

  +
    dependent induction p.
    pose proof (r_ro_cond_prt_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ p) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w0) as [[r1 r2] r3].
    pose proof (r_rw_cond_prt_inv _ _ _ _ _ _ w0 r1 r2 r3 _ _ r) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    assert (r1 |~ {{(fun γ : sem_ro_ctx (Δ ++ Γ) => P (tt, γ))}} e {{y | θ y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_proves_ro_prt_typing_irrl X).

    
    apply r_admissible_move_rw_prt in m2.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; simpl.
    simpl in s.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl.
    unfold snd_app.
    simpl.
    auto.

    apply r_admissible_move_rw_prt in m3.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; simpl.
    simpl in s.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl.
    unfold snd_app.
    simpl.
    auto.
Defined.

Fixpoint r_rw_cond_tot_inv {Γ Δ} {e c1 c2} {τ} {w : Γ ;;; Δ ||- (IF e THEN c1 ELSE c2 END) : τ}
  (w1 : (Δ ++ Γ) |- e : BOOL)
  (w2 : Γ ;;; Δ ||- c1 : τ)
  (w3 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w ||~ [{ϕ}] (IF e THEN c1 ELSE c2 END) [{ψ}]) {struct p}:
  {θ & (w1 |~ [{fun x => ϕ (fst_app x, snd_app x)}] e [{θ}]) * (w2 ||~ [{ro_to_rw_pre (θ true)}] c1 [{ψ}]) * (w3 ||~ [{ro_to_rw_pre (θ false)}] c2 [{ψ}])}%type
with r_ro_cond_tot_inv {Γ Δ} {e c1 c2} {τ} {w : (Δ ++ Γ) |- (IF e THEN c1 ELSE c2 END) : τ}
  (w1 : (Δ ++ Γ) |- e : BOOL)
  (w2 : Γ ;;; Δ ||- c1 : τ)
  (w3 : Γ ;;; Δ ||- c2 : τ)
  {ϕ} {ψ} (p : w |~ [{ϕ}] (IF e THEN c1 ELSE c2 END) [{ψ}]) {struct p}:
  {θ & (w1 |~ [{ϕ}] e [{θ}]) * (w2 ||~ [{ro_to_rw_pre (θ true)}] c1 [{fun y x => ψ y (fst x; snd x)}]) * (w3 ||~ [{ro_to_rw_pre (θ false)}] c2 [{fun y x => ψ y (fst x; snd x)}])}%type.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_cond_tot_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ p) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    
    pose proof (r_ro_cond_tot_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ r) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    rewrite tedious_equiv_2.
    exact h2.

    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl.
    auto.
    
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h2.
    simpl.
    auto.
    
    exists θ.
    split; auto.
    split.
    assert (w4 |~ [{(fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (fst_app x, snd_app x))}] e [{y | θ y}]).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    unfold rw_to_ro_pre.
    unfold fst_app, snd_app in h2.
    destruct (tedious_sem_app Δ Γ h1); auto.
    apply (r_proves_ro_tot_typing_irrl X).
    apply (r_proves_rw_tot_typing_irrl p1).
    apply (r_proves_rw_tot_typing_irrl p2).

  +
    dependent induction p.
    pose proof (r_ro_cond_tot_inv _ _ _ _ _ _ w0 w1 w2 w3 _ _ p) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    pose proof (has_type_rw_Cond_inverse _ _ _ _ _ _ w0) as [[r1 r2] r3].
    pose proof (r_rw_cond_tot_inv _ _ _ _ _ _ w0 r1 r2 r3 _ _ r) as [θ [[m1 m2] m3]].
    exists θ.
    split.
    split.
    assert (r1 |~ [{(fun γ : sem_ro_ctx (Δ ++ Γ) => P (tt, γ))}] e [{y | θ y}]).
    apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m1);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply (r_proves_ro_tot_typing_irrl X).

    
    apply r_admissible_move_rw_tot in m2.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m2);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; simpl.
    simpl in s.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl.
    unfold snd_app.
    simpl.
    auto.

    apply r_admissible_move_rw_tot in m3.
    apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a m3);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1; simpl.
    simpl in s.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl.
    unfold snd_app.
    simpl.
    auto.
Defined.

Fixpoint r_rw_case_list_prt_inv {Γ Δ} {l} {τ} {w : Γ ;;; Δ ||- (CaseList l) : τ}
  wty_l
  {ϕ} {ψ} (p : w ||~ {{ϕ}} (CaseList l) {{ψ}}) {struct p} :
  {θ & ForallT2 (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l0 : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ)) (θ0 : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) =>
            ((fst wty_l0 |~ {{rw_to_ro_pre ϕ}} fst ec {{y | θ0 y}}) * (snd wty_l0 ||~ {{ro_to_rw_pre (θ0 true)}} snd ec {{y | ψ y}}))%type) l wty_l θ}
with r_ro_case_list_prt_inv {Γ Δ} {l} {τ} {w : (Δ ++ Γ) |- (CaseList l) : τ}
  wty_l
  {ϕ} {ψ} (p : w |~ {{ϕ}} (CaseList l) {{ψ}}) {struct p} :
  {θ : ForallT (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) l &
  ForallT2 (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type)
    (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
    (fun (ec : exp * exp) (wty_l0 : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ)) (θ0 : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) =>
     ((fst wty_l0 |~ {{rw_to_ro_pre (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ (tedious_prod_sem Δ Γ γδ))}} fst ec {{y | θ0 y}}) *
      (snd wty_l0 ||~ {{ro_to_rw_pre (θ0 true)}} snd ec {{y | (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ψ y (tedious_prod_sem Δ Γ γδ))}}))%type) l wty_l
    θ}.
Proof.
  +
    dependent induction p.
    pose proof (r_rw_case_list_prt_inv _ _ _ _ w0 wty_l _ _ p) as [θ F].
    clear IHp .
    clear w.
    clear p w0.
    exists θ.
    dependent induction F.
    apply ForallT2_nil.
    apply ForallT2_cons.
    simpl.
    apply IHF.
    clear IHF.
    simpl in F.
    destruct F.
    destruct r.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply a.
    unfold rw_to_ro_pre in h2.
    auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct r.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply a.
    unfold rw_to_ro_pre in h2.
    auto.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

    apply (r_ro_case_list_prt_inv _ _ _ _ w0); auto.

    exists θ.
    clear w.
    dependent induction f.
    simpl.
    dependent destruction wty_l.
    apply ForallT2_nil.
    dependent destruction wty_l.
    apply ForallT2_cons.
    apply IHf.
    destruct r.
    clear IHf wty_l.
    split.
    apply (r_proves_ro_prt_typing_irrl r).
    apply (r_proves_rw_prt_typing_irrl r0).
  +
    dependent induction p.
    pose proof (r_ro_case_list_prt_inv _ _ _ _ w0 wty_l _ _ p) as [θ f].
    exists θ.
    clear p w0 w IHp.
    induction f.
    apply ForallT2_nil.
    apply ForallT2_cons.
    apply IHf.
    clear IHf.
    destruct r.
    split.
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    apply a.
    apply h2.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).

    pose proof (has_type_rw_CaseList_inverse _ _ _ _ w0).
    pose proof (r_rw_case_list_prt_inv _ _ _ _ w0 H _ _ r) as [θ f].
    exists θ.
    clear r w w0.
    dependent induction f.
    dependent destruction wty_l.
    apply ForallT2_nil.
    dependent destruction wty_l.
    apply ForallT2_cons.
    apply IHf.
    clear IHf.
    destruct r.
    split.
    assert (fst p0 |~ {{rw_to_ro_pre (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => P (tt, tedious_prod_sem Δ Γ γδ))}} fst a {{y | q y}}).
    apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    simpl in h1.
    unfold rw_to_ro_pre.
    unfold rw_to_ro_pre in h2.
    simpl.
    pose proof (tedious_equiv_2 h1).
    rewrite H.
    rewrite H in h2.
    unfold fst_app, snd_app.
    unfold fst_app, snd_app in h2.
    destruct (tedious_sem_app Δ Γ h1).
    simpl.
    simpl in h2.
    rewrite tedious_equiv_1 in h2.
    exact h2.
    apply (r_proves_ro_prt_typing_irrl X).
    
    assert (snd p0 ||~ {{ro_to_rw_pre (q true)}} snd a {{y | (fun x => Q y (tt, snd x))}}).
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a r0);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    simpl in h2.
    destruct h2.
    simpl.
    destruct u.
    auto.
    apply r_admissible_move_rw_prt in X.
    apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X);
      try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    destruct h1.
    simpl.
    unfold ro_to_rw_pre.
    unfold ro_to_rw_pre in h2.
    simpl in s.
    simpl.
    unfold snd_app; simpl.
    auto.
    destruct h2.
    simpl in s.
    simpl.
    unfold snd_app; simpl.
    auto.
Defined.



Fixpoint has_type_rw_Case_inverse Γ Δ e1 c1 e2 c2 τ (w : Γ ;;; Δ ||- (Case e1 c1 e2 c2) : τ) :
  (
    ((Δ ++ Γ) |- e1 : BOOL) *
    ((Δ ++ Γ) |- e2 : BOOL) *
      (Γ ;;; Δ ||- c1 : τ) * (Γ ;;; Δ ||- c2 : τ))%type.
Proof.
  apply has_type_rw_r_has_type_rw in w.
  dependent destruction w.
  apply r_has_type_ro_has_type_ro in r.
  apply r_has_type_ro_has_type_ro in r0.
  apply r_has_type_rw_has_type_rw in w1.
  apply r_has_type_rw_has_type_rw in w2.
  repeat split; auto.
Defined.


Fixpoint r_rw_case_prt_inv {Γ Δ} {e1 e2 c1 c2} {τ} {w :  Γ ;;; Δ ||- Case e1 c1 e2 c2  : τ}
  (wty_e1 : (Δ ++ Γ) |- e1 : BOOL)
  (wty_e2 : (Δ ++ Γ) |- e2 : BOOL)
   wty_c1 wty_c2 {ϕ} {ψ}
  (p : w ||~ {{ϕ}} Case e1 c1 e2 c2 {{ψ}}) {struct p}:
  {θ1 & {θ2 &
       (wty_e1 |~ {{rw_to_ro_pre ϕ}} e1 {{y | θ1 y}}) *
       (wty_e2 |~ {{rw_to_ro_pre ϕ}} e2 {{y | θ2 y}}) *
       (wty_c1 ||~ {{ro_to_rw_pre (θ1 true)}} c1 {{y | ψ y}}) *
         (wty_c2 ||~ {{ro_to_rw_pre (θ2 true)}} c2 {{y | ψ y}}) } }%type
with r_ro_case_prt_inv {Γ Δ} {e1 e2 c1 c2} {τ} {w :  (Δ ++ Γ) |- Case e1 c1 e2 c2  : τ}
  (wty_e1 : (Δ ++ Γ) |- e1 : BOOL)
  (wty_e2 : (Δ ++ Γ) |- e2 : BOOL)
  (wty_c1 : Γ ;;; Δ ||- c1 : τ)
  (wty_c2 : Γ ;;; Δ ||- c2 : τ) {ϕ} {ψ}
   (p : w |~ {{ϕ}} Case e1 c1 e2 c2 {{ψ}}) {struct p}:
  {θ1 & {θ2 &
           (wty_e1 |~ {{ϕ}} e1 {{y | θ1 y}}) *
             (wty_e2 |~ {{ϕ}} e2 {{y | θ2 y}}) *
             (wty_c1 ||~ {{ro_to_rw_pre (θ1 true)}} c1 {{y | ro_to_rw_pre (ψ y)}}) *
             (wty_c2 ||~ {{ro_to_rw_pre (θ2 true)}} c2 {{y | ro_to_rw_pre (ψ y)}}) } }%type.                                                                     
Proof.
  +
    dependent induction p.
    {
      pose proof (r_rw_case_prt_inv _ _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 _ _ p)
        as [θ1 [θ2 [[[p1 p2] p3] p4]]].
      exists θ1.
      exists θ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply a; auto.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply a; auto.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }

    {
      pose proof (r_ro_case_prt_inv _ _ _ _ _ _ _ w0 wty_e1 wty_e2 wty_c1 wty_c2 _ _ r)
        as [θ1 [θ2 [[[p1 p2] p3] p4]]].
      exists θ1.
      exists θ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre in h2.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre in h2.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }

    {
      exists θ1.
      exists θ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
    }

  +
    dependent induction p.
    {
      pose proof (r_ro_case_prt_inv _ _ _ _ _ _ _ w0 wty_e1 wty_e2 wty_c1 wty_c2 _ _ p)
        as [θ1 [θ2 [[[p1 p2] p3] p4]]].
      exists θ1.
      exists θ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      apply a0.
      exact H.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      apply a0.
      exact H.
      }

      {
        pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ _ w0) as [[[w1 w2] w3] w4].
        simpl in w1.
        simpl in w2.
        pose proof (r_rw_case_prt_inv _ nil _ _ _ _ _ _ w1 w2 w3 w4 _ _ r)
          as [θ1 [θ2 [[[p1 p2] p3] p4]]].
        exists θ1.
        exists θ2.
        repeat split.
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply r_admissible_move_rw_prt in p3.
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        unfold fst_app, snd_app.
        simpl.
        destruct h1; simpl; exact h2.
        unfold fst_app, snd_app.
        simpl.
        simpl in h2.
        destruct h2; auto.
        apply r_admissible_move_rw_prt in p4.
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a p4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        unfold fst_app, snd_app.
        simpl.
        destruct h1; simpl; exact h2.
        unfold fst_app, snd_app.
        simpl.
        simpl in h2.
        destruct h2; auto.
      }
Defined.      

Check r_rw_case_tot.
Fixpoint r_rw_case_tot_inv {Γ Δ} {e1 e2 c1 c2} {τ} {w :  Γ ;;; Δ ||- Case e1 c1 e2 c2  : τ}
  (wty_e1 : (Δ ++ Γ) |- e1 : BOOL)
  (wty_e2 : (Δ ++ Γ) |- e2 : BOOL)
   wty_c1 wty_c2 {ϕ} {ψ}
  (p : w ||~ [{ϕ}] Case e1 c1 e2 c2 [{ψ}]) {struct p}:
  {θ1 & {θ2 &
           {ϕ1 & {ϕ2 &
                    (wty_e1 |~ {{rw_to_ro_pre ϕ}} e1 {{y | θ1 y}}) *
                      (wty_e2 |~ {{rw_to_ro_pre ϕ}} e2 {{y | θ2 y}}) *
                      (wty_c1 ||~ [{ro_to_rw_pre (θ1 true)}] c1 [{y | ψ y}]) *
                      (wty_c2 ||~ [{ro_to_rw_pre (θ2 true)}] c2 [{y | ψ y}]) *
                      (wty_e1 |~ [{ϕ1}] e1 [{b | (fun _ : sem_ro_ctx (Δ ++ Γ) => b = true)}]) *
                      (wty_e2 |~ [{ϕ2}] e2 [{b | (fun _ : sem_ro_ctx (Δ ++ Γ) => b = true)}]) *
                      (forall x : sem_ro_ctx (Δ ++ Γ), rw_to_ro_pre ϕ x -> ϕ1 x \/ ϕ2 x)} } } }%type
with r_ro_case_tot_inv {Γ Δ} {e1 e2 c1 c2} {τ} {w :  (Δ ++ Γ) |- Case e1 c1 e2 c2  : τ}
  (wty_e1 : (Δ ++ Γ) |- e1 : BOOL)
  (wty_e2 : (Δ ++ Γ) |- e2 : BOOL)
  (wty_c1 : Γ ;;; Δ ||- c1 : τ)
  (wty_c2 : Γ ;;; Δ ||- c2 : τ) {ϕ} {ψ}
   (p : w |~ [{ϕ}] Case e1 c1 e2 c2 [{ψ}]) {struct p}:
  {θ1 & {θ2 &
           {ϕ1 & {ϕ2 &
                    (wty_e1 |~ {{ϕ}} e1 {{y | θ1 y}}) *
                      (wty_e2 |~ {{ϕ}} e2 {{y | θ2 y}}) *
                      (wty_c1 ||~ [{ro_to_rw_pre (θ1 true)}] c1 [{y | ro_to_rw_pre (ψ y)}]) *
                      (wty_c2 ||~ [{ro_to_rw_pre (θ2 true)}] c2 [{y | ro_to_rw_pre (ψ y)}]) *
                      (wty_e1 |~ [{ϕ1}] e1 [{b | (fun _ : sem_ro_ctx (Δ ++ Γ) => b = true)}]) *
                      (wty_e2 |~ [{ϕ2}] e2 [{b | (fun _ : sem_ro_ctx (Δ ++ Γ) => b = true)}]) *
                      (forall x : sem_ro_ctx (Δ ++ Γ),  ϕ x -> ϕ1 x \/ ϕ2 x)} } } }%type.
Proof.
  +
    dependent induction p.
    {
      pose proof (r_rw_case_tot_inv _ _ _ _ _ _ _ _ wty_e1 wty_e2 wty_c1 wty_c2 _ _ p)
        as [θ1 [θ2 [ϕ1 [ϕ2 [[[[[[p1 p2] p3] p4] p5] p6] p7]]]]].
      exists θ1.
      exists θ2.
      exists ϕ1.
      exists ϕ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply a; auto.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply a; auto.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p5);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p6);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      apply p7.
      apply a.
      exact H.
    }

    {
      pose proof (r_ro_case_tot_inv _ _ _ _ _ _ _ w0 wty_e1 wty_e2 wty_c1 wty_c2 _ _ r)
        as [θ1 [θ2 [ϕ1 [ϕ2 [[[[[[p1 p2] p3] p4] p5] p6] p7]]]]].
      exists θ1.
      exists θ2.
      exists ϕ1.
      exists ϕ2.

      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre in h2.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre in h2.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p5);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p6);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      apply p7.
      unfold rw_to_ro_pre in H.
      rewrite tedious_equiv_3 in H.
      exact H.
    }

    {
      exists θ1.
      exists θ2.
      exists ϕ1.
      exists ϕ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply o.
    }

  +
    dependent induction p.
    {
      pose proof (r_ro_case_tot_inv _ _ _ _ _ _ _ w0 wty_e1 wty_e2 wty_c1 wty_c2 _ _ p)
        as [θ1 [θ2 [ϕ1 [ϕ2 [[[[[[p1 p2] p3] p4] p5] p6] p7]]]]].
      exists θ1.
      exists θ2.
      exists ϕ1.
      exists ϕ2.
      repeat split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      apply a0.
      exact H.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      apply a0.
      exact H.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p5);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p6);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      apply p7.
      apply a.
      exact H.
    }

    {
      pose proof (has_type_rw_Case_inverse _ _ _ _ _ _ _ w0) as [[[w1 w2] w3] w4].
      simpl in w1.
      simpl in w2.
      pose proof (r_rw_case_tot_inv _ nil _ _ _ _ _ _ w1 w2 w3 w4 _ _ r)
        as [θ1 [θ2 [ϕ1 [ϕ2 [[[[[[p1 p2] p3] p4] p5] p6] p7]]]]].
      exists θ1.
      exists θ2.
      exists ϕ1.
      exists ϕ2.
      repeat split.
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p1);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a p2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply r_admissible_move_rw_tot in p3.
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p3);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        unfold fst_app, snd_app.
        simpl.
        destruct h1; simpl; exact h2.
        unfold fst_app, snd_app.
        simpl.
        simpl in h2.
        destruct h2; auto.
        apply r_admissible_move_rw_tot in p4.
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a p4);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        unfold fst_app, snd_app.
        simpl.
        destruct h1; simpl; exact h2.
        unfold fst_app, snd_app.
        simpl.
        simpl in h2.
        destruct h2; auto.
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p5);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a p6);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply p7.        
      }
Defined.      
  
    
Fixpoint r_rw_case_list_tot_inv {Γ Δ} {l} {τ} {w : Γ ;;; Δ ||- (CaseList l) : τ}
  wty_l
  {ϕ} {ψ} (p : w ||~ [{ϕ}] (CaseList l) [{ψ}]) {struct p} :
  {θ & {ϕi & (ForallT3 (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type)
         (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
         (fun _ : exp * exp => sem_ro_ctx (Δ ++ Γ) -> Prop)
         (fun (ec : exp * exp) (wty_l0 : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))
            (θ0 : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) (ϕi0 : sem_ro_ctx (Δ ++ Γ) -> Prop) =>
          ((fst wty_l0 |~ {{rw_to_ro_pre ϕ}} fst ec {{y | θ0 y}}) *
           (snd wty_l0 ||~ [{ro_to_rw_pre (θ0 true)}] snd ec [{y | ψ y}]) *
             (fst wty_l0 |~ [{ϕi0}] fst ec [{b | (fun _ : sem_ro_ctx (Δ ++ Γ) => b = true)}]))%type) l wty_l θ ϕi) *
               (forall x : sem_ro_ctx (Δ ++ Γ),
        rw_to_ro_pre ϕ x ->
        ForallT_disj (fun _ : exp * exp => sem_ro_ctx (Δ ++ Γ) -> Prop)
                     (fun (_ : exp * exp) (ϕi0 : sem_ro_ctx (Δ ++ Γ) -> Prop) => ϕi0 x) l ϕi)} }%type
with r_ro_case_list_tot_inv {Γ Δ} {l} {τ} {w : (Δ ++ Γ) |- (CaseList l) : τ}
                            wty_l
                            {ϕ} {ψ} (p : w |~ [{ϕ}] (CaseList l) [{ψ}]) {struct p} :
  {θ & {ϕi & (ForallT3 (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type)
                       (fun _ : exp * exp => bool -> sem_ro_ctx (Δ ++ Γ) -> Prop)
                       (fun _ : exp * exp => sem_ro_ctx (Δ ++ Γ) -> Prop)
                       (fun (ec : exp * exp) (wty_l0 : ((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))
                            (θ0 : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop) (ϕi0 : sem_ro_ctx (Δ ++ Γ) -> Prop) =>
                          ((fst wty_l0 |~ {{ϕ}} fst ec {{y | θ0 y}}) *
                             (snd wty_l0 ||~ [{ro_to_rw_pre (θ0 true)}] snd ec [{y | ro_to_rw_pre (ψ y)}]) *
                             (fst wty_l0 |~ [{ϕi0}] fst ec [{b | (fun _ : sem_ro_ctx (Δ ++ Γ) => b = true)}]))%type) l wty_l θ ϕi) *
               (forall x,
                   ϕ x ->
                   ForallT_disj (fun _ : exp * exp => sem_ro_ctx (Δ ++ Γ) -> Prop)
                                (fun (_ : exp * exp) (ϕi0 : sem_ro_ctx (Δ ++ Γ) -> Prop) => ϕi0 x) l ϕi)} }%type.
Proof.
  +
    dependent induction p.
    {
      pose proof (r_rw_case_list_tot_inv _ _ _ _ w0 wty_l _ _ p) as [θ F].
      clear  r_rw_case_list_tot_inv  r_ro_case_list_tot_inv.
      clear IHp .
      clear w.
      clear p w0.
      exists θ.
      destruct F.
      destruct p.
      exists x.
      split.
      clear f0.
      dependent induction f.
      apply ForallT3_nil.
      apply ForallT3_cons.
      simpl.
      apply IHf.
      clear IHf.
      simpl in f.
      (* destruct f. *)
      destruct j as [[h h0] h1].
      
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a h);
        try (intros i1 i2; auto); try (intros i1 i2 i3; auto).
      unfold rw_to_ro_pre.
      apply a.
      exact i2.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a h0);
        try (intros i1 i2; auto); try (intros i1 i2 i3; auto).
      exact h1.

      intros.
      apply f0.
      apply a.
      exact H.
    }

    {
      pose proof (r_ro_case_list_tot_inv _ _ _ _ w0 wty_l _ _ r) as [θ [ϕi [f f0]]].
      exists θ.
      exists ϕi.
      split.
      clear f0 r w0 w.
      dependent induction f.
      apply ForallT3_nil.
      apply ForallT3_cons.
      apply IHf.
      clear IHf.
      destruct j as [[j1 j2] j3].
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a j1);
        try (intros i1 i2; auto); try (intros i1 i2 i3; auto).
      
      unfold rw_to_ro_pre in i2.
      rewrite tedious_equiv_3 in i2.
      exact i2.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a j2);
        try (intros i1 i2; auto); try (intros i1 i2 i3; auto).
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a j3);
        try (intros i1 i2; auto); try (intros i1 i2 i3; auto).
      intros.
      apply f0.
      unfold rw_to_ro_pre in H.
      rewrite tedious_equiv_3 in H.
      exact H.
    }

    { 
      exists θ.
      clear w.
      exists ϕi.
      split.
      clear f0.
      dependent induction f.
      simpl.
      dependent destruction wty_l.
      apply ForallT3_nil.
      dependent destruction wty_l.
      apply ForallT3_cons.
      apply IHf.
      destruct j as [[i1 i2] i3].
      clear IHf wty_l.
      split.
      split.
      apply (r_proves_ro_prt_typing_irrl i1).
      apply (r_proves_rw_tot_typing_irrl i2).
      apply (r_proves_ro_tot_typing_irrl i3).

      intros.
      apply f0.
      exact H.
    }
  +
    dependent induction p.
    {
      pose proof (r_ro_case_list_tot_inv _ _ _ _ w0 wty_l _ _ p) as [θ f].
      exists θ.
      clear p w0 w IHp.
      destruct f.
      exists x.
      split.
      destruct p.
      clear f0.
      dependent induction f.
      apply ForallT3_nil.
      apply ForallT3_cons.
      apply IHf.
      clear IHf.
      destruct j as [[j1 j2] j3].
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a j1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a j2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      apply a0.
      apply H.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a j3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct p.
      intros.
      apply f0.
      apply a.
      exact H.
    }

    {
      pose proof (has_type_rw_CaseList_inverse _ _ _ _ w0).
      pose proof (r_rw_case_list_tot_inv _ _ _ _ w0 H _ _ r) as [θ [ϕi [f f0]]].
      exists θ.
      exists ϕi.
      split.
      clear r w w0 f0.
      dependent induction f.
      dependent destruction wty_l.
      apply ForallT3_nil.
      dependent destruction wty_l.
      apply ForallT3_cons.
      apply IHf.
      clear IHf.
      destruct j as [[j1 j2] j3].
      split.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a j1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply r_admissible_move_rw_tot in j2.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a j2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      destruct h1; unfold ro_to_rw_pre, fst_app, snd_app; simpl.
      exact h2.
      destruct h2; unfold ro_to_rw_pre, fst_app, snd_app; simpl.
      auto.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a j3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      exact f0.
    }
Defined.
  
Fixpoint r_rw_while_prt_inv {Γ Δ} {e c} {w : Γ ;;; Δ ||- (WHILE e DO c END) : UNIT}
         (we : (Δ ++ Γ) |- e : BOOL)
         (wc : Γ ;;; Δ ||- c : UNIT) {ϕ} {ψ} (p : w ||~ {{ϕ}} (WHILE e DO c END) {{ψ}}) {struct p} :
  {I & {θ &
          (ϕ ->> I) * ((I /\\ ro_to_rw_pre (θ false)) ->> ψ tt) *
            (we |~ {{rw_to_ro_pre I}} e {{θ}}) *
            (wc ||~ {{ro_to_rw_pre (θ true)}} c {{fun _ => I}})} }%type
with r_ro_while_prt_inv {Γ Δ} {e c} {w0 : (Δ ++ Γ) |- (WHILE e DO c END) : UNIT}
                        (we : (Δ ++ Γ) |- e : BOOL)
                        (wc : Γ ;;; Δ ||- c : UNIT) {ϕ0} {ψ0} (p : w0 |~ {{ϕ0}} (WHILE e DO c END) {{ψ0}}) {struct p} :
  let ϕ := (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ0 (tedious_prod_sem Δ Γ γδ)) in
  let ψ := (fun (v : unit) (γδ : sem_ro_ctx Δ * sem_ro_ctx Γ) => ψ0 v (tedious_prod_sem Δ Γ γδ)) in
  {I  &
     {θ  &
        ((ϕ ->> I) * ((I /\\ ro_to_rw_pre (θ false)) ->> ψ tt) * (we |~ {{rw_to_ro_pre I}} e {{y | θ y}}) *
           (wc ||~ {{ro_to_rw_pre (θ true)}} c {{_ | I}}))%type } }.
Proof.
  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H7.    

      pose proof (r_rw_while_prt_inv _ _ _ _ _ we wc _ _ X) as [I [θ [[[m1 m2] m3] m4]]].
      exists I.
      exists θ.
      repeat split; auto.
      intros x q.
      apply m1.
      induction H5.
      apply H6.
      exact q.
      intros q [h1 h2].
      induction H7.
      apply H8.
      apply m2.
      split; auto.
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.    
      induction H6.
      induction H7.
      apply (r_ro_while_prt_inv _ _ _ _ w0 we wc _ _ X).
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.    
      exists ϕ.
      exists θ.
      repeat split; (try intros h1 h2; auto); auto.
      induction H7.
      induction H6.
      exact h2.
      induction H6.
      apply (r_proves_ro_prt_typing_irrl X).
      induction H6.
      apply (r_proves_rw_prt_typing_irrl X0).
    }

  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H6.
      pose proof (r_ro_while_prt_inv _ _ _ _ _ we wc _ _ X) as [I [θ [[[m1 m2] m3] m4]]].
      exists I.
      exists θ.
      repeat split; auto.
      induction H4.
      intros x h.
      apply m1.
      apply H5.
      exact h.

      induction H6.
      intros x h.
      apply H7.
      apply m2.
      exact h.
    }
   
    {
      repeat apply projT2_eq in H3.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      pose proof (has_type_rw_While_inverse w) as [r1 r2]. 
      pose proof (r_rw_while_prt_inv _ _ _ _ _ r1 r2 _ _ X) as [I [θ [[[m1 m2] m3] m4]]].
      exists (fun x => I (tt, tedious_prod_sem _ _ x)).
      exists (θ).
      repeat split; auto.
      intros x h.
      apply m1.
      induction H5.
      exact h.
      intros x h.
      induction H6.
      apply m2.
      exact h.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a m3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold rw_to_ro_pre.
      unfold rw_to_ro_pre in h2.
      simpl in h2.
      simpl.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply r_admissible_move_rw_prt in m4.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a m4);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold ro_to_rw_pre, fst_app, snd_app.
      simpl.
      
      unfold ro_to_rw_pre in h2.
      destruct h1; auto.
      destruct h2; auto.      
    }
Defined.

Definition app_nil_r := 
fun (A : Type) (l : list A) =>
list_ind (fun l0 : list A => l0 ++ nil = l0)
  ((let H : A = A := eq_refl in (fun _ : A = A => eq_refl) H) : nil ++ nil = nil)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ nil = l0) =>
   (let H : l0 ++ nil = l0 := IHl in
    (let H0 : a = a := eq_refl in
     (let H1 : A = A := eq_refl in
      (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ nil = l0) =>
       eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ nil)) eq_refl) (f_equal (cons a) H4)) H1) H0) H)
   :
   (a :: l0) ++ nil = a :: l0) l.

Arguments app_nil_r [A]%type_scope l%list_scope.

(* Lemma tmp_eq_tr' : forall Γ Δ h2, tr (fun a : ro_ctx => sem_ro_ctx a) (eq_sym (app_nil_r (Δ ++ Γ))) h2 = (h2 ; tt). Admitted. *)
Fixpoint r_rw_while_tot_inv {Γ Δ} {e c} {w : Γ ;;; Δ ||- (WHILE e DO c END) : UNIT}
         (we : (Δ ++ Γ) |- e : BOOL)
         (wc : (Γ ++ Δ) ;;; Δ ||- c : UNIT) {ϕ} {ψ} (p : w ||~ [{ϕ}] (WHILE e DO c END) [{ψ}]) {struct p} :
  {I & {θ & {V & 
               (ϕ ->> I) * ((I /\\ ro_to_rw_pre (θ false)) ->> ψ tt) *
                 (we |~ [{rw_to_ro_pre I}] e [{θ}]) *
                 (wc ||~ [{fun x => ro_to_rw_pre (θ true) (fst x, fst_app (snd x)) /\ fst x = snd_app (snd x)}]
                    c
                    [{_ | fun x => I (fst x, fst_app (snd x)) /\ V x}])
               * (forall δ γ,
                     I (δ, γ) -> ~ (exists f : nat -> sem_ro_ctx Δ, f 0 = δ /\ (forall n : nat, V (f (S n), (γ; f n)))))

  } } }%type
with r_ro_while_tot_inv {Γ Δ} {e c} {w0 : (Δ ++ Γ) |- (WHILE e DO c END) : UNIT}
                        (we : (Δ ++ Γ) |- e : BOOL)
                        (* (wc : Γ  ;;; Δ ||- c : UNIT) *)
                        (wc : (Γ ++ Δ) ;;; Δ ||- c : UNIT)
                        {ϕ0} {ψ0} (p : w0 |~ [{ϕ0}] (WHILE e DO c END) [{ψ0}]) {struct p} :
  let ϕ := (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ0 (tedious_prod_sem Δ Γ γδ)) in
  let ψ := (fun (v : unit) (γδ : sem_ro_ctx Δ * sem_ro_ctx Γ) => ψ0 v (tedious_prod_sem Δ Γ γδ)) in
  {I : sem_ro_ctx Δ * sem_ro_ctx Γ -> Prop &
  {θ : bool -> sem_ro_ctx (Δ ++ Γ) -> Prop &
  {V : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) -> Prop &
  ((ϕ ->> I) * ((I /\\ ro_to_rw_pre (θ false)) ->> ψ tt) * (we |~ [{rw_to_ro_pre I}] e [{y | θ y}]) *
   (wc
    ||~ [{(fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) =>
           ro_to_rw_pre (θ true) (fst x, fst_app (snd x)) /\ fst x = snd_app (snd x))}] c [{_
    | (fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => I (fst x, fst_app (snd x)) /\ V x)}]) *
   (forall (δ : sem_ro_ctx Δ) (γ : sem_ro_ctx Γ),
    I (δ, γ) -> ~ (exists f : nat -> sem_ro_ctx Δ, f 0 = δ /\ (forall n : nat, V (f (S n), (γ; f n))))))%type } } }.
Proof.
  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H7.    

      pose proof (r_rw_while_tot_inv _ _ _ _ _ we wc _ _ X) as [I [θ [V [[[[m1 m2] m3] m4] m5]]]].
      exists I.
      exists θ.
      exists V.
      repeat split; auto.
      intros x q.
      apply m1.
      induction H5.
      apply H6.
      exact q.
      intros q [h1 h2].
      induction H7.
      apply H8.
      apply m2.
      split; auto.
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.    
      induction H6.
      induction H7.
      apply (r_ro_while_tot_inv _ _ _ _ w0 we wc _ _ X).
    }

    {
      repeat apply projT2_eq in H2.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.
      exists ϕ.
      exists θ.
      exists ψ0.
      repeat split; (try intros h1 h2; auto); auto.
      induction H7.
      induction H6.
      exact h2.
      induction H6.
      apply (r_proves_ro_tot_typing_irrl X).
      induction H6.
      apply (r_proves_rw_tot_typing_irrl X0).
      induction H6.
      apply H5.
    }

  +    
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H6.
      pose proof (r_ro_while_tot_inv _ _ _ _ _ we wc _ _ X) as [I [θ [V [[[[m1 m2] m3] m4] m5]]]].
      exists I.
      exists θ.
      exists V.
      repeat split; auto.
      induction H4.
      intros x h.
      apply m1.
      apply H5.
      exact h.

      induction H6.
      intros x h.
      apply H7.
      apply m2.
      exact h.
    }
   
    {
      repeat apply projT2_eq in H3.
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      pose proof (has_type_rw_While_inverse w) as [r1 r2].
      rewrite (app_nil_end (Δ ++ Γ))  in r2.
      pose proof (r_rw_while_tot_inv _ _ _ _ _ r1 r2 _ _ X) as [I [θ [V [[[[m1 m2] m3] m4] m5]]]].
      exists (fun x => I (tt, tedious_prod_sem _ _ x)).
      exists (fun y x => θ y x /\ y = false).
      exists (fun _ => False).
      repeat split; auto.
      intros x h.
      apply m1.
      induction H5.
      exact h.
      intros x h.
      induction H6.
      destruct h.
      apply m2.
      split; auto.
      destruct H6.
      unfold ro_to_rw_pre.
      exact H6.

      simpl in r1.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a m3);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      simpl in h2.
      unfold rw_to_ro_pre in h2.
      unfold rw_to_ro_pre.
      simpl.
      rewrite tedious_equiv_3 in h2.
      exact h2.
      apply r_proves_rw_tot_proves_rw_tot in m4.
      apply proves_rw_tot_sound in m4.
      simpl in h2.
      pose proof (m4 (tedious_prod_sem (Δ ++ Γ) nil (h2, tt))).

      simpl in H2.
      intro.
      destruct h1.
      
      destruct (H2 tt).
      unfold ro_to_rw_pre.
      rewrite tedious_equiv_fst.
      simpl.
      split; auto.
      destruct tt; rewrite tedious_equiv_snd; auto.
      

      apply pdom_neg_is_empty_to_evidence in H8 as [t1 t2].
      pose proof (H9 _ t2).
      destruct H8.
      destruct H8.
      destruct H10.
      destruct x.
      destruct u, u0.
      simpl in H10, H11.
      rewrite tedious_equiv_fst in H10.
      pose proof (m5 tt h2 H10).
      contradict H12.
      exists (fun _ => tt).
      split; auto.
      split; auto.

      assert (  wc
  ||~ [{(fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) =>
         False)}] c [{_
  | (fun x : sem_ro_ctx Δ * sem_ro_ctx (Γ ++ Δ) => I (tt, (fst x; fst_app (snd x))) /\ False)}]).
      apply r_admissible_rw_exfalso_tot.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      unfold ro_to_rw_pre in h2.
      destruct h2.
      destruct H2.
      contradict H8; discriminate.
      

      intros.
      destruct (lem ((exists f : nat -> sem_ro_ctx Δ, f 0 = δ /\ (nat -> False)))); auto.
      destruct H7.
      destruct H7.
      contradict (H8 0).
    }
Defined.    

Fixpoint r_rw_new_var_prt_inv {Γ Δ} {e c} {τ σ} {w : Γ ;;; Δ ||- (NEWVAR e IN c) : τ}
         (we : (Δ ++ Γ) |- e : σ)
         (wc : Γ ;;; (σ :: Δ) ||- c : τ) {ϕ} {ψ} (p : w ||~ {{ϕ}} (NEWVAR e IN c) {{ψ}}) {struct p} :
  {θ &
     (we |~ {{(fun x => ϕ (tedious_sem_app Δ Γ x))}} e {{y | θ y}}) *
       (wc ||~ {{(fun x => θ (fst (fst x)) (snd (fst x); snd x))}} c {{fun y x => ψ y (snd (fst x), snd x)}}) }%type
with r_ro_new_var_prt_inv {Γ Δ} {e c} {τ σ} {w0 : (Δ ++ Γ) |- (NEWVAR e IN c) : τ}
         (we : (Δ ++ Γ) |- e : σ)
         (wc : Γ ;;; (σ :: Δ) ||- c : τ) {ϕ0} {ψ0} (p : w0 |~ {{ϕ0}} (NEWVAR e IN c) {{ψ0}}) {struct p} :
  let ϕ := (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ0 (tedious_prod_sem Δ Γ γδ)) in
  let ψ := (fun (v : sem_datatype τ) (γδ : sem_ro_ctx Δ * sem_ro_ctx Γ) => ψ0 v (tedious_prod_sem Δ Γ γδ)) in
  {θ : sem_datatype σ -> sem_ro_ctx (Δ ++ Γ) -> Prop &
  ((we |~ {{(fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ x))}} e {{y | θ y}}) *
   (wc ||~ {{(fun x : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst x)) (snd (fst x); snd x))}} c {{y
    | (fun x : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => ψ y (snd (fst x), snd x))}}))%type}.
Proof.
  +
    inversion p.
    {
      repeat apply projT2_eq in H;
        repeat apply projT2_eq in H0;
        repeat apply projT2_eq in H5;
        repeat apply projT2_eq in H7.

      pose proof (r_rw_new_var_prt_inv _ _ _ _ _ _ _ we wc _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H6.
      induction H5.
      exact h2.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a t2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      induction H7.
      apply H8.
      exact H9.
    }
    
    {
      repeat apply projT2_eq in H4;
      repeat apply projT2_eq in H5;
      repeat apply projT2_eq in H6;
      repeat apply projT2_eq in H7.
      induction H6.
      induction H7.
      apply (r_ro_new_var_prt_inv _ _ _ _ _ _ w0 we wc _ _ X).
    }
    
    {
      repeat apply projT2_eq in H5;
      repeat apply projT2_eq in H6;
      repeat apply projT2_eq in H7;
      repeat apply projT2_eq in H8.
      induction (has_type_ro_unambiguous _ _ _ _ we w1).
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H7.
      exact h2.
      apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H8.
      intro x; exact x.      
    }

    +
      inversion p.
      {
        repeat apply projT2_eq in H;
        repeat apply projT2_eq in H0;
        repeat apply projT2_eq in H4;
        repeat apply projT2_eq in H6.
        pose proof (r_ro_new_var_prt_inv _ _ _ _ _ _ _ we wc _ _ X) as [θ [t1 t2]].
        exists θ.
        split.
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply H5.
        induction H4.
        exact h2.
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a t2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        intro.
        induction H6.
        apply H7.
        exact H8.
      }

      {
        repeat apply projT2_eq in H3;
        repeat apply projT2_eq in H4;
        repeat apply projT2_eq in H5;
        repeat apply projT2_eq in H6.
        pose proof (has_type_rw_Newvar_inverse w) as [σ' [r1 r2]].
        induction (has_type_ro_unambiguous _ _ _ _ we r1).        
        pose proof (r_rw_new_var_prt_inv _ _ _ _ _ _ _ r1 r2 _ _ X) as [θ [t1 t2]].
        exists θ.
        split.
        apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        induction H5.
        simpl.
        rewrite tedious_equiv_3 in h2.
        exact h2.
        apply r_admissible_move_rw_prt in t2.
        apply (fun a => r_rw_imply_prt _ _ _ _ _ _ _ _ _ _ a t2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h1.
        simpl.
        simpl in h2.
        destruct s.
        simpl.
        simpl in h2.
        simpl in s1.
        unfold snd_app; simpl.
        exact h2.
        destruct h2.
        destruct s.
        simpl.
        unfold snd_app; simpl.
        induction H6.
        intro x; exact x.
      }
Defined.

Fixpoint r_rw_new_var_tot_inv {Γ Δ} {e c} {τ σ} {w : Γ ;;; Δ ||- (NEWVAR e IN c) : τ}
         (we : (Δ ++ Γ) |- e : σ)
         (wc : Γ ;;; (σ :: Δ) ||- c : τ) {ϕ} {ψ} (p : w ||~ [{ϕ}] (NEWVAR e IN c) [{ψ}]) {struct p} :
  {θ &
     (we |~ [{(fun x => ϕ (tedious_sem_app Δ Γ x))}] e [{y | θ y}]) *
       (wc ||~ [{(fun x => θ (fst (fst x)) (snd (fst x); snd x))}] c [{fun y x => ψ y (snd (fst x), snd x)}]) }%type
with r_ro_new_var_tot_inv {Γ Δ} {e c} {τ σ} {w0 : (Δ ++ Γ) |- (NEWVAR e IN c) : τ}
         (we : (Δ ++ Γ) |- e : σ)
         (wc : Γ ;;; (σ :: Δ) ||- c : τ) {ϕ0} {ψ0} (p : w0 |~ [{ϕ0}] (NEWVAR e IN c) [{ψ0}]) {struct p} :
  let ϕ := (fun γδ : sem_ro_ctx Δ * sem_ro_ctx Γ => ϕ0 (tedious_prod_sem Δ Γ γδ)) in
  let ψ := (fun (v : sem_datatype τ) (γδ : sem_ro_ctx Δ * sem_ro_ctx Γ) => ψ0 v (tedious_prod_sem Δ Γ γδ)) in
  {θ : sem_datatype σ -> sem_ro_ctx (Δ ++ Γ) -> Prop &
  ((we |~ [{(fun x : sem_ro_ctx (Δ ++ Γ) => ϕ (tedious_sem_app Δ Γ x))}] e [{y | θ y}]) *
   (wc ||~ [{(fun x : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => θ (fst (fst x)) (snd (fst x); snd x))}] c [{y
    | (fun x : sem_ro_ctx (σ :: Δ) * sem_ro_ctx Γ => ψ y (snd (fst x), snd x))}]))%type}.
Proof.
  +
    inversion p.
    {
      repeat apply projT2_eq in H;
        repeat apply projT2_eq in H0;
        repeat apply projT2_eq in H5;
        repeat apply projT2_eq in H7.

      pose proof (r_rw_new_var_tot_inv _ _ _ _ _ _ _ we wc _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      apply H6.
      induction H5.
      exact h2.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a t2);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intro.
      induction H7.
      apply H8.
      exact H9.
    }
    
    {
      repeat apply projT2_eq in H4;
      repeat apply projT2_eq in H5;
      repeat apply projT2_eq in H6;
      repeat apply projT2_eq in H7.
      induction H6.
      induction H7.
      apply (r_ro_new_var_tot_inv _ _ _ _ _ _ w0 we wc _ _ X).
    }
    
    {
      repeat apply projT2_eq in H5;
      repeat apply projT2_eq in H6;
      repeat apply projT2_eq in H7;
      repeat apply projT2_eq in H8.
      induction (has_type_ro_unambiguous _ _ _ _ we w1).
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H7.
      exact h2.
      apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a X0);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      induction H8.
      intro x; exact x.      
    }

    +
      inversion p.
      {
        repeat apply projT2_eq in H;
        repeat apply projT2_eq in H0;
        repeat apply projT2_eq in H4;
        repeat apply projT2_eq in H6.
        pose proof (r_ro_new_var_tot_inv _ _ _ _ _ _ _ we wc _ _ X) as [θ [t1 t2]].
        exists θ.
        split.
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        apply H5.
        induction H4.
        exact h2.
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a t2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        intro.
        induction H6.
        apply H7.
        exact H8.
      }

      {
        repeat apply projT2_eq in H3;
        repeat apply projT2_eq in H4;
        repeat apply projT2_eq in H5;
        repeat apply projT2_eq in H6.
        pose proof (has_type_rw_Newvar_inverse w) as [σ' [r1 r2]].
        induction (has_type_ro_unambiguous _ _ _ _ we r1).        
        pose proof (r_rw_new_var_tot_inv _ _ _ _ _ _ _ r1 r2 _ _ X) as [θ [t1 t2]].
        exists θ.
        split.
        apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        induction H5.
        simpl.
        rewrite tedious_equiv_3 in h2.
        exact h2.
        apply r_admissible_move_rw_tot in t2.
        apply (fun a => r_rw_imply_tot _ _ _ _ _ _ _ _ _ _ a t2);
          try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
        destruct h1.
        simpl.
        simpl in h2.
        destruct s.
        simpl.
        simpl in h2.
        simpl in s1.
        unfold snd_app; simpl.
        exact h2.
        destruct h2.
        destruct s.
        simpl.
        unfold snd_app; simpl.
        induction H6.
        intro x; exact x.
      }
Defined.

Lemma update'_typing_irrl {Γ Δ} {e} {k} {τ} (w1 w2 : (Δ ++ Γ) |- e : τ) (w1' w2' : Γ ;;; Δ ||- (LET k := e) : UNIT) :
  forall δ x, update' w1 w1' δ x = update' w2 w2' δ x.
Proof.
  intros.
  unfold update'.
  apply lp.
  apply assignable_unique.
Defined.
  
Fixpoint r_rw_assign_prt_inv {Γ Δ} {e} {k} {τ} {w : Γ ;;; Δ ||- (LET k := e) : UNIT}
         (we : (Δ ++ Γ) |- e : τ) {ϕ} {ψ} (p : w ||~ {{ϕ}} (LET k := e) {{ψ}}) {struct p} :
  {θ & (we |~ {{(fun x => ϕ (tedious_sem_app Δ Γ x))}} e {{θ}}) *
         (forall x γ δ, θ x (δ; γ) -> ψ tt (update' we w δ x, γ))}%type.
Proof.
  +
    dependent destruction p.
    {
      pose proof (r_rw_assign_prt_inv _ _ _ _ _ _ we _ _ p) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      rewrite (update'_typing_irrl we we w w0).
      apply a0.
      apply t2.
      exact H.
    }
    
    {
      contradict (ro_assign_absurd _ _ _ w0).
    }
    
    {
      induction (has_type_ro_unambiguous _ _ _ _ we w0).
      exists θ.
      split.
      apply (fun a => r_ro_imply_prt _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      intros.
      rewrite (update'_typing_irrl we w0 w w).
      apply ψ1.
      exact H.
    }
Defined.

Fixpoint r_rw_assign_tot_inv {Γ Δ} {e} {k} {τ} {w : Γ ;;; Δ ||- (LET k := e) : UNIT}
         (we : (Δ ++ Γ) |- e : τ) {ϕ} {ψ} (p : w ||~ [{ϕ}] (LET k := e) [{ψ}]) {struct p} :
  {θ & (we |~ [{(fun x => ϕ (tedious_sem_app Δ Γ x))}] e [{θ}]) *
         (forall x γ δ, θ x (δ; γ) -> ψ tt (update' we w δ x, γ))}%type.
Proof.
  +
    dependent destruction p.
    {
      pose proof (r_rw_assign_tot_inv _ _ _ _ _ _ we _ _ p) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).
      intros.
      rewrite (update'_typing_irrl we we w w0).
      apply a0.
      apply t2.
      exact H.
    }
    
    {
      contradict (ro_assign_absurd _ _ _ w0).
    }
    
    {
      induction (has_type_ro_unambiguous _ _ _ _ we w0).
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a r);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      intros.
      rewrite (update'_typing_irrl we w0 w w).
      apply ψ1.
      exact H.
    }
Defined.


Fixpoint r_ro_lim_prt_inv {Γ} {e} {w : Γ |- (Lim e) : REAL}
         (we : (INTEGER :: Γ) |- e : REAL) {ϕ} {ψ} (p : w |~ {{ϕ}} (Lim e) {{ψ}}) {struct p} :
  {θ & (we |~ [{(fun γ' : sem_ro_ctx (INTEGER :: Γ) => ϕ (snd γ'))}] e [{y | θ y}]) *
       (forall γ, ϕ γ ->
                  exists y : R,
                    ψ y γ /\
                      (forall x z , θ z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x))%R)}%type
with r_rw_lim_prt_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (Lim e) : REAL}
         (we : (INTEGER :: (Δ ++ Γ)) |- e : REAL) {ϕ} {ψ} (p : w ||~ {{ϕ}} (Lim e) {{ψ}}) {struct p} : 
  let ϕ' := fun x => ϕ (tedious_sem_app _ _ x) in
  let ψ' := fun y x => ψ y (tedious_sem_app _ _ x) in
  {θ  & ((we |~ [{(fun γ' => ϕ' (snd γ'))}] e [{y | θ y}]) *
             (forall γ,
                 ϕ' γ ->
                 exists y : R,
                   ψ' y γ /\
                     (forall x z, θ z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x))%R))}%type.
Proof.
  +
    simple inversion p;
      try (contradict H0; discriminate).
    (* try (induction (eq_sym H)); *)
    (* try (induction (eq_sym H0)); *)
    (* try (induction (eq_sym H1)); *)
    (* try (induction (eq_sym H2)); *)
    (* try (induction (eq_sym H3)).  *)
    {
      use_eq_r H1.
      use_eq_r H2.
      use_eq_r H3.
      repeat apply projT2_eq in H4.
      use_eq_l H4.
      repeat apply projT2_eq in H5.
      injection H5.
      intros.

      pose proof (r_ro_lim_prt_inv _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      apply H1.
      induction H0.
      exact h2.

      intros.
      induction H0.
      apply H1 in H3.
      pose proof (t2 γ H3) as [y [a b]].
      exists y.
      split.
      induction H.
      apply H2.
      exact a.
      exact b.    
    }

    {
      intros.
      use_eq_r H.
      use_eq_r H1.
      use_eq_r H0.    
      repeat apply projT2_eq in H2.
      use_eq_r H2.
      repeat apply projT2_eq in H3.
      injection H3; intros.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_lim_prt_inv _ nil _ _ we _ _ X).    
    }

    {
      intros.
      use_eq_r H0.
      injection H1.
      intro.
      clear H1.
      use_eq_r H0.
      repeat apply projT2_eq in H3.
      use_eq_r H3.
      repeat apply projT2_eq in H4.
      injection H4; intros.
      use_eq_r H0.
      use_eq_r H1.
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      exact H.
    }
  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H7.
      pose proof (r_rw_lim_prt_inv _ _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      apply H6.
      induction H5.
      exact h2.
      intros.
      induction H5.
      apply H6 in H9.
      pose proof (t2 _ H9) as [y [a b]].
      exists y.
      split.
      induction H7.
      apply H8.
      exact a.
      exact b.
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.
      induction H6.
      induction H7.
      pose proof (r_ro_lim_prt_inv _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      rewrite tedious_equiv_3 in h2.
      exact h2.
      intros.
      pose proof (t2 _ H3) as [y [a b]].
      exists y.
      split; auto.
      intros.
      apply b.
      rewrite tedious_equiv_3.
      exact H6.
    }      
Defined.

Fixpoint r_ro_lim_tot_inv {Γ} {e} {w : Γ |- (Lim e) : REAL}
         (we : (INTEGER :: Γ) |- e : REAL) {ϕ} {ψ} (p : w |~ [{ϕ}] (Lim e) [{ψ}]) {struct p} :
  {θ & (we |~ [{(fun γ' : sem_ro_ctx (INTEGER :: Γ) => ϕ (snd γ'))}] e [{y | θ y}]) *
       (forall γ, ϕ γ ->
                  exists y : R,
                    ψ y γ /\
                      (forall x z , θ z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x))%R)}%type
with r_rw_lim_tot_inv {Γ Δ} {e} {w : Γ ;;; Δ ||- (Lim e) : REAL}
         (we : (INTEGER :: (Δ ++ Γ)) |- e : REAL) {ϕ} {ψ} (p : w ||~ [{ϕ}] (Lim e) [{ψ}]) {struct p} : 
  let ϕ' := fun x => ϕ (tedious_sem_app _ _ x) in
  let ψ' := fun y x => ψ y (tedious_sem_app _ _ x) in
  {θ  & ((we |~ [{(fun γ' => ϕ' (snd γ'))}] e [{y | θ y}]) *
             (forall γ,
                 ϕ' γ ->
                 exists y : R,
                   ψ' y γ /\
                     (forall x z, θ z (x, γ) -> Rabs (z - y) < powerRZ 2 (- x))%R))}%type.
Proof.
  +
    simple inversion p;
      try (contradict H0; discriminate).
    (* try (induction (eq_sym H)); *)
    (* try (induction (eq_sym H0)); *)
    (* try (induction (eq_sym H1)); *)
    (* try (induction (eq_sym H2)); *)
    (* try (induction (eq_sym H3)).  *)
    {
      use_eq_r H1.
      use_eq_r H2.
      use_eq_r H3.
      repeat apply projT2_eq in H4.
      use_eq_l H4.
      repeat apply projT2_eq in H5.
      injection H5.
      intros.

      pose proof (r_ro_lim_tot_inv _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      apply H1.
      induction H0.
      exact h2.

      intros.
      induction H0.
      apply H1 in H3.
      pose proof (t2 γ H3) as [y [a b]].
      exists y.
      split.
      induction H.
      apply H2.
      exact a.
      exact b.    
    }

    {
      intros.
      use_eq_r H.
      use_eq_r H1.
      use_eq_r H0.    
      repeat apply projT2_eq in H2.
      use_eq_r H2.
      repeat apply projT2_eq in H3.
      injection H3; intros.
      use_eq_l H.
      use_eq_l H0.
      apply (r_rw_lim_tot_inv _ nil _ _ we _ _ X).    
    }

    {
      intros.
      use_eq_r H0.
      injection H1.
      intro.
      clear H1.
      use_eq_r H0.
      repeat apply projT2_eq in H3.
      use_eq_r H3.
      repeat apply projT2_eq in H4.
      injection H4; intros.
      use_eq_r H0.
      use_eq_r H1.
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a X);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      exact H.
    }
  +
    inversion p.
    {
      repeat apply projT2_eq in H.
      repeat apply projT2_eq in H0.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H7.
      pose proof (r_rw_lim_tot_inv _ _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      apply H6.
      induction H5.
      exact h2.
      intros.
      induction H5.
      apply H6 in H9.
      pose proof (t2 _ H9) as [y [a b]].
      exists y.
      split.
      induction H7.
      apply H8.
      exact a.
      exact b.
    }

    {
      repeat apply projT2_eq in H4.
      repeat apply projT2_eq in H5.
      repeat apply projT2_eq in H6.
      repeat apply projT2_eq in H7.
      induction H6.
      induction H7.
      pose proof (r_ro_lim_tot_inv _ _ _ we _ _ X) as [θ [t1 t2]].
      exists θ.
      split.
      apply (fun a => r_ro_imply_tot _ _ _ _ _ _ _ _ _ a t1);
        try (intros h1 h2; auto); try (intros h1 h2 h3; auto).      
      rewrite tedious_equiv_3 in h2.
      exact h2.
      intros.
      pose proof (t2 _ H3) as [y [a b]].
      exists y.
      split; auto.
      intros.
      apply b.
      rewrite tedious_equiv_3.
      exact H6.
    }      
Defined.

