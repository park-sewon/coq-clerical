Require Import List.
Require Import Coq.Program.Equality.
From Clerical.Preliminaries Require Import Preliminaries.
Require Import Clerical.Syntax.
Require Import Clerical.Typing.

(* In this file, we prove various properties regarding the type system of Clerical. The main theorem here is that the typing rules are unambiguous in the sense that when Γ |- e : τ and Γ |- e : σ, τ = σ. Similarly, we prove that when Γ ;;; Δ ||- e : τ and Γ ;;; Δ ||- e : σ, τ = σ.

The difficulty in proving this is that using our typing rules, well-typednesses are not unique becuase of readonly-readwrite and readwrite-readonly rules. For a well-typedness, there can be a derivation of it of arbitrary depth.

We define a restricted type system that restricts the readonly-readwrite and readwrtie-readonly jumps by depth 1. Denoting the restricted judgement by Γ |~ e : τ and Γ ;;; Δ ||~ e : τ, we prove by recursion that 

Γ |~ e : τ <-> Γ |~ e : τ
and 
Γ ;;; Δ ||~ e : τ <-> Γ ;;; Δ ||~ e : τ.

Then, we transfer the desired unambiguity by the unambiguity of the restricted typing rules. *)

Fixpoint ro_assign_absurd Γ k e (w : Γ |- Assign k e : DUnit) : False.
Proof.
  inversion w.
  inversion H.
  simpl in H7.
  apply (ro_assign_absurd Γ k e H7) .
  contradict H6.
  intro.
  inversion H6.
Defined.

Lemma assignable_push_back Γ Δ k τ (t : assignable Γ k τ) : assignable (Γ ++ Δ) k τ.
Proof.
  induction t.
  simpl.
  constructor.
  constructor.
  exact IHt.
Defined.

Fixpoint has_type_rw_CaseList_nil_absurd Γ Δ τ (w : Γ ;;; Δ ||- CaseList nil : τ) : False.
Proof.
  
  dependent destruction w.
  dependent destruction h.
  apply (has_type_rw_CaseList_nil_absurd _ _ _ h); auto.
  contradict l0.
  simpl; apply PeanoNat.Nat.nle_succ_0.
Qed.

Lemma assignable_absurd k τ (a : assignable nil τ k) : False.
Proof.
  inversion a.
Defined.

Fixpoint has_type_rw_Assign_absurd Γ k e (w : Γ ;;; nil ||- Assign k e : DUnit) : False.
Proof.
  dependent destruction w.
  dependent destruction h.
  apply (has_type_rw_Assign_absurd _ _ _ h).
  apply (assignable_absurd k τ a); auto.
Defined.


Fixpoint assignable_unique Δ τ n (a1 a2 : assignable Δ τ n) : a1 = a2.
Proof.
  dependent destruction a1;
    dependent destruction a2; try reflexivity.
  rewrite (assignable_unique _ _ _ a1 a2).
  reflexivity.
Qed.


Reserved Notation " Γ |~ t : T " (at level 50, t, T at next level). 
Reserved Notation " Γ ;;; Δ ||~ t : T " (at level 50, Δ, t, T at next level). 


Section RestrictedTyping.

  Inductive r_has_type_ro : ro_ctx -> exp -> datatype -> Type :=
  (* from readwrite *)
  | r_has_type_ro_rw_Seq : forall Γ c1 c2 τ, Γ ;;; nil ||~ (c1 ;; c2) : τ -> Γ |~ (c1 ;; c2) : τ 

  | r_has_type_ro_rw_Assign : forall Γ e k, Γ ;;; nil ||~ (Assign k e) : DUnit -> Γ |~ (Assign k e) : DUnit
                                                                                                        
  | r_has_type_ro_rw_Newvar : forall Γ e c τ, Γ ;;; nil ||~ (Newvar e c) : τ -> Γ |~ (Newvar e c) : τ

  | r_has_type_ro_rw_Cond : forall Γ e c1 c2 τ, Γ ;;; nil ||~ (Cond e c1 c2) : τ -> Γ |~ (Cond e c1 c2) : τ

  | r_has_type_ro_rw_Case : forall Γ e1 c1 e2 c2 τ,
      Γ ;;; nil ||~ (Case e1 c1 e2 c2) : τ -> Γ |~ (Case e1 c1 e2 c2) : τ

  | r_has_type_ro_rw_CaseList : forall Γ l τ,
      Γ ;;; nil ||~ CaseList l : τ -> Γ |~ (CaseList l) : τ
                                                            
  | r_has_type_ro_rw_While : forall Γ e c, Γ ;;; nil ||~ (While e c) : DUnit -> Γ |~ (While e c) : DUnit
                                                                                                     
  (* variables *)
  | r_has_type_ro_Var_0 : forall Γ τ,  ((τ :: Γ) |~ (VAR 0) : τ)
  | r_has_type_ro_Var_S : forall Γ σ τ k, Γ |~ Var k : τ -> (σ :: Γ) |~ VAR (S k) : τ

  (* constants *)
  | r_has_type_ro_True : forall Γ, Γ |~ TRUE : DBoolean
  | r_has_type_ro_False : forall Γ, Γ |~ FALSE : DBoolean
  | r_has_type_ro_Skip : forall Γ, Γ |~ SKIP : DUnit
  | r_has_type_ro_Int : forall Γ k, Γ |~ INT k : DInteger

  (* unary ops *)
  | r_has_type_ro_OpRrecip : forall Γ e, Γ |~ e : DReal -> Γ |~ (UniOp OpRrecip e) : DReal
  | r_has_type_ro_OpZRcoerce : forall Γ e, Γ |~ e : DInteger -> Γ |~ (UniOp OpZRcoerce e) : DReal
  | r_has_type_ro_OpZRexp : forall Γ e, Γ |~ e : DInteger -> Γ |~ (UniOp OpZRexp e) : DReal

  (* binary ops *)
  | r_has_type_ro_OpZplus : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZplus e1 e2) : DInteger
  | r_has_type_ro_OpZminus : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZminus e1 e2) : DInteger
  | r_has_type_ro_OpZmult : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZmult e1 e2) : DInteger
  | r_has_type_ro_OpZlt : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZlt e1 e2) : DBoolean
  | r_has_type_ro_OpZeq : forall Γ e1 e2, Γ |~ e1 : DInteger -> Γ |~ e2 : DInteger -> Γ |~ (BinOp OpZeq e1 e2) : DBoolean 
  | r_has_type_ro_OpRplus : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRplus e1 e2) : DReal
  | r_has_type_ro_OpRminus : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRminus e1 e2) : DReal
  | r_has_type_ro_OpRmult : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRmult e1 e2) : DReal
  | r_has_type_ro_OpRlt : forall Γ e1 e2, Γ |~ e1 : DReal -> Γ |~ e2 : DReal -> Γ |~ (BinOp OpRlt e1 e2) : DBoolean

  (* limit *)
  | r_has_type_ro_Lim : forall Γ e, (DInteger :: Γ) |~ e : DReal -> Γ |~ Lim e : DReal
                                                                                   
  with r_has_type_rw : rw_ctx -> exp -> datatype -> Type :=
  (* from readonly *)
  | r_has_type_rw_ro_Var :
    forall Γ Δ k τ,
      (Δ ++ Γ) |~ Var k : τ -> Γ ;;; Δ ||~ Var k : τ
  | r_has_type_rw_ro_Boolean :
    forall Γ Δ b,
      (Δ ++ Γ) |~ Boolean b : DBoolean -> Γ ;;; Δ ||~ Boolean b : DBoolean
  | r_has_type_rw_ro_Integer :
    forall Γ Δ k,
      (Δ ++ Γ) |~ Integer k : DInteger -> Γ ;;; Δ ||~ Integer k : DInteger
  | r_has_type_rw_ro_BinOp :
    forall Γ Δ e1 e2 τ op,
      (Δ ++ Γ) |~ BinOp op e1 e2 : τ -> Γ ;;; Δ ||~ BinOp op e1 e2 : τ
  | r_has_type_rw_ro_UniOp :
    forall Γ Δ e τ op,
      (Δ ++ Γ) |~ UniOp op e : τ -> Γ ;;; Δ ||~ UniOp op e : τ
  | r_has_type_rw_ro_Skip :
    forall Γ Δ ,
      (Δ ++ Γ) |~ Skip : DUnit -> Γ ;;; Δ ||~ Skip : DUnit
                                                       
  | r_has_type_rw_ro_Lim :
    forall Γ Δ  e,
      (Δ ++ Γ) |~ Lim e : DReal -> Γ ;;; Δ ||~ Lim e : DReal

  (* sequential *)
  | r_has_type_rw_Seq : forall Γ Δ c1 c2 τ, Γ ;;; Δ ||~ c1 : DUnit -> Γ;;; Δ ||~ c2 : τ -> Γ ;;; Δ ||~ (Seq c1 c2) : τ 
                                                                                                                       
  (* assignment *)
  | r_has_type_rw_Assign : forall Γ Δ e τ k, assignable Δ τ k -> (Δ ++ Γ) |~ e : τ -> Γ ;;; Δ ||~ Assign k e : DUnit

  (* newvar *)
  | r_has_type_rw_Newvar : forall Γ Δ e c σ τ, (Δ ++ Γ) |~ e : σ -> Γ ;;; σ :: Δ ||~ c : τ -> Γ ;;; Δ ||~ Newvar e c : τ

  (* cond *)
  | r_has_type_rw_Cond : forall Γ Δ e c1 c2 τ, (Δ ++ Γ) |~ e : DBoolean -> Γ ;;; Δ ||~ c1 : τ -> Γ ;;; Δ ||~ c2 : τ -> Γ ;;; Δ ||~ Cond e c1 c2 : τ

  (* case *)
  | r_has_type_rw_Case : forall Γ Δ e1 c1 e2 c2 τ, (Δ ++ Γ) |~ e1 : DBoolean -> Γ ;;; Δ ||~ c1 : τ -> (Δ ++ Γ) |~ e2 : DBoolean -> Γ ;;; Δ ||~ c2 : τ -> Γ ;;; Δ ||~ Case e1 c1 e2 c2 : τ

  | r_has_type_rw_CaseList : forall Γ Δ l τ,
      (1 <= length l)%nat -> 
      ForallT (fun ec => ((Δ ++ Γ) |~ fst ec : DBoolean) * (Γ ;;; Δ ||~ snd ec : τ))%type l ->
      Γ ;;; Δ ||~ CaseList l : τ
                                 
  (* while *)
  | r_has_type_rw_While : forall Γ Δ e c, (Δ ++ Γ) |~ e : DBoolean -> Γ ;;; Δ ||~ c : DUnit -> Γ ;;; Δ ||~ While e c : DUnit
                                                                                                                         
                                                                                                                         
  where " Γ |~ c : τ " := (r_has_type_ro Γ c τ) and " Γ ;;; Δ ||~ c : τ " := (r_has_type_rw (mk_rw_ctx Γ Δ) c τ).


  Fixpoint r_has_type_rw_move Γ Δ1 Δ2 e τ (w : (Δ2 ++ Γ) ;;; Δ1 ||~ e : τ) {struct w}: Γ ;;; (Δ1 ++ Δ2) ||~ e : τ.
  Proof.
    inversion w.
    apply r_has_type_rw_ro_Var; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply r_has_type_rw_ro_Boolean; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply r_has_type_rw_ro_Integer; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply r_has_type_rw_ro_BinOp; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply r_has_type_rw_ro_UniOp; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply r_has_type_rw_ro_Skip; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply r_has_type_rw_ro_Lim; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    pose proof (r_has_type_rw_move _ _ _ _ _ H1).
    pose proof (r_has_type_rw_move _ _ _ _ _ H4).
    apply r_has_type_rw_Seq; auto.
    apply (r_has_type_rw_Assign _ _ _ τ0).
    apply assignable_push_back; auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    apply (r_has_type_rw_Newvar _ _ _ _ σ); auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    replace ((σ :: Δ1 ++ Δ2)) with ((σ :: Δ1) ++ Δ2) by apply app_comm_cons.
    apply r_has_type_rw_move; auto.
    apply (r_has_type_rw_Cond _ _ _ _ _); auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    {
      apply (r_has_type_rw_Case _ _ _ _ _); auto.
      replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
      replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    }
    
    apply (r_has_type_rw_CaseList _ _ _ _); auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
    clear H H0 H2 H3 H1.
    induction H4.
    apply ForallT_nil.
    apply ForallT_cons.
    destruct p.
    split.
    exact r.
    exact (r_has_type_rw_move _ _ _ _ _ r0).
    apply IHForallT.

    apply (r_has_type_rw_While _ _ _ _); auto.
    replace ((Δ1 ++ Δ2) ++ Γ) with (Δ1 ++ Δ2 ++ Γ) by apply app_assoc; auto.
  Qed.

  Fixpoint unamb_Var_0' Γ τ σ (w : (σ :: Γ) |~ Var 0 : τ) : σ = τ.
  Proof.
    inversion w.
    auto.
  Defined.

  Fixpoint r_has_type_ro_Var_S_inv  Γ k τ a (H : (a :: Γ) |~ VAR S k : τ) : Γ |~ Var k : τ.
  Proof.
    intros.
    inversion H.
    inversion H0.
    auto.
  Defined.

  Fixpoint r_has_type_ro_Var_absurd k τ (w : nil |~ Var k : τ) : False.
  Proof.
    inversion w.
  Defined.


  Definition unamb_Var' k Γ τ σ (w1 : Γ |~ Var k : τ) (w2 : Γ |~ Var k : σ) : τ = σ.
  Proof.
    generalize Γ τ σ w1 w2.
    clear Γ τ σ w1 w2.
    induction k.
    intros.
    destruct Γ.
    contradict (r_has_type_ro_Var_absurd _ _ w1).
    rewrite <- (unamb_Var_0' _ _ _ w1).
    rewrite <- (unamb_Var_0' _ _ _ w2).
    auto.
    intros.
    destruct Γ.
    contradict (r_has_type_ro_Var_absurd _ _ w1).
    apply (IHk _ _ _ (r_has_type_ro_Var_S_inv _ _ _ _ w1) (r_has_type_ro_Var_S_inv _ _ _ _ w2)).
  Defined.

  Lemma r_has_type_rw_CaseList_nil_absurd : forall Γ Δ τ, Γ ;;; Δ ||~ CaseList nil : τ -> False.
  Proof.
    intros.
    dependent destruction H.
    contradict l0.
    simpl; apply PeanoNat.Nat.nle_succ_0.
  Qed.

  Lemma r_has_type_ro_inv_Seq_1 Γ c1 c2 τ (w : Γ |~ (c1 ;; c2) : τ) : Γ ;;; nil ||~ c1 : DUnit.
  Proof.
    dependent destruction w.
    dependent destruction r.
    simpl in r1.
    exact r1.
  Defined.

  Lemma r_has_type_ro_inv_Seq_2 Γ c1 c2 τ (w : Γ |~ (c1 ;; c2) : τ) : Γ ;;; nil ||~ c2 : τ.
  Proof.
    dependent destruction w.
    dependent destruction r.
    simpl in r2.
    exact r2.
  Defined.
  
  

  Fixpoint r_has_type_ro_unambiguous Γ e τ σ (w1 : Γ |~ e : τ){struct w1} : (Γ |~ e : σ) -> τ = σ
  with r_has_type_rw_unambiguous Γ Δ e τ σ (w1 : Γ ;;; Δ ||~ e : τ){struct w1} : ( Γ ;;; Δ ||~ e  : σ)  -> τ = σ.
  Proof.
    +
      intro w2.
      dependent destruction w1;
        dependent destruction w2; auto.
      rename r into p; rename r0 into p0.
      dependent destruction p.
      dependent destruction p0.
      apply (r_has_type_rw_unambiguous _ _ _ _ _ p2 p0_2).
      dependent destruction r.
      dependent destruction r1.
      rewrite (r_has_type_ro_unambiguous _ _ _ _ r r1) in r0.
      apply (r_has_type_rw_unambiguous _ _ _ _ _ r0 r2).
      dependent destruction r.
      dependent destruction r0.
      apply (r_has_type_rw_unambiguous _ _ _ _ _ r2 r0_1).
      dependent destruction r.
      dependent destruction r0.
      apply (r_has_type_rw_unambiguous _ _ _ _ _ r2 r0_1).
      apply (r_has_type_rw_unambiguous _ _ _ _ _ r r0).
      apply (unamb_Var' _ _ _ _ w1 w2).
    +
      intro w2.
      dependent destruction w1;
        dependent destruction w2; auto.
      apply (unamb_Var' _ _ _ _ r r0).
      dependent destruction r;
        dependent destruction r0; auto.
      dependent destruction r;
        dependent destruction r0; auto.
      apply (r_has_type_rw_unambiguous _ _ _ _ _ w1_2 w2_2).
      rewrite (r_has_type_ro_unambiguous _ _ _ _ r r0) in w1.
      apply (r_has_type_rw_unambiguous _ _ _ _ _ w1 w2).
      apply (r_has_type_rw_unambiguous _ _ _ _ _ w1_1 w2_1).
      apply (r_has_type_rw_unambiguous _ _ _ _ _ w1_1 w2_1).

      {
        destruct l.
        
        contradict l0.
        simpl; apply PeanoNat.Nat.nle_succ_0.

        dependent destruction f.
        dependent destruction f0.
        
        destruct p0.
        destruct p1.
        apply (r_has_type_rw_unambiguous _ _ _ _ _ r0 r2).
      }
  Defined.


  
  Fixpoint r_has_type_ro_unique Γ e τ (w1 w2 : Γ |~ e : τ) {struct w1}: w1 = w2 
  with r_has_type_rw_unique Γ Δ e τ (w1 w2 : Γ ;;; Δ ||~ e : τ) {struct w1}: w1 = w2.
  Proof.
    dependent destruction w1;
      dependent destruction w2;
      try 
        (rewrite (r_has_type_rw_unique _ _ _ _ r r0); reflexivity);
      try 
        (rewrite (r_has_type_ro_unique _ _ _ w1 w2); reflexivity);
      try 
        (rewrite (r_has_type_ro_unique _ _ _ w1_1 w2_1); rewrite (r_has_type_ro_unique _ _ _ w1_2 w2_2); reflexivity);
      try reflexivity.
    dependent destruction w1;
      dependent destruction w2;
      try 
        (rewrite (r_has_type_rw_unique _ _ _ _ r r0); reflexivity);
      try 
        (rewrite (r_has_type_ro_unique _ _ _ r r0); reflexivity);
      try 
        (rewrite (r_has_type_ro_unique _ _ _ w1_1 w2_1); rewrite (r_has_type_ro_unique _ _ _ w1_2 w2_2); reflexivity);
      try reflexivity.

    rewrite (r_has_type_rw_unique _ _ _ _ w1_1 w2_1);
      rewrite (r_has_type_rw_unique _ _ _ _ w1_2 w2_2); reflexivity.

    induction (r_has_type_ro_unambiguous _ _ _ _ r r0).
    rewrite (assignable_unique _ _ _ a a0).
    rewrite (r_has_type_ro_unique _ _ _ r r0); reflexivity.
    
    induction (r_has_type_ro_unambiguous _ _ _ _ r r0).

    rewrite (r_has_type_ro_unique _ _ _  r r0);
      rewrite (r_has_type_rw_unique _ _ _ _ w1 w2); reflexivity.
    
    rewrite (r_has_type_ro_unique _ _ _ r r0);
      rewrite (r_has_type_rw_unique _ _ _ _ w1_1 w2_1);
      rewrite (r_has_type_rw_unique _ _ _ _ w1_2 w2_2); reflexivity.

    rewrite (r_has_type_ro_unique _ _ _ r r1);
      rewrite (r_has_type_ro_unique _ _ _ r0 r2);
      rewrite (r_has_type_rw_unique _ _ _ _ w1_1 w2_1);
      rewrite (r_has_type_rw_unique _ _ _ _ w1_2 w2_2); reflexivity.

    rewrite (prop_irrl _ l0 l2).
    assert (f = f0).
    clear l0 l2.
    induction f.
    dependent destruction f0.
    reflexivity.
    dependent destruction f0.
    destruct p, p0.
    rewrite (r_has_type_ro_unique _ _ _ r r1).
    rewrite (r_has_type_rw_unique _ _ _ _ r0 r2).
    rewrite (IHf f0).
    reflexivity.
    rewrite H; reflexivity.

    rewrite (r_has_type_ro_unique _ _ _ r r0);
      rewrite (r_has_type_rw_unique _ _ _ _ w1 w2); reflexivity.
  Qed.

End RestrictedTyping.

Notation " Γ |~ c : τ " := (r_has_type_ro Γ c τ).
Notation " Γ ;;; Δ ||~ c : τ " := (r_has_type_rw (mk_rw_ctx Γ Δ) c τ).

Section Unambiguity.

  Fixpoint has_type_ro_r_has_type_ro Γ e τ (w : Γ |- e : τ) {struct w}: Γ |~ e : τ
  with has_type_rw_r_has_type_rw Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) {struct w}: Γ ;;; Δ ||~ e : τ.
  Proof.
    +
      inversion w.
      inversion H.
      apply (has_type_ro_r_has_type_ro _ _ _ H7).
      apply r_has_type_ro_rw_Seq.
      apply r_has_type_rw_Seq.
      apply has_type_rw_r_has_type_rw; auto.
      apply has_type_rw_r_has_type_rw; auto.
      apply r_has_type_ro_rw_Assign.
      apply (r_has_type_rw_Assign _ _ _ τ1); auto.
      apply r_has_type_ro_rw_Newvar.
      apply (r_has_type_rw_Newvar _ _ _ _ σ); auto.
      apply r_has_type_ro_rw_Cond.
      apply (r_has_type_rw_Cond _ _ _ _ _ τ); auto.
      {
        (* binary case will be deleted later *)
        apply r_has_type_ro_rw_Case.
        apply (r_has_type_rw_Case _ _ _ _ _ _ τ); auto.
      }

      {
        apply r_has_type_ro_rw_CaseList.
        apply r_has_type_rw_CaseList; auto.
        clear H5 H3 H4 H6 H7.
        induction H8.
        apply ForallT_nil.
        apply ForallT_cons.
        destruct p.
        split.
        exact (has_type_ro_r_has_type_ro _ _ _ h).
        exact (has_type_rw_r_has_type_rw _ _ _ _ h0).
        apply IHForallT.      
      }
      
      apply r_has_type_ro_rw_While.
      apply (r_has_type_rw_While _ _ _ _); auto.
      apply r_has_type_ro_Var_0; auto.
      apply r_has_type_ro_Var_S; auto.
      apply r_has_type_ro_True.
      apply r_has_type_ro_False.
      apply r_has_type_ro_Skip.
      apply r_has_type_ro_Int.
      apply r_has_type_ro_OpRrecip; auto.
      apply r_has_type_ro_OpZRcoerce; auto.
      apply r_has_type_ro_OpZRexp; auto.
      apply r_has_type_ro_OpZplus; auto.
      apply r_has_type_ro_OpZminus; auto.
      apply r_has_type_ro_OpZmult; auto.
      apply r_has_type_ro_OpZlt; auto.
      apply r_has_type_ro_OpZeq; auto.
      apply r_has_type_ro_OpRplus; auto.
      apply r_has_type_ro_OpRminus; auto.
      apply r_has_type_ro_OpRmult; auto.
      apply r_has_type_ro_OpRlt; auto.
      apply r_has_type_ro_Lim; auto.
    +
      dependent destruction w.
      dependent destruction h.
      apply has_type_rw_r_has_type_rw in h.
      apply r_has_type_rw_move in h.
      exact h.
      apply r_has_type_rw_ro_Var.
      rewrite <- x.
      apply r_has_type_ro_Var_0.
      apply r_has_type_rw_ro_Var.
      rewrite <- x.
      apply r_has_type_ro_Var_S; auto.
      apply r_has_type_rw_ro_Boolean.
      apply r_has_type_ro_True.
      apply r_has_type_rw_ro_Boolean.
      apply r_has_type_ro_False.
      apply r_has_type_rw_ro_Skip; constructor.
      apply r_has_type_rw_ro_Integer; constructor.
      apply r_has_type_rw_ro_UniOp.
      apply has_type_ro_r_has_type_ro in h.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h.
      constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h.
      constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h1;
        apply has_type_ro_r_has_type_ro in h2;
        constructor; auto.
      constructor; auto.

      apply has_type_ro_r_has_type_ro in h;
        constructor; auto.
      constructor; auto.
      
      apply has_type_rw_r_has_type_rw in w1;
        apply has_type_rw_r_has_type_rw in w2.
      constructor; auto.
      apply has_type_ro_r_has_type_ro in h.
      apply (r_has_type_rw_Assign _ _ _ τ); auto.
      apply has_type_ro_r_has_type_ro in h;
        apply has_type_rw_r_has_type_rw in w.
      apply (r_has_type_rw_Newvar _ _ _ _ σ); auto.
      apply has_type_ro_r_has_type_ro in h;
        apply has_type_rw_r_has_type_rw in w1;
        apply has_type_rw_r_has_type_rw in w2.
      apply (r_has_type_rw_Cond); auto.
      apply has_type_ro_r_has_type_ro in h;
        apply has_type_ro_r_has_type_ro in h0;
        apply has_type_rw_r_has_type_rw in w1;
        apply has_type_rw_r_has_type_rw in w2.
      apply (r_has_type_rw_Case); auto.
      {
        apply r_has_type_rw_CaseList.
        apply l0.
        clear l0.
        induction f.
        apply ForallT_nil.
        apply ForallT_cons.
        destruct p.
        split.
        exact (has_type_ro_r_has_type_ro _ _ _ h).
        exact (has_type_rw_r_has_type_rw _ _ _ _ h0).
        apply IHf.
      }
      
      apply has_type_ro_r_has_type_ro in h;
        apply has_type_rw_r_has_type_rw in w.
      apply (r_has_type_rw_While); auto.

  Defined.

  Fixpoint r_has_type_ro_has_type_ro Γ e τ (w : Γ |~ e : τ) {struct w}: Γ |- e : τ
  with r_has_type_rw_has_type_rw Γ Δ e τ (w : Γ ;;; Δ ||~ e : τ) {struct w}: Γ ;;; Δ ||- e : τ.
  Proof.
    +
      dependent destruction w;
        try(
            apply r_has_type_rw_has_type_rw in r;
            apply has_type_ro_rw;
            auto
          );
        try(
            constructor 2; auto);
        try(
            constructor; constructor 2; auto).
      apply has_type_ro_Var_S; auto.
      apply has_type_ro_OpRrecip; auto.
      apply has_type_ro_OpZRcoerce; auto.
      apply has_type_ro_OpZRexp; auto.
      apply has_type_ro_OpZplus; auto.
      apply has_type_ro_OpZminus; auto.
      apply has_type_ro_OpZmult; auto.
      apply has_type_ro_OpZlt; auto.
      apply has_type_ro_OpZeq; auto.
      apply has_type_ro_OpRplus; auto.
      apply has_type_ro_OpRminus; auto.
      apply has_type_ro_OpRmult; auto.
      apply has_type_ro_OpRlt; auto.
      apply has_type_ro_Lim; auto.

    +
      dependent destruction w;
        try(
            apply r_has_type_ro_has_type_ro in r;
            apply has_type_rw_ro;
            apply r
          );
        try(
            constructor 2; auto);
        try(
            constructor; constructor 2; auto).
      apply (has_type_rw_Assign _ _ _ τ).
      auto.
      apply r_has_type_ro_has_type_ro in r; auto.
      apply (has_type_rw_Newvar _ _ _ _ σ).
      auto.
      apply r_has_type_ro_has_type_ro in r; auto.
      apply (has_type_rw_Cond).
      apply r_has_type_ro_has_type_ro in r; auto.
      apply r_has_type_rw_has_type_rw in w1; auto.
      apply r_has_type_rw_has_type_rw in w2; auto.
      apply (has_type_rw_Case).
      apply r_has_type_ro_has_type_ro in r; auto.
      apply r_has_type_rw_has_type_rw in w1; auto.
      apply r_has_type_ro_has_type_ro in r0; auto.
      apply r_has_type_rw_has_type_rw in w2; auto.

      {
        apply has_type_rw_CaseList.
        apply l0.
        clear l0.
        induction f.
        apply ForallT_nil.
        apply ForallT_cons.
        destruct p.
        split.
        exact (r_has_type_ro_has_type_ro _ _ _ r).
        exact (r_has_type_rw_has_type_rw _ _ _ _ r0).
        apply IHf.
      }

      apply (has_type_rw_While).
      apply r_has_type_ro_has_type_ro in r; auto.
      apply r_has_type_rw_has_type_rw in w; auto.
  Defined.


  Definition has_type_while_inv_body Γ Δ e c (w : Γ ;;; Δ ||- While e c : DUnit) : Γ ;;; Δ ||- c : DUnit.
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    inversion w.
    apply r_has_type_rw_has_type_rw in H4.
    exact H4.
  Defined.  

  Lemma has_type_ro_unambiguous Γ e τ σ :  Γ |- e : τ -> Γ |- e : σ -> τ = σ.
  Proof.
    intros w1 w2.
    apply has_type_ro_r_has_type_ro in w1.
    apply has_type_ro_r_has_type_ro in w2.
    apply (r_has_type_ro_unambiguous _ _ _ _ w1 w2).
  Defined.

  Lemma has_type_rw_unambiguous Γ Δ e τ σ : Γ ;;; Δ ||- e : τ -> Γ ;;; Δ ||- e  : σ -> τ = σ.
  Proof.
    intros w1 w2.
    apply has_type_rw_r_has_type_rw in w1.
    apply has_type_rw_r_has_type_rw in w2.
    apply (r_has_type_rw_unambiguous _ _ _ _ _ w1 w2).
  Defined.

  
  Lemma has_type_ro_r_has_type_ro_unambiguous : forall Γ e τ σ, Γ |- e : τ -> Γ |~ e : σ -> τ = σ.
  Proof.
    intros.
    apply (has_type_ro_r_has_type_ro) in H.
    apply (r_has_type_ro_unambiguous _ _ _ _ H H0).
  Qed.

  Lemma has_type_rw_r_has_type_rw_unambiguous : forall Γ Δ e τ σ, Γ ;;; Δ ||- e : τ -> Γ ;;; Δ ||~ e : σ -> τ = σ.
  Proof.
    intros.
    apply (has_type_rw_r_has_type_rw) in H.
    apply (r_has_type_rw_unambiguous _ _ _ _ _ H H0).
  Qed.

  
  
End Unambiguity.


Section InverseTyping.


  Fixpoint has_type_ro_Var_S_inverse {Γ} {τ} {σ} {k} (w : (σ :: Γ) |- Var (S k) : τ) : Γ |- Var k : τ.
  Proof.
    dependent destruction w.
    dependent destruction h.
    simpl in h.
    exact (has_type_ro_Var_S_inverse _ _ _ _ h).
    exact w.
  Defined.  


  Lemma assignable_S_inverse {Γ} {τ} {σ} {k} (a : assignable (σ :: Γ) τ (S k)) :
    assignable Γ τ k.
  Proof.
    dependent destruction a.
    exact a.
  Defined.


  Fixpoint has_type_ro_OpRrecip_inverse Γ e (w : Γ |- (;/; e) : REAL) : Γ |- e  : REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRrecip_inverse _ _ h).
    exact w.
  Defined.

  Fixpoint has_type_ro_OpZRcoerce_inverse Γ e (w : Γ |- (RE e) : REAL) : Γ |- e  : INTEGER.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZRcoerce_inverse _ _ h).
    exact w.
  Defined.

  Fixpoint has_type_ro_OpZRexp_inverse Γ e (w : Γ |- (EXP e) : REAL) : Γ |- e  : INTEGER.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZRexp_inverse _ _ h).
    exact w.
  Defined.

  Fixpoint has_type_ro_OpZplus_inverse Γ e1 e2 (w : Γ |- (e1 :+: e2) : INTEGER) : ((Γ |- e1  : INTEGER) * (Γ |- e2  : INTEGER))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZplus_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpZminus_inverse Γ e1 e2 (w : Γ |- (e1 :-: e2) : INTEGER) : ((Γ |- e1  : INTEGER) * (Γ |- e2  : INTEGER))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZminus_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpZmult_inverse Γ e1 e2 (w : Γ |- (e1 :*: e2) : INTEGER) : ((Γ |- e1  : INTEGER) * (Γ |- e2  : INTEGER))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZmult_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpZlt_inverse Γ e1 e2 (w : Γ |- (e1 :<: e2) : BOOL) : ((Γ |- e1  : INTEGER) * (Γ |- e2  : INTEGER))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZlt_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpZeq_inverse Γ e1 e2 (w : Γ |- (e1 :=: e2) : BOOL) : ((Γ |- e1  : INTEGER) * (Γ |- e2  : INTEGER))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZeq_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpRplus_inverse Γ e1 e2 (w : Γ |- (e1 ;+; e2) : REAL) : ((Γ |- e1  : REAL) * (Γ |- e2  : REAL))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRplus_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpRminus_inverse Γ e1 e2 (w : Γ |- (e1 ;-; e2) : REAL) : ((Γ |- e1  : REAL) * (Γ |- e2  : REAL))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRminus_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_OpRmult_inverse Γ e1 e2 (w : Γ |- (e1 ;*; e2) : REAL) : ((Γ |- e1  : REAL) * (Γ |- e2  : REAL))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRmult_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.


  Fixpoint has_type_ro_OpRlt_inverse Γ e1 e2 (w : Γ |- (e1 ;<; e2) : BOOL) : ((Γ |- e1  : REAL) * (Γ |- e2  : REAL))%type.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRlt_inverse _ _ _ h).
    exact (pair w1 w2).
  Defined.

  Fixpoint has_type_ro_Lim_inverse Γ e (w : Γ |- (Lim e) : REAL) : ((INTEGER :: Γ) |- e  : REAL).
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_Lim_inverse _ _ h).
    exact w.
  Defined.

  
  Fixpoint has_type_rw_Seq_inverse Γ Δ c1 c2 τ (w : Γ ;;; Δ ||- (c1 ;; c2) : τ) :
    ((Γ ;;; Δ ||- c1 : UNIT) * (Γ ;;; Δ ||- c2 : τ))%type.
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    dependent destruction w.
    apply r_has_type_rw_has_type_rw in w1.
    apply r_has_type_rw_has_type_rw in w2.
    exact (pair w1 w2).
  Defined.


  Fixpoint has_type_rw_Cond_inverse Γ Δ e c1 c2 τ (w : Γ ;;; Δ ||- (IF e THEN c1 ELSE c2 END) : τ) :
    (((Δ ++ Γ) |- e : BOOL) * (Γ ;;; Δ ||- c1 : τ) * (Γ ;;; Δ ||- c2 : τ))%type.
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    dependent destruction w.
    apply r_has_type_ro_has_type_ro in r.
    apply r_has_type_rw_has_type_rw in w1.
    apply r_has_type_rw_has_type_rw in w2.
    repeat split; auto.
  Defined.

  Fixpoint has_type_rw_CaseList_inverse Γ Δ l τ (w : Γ ;;; Δ ||- (CaseList l) : τ) :
    (ForallT (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ ;;; Δ ||- snd ec : τ))%type) l).
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    dependent destruction w.
    clear l1.
    dependent induction f.
    apply ForallT_nil.
    apply ForallT_cons.
    destruct p.
    split.
    apply r_has_type_ro_has_type_ro; auto.
    apply r_has_type_rw_has_type_rw; auto.
    exact IHf.    
  Defined.

  Fixpoint has_type_rw_While_inverse {Γ Δ} {e c} (w : Γ ;;; Δ ||-(WHILE e DO c END) : UNIT) :
    ((Δ ++ Γ) |- e : BOOL) * (Γ ;;; Δ ||- c : UNIT)%type.
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    dependent destruction w.
    apply r_has_type_ro_has_type_ro in r.
    apply r_has_type_rw_has_type_rw in w.
    repeat split; auto.
  Defined.
  
  Fixpoint has_type_rw_Assign_inverse {Γ Δ} {k} {e} (w : Γ ;;; Δ ||-(Assign k e) : UNIT) :
    {τ & (assignable Δ τ k) * ((Δ ++ Γ) |- e : τ)} %type.
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    dependent destruction w.
    exists τ.
    apply r_has_type_ro_has_type_ro in r.
    repeat split; auto.
  Defined.

  Fixpoint has_type_rw_Newvar_inverse {Γ Δ} {e c} {τ} (w : Γ ;;; Δ ||- (NEWVAR e IN c) : τ) :
    {σ &     ((Δ ++ Γ) |- e : σ) * (Γ ;;; (σ :: Δ) ||- c : τ) }%type.
  Proof.
    apply has_type_rw_r_has_type_rw in w.
    dependent destruction w.
    exists σ.
    apply r_has_type_ro_has_type_ro in r.
    apply r_has_type_rw_has_type_rw in w.
    repeat split; auto.
  Defined.
  
End InverseTyping.


Section InferTyping.
  Fixpoint has_type_ro_OpRrecip_infer Γ e τ (w : Γ |- (;/; e) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRrecip_infer _ _ _ h).
    apply eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZRcoerce_infer Γ e τ (w : Γ |- (RE e) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZRcoerce_infer _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZRexp_infer Γ e τ (w : Γ |- (EXP e) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZRexp_infer _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZplus_infer Γ e1 e2 τ (w : Γ |- (e1 :+: e2) : τ) : τ = INTEGER.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZplus_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZminus_infer Γ e1 e2 τ (w : Γ |- (e1 :-: e2) : τ) : τ = INTEGER.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZminus_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZmult_infer Γ e1 e2 τ (w : Γ |- (e1 :*: e2) : τ) : τ = INTEGER.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZmult_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZlt_infer Γ e1 e2 τ (w : Γ |- (e1 :<: e2) : τ) : τ = BOOL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZlt_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpZeq_infer Γ e1 e2 τ (w : Γ |- (e1 :=: e2) : τ) : τ = BOOL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpZeq_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpRplus_infer Γ e1 e2 τ (w : Γ |- (e1 ;+; e2) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRplus_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpRminus_infer Γ e1 e2 τ (w : Γ |- (e1 ;-; e2) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRminus_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_OpRmult_infer Γ e1 e2 τ (w : Γ |- (e1 ;*; e2) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRmult_infer _ _ _ _ h).
    exact eq_refl.
  Defined.


  Fixpoint has_type_ro_OpRlt_infer Γ e1 e2 τ (w : Γ |- (e1 ;<; e2) : τ) : τ = BOOL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_OpRlt_infer _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_Lim_infer Γ e τ (w : Γ |- (Lim e) : τ) : τ = REAL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_Lim_infer _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_rw_While_infer {Γ Δ} {e} {c} {τ} (w : Γ ;;; Δ ||- (While e c) : τ) : τ = UNIT.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_rw_While_infer _ _ _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_rw_Assign_infer {Γ Δ} {k} {e} {τ} (w : Γ ;;; Δ ||- (Assign k e) : τ) : τ = UNIT.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_rw_Assign_infer _ _ _ _ _ h).
    exact eq_refl.
  Defined.

  
  Fixpoint has_type_ro_Int_infer Γ k τ (w : Γ |- INT k : τ) : τ = INTEGER.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_Int_infer _ _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_True_infer Γ τ (w : Γ |- TRUE : τ) : τ = BOOL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_True_infer _ _ h).
    exact eq_refl.
  Defined.

  Fixpoint has_type_ro_False_infer Γ τ (w : Γ |- FALSE : τ) : τ = BOOL.
  Proof.
    dependent destruction w.
    dependent destruction h.
    apply (has_type_ro_False_infer _ _ h).
    exact eq_refl.
  Defined.

  
End InferTyping.

  (* Fixpoint has_type_rw_Assign Γ Δ e τ k (w : Γ ;;; Δ ||- (LET k := e)) :   : forall (Γ : list datatype) (Δ : ro_ctx) (e : exp) (τ : datatype) (k : nat), *)
  (*                        assignable Δ τ k -> (Δ ++ Γ) |- e : τ -> Γ;;; Δ ||- (LET k := e) : UNIT *)
  (* Fixpoint has_type_rw_Newvar Γ c :  : forall (Γ Δ : list datatype) (e c : exp) (σ τ : datatype), *)
  (*                        (Δ ++ Γ) |- e : σ -> Γ;;; (σ :: Δ) ||- c : τ -> Γ;;; Δ ||- (NEWVAR e IN c) : τ *)
  (* Fixpoint has_type_rw_Cond Γ c :  : forall (Γ Δ : list datatype) (e c1 c2 : exp) (τ : datatype), *)
  (*                      (Δ ++ Γ) |- e : BOOL -> *)
  (*                      Γ;;; Δ ||- c1 : τ -> Γ;;; Δ ||- c2 : τ -> Γ;;; Δ ||- (IF e THEN c1 ELSE c2 END) : τ *)
  (* Fixpoint has_type_rw_Case Γ c :  : forall (Γ Δ : list datatype) (e1 c1 e2 c2 : exp) (τ : datatype), *)
  (*                      (Δ ++ Γ) |- e1 : BOOL -> *)
  (*                      Γ;;; Δ ||- c1 : τ -> *)
  (*                      (Δ ++ Γ) |- e2 : BOOL -> *)
  (*                      Γ;;; Δ ||- c2 : τ -> Γ;;; Δ ||- (CASE e1 ==> c1 OR e2 ==> c2 END) : τ *)
  (* Fixpoint has_type_rw_CaseList Γ c :  : forall (Γ Δ : list datatype) (l : list (exp * exp)) (τ : datatype), *)
  (*                          1 <= length l -> *)
  (*                          ForallT *)
  (*                            (fun ec : exp * exp => (((Δ ++ Γ) |- fst ec : BOOL) * (Γ;;; Δ ||- snd ec : τ))%type) l -> *)
  (*                          Γ;;; Δ ||- CaseList l : τ *)
  (* Fixpoint has_type_rw_While Γ c :  : forall (Γ Δ : list datatype) (e c : exp), *)
  (*                       (Δ ++ Γ) |- e : BOOL -> Γ;;; Δ ||- c : UNIT -> Γ;;; Δ ||- (WHILE e DO c END) : UNIT. *)

Fixpoint r_has_type_ro_add_auxiliary Γ e τ (w : Γ |~ e : τ) Γ' {struct w}: (Γ ++ Γ') |~ e : τ
with r_has_type_rw_add_auxiliary Γ Δ e τ (w : Γ ;;; Δ ||~ e : τ) Γ' {struct w} : (Γ ++ Γ') ;;; Δ ||~ e : τ.
Proof.
  dependent destruction w;
    try
      (pose proof (r_has_type_rw_add_auxiliary _ _ _ _ r Γ') as H;
       constructor;
       exact H);
    try constructor; auto.
  rewrite app_comm_cons.
  apply r_has_type_ro_add_auxiliary.
  exact w.
  
  dependent destruction w;
    try
      (pose proof (r_has_type_ro_add_auxiliary _ _ _ r Γ') as H;
       constructor;
       rewrite app_assoc;
       auto; fail);
    try (constructor; apply r_has_type_rw_add_auxiliary; auto; fail);
    try (constructor; auto; fail).
  
  apply (r_has_type_rw_Assign _ _ _ τ); auto.
  rewrite app_assoc.
  apply r_has_type_ro_add_auxiliary; auto.
  
  apply (r_has_type_rw_Newvar _ _ _ _ σ); auto.
  rewrite app_assoc.
  apply r_has_type_ro_add_auxiliary; auto.

  apply (r_has_type_rw_Cond); auto.
  rewrite app_assoc.
  apply r_has_type_ro_add_auxiliary; auto.

  apply (r_has_type_rw_Case); auto.
  rewrite app_assoc.
  apply r_has_type_ro_add_auxiliary; auto.
  rewrite app_assoc.
  apply r_has_type_ro_add_auxiliary; auto.

  apply (r_has_type_rw_CaseList).
  exact l0.  
  clear l0.
  dependent induction f.
  apply ForallT_nil.
  apply ForallT_cons.
  destruct p.
  split.
  rewrite app_assoc.  
  exact (r_has_type_ro_add_auxiliary _ _ _ r _).
  exact (r_has_type_rw_add_auxiliary _ _ _ _ r0 _).
  apply IHf.

  apply (r_has_type_rw_While); auto.
  rewrite app_assoc.
  apply r_has_type_ro_add_auxiliary; auto.
Defined.

Lemma has_type_ro_add_auxiliary Γ e τ (w : Γ |- e : τ) Γ': (Γ ++ Γ') |- e : τ.
Proof.
  apply r_has_type_ro_has_type_ro.
  apply r_has_type_ro_add_auxiliary.
  apply has_type_ro_r_has_type_ro.
  exact w.
Defined.

Lemma has_type_rw_add_auxiliary Γ Δ e τ (w : Γ ;;; Δ ||- e : τ) Γ' : (Γ ++ Γ') ;;; Δ ||- e : τ.
Proof.
  apply r_has_type_rw_has_type_rw.
  apply r_has_type_rw_add_auxiliary.
  apply has_type_rw_r_has_type_rw.
  exact w.
Defined.


Lemma has_type_rw_move
     : forall (Γ : list datatype) (Δ1 : ro_ctx) (Δ2 : list datatype) (e : exp) (τ : datatype),
    (Δ2 ++ Γ);;; Δ1 ||- e : τ -> Γ;;; (Δ1 ++ Δ2) ||- e : τ.
Proof.
  intros.
  apply r_has_type_rw_has_type_rw.
  apply has_type_rw_r_has_type_rw in H.
  apply r_has_type_rw_move.
  exact H.
Defined.
