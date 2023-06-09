(* A formalization of the Clerical language a joint project
   by Andrej Bauer, Sewon Park, and Alex Simpson. *)
   
Require Import ZArith.
Require Import List.

(* Binary operations *)
Inductive binary_op :=
| OpZplus | OpZminus | OpZmult | OpZlt | OpZeq 
| OpRplus | OpRminus | OpRlt | OpRmult
.

(* Unary operations *)
Inductive unary_op :=
  OpRrecip | OpZRcoerce | OpZRexp.

(* Computations *)
Inductive exp :=
  Var : nat -> exp
| Boolean : bool -> exp
| Integer : Z -> exp
| BinOp : binary_op -> exp -> exp -> exp
| UniOp : unary_op -> exp -> exp
| Skip : exp
| Seq : exp -> exp -> exp
| Cond : exp -> exp -> exp -> exp
(* | Case : exp -> exp -> exp -> exp -> exp *)
| CaseList : list (exp * exp) -> exp
| While : exp -> exp -> exp
| Newvar : exp -> exp -> exp
| Assign : nat -> exp -> exp
| Lim : exp -> exp.
                  
(* Datatypes *)
Inductive datatype :=
  DUnit
| DBoolean
| DInteger
| DReal.

(* Notations for writing clerical programs. *)
Declare Scope clerical_scope.
              
Notation "'VAR' k" := (Var k) (at level 30) : clerical_scope.

Notation "'TRUE'" := (Boolean true) : clerical_scope.

Notation "'FALSE'" := (Boolean false) : clerical_scope.

Notation "'INT' k" := (Integer k) (at level 30) : clerical_scope.

Notation "e1 ':+:' e2" := (BinOp OpZplus e1 e2) (at level 65, left associativity) : clerical_scope.

Notation "e1 ':*:' e2" := (BinOp OpZmult e1 e2) (at level 65, left associativity) : clerical_scope.

Notation "e1 ':-:' e2" := (BinOp OpZminus e1 e2) (at level 65, left associativity) : clerical_scope.

Notation "e1 ':<:' e2" := (BinOp OpZlt e1 e2) (at level 71, left associativity) : clerical_scope.

Notation "e1 ':=:' e2" := (BinOp OpZeq e1 e2) (at level 71, left associativity) : clerical_scope.

Notation "e1 ';+;' e2" := (BinOp OpRplus e1 e2) (at level 65, left associativity) : clerical_scope.

Notation "e1 ';-;' e2" := (BinOp OpRminus e1 e2) (at level 65, left associativity) : clerical_scope.

Notation "e1 ';*;' e2" := (BinOp OpRmult e1 e2) (at level 65, left associativity) : clerical_scope.

Notation "e1 ';/;' e2" := (BinOp OpRmult e1 (UniOp OpRrecip e2)) (at level 65, left associativity) : clerical_scope.

Notation "e1 ';<;' e2" := (BinOp OpRlt e1 e2) (at level 71, left associativity) : clerical_scope.

Notation "'RE' e " := (UniOp OpZRcoerce e) (at level 30) : clerical_scope.

Notation "'EXP' e " := (UniOp OpZRexp e) (at level 30) : clerical_scope.

Notation "';/;' e " := (UniOp OpRrecip e) (at level 30) : clerical_scope.

Notation "'SKIP'" := (Skip) : clerical_scope.

Notation "c1 ;; c2" := (Seq c1 c2) (at level 80, right associativity) : clerical_scope.

(* Notation "'CASE' b1 '==>' c1 'OR' b2 '==>' c2 'END'" := (Case b1 c1 b2 c2) (at level 89)  : clerical_scope. *)

Declare Custom Entry clerical_sub_expr.

Notation "e '==>' c" := (e, c) (in custom clerical_sub_expr at level 0, e constr, c constr) : clerical_scope. 

Notation "'CASE' p1 '|' .. '|' p2 'END'" :=
  (CaseList  (cons (p1) .. (cons (p2) nil) ..)) (p1 custom clerical_sub_expr, p2 custom clerical_sub_expr) : clerical_scope.


Notation "'IF' b 'THEN' c1 'ELSE' c2 'END'" := (Cond b c1 c2) (at level 85) : clerical_scope.

Notation "'WHILE' b 'DO' c 'END'" := (While b c) (at level 85) : clerical_scope.

Notation "'NEWVAR' e 'IN' c" := (Newvar e c) (at level 85) : clerical_scope.

Notation "'LET' n ':=' e" := (Assign n e) (at level 78) : clerical_scope.

Notation "'REAL'" := DReal : clerical_scope.

Notation "'BOOL'" := DBoolean : clerical_scope.

Notation "'UNIT'" := DUnit : clerical_scope.

Notation "'INTEGER'" := DInteger : clerical_scope.

Notation "':-:' e" := (BinOp OpZminus ((Integer 0)) e) (at level 45, right associativity) : clerical_scope.

Notation "';-;' e" := (BinOp OpRminus (UniOp OpZRcoerce (Integer 0)) e) (at level 45, right associativity) : clerical_scope.

Open Scope clerical_scope.

Delimit Scope clerical_scope with clerical.
