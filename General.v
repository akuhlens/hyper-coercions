Require Import LibTactics.
Require Import Omega. 
Require Import NArith. 

Class Deep (A : Type) : Type :=  depth : A -> nat.
Hint Unfold depth: core.  

Bind Scope depth_scope with Deep.

Notation "[| x |]" := (depth x) (at level 0) : depth_scope.

Open Scope depth_scope. 
Definition nat_id (n : nat) := n.
Hint Unfold nat_id. 
Instance nat_deep : Deep nat := nat_id. 
Hint Unfold nat_deep. 

Example e1 : [| 2 |] = 2. 
Proof. repeat autounfold. omega. Qed. 