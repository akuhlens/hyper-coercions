Require Import LibTactics.
Require Import Omega. 
Require Import NArith. 

Class Deep (A : Type) : Type :=  depth : A -> nat.

Bind Scope depth_scope with Deep.

Notation "[| x |]" := (depth x) (at level 0) : depth_scope.


Lemma brute_force_max_le : forall m o n,
    n <= max m o <-> (n <= m /\ o <= m) \/ (n <= o /\ m <= o).
Proof.
  intros m o n. destruct (Max.max_spec m o) as [[]|[]]; omega. 
Qed.

Lemma brute_force_max_lt : forall m o n,
    n < max m o <-> (n < m /\ o <= m) \/ (n < o /\ m <= o).
Proof.
  intros m o n. destruct (Max.max_spec m o) as [[]|[]]; omega. 
Qed.

Lemma brute_force_max_eq : forall m o n,
    max m o = n <-> (n = m /\ o <= m) \/ (n = o /\ m <= o).
Proof.
  intros m o n. destruct (Max.max_spec m o) as [[]|[]]; omega. 
Qed.

Lemma max_0_eq : forall n, max n 0 = 0 -> n = 0.
Proof. induction n; intros; assumption. Qed. 

Lemma max_0_eql : forall n, max 0 n = 0 -> n = 0.
Proof. simpl. trivial. Qed. 


Ltac max_tac :=
  let rec solver := assumption || jauto || solve[simpl in *; omega] in
  let rec le_rw n m :=
      let H:=fresh in
      (assert (H: max n m = n);
       [apply Max.max_l; solver | idtac ..])
      ||
      (assert (H: max n m = m);
       [apply Max.max_l; solver | idtac ..]);
       rewrite H in *
         in
           repeat
             match goal with
             (* Rewrites that remove max without extending the proof tree *)
             | H: max 0 ?n = 0 |- _ => simpl in H
             | H: max ?n 0 = 0 |- _ => apply max_0_eq in H
             | _ => rewrite Max.max_idempotent
             | _ => rewrite Max.max_0_l in *
             | _ => rewrite Max.max_0_r in *
             (* Searches that lead to rewrite without extending the tree *) 
             (* try to solve without dividing the proof *)
             | _ => solver
             (* try to prove properties that allow us to rewrite *)
             | H: context[max ?n ?m] |- _ => le_rw n m
             | |- context[max ?n ?m] => le_rw n m
             (* Begin brute force tactics *)
             | H: max _ _ = _  |- _ => apply brute_force_max_eq in H
             | H: _ <= max _ _ |- _ => apply brute_force_max_le in H
             | H: _ <  max _ _ |- _ => apply brute_force_max_lt in H
             | _ => solver
             | _ => auto
             end.