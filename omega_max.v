Require Coq.Arith.PeanoNat. 



SearchAbout "max".




SearchAbout "UsualMinMaxProperties".
 
Require Import Omega. 


Require Import LibTactics. 

Require Import General. 

Ltac spec_max_with_guard m n :=
  match goal with
  | H: m < n |- _ => fail 1
  | H: n <= m |- _ => fail 1
  | _ =>
    let ineq:=fresh "ineq" in
    let eq:=fresh  "eq" in
    destruct (Max.max_spec m n) as [[ineq eq]|[ineq eq]];
    rewrite eq in *
  end.


Ltac le_gives_eq_tac m n :=
  let H:=fresh in
  assert (H: m <= n);
  [omega |
   rewrite (Max.max_l m n H) in *;
   rewrite (Max.max_r n m H) in *].

Lemma lt_max_right : forall m n o, m < n -> m < max o n.
Proof. intuition. spec_max_with_guard o n; omega. Qed. 
Lemma lt_max_left  : forall m n o, m < n -> m < max n o. 
Proof. intuition. spec_max_with_guard n o; omega. Qed. 
Lemma max_lt : forall m n o, m < o -> n < o -> max m n < o. 
Proof. intuition. spec_max_with_guard m n; omega. Qed. 
Lemma max_lt_imp_left : forall m n o, max m n < o -> m < o.
Proof. intuition. spec_max_with_guard m n; omega. Qed. 
Lemma max_lt_imp_right : forall m n o, max m n < o -> n < o. 
Proof. intuition. spec_max_with_guard m n; omega. Qed. 
Hint Resolve 
     lt_max_right
     lt_max_left
     max_lt
     max_lt_imp_left
     max_lt_imp_right.

Lemma le_max_right : forall m n o, m <= n -> m <= max o n.
Proof. intuition. spec_max_with_guard o n; omega. Qed. 
Lemma le_max_left  : forall m n o, m <= n -> m <= max n o. 
Proof. intuition. spec_max_with_guard n o; omega. Qed. 
Lemma max_le : forall m n o, m <= o -> n <= o -> max m n <= o. 
Proof. intuition. spec_max_with_guard m n; omega. Qed. 
Lemma max_le_imp_left : forall m n o, max m n <= o -> m <= o.
Proof. intuition. spec_max_with_guard m n; omega. Qed. 
Lemma max_le_imp_right : forall m n o, max m n <= o -> n <= o. 
Proof. intuition. spec_max_with_guard m n; omega. Qed. 
Hint Resolve
     le_max_right 
     le_max_left 
     max_le
     max_le_imp_left
     max_le_imp_left. 

SearchAbout "le". 
Lemma lt_S : forall n m, n < m -> S n < S m. 
Proof. intuition. Qed. 
Lemma le_S : forall n m, n <= m -> S n <= S m. 
Proof. intuition. Qed. 
Lemma eq_S : forall n m, n = m -> S n = S m.
Proof. congruence. Qed. 
Lemma lt_P : forall n m,  S n < S m -> n < m. 
Proof. intuition. Qed. 
Lemma le_P : forall n m, S n <= S m -> n <= m.  
Proof. intuition. Qed. 
Lemma eq_P : forall n m, S n = S m -> n = m. 
Proof. congruence. Qed. 

Lemma S_max_strategy : forall m n, S (max m n) = max (S m) (S n).
Proof. simpl. congruence. Qed. 
                              
Lemma lt_max_strategy : forall m n p, 
    m < max n p <-> ((m < n /\ p <= n) \/ (m < p /\ n < p)).
Proof. intuition. spec_max_with_guard n p; intuition. Qed. 
Lemma max_lt_strategy : forall m n p,
    max m n < p <-> (m < p /\ n < p).
Proof.  intros m n p. spec_max_with_guard m n; intuition. Qed. 
Lemma le_max_strategy : forall m n p, 
    m <=max n p <-> ((m <=n /\ p <= n) \/ (m <=p /\ n <=p)).
Proof. intuition. spec_max_with_guard n p; intuition. Qed. 
Lemma max_le_strategy : forall m n p,
    max m n <=p <-> (m <=p /\ n <=p).
Proof.  intros m n p. spec_max_with_guard m n; intuition. Qed. 


Lemma brute_force_max_eq : forall n m o,
    n = max m o <-> (n = m /\ o <= m) \/ (n = o /\ m < o).
Proof.
  intros n m o. destruct (Max.max_spec m o) as [[]|[]]; omega. 
Qed.

Lemma brute_force_max_lt : forall n m o,
    max n m < o <-> (n < o /\ m < o).
Proof.
  intros n m o. destruct (Max.max_spec n m) as [[]|[]]; omega.
Qed.  

Lemma brute_force_lt_max : forall n m o,
    n < max m o <-> (n < m /\ o <= m) \/ (n < o /\ m < o).
Proof.
  intros n m o. destruct (Max.max_spec m o) as [[]|[]]; omega.
Qed.                                    

Lemma brute_force_max_le : forall n m o,
    max n m <= o <-> (n <= o /\ m <= o). 
Proof. 
  intros n m o. destruct (Max.max_spec n m) as [[]|[]]; omega.
Qed.                                    

Lemma brute_force_le_max : forall n m o,
        n <= max m o <-> (n <= m /\ o <= m) \/ (n <= o /\ m <= o).
Proof. 
  intros n m o. destruct (Max.max_spec m o) as [[]|[]]; omega.
Qed.                                    

  Ltac rewrite_triple_tac p m n o :=
  (let m':=fresh in
   let n':=fresh in
   let o':=fresh in
   remember m as m';
   remember n as n'; 
   remember o as o';
   rewrite (p m' n' o') in *) .

Ltac explain_max' n p :=
  let m:=fresh in
  remember (max n p) as m;
  rewrite_triple_tac brute_force_max_eq m n p.

Ltac explain_max :=
  repeat match goal with
         | _ => rewrite Max.max_idempotent in *
         | _ => apply lt_S || apply le_S || apply eq_S
         | H: _ |- _ => apply lt_P in H
         | H: _ |- _ => apply le_P in H
         | H: _ |- _ => apply le_P in H
         | _ => rewrite Max.max_idempotent in *
         | H: context[?n <= max ?m ?p] |- _ => 
           rewrite_triple_tac brute_force_le_max ?n ?m ?p
         | H: context[max ?n ?m <= ?p] |- _ =>  
           rewrite_triple_tac brute_force_max_le ?n ?m ?p
         | H: context[?n <  max ?m ?p] |- _ =>  
           rewrite_triple_tac brute_force_lt_max ?n ?m ?p
         | H: context[max ?n ?m <  ?p] |- _ =>  
           rewrite_triple_tac brute_force_max_lt ?n ?m ?p
         (* these last two are all that are really needed *)
         | |- context[max ?n ?p] => explain_max' n p
         | H: context[max ?n ?p] |- _  => explain_max' n p
         end.


Ltac omega_max_search :=
  repeat match goal with
         | _ => rewrite Max.max_idempotent in *
         | _ => solve[assumption || congruence || auto || omega]
         | _ => apply lt_S || apply le_S || apply eq_S
         | |- _ < max _ _ => 
           (apply lt_max_left; omega_max_search) 
           || (apply lt_max_right; omega_max_search)
         | |- max _ _ < _ => apply max_lt
         | |- context[max ?m ?n] => spec_max_with_guard m n
         | H: context[max ?m ?n] |- _ => spec_max_with_guard m n
         | |- context[match ?t with _ => _ end] =>
           match goal with
           | |- ?g => destruct t
           end
         end.

Ltac omega_max :=
  intros;
  try rewrite Max.max_0_l in *;
  try rewrite Max.max_0_r in *;
  try rewrite Max.max_idempotent in *;
  explain_max;
  subst; 
  omega. 



Ltac ineq_tac := intuition;
                 (solve[eauto 7] 
                  || solve[unfold depth in *; simpl in *; time "omega_max" omega_max]). 


Example lt1 : forall n m o p, n < m -> n < max o (max p m). 
Proof. ineq_tac. Qed. 
Example lt2 : forall n m o p, n < m -> n < max (max p m) o. 
Proof. ineq_tac. Qed. 
Example eq1 : forall n m o p s t,
    S (max (max (max n m) (max o p)) (max s t))
    =
    S (max (max (max o p) (max n m)) (max s t)).
Proof. ineq_tac. Qed. 

Example le1 : forall t1 t2 x x1, x = x1 -> x <= max t1 t2 ->  
  S (max (max t1 t2) (max x x1)) 
       <=
       S (max t1 t2).
Proof. ineq_tac. Qed.



Example le2 : forall t0 t4 t5 t6 t8 t9 c0 c1 c2 c3 c4 c,
  S (max (max (max t8 t9) (max t4 t5)) (max c0 c3)) <=
  S (max (max t8 t9) (max t4 t5))
  ->
  c <= max c0 c1
  -> 
  c4 <= max c2 c3
  -> 
  S (max (max (max t0 t6) (max t4 t5)) (max c c4)) <=
  S (max (max (max (max t0 t6) (max t8 t9)) 
              (max c1 c2))
         (max (max t4 t5) (max t4 t5))).
Proof. Admitted. 
