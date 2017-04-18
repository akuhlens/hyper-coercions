Require Import General. 
Require Import Coq.Bool.Bool. 
Require Import LibTactics.


Inductive ty := 
| Int   : ty
| Bool  : ty
| Dyn   : ty
| Ref   : ty -> ty
| Arr   : ty -> ty -> ty. 

Hint Constructors ty. 

Notation "x → y" := (Arr x y) (at level 60, right associativity).

Fixpoint ty_depth t : nat :=
  match t with
  | t → g => 1 + max (ty_depth t) (ty_depth g)
  | Ref t  => 1 + ty_depth t
  | _ => 0
  end.

Open Scope depth_scope. 
Instance ty_deep : Deep ty := ty_depth.

Lemma ty_depth_lt_0 : forall (t:ty), [| t |] < 0 -> False. 
Proof. unfold depth. intros [] H; inverts H. Qed.

Hint Resolve ty_depth_lt_0.
  
Fixpoint beq_ty (x y : ty) : bool :=
  match x, y with
    | Dyn, Dyn => true
    | Int, Int => true
    | Bool, Bool => true
    | t11 → t12, t21 → t22 => (beq_ty t11 t21) && (beq_ty t12 t22)
    | Ref t1, Ref t2 => beq_ty t1 t2
    | _, _ => false
  end.

Inductive Static (x : ty) : Prop :=
| NotDyn : x <> Dyn -> Static x.

Inductive cty :=
| CArr : ty -> ty -> cty.

Notation "x ⇒ y" := (CArr x y) (at level 70, right associativity).

Inductive consistent : ty -> ty -> Prop :=
| Consistent_Dyn_L {t} : consistent Dyn t
| Consistent_Dyn_R {t} : consistent t Dyn
| Consistent_Eq {t} : consistent t t
| Consistent_Arr {t1 t2 t3 t4} :
    consistent t1 t3 -> consistent t2 t4 ->
    consistent (t1 → t2) (t3 → t4)
| Consistent_Ref {t1 t2} :
    consistent t1 t2 -> consistent (Ref t1) (Ref t2).

Hint Constructors consistent. 

Definition inconsistent x y := consistent x y -> False. 
Notation "x ∼ y" := (consistent x y) (at level 70, no associativity). 
Notation "x ≁ y" := (x ∼ y -> False) (at level 70, no associativity).

(* shallow consistency *)
Reserved Notation "x !# y" (at level 70, no associativity). 
Inductive shallow_consistent : ty -> ty -> Prop :=
| Shallow_Consistent_Dyn_L {t} : Dyn !# t 
| Shallow_Consistent_Dyn_R {t} : t   !# Dyn
| Shallow_Consistent_Eq {t}    : t   !# t
| Shallow_Consistent_Arr {t1 t2 t3 t4} : (t1 → t2) !# (t3 → t4)
| Shallow_Consistent_Ref {t1 t2} :       (Ref t1)  !# (Ref t2)
where "x !# y" := (shallow_consistent x y).

Hint Constructors shallow_consistent. 
Notation "x # y" := (x !# y -> False) (at level 70, no associativity). 

Theorem ty_eqdec :
  forall x y : ty,
    {x = y} + {x <> y}.
Proof.                   
  decide equality.
Defined.

Lemma beq_ty_t : forall x, beq_ty x x = true. 
Proof.
  induction x; simpl;
    repeat
      (match goal with
       | [ H: beq_ty _ _ = _ |- _ ] => rewrite H; clear H
       end);
    try reflexivity.
Qed.

Lemma neq_nbeq : forall t g, t <> g ->  beq_ty t g = false. 
Proof.
  induction t; intros [] H; tryfalse; jauto. 
  - simpl. apply IHt. intuition congruence.
  - destruct (ty_eqdec t1 t); destruct (ty_eqdec t2 t0).
    try intuition congruence.
    all: simpl.
    all: repeat match goal with
                | IH: context[ beq_ty ?t _ ] |- _  =>
                  rewrite IH; [idtac | assumption]
                end.
    all: subst; try rewrite beq_ty_t; reflexivity.       
Qed.

Lemma beq_ty_iff : forall x y, beq_ty x y = true <-> x = y.
Proof.
  split.
  - generalize dependent y. induction x;
    try (destruct y; try discriminate; intuition). 
    + apply IHx in H. subst. reflexivity.
    + simpl in H. apply andb_true_iff in H. destruct H as [H0 H1]. 
      apply IHx1 in H0. apply IHx2 in H1.
      subst. reflexivity.
  - intros; subst. apply beq_ty_t. 
Qed.


Lemma beq_ty_neg : forall x y, beq_ty x y = false -> x <> y. 
  induction x; intros y H contr;
        try subst;
        try rewrite beq_ty_t;
        try discriminate.
      + apply IHx in H. contradiction H. reflexivity. 
      + simpl in H. apply andb_false_iff in H. destruct H.
        * apply IHx1 in H. contradiction H. reflexivity. 
        * apply IHx2 in H. contradiction H. reflexivity. 
Qed.


Lemma H : forall t1 t2 t3 t4,
    t1 → t2 <> t3 → t4 -> t1 <> t3 \/ t2 <> t4.
Proof.
  intros t1 t2 t3 t4. destruct (ty_eqdec t1 t3).
  - intros H. right. intros c. destruct H. congruence. 
  - intros. left. assumption. 
Qed.

Lemma beq_tyP : forall t g, reflect (t = g) (beq_ty t g).
Proof.
  induction t; destruct g;
    try (constructor; intuition; discriminate). 
  - destruct (IHt g).
    + subst. rewrite beq_ty_t. constructor. reflexivity. 
    + rewrite neq_nbeq. constructor. intuition. congruence.
      intuition. congruence. 
  - destruct (ty_eqdec t1 g1); destruct (ty_eqdec t2 g2);
      destruct (IHt1 g1); destruct (IHt2 g2);
      try subst;
      repeat rewrite beq_ty_t;
      try (rewrite neq_nbeq);
      try (constructor);
      try (reflexivity);
      try (intuition; inversion H0; contradiction).
Qed. 

Lemma nbeq_ty_iff : forall x y, beq_ty x y = false <-> x <> y.
Proof.
  intros x y. split; destruct (beq_tyP x y); intros H; intuition. 
Qed.

Theorem ty_consistency_dec :
  forall x y : ty, {x ∼ y} + {x ≁ y}.
Proof.
  induction x; destruct y;
    repeat
      match goal with
      | _ => progress auto
      | h: forall y, { _ } + { _ }, t: ty |- _ => specialize (h t)
      | h: {_} + {_} |- _ => destruct h
      | h: ?t ≁ ?t |- _ => contradiction h; constructor
      | h: _ ≁ _ |- _ => right                                  
      | |- _ ≁ _ => intros h; inversion h; subst
      | _ => right; intro h; inversion h
  end.
Qed. 

Theorem ty_shallow_consistency_dec :
  forall x y : ty, {x !# y} + {x # y}.
Proof.
  induction x; destruct y;
    repeat
      match goal with
      | _ => progress auto
      | h: forall y, { _ } + { _ }, t: ty |- _ => specialize (h t)
      | h: {_} + {_} |- _ => destruct h
      | _ => right; intro h; inversion h
  end.
Qed. 

Lemma shallow_inconsistency_strengthening : forall x y, x # y -> x ≁ y.  
Proof. induction x; intros []; intros; inversion H1; auto. Qed.

Hint Resolve shallow_inconsistency_strengthening. 

Lemma inconsistency_strengthening : forall x y, x ≁ y -> x = y -> False. 
Proof. induction x; intros [] H1 H2; try discriminate;
         try (inversion H2); intuition eauto.
Qed. 

Hint Resolve inconsistency_strengthening.

Lemma shallow_insconsistency_dyn_r : forall t, not (t # Dyn).  
Proof. induction t; auto. Qed. 
Lemma shallow_insconsistency_refl : forall t, not (t # t).
Proof. induction t; auto. Qed.
Lemma shallow_insconsistency_dyn_l : forall t, not (Dyn # t). 
Proof. induction t; auto. Qed.

Hint Resolve
     shallow_insconsistency_dyn_l
     shallow_insconsistency_dyn_r
     shallow_insconsistency_refl.

Lemma consistent_symetric : forall t1 t2, t1 ∼ t2 -> t2 ∼ t1. 
Proof. intros t1 t2 H. induction H; auto. Qed.

Lemma shallow_consistent_symetric : forall t1 t2, t1 !# t2 -> t2 !# t1. 
Proof. intros t1 t2 H. induction H; auto. Qed.

Hint Resolve consistent_symetric shallow_consistent_symetric. 

Lemma inconsistent_symetric : forall t1 t2, t1 ≁ t2 -> t2 ≁ t1. 
Proof. auto. Qed. 

Lemma shallow_inconsistent_symetric : forall t1 t2, t1 # t2 -> t2 # t1. 
Proof. auto. Qed. 

Hint Resolve inconsistent_symetric shallow_inconsistent_symetric. 

Definition blame_info : Type := nat.

Lemma ty_depth_min : forall (t : ty), 0 <= ty_depth t.
Proof. induction t; unfold depth; simpl; eauto. 
       - destruct (Max.max_spec (ty_depth t1) (ty_depth t2)) as [[]|[]].
         *  rewrite H1. auto. 
         * rewrite H1. auto. 
Qed.

Hint Resolve ty_depth_min. 

Example depth_t_min : forall (t : ty), 0 <= [| t |]. 
Proof. auto. Qed. 


