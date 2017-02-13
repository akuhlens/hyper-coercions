Require Import Coq.Init.Datatypes.
Require Import GTypes. 
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import LibTactics.

(* Library worthy *)
Ltac cut_if_not_hypothesis h :=
  match goal with
  |  H: h |- _ => fail 1
  | _ => cut h
  end. 

Definition Label : Type := nat. 

(* The main definition in Question *) 
Inductive coercion := 
| Id_c   : coercion
| Prj_c  : Ty -> Label -> coercion                          
| Inj_c  : Ty -> coercion
| Seq_c  : coercion -> coercion -> coercion
| Ref_c  : coercion -> coercion -> coercion
| Arr_c  : coercion -> coercion -> coercion                           
| Fail_c : Label -> coercion.

Notation "t →c g" := (Arr_c t g) (at level 70).
Definition crcn := coercion. 

Inductive wt_coercion : coercion -> CTy -> Prop :=
| Wt_Id_c   : forall t1, wt_coercion Id_c (t1 ⇒ t1)
| Wt_Proj_c : forall t l, wt_coercion (Prj_c t l) (Dyn ⇒ t)
| Wt_Inj_c  : forall t, wt_coercion (Inj_c t) (t ⇒ Dyn)
| Wt_Seq_c  : forall t1 t2 t3 c1 c2,
    wt_coercion c1 (t1 ⇒ t2) ->
    wt_coercion c2 (t2 ⇒ t3) ->
    wt_coercion (Seq_c c1 c2) (t1 ⇒ t3)
| Wt_Ref_c  : forall t1 t2 c1 c2,
    wt_coercion c1 (t1 ⇒ t2) ->
    wt_coercion c2 (t2 ⇒ t1) ->
    wt_coercion (Ref_c c1 c2) ((Ref t1) ⇒ (Ref t2))
| Wt_Arr_c  : forall t1 t2 t3 t4 c1 c2,
    wt_coercion c1 (t1 ⇒ t2) ->
    wt_coercion c2 (t3 ⇒ t4) ->
    wt_coercion (c1 →c c2) ((t2 → t3) ⇒ (t1 → t4))
| Wt_Fail_c : forall t1 t2 l, wt_coercion (Fail_c l) (t1 ⇒ t2).

Hint Constructors wt_coercion. 

Example wt_coercion_example :
  wt_coercion (Seq_c (Inj_c Int) (Prj_c Int 0)) (Int ⇒ Int).
Proof. eauto. Qed.

Inductive se_coercion : coercion -> CTy -> Prop :=
| Se_Id {t} : se_coercion Id_c (t ⇒ t)
| Se_Seq  : forall t1 t2 l c,
    t1 <> Dyn -> 
    se_inj_coercion c (t1 ⇒ t2) -> 
    se_coercion (Seq_c (Prj_c t1 l) c) (Dyn ⇒ t2)
| Se_Inj  : forall t1 t2 c,
    se_inj_coercion c (t1 ⇒ t2) -> 
    se_coercion c (t1 ⇒ t2)
with se_inj_coercion : coercion -> CTy -> Prop := 
| Se_Inj_Fail : forall t1 t2 l,
    se_inj_coercion (Fail_c l) (t1 ⇒ t2)
| Se_Inj_Med  : forall t1 t2 c,
    se_med_coercion c (t1 ⇒ t2) ->
    se_inj_coercion (Seq_c c (Inj_c t2)) (t1 ⇒ Dyn)
| Se_Inj_Id   : forall t1 t2 c,
    se_med_coercion c (t1 ⇒ t2) ->
    se_inj_coercion c (t1 ⇒ t2)
with se_med_coercion : coercion -> CTy -> Prop :=
| Se_Med_Id : forall t,
         se_med_coercion Id_c (t ⇒ t)
| Se_Med_Ref  : forall t1 t2 c1 c2,
    se_coercion c1 (t1 ⇒ t2) ->
    se_coercion c2 (t2 ⇒ t1) ->
    se_med_coercion (Ref_c c1 c2) ((GTypes.Ref t1) ⇒ (GTypes.Ref t2))
| Se_Med_Arr : forall t1 t2 t3 t4 c1 c2,
    se_coercion c1 (t1 ⇒ t2) ->
    se_coercion c2 (t3 ⇒ t4) ->
    se_med_coercion (c1 →c c2) ((t2 → t3) ⇒ (t1 → t4)). 

Hint Constructors se_coercion se_inj_coercion se_med_coercion.

Scheme se_ind :=
  Induction for se_coercion Sort Prop
with se_inj_ind :=
  Induction for se_inj_coercion Sort Prop
with se_med_ind :=
  Induction for se_med_coercion Sort Prop.

Fixpoint crcn_depth (c : coercion) : nat :=
  match c with
  | Seq_c c1 c2 => max (crcn_depth c1) (crcn_depth c2)
  | c1 →c c2 => max (crcn_depth c1) (crcn_depth c2)
  | Ref_c c1 c2 => max (crcn_depth c1) (crcn_depth c2)
  | _ => 1
  end. 

Hint Resolve le_0_n le_n_S le_S_n le_S. 

Lemma max_le_fst : forall a b, a <= max a b. 
Proof.
  induction a; intros []; try intros; simpl; auto. 
Qed.

Lemma max_le_snd : forall a b,  b <= max a b. 
Proof. 
  induction a; intros []; try intros; simpl; auto. 
Qed. 

Hint Resolve max_le_snd max_le_fst. 

Lemma tydepth_Arr_le_snd: forall t1 t2, ty_depth t2 < ty_depth (t1 → t2). 
Proof. simpl. auto. Qed.

Lemma tydepth_Arr_le_fst : forall t1 t2, ty_depth t1 < ty_depth (t1 → t2). 
Proof. simpl. auto. Qed.

SearchAbout "+". 

(* plus_n_O: forall n : nat, n = n + 0 *)
(* plus_O_n: forall n : nat, 0 + n = n *)
(* plus_n_Sm: forall n m : nat, S (n + m) = n + S m *)
(* plus_Sn_m: forall n m : nat, S n + m = S (n + m) *)




Require Import Omega. 

Program Fixpoint mk_coercion t1 t2 l {measure ((ty_depth t1) + (ty_depth t2))}
  : coercion :=
  if (beq_ty t1 t2) then Id_c else
    match t1, t2 with
    | Dyn, t2  => (Prj_c t2 l)
    | t1 , Dyn => (Inj_c t1)
    | (t11 → t12), (t21 → t22) =>
      (mk_coercion t21 t11 l) →c (mk_coercion t12 t22 l)
    | (Ref t1), (Ref t2) =>
      Ref_c (mk_coercion t1 t2 l) (mk_coercion t2 t1 l)
    | _, _ => (Fail_c l)
    end.

Ltac tc_mk_coercion :=
  intuition;
  subst;
  repeat
    (simpl;
    match goal with
     | |- forall x, _ => intro
     | |- context[_ + S _] => rewrite <- plus_n_Sm
     | |- context[_ < _] => unfold lt
     | |- context[S _ <= S _] => apply le_n_S
     | |- (_ + ?l) <= ?C2 ((max ?l ?r) + _)  => 
       cut_if_not_hypothesis (l <= max l r)
     | |- (?l + _) <= ?C2 (_ + (max ?l ?r))  => 
       cut_if_not_hypothesis (l <= max l r)
     | |- (_ + ?l) <= ?C2 (_ + (max ?r ?l))  => 
       cut_if_not_hypothesis (l <= max r l)
     | |- (?l + _) <= ?C2 ((max ?r ?l) + _)  => 
       cut_if_not_hypothesis (l <= max r l)
     | _ => solve [auto]
     | _ => omega
     | _ => intuition discriminate
     end).

Solve All Obligations with tc_mk_coercion. 

Inductive make_coercion : (Ty * Ty * blame_info) -> coercion -> Prop :=
| Mk_Id_c : forall t l,  make_coercion (t, t, l) Id_c
| Mk_Inj : forall t l, make_coercion (t, Dyn, l) (Inj_c t)
| Mk_Prj_c : forall g l, make_coercion (Dyn, g, l) (Prj_c g l)
| Mk_Arr : forall t1 t2 t3 t4 l c1 c2,
    make_coercion (t3, t1, l) c1 ->
    make_coercion (t2, t4, l) c2 ->
    make_coercion ((t1 → t2), (t3 → t4), l) (c1 →c c2)
| Mk_Ref : forall t1 t2 l c1 c2,
    make_coercion (t1, t2, l) c1 ->
    make_coercion (t2, t1, l) c2 ->
    make_coercion (Ref t1, Ref t2, l) (Ref_c c1 c2)
| Mk_Fail_c : forall t1 t2 l, make_coercion (t1, t2, l) (Fail_c l).

Hint Constructors make_coercion.

Lemma make_coercion_total : forall t1 t2 l,
    exists c, make_coercion (t1, t2, l) c. 
Proof. induction t1; destruct t2; eauto. Qed. 

Lemma make_coercion_wt : forall c t1 t2 l,
    make_coercion (t1, t2, l) c -> wt_coercion c (t1 ⇒ t2). 
Proof. induction c; inversion 1; constructor; eauto. Qed.        

Hint Immediate make_coercion_wt. 

Lemma mk_coercion_correct : forall t1 t2 l c,
    mk_coercion t1 t2 l = c -> make_coercion (t1, t2, l) c. 
Proof. induction t1; destruct t2. 
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto). 
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + admit. 
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + cbn; intuition (subst; eauto).
       + admit.
Abort. 

Hint Immediate make_coercion_wt. 

Inductive make_se_coercion
  : (Ty * Ty * blame_info) -> coercion -> Prop :=
| Mk_Se_Id_c : forall t l, make_se_coercion (t, t, l) Id_c
| Mk_Se_Inj : forall g l, make_se_coercion (g, Dyn, l) (Seq_c Id_c (Inj_c g))
| Mk_Se_Prj_c : forall t l,
    t <> Dyn -> 
    make_se_coercion (Dyn, t, l) (Seq_c (Prj_c t l) Id_c)
| Mk_Se_Arr : forall t1 t2 t3 t4 l c1 c2,
    make_se_coercion (t3, t1, l) c1 ->
    make_se_coercion (t2, t4, l) c2 ->
    make_se_coercion (t1 → t2, t3 → t4, l) (c1 →c c2)
| Mk_Se_Ref : forall t1 t2 l c1 c2,
    make_se_coercion (t1, t2, l) c1 ->
    make_se_coercion (t2, t1, l) c2 ->
    make_se_coercion (Ref t1, Ref t2, l) (Ref_c c1 c2).

Hint Constructors make_se_coercion. 

Lemma  beq_ty_true : forall t, beq_ty t t = true. 
Proof. 
  induction t;
    repeat (simpl;
            match goal with
            | H : _ = true |- _ => rewrite H; clear H
            end);
    auto. 
Qed. 

Lemma mk_coercion_t : forall t l, mk_coercion t t l = Id_c.
Proof. induction t; intros; cbn; repeat rewrite beq_ty_true; auto. Qed.

Lemma make_se_coercion_wt : forall c t1 t2 l,
    make_se_coercion (t1, t2, l) c -> se_coercion c (t1 ⇒ t2). 
Proof.     
  induction c; intros t1 t2 l' H; inversion H;
    repeat match goal with
           | IH: context [ make_se_coercion _ ?c -> _ ],
                 H: make_se_coercion _ ?c |- _ =>
             apply IH in H
           end;
    auto. 
Qed. 

Inductive compose_coercions : coercion * coercion -> coercion -> Prop :=
| Comp_Inj_Prj : forall t l,
    compose_coercions (Inj_c t, Prj_c t l) Id_c
| Compose_Id_L : forall c, compose_coercions (Id_c, c) c
| Compose_Id_R : forall c, compose_coercions (c, Id_c) c
| Comp_Arr   : forall c1 c2 c3 c4 c5 c6,
    compose_coercions (c3, c1) c5 ->
    compose_coercions (c2, c4) c6 ->
    compose_coercions (c1 →c c2, c3 →c c4) (c5 →c c6)
| Comp_Ref   : forall c1 c2 c3 c4 c5 c6,
    compose_coercions (c3, c1) c5 ->
    compose_coercions (c2, c4) c6 ->
    compose_coercions (Ref_c c1 c2, Ref_c c3 c4) (Ref_c c5 c6)
| Compose_Seq_c_L : forall c1 c2 c3 c4,
    compose_coercions (c2, c3) c4 -> 
    compose_coercions (Seq_c c1 c2, c3) (Seq_c c1 c4)
| Compose_Seq_c_R : forall c1 c2 c3 c4,
    compose_coercions (c1, c2) c4 -> 
    compose_coercions (c1, Seq_c c2 c3) (Seq_c c4 c3)                       
| Comp_Other : forall c1 c2,
    compose_coercions (c1, c2) (Seq_c c1 c2)
| Comp_Fail_c    : forall t g l,
    t <> g -> compose_coercions (Inj_c t, Prj_c g l) (Fail_c l).

Hint Constructors compose_coercions.

Lemma compose_wt : forall c1 c2 t1 t2 t3,
    wt_coercion c1 (t1 ⇒ t2) /\ wt_coercion c2 (t2 ⇒ t3) ->
    exists c3, compose_coercions (c1, c2) c3 /\ wt_coercion c3 (t1 ⇒ t3).
Proof.
  intros c1 c2 t1 t2 t3 [wt_c1 wt_c2].
  inversion wt_c1; inversion wt_c2; subst; eauto. 
Qed. 


Inductive  compose_se : coercion * coercion -> coercion -> Prop :=
| Comp_Se_Inj_Prj : forall g t' t l i i' t'' m c,
    se_med_coercion g (t' ⇒ Dyn) ->
    se_inj_coercion i (t  ⇒ t'') ->
    make_se_coercion (t, t', l) m ->
    compose_se (g, m) i' ->
    compose_se (i', i) c ->
    compose_se (Seq_c g (Inj_c t), Seq_c (Prj_c t l) i) c
| Comp_Se_Prj : forall t l i t'' s c,
    se_inj_coercion i (t  ⇒ t'') ->
    compose_se (i, s) c ->
    compose_se (Seq_c (Prj_c t l) i, s) (Seq_c (Prj_c t l) c)
| Comp_Se_Inj : forall g g' t t' t'' c,
    se_inj_coercion g (t ⇒ t') ->
    se_inj_coercion g' (t' ⇒ Dyn) ->
    compose_se (g, g') c ->
    compose_se (g, Seq_c g' (Inj_c t'')) (Seq_c c (Inj_c t''))              
| Comp_Se_Arr   : forall c1 c2 c3 c4 c5 c6,
    compose_se (c3, c1) c5 ->
    compose_se (c2, c4) c6 ->
    compose_se (c1 →c c2, c3 →c c4) (c5 →c c6)
| Comp_Se_Ref_c   : forall c1 c2 c3 c4 c5 c6,
    compose_se (c3, c1) c5 ->
    compose_se (c2, c4) c6 ->
    compose_se (Ref_c c1 c2, Ref_c c3 c4) (Ref_c c5 c6)
| Comp_Se_Id_L : forall c,
    compose_se (Id_c, c) c
| Comp_Se_Id_R : forall c,
    compose_se (c, Id_c) c
| Compose_Fail_c_R : forall g t t' l,
    se_med_coercion g (t ⇒ t') ->
    compose_se (g, Fail_c l) (Fail_c l)
| Compose_Fail_c_L : forall c l,
    compose_se (Fail_c l, c) (Fail_c l).

Hint Constructors compose_se. 

Lemma compose_se_wt : forall c1 t1 t2,
    se_coercion c1 (t1 ⇒ t2) ->
    forall c2 t3,
      se_coercion c2 (t2 ⇒ t3) ->
      exists c3,
        compose_se (c1, c2) c3 /\
        se_coercion c3 (t1 ⇒ t3).
Proof. Admitted.


