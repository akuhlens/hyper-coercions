Require Import Coq.Init.Datatypes.
Require Import LibTactics.
Require Export General.
Require Import GTypes. 
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.

Open Scope depth_scope. 

Definition Label : Type := nat. 

(* The main definition in Question *) 
Inductive coercion := 
| Id_c   : ty -> coercion
| Prj_c  : ty -> Label -> coercion                          
| Inj_c  : ty -> coercion
| Seq_c  : coercion -> coercion -> coercion
(* Ref_c write read *)
| Ref_c  : coercion -> coercion -> coercion
| Arr_c  : coercion -> coercion -> coercion                           
| Fail_c : ty -> Label -> ty -> coercion.

Notation "'ιc' t" := (Id_c t) (at level 50) : coercion_scope. 
Notation "t →c g" := (Arr_c t g) (at level 70, right associativity) : coercion_scope. 
Notation "t #c g"  := (Ref_c t g) (at level 70, right associativity) : coercion_scope. 
Notation "x ';c' y" := (Seq_c x y) (at level 74, left associativity) : coercion_scope.
Notation "⊥c t l g" := (Fail_c t l g) (at level 0): coercion_scope. 

Open Scope coercion_scope.




Definition crcn := coercion. 

Inductive wt_coercion : coercion -> Cty -> Prop :=
| Wt_Id_c   : forall t1, wt_coercion (ιc t1) (t1 ⇒ t1)
| Wt_Proj_c : forall t l, wt_coercion (Prj_c t l) (Dyn ⇒ t)
| Wt_Inj_c  : forall t, wt_coercion (Inj_c t) (t ⇒ Dyn)
| Wt_Seq_c  : forall t1 t2 t3 c1 c2,
    wt_coercion c1 (t1 ⇒ t2) ->
    wt_coercion c2 (t2 ⇒ t3) ->
    wt_coercion (c1 ;c c2) (t1 ⇒ t3)
| Wt_Ref_c  : forall t1 t2 c1 c2,
    wt_coercion c1 (t2 ⇒ t1) ->
    wt_coercion c2 (t1 ⇒ t2) ->
    wt_coercion (c1 #c c2) ((Ref t1) ⇒ (Ref t2))
| Wt_Arr_c  : forall t1 t2 g1 g2 c1 c2,
    wt_coercion c1 (g1 ⇒ t1) ->
    wt_coercion c2 (t2 ⇒ g2) ->
    wt_coercion (c1 →c c2) ((t1 → t2) ⇒ (g1 → g2))
| Wt_Fail_c : forall t1 t2 l,
    t1 <> Dyn -> wt_coercion (Fail_c t1 l t2) (t1 ⇒ t2).

Hint Constructors wt_coercion. 

Example wt_coercion_example :
  wt_coercion (Seq_c (Inj_c Int) (Prj_c Int 0)) (Int ⇒ Int).
Proof. eauto. Qed.



Inductive se_coercion : coercion -> Cty -> Prop :=
| Se_Id {t} : se_coercion (ιc t) (t ⇒ t)
| Se_Seq  : forall t1 t2 l c,
    t1 <> Dyn -> 
    se_inj_coercion c (t1 ⇒ t2) -> 
    se_coercion (Prj_c t1 l ;c c) (Dyn ⇒ t2)
| Se_Inj  : forall t1 t2 c,
    t1 <> Dyn ->
    se_inj_coercion c (t1 ⇒ t2) -> 
    se_coercion c (t1 ⇒ t2)
with se_inj_coercion : coercion -> Cty -> Prop := 
| Se_Inj_Fail : forall t1 t2 l,
    se_inj_coercion (Fail_c t1 l t2) (t1 ⇒ t2)
| Se_Inj_Med  : forall t1 t2 c,
    se_med_coercion c (t1 ⇒ t2) ->
    se_inj_coercion (c ;c Inj_c t2) (t1 ⇒ Dyn)
| Se_Inj_Id   : forall t1 t2 c,
    se_med_coercion c (t1 ⇒ t2) ->
    se_inj_coercion c (t1 ⇒ t2)
with se_med_coercion : coercion -> Cty -> Prop :=
| Se_Med_Id : forall t,
         se_med_coercion (ιc t) (t ⇒ t)
| Se_Med_Ref  : forall t1 t2 c1 c2,
    se_coercion c1 (t2 ⇒ t1) ->
    se_coercion c2 (t1 ⇒ t2) ->
    se_med_coercion (c1 #c c2) (Ref t1 ⇒ Ref t2)
| Se_Med_Arr : forall t1 t2 g1 g2 c1 c2,
    se_coercion c1 (g1 ⇒ t1) ->
    se_coercion c2 (t2 ⇒ g2) ->
    se_med_coercion (c1 →c c2) (t1 → t2 ⇒ g1 → g2). 




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
  | c1 →c c2 => 1 + max (crcn_depth c1) (crcn_depth c2)
  | c1 #c c2 => 1 + max (crcn_depth c1) (crcn_depth c2)
  | Prj_c t _ => (ty_depth t)
  | Inj_c t =>  (ty_depth t) 
  | ιc t => (ty_depth t)
  | Fail_c t1 _ t2 => max (ty_depth t1) (ty_depth t2)
  end. 

Instance crcn_deep : Deep crcn := crcn_depth. 

Example cd : [| Prj_c Int 1 |] = 1.
Proof. auto. Qed. 

Lemma crcn_depth_le_0 : forall (c:crcn), [|c|] <= 0 -> False.
Proof. induction c; intros H; unfold depth in *; simpl in *;
       try match goal with
           | H: context[max ?n ?m] |- _ =>
             destruct (Max.max_spec n m)
           end;
       try match goal with
           | H: _ /\ _ |- _ => destruct H
           end;
       try match goal with
           | H: max _ _ = _ |- _ => rewrite H in *
           end;
       try match goal with
           | H: _ <= 0 |- _ => solve [inverts H]
           end;       
       eauto.
Qed.

Hint Resolve le_0_n le_n_S le_S_n le_S crcn_depth_le_0. 

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



Program Fixpoint mk_coercion t1 t2 l {measure ((ty_depth t1) + (ty_depth t2))}
  : coercion :=
  if (beq_ty t1 t2) then (ιc t1) else
    match t1, t2 with
    | Dyn, t2  => (Prj_c t2 l)
    | t1 , Dyn => (Inj_c t1)
    | (t11 → t12), (t21 → t22) =>
      (mk_coercion t21 t11 l) →c (mk_coercion t12 t22 l)
    | (Ref t1), (Ref t2) =>
      (mk_coercion t1 t2 l) #c (mk_coercion t2 t1 l)
    | _, _ => (Fail_c t1 l t2)
    end.

(* Library worthy *)
Ltac cut_if_not_hypothesis h :=
  match goal with
  |  H: h |- _ => fail 1
  | _ => cut h
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

Inductive make_coercion : (ty * ty * blame_info) -> coercion -> Prop :=
| Mk_Id_c : forall t l,  make_coercion (t, t, l) (ιc t)
| Mk_Inj : forall t l,
    t <> Dyn -> make_coercion (t, Dyn, l) (Inj_c t)
| Mk_Prj_c : forall g l,
    g <> Dyn -> make_coercion (Dyn, g, l) (Prj_c g l)
| Mk_Arr : forall t1 t2 t3 t4 l c1 c2,
    make_coercion (t3, t1, l) c1 ->
    make_coercion (t2, t4, l) c2 ->
    make_coercion ((t1 → t2), (t3 → t4), l) (c1 →c c2)
| Mk_Ref : forall t1 t2 l c1 c2,
    make_coercion (t2, t1, l) c1 ->
    make_coercion (t1, t2, l) c2 ->
    make_coercion (Ref t1, Ref t2, l) (Ref_c c1 c2)
| Mk_Fail_c : forall t1 t2 l,
    t1 <≁> t2 -> make_coercion (t1, t2, l) (Fail_c t1 l t2).

Hint Constructors make_coercion.

Lemma make_coercion_symmetry : forall c1 t1 t2 l,
    make_coercion (t1, t2, l) c1 -> exists c2, make_coercion (t2, t1, l) c2.
Proof. induction c1;
         intros t1 t2 l2 H;
         inverts H;
         repeat match goal with
                | IH: context[ _ -> exists c, _], H: make_coercion (?t, ?g, _) _ |- _ =>
                  match goal with
                  | H: make_coercion (g, t, _) _ |- _ => fail 1
                  | _ => destruct (IH _ _ _ H)
                  end
                end;
         eauto.
Qed. 

Lemma make_coercion_total : forall t1 t2 l,
    exists c, make_coercion (t1, t2, l) c. 
Proof. induction t1; destruct t2; intros;
       repeat match goal with
              | |- context[make_coercion (?t, ?g, _) _] =>
                let H:=fresh in
                assert (t <≁> g); [solve[intros H; inverts H]| eauto] 
              | t:ty, l:blame_info, IH: context[make_coercion (?g, _, _) _] |- _ =>
                match goal with
                | H: make_coercion (g, t, _) _ |- _ => fail 1
                | _ => let c:=fresh in
                      let P:=fresh in
                      destruct (IH t l) as [c P];
                        destruct (make_coercion_symmetry _ _ _ _ P)
                end
              | _ => solve[eexists; econstructor; intro; discriminate]
              | _ => eauto
              end.
Qed.

Lemma make_coercion_wt : forall c t1 t2 l,
    make_coercion (t1, t2, l) c -> wt_coercion c (t1 ⇒ t2). 
Proof.
  induction c; inversion 1; constructor; eauto.
  - intuition. contradiction H1. subst. auto. 
Qed.        

Hint Immediate make_coercion_wt. 

Lemma ty_depth_min : forall (t : ty), 1 <= [| t |].
Proof. induction t; unfold depth; simpl; omega. Qed. 

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


Ltac omega_max :=
  repeat match goal with
         | _ => rewrite Max.max_0_l in *
         | _ => rewrite Max.max_0_r in *
         | _ => rewrite Max.max_idempotent in *
         | _ => solve[eauto]
         | _ => omega
         | |- context[Init.Nat.max ?m ?n] => idtac "1" m n; spec_max_with_guard m n
         | H: context[max ?m ?n] |- _ => spec_max_with_guard m n
         | |- context[match ?t with _ => _ end] => destruct t
         end.
Ltac ineq_tac := solve[omega_max] || unfold depth in *; cbn in *; omega_max.



Ltac max_tac :=
  let rec solver := assumption || jauto || solve[simpl in *; omega] in
  let rec rem s :=
      (let x:=fresh in
       let e:=fresh in
       remember s as x eqn:e; symmetry in e) in
  let rec le_rw n m :=
      let H:=fresh in
      (assert (H: max n m = n);
       [apply Max.max_l; solver | idtac ..])
      ||
      (assert (H: max n m = m);
       [apply Max.max_l; solver | idtac ..]);
       rewrite H in *
         in
           do 20
             match goal with
             | H: context[max ?x ?y] |- _ =>
               idtac H;
               match type of H with
               | max 0 ?n = 0  => simpl in H
               | max ?n 0 = 0  => apply max_0_eq in H
               
               | max (max ?x ?y) _ = _ => rem (max x y)
               | max _ (max ?x ?y) = _ => rem (max x y)
               | max _ _ = (max ?x ?y) => rem (max x y)
               | max _ _ = _ => fail 1
               | max _ _ < _ => fail 1
               | max _ _ <= _ => fail 1
               | _ => rem (max x y)
               end
             (* Rewrites that remove max without extending the proof tree *)
             | _ => rewrite Max.max_idempotent
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

Hint Immediate make_coercion_wt. 

Inductive make_se_coercion
  : (ty * ty * blame_info) -> coercion -> Prop :=
| Mk_Se_Id_c : forall t l, make_se_coercion (t, t, l) (Id_c t)
| Mk_Se_Inj : forall g l,
    g <> Dyn ->
    make_se_coercion (g, Dyn, l) (Seq_c (Id_c g) (Inj_c g))
| Mk_Se_Prj_c : forall t l,
    t <> Dyn -> 
    make_se_coercion (Dyn, t, l) (Seq_c (Prj_c t l) (ιc t))
| Mk_Se_Arr : forall t1 t2 t3 t4 l c1 c2,
    t1 → t2 <> t3 → t4 -> 
    make_se_coercion (t3, t1, l) c1 ->
    make_se_coercion (t2, t4, l) c2 ->
    make_se_coercion (t1 → t2, t3 → t4, l) (c1 →c c2)
| Mk_Se_Ref : forall t1 t2 l c1 c2,
    Ref t1 <> Ref t2 -> 
    make_se_coercion (t2, t1, l) c1 ->
    make_se_coercion (t1, t2, l) c2 ->
    make_se_coercion (Ref t1, Ref t2, l) (Ref_c c1 c2)
| Mk_Se_Fail : forall t1 t2 l,
    t1 <≁> t2 -> make_se_coercion (t1, t2, l) (Fail_c t1 l t2) .

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

(*
Lemma mk_coercion_t : forall t l, mk_coercion t t l = (ιc t).
Proof. induction t; intros; cbn; repeat rewrite beq_ty_true; auto. Qed. Qed. 
*)

Lemma make_se_coercion_wt : forall c t1 t2 l,
    make_se_coercion (t1, t2, l) c -> se_coercion c (t1 ⇒ t2). 
Proof.     
  induction c; intros t1 t2 l' H; inverts H;
    repeat match goal with
           | IH: context [ make_se_coercion _ ?c -> _ ],
                 H: make_se_coercion _ ?c |- _ =>
             apply IH in H
           end;
    try solve[econstructor; try congruence; eauto]. 
  - econstructor. intro. subst. contradiction H1. auto. eauto.
Qed. 

Lemma make_se_coercion_symmetry : forall c1 t1 t2 l,
    make_se_coercion (t1, t2, l) c1 ->
    exists c2, make_se_coercion (t2, t1, l) c2 /\
          [|c1|]  = [|c2|].
Proof.
  induction c1; intros t1 t2 l2 H; 
  inverts H;
  repeat match goal with
         | H: make_se_coercion _ ?c, IH: context[make_se_coercion _ ?c -> _] |- _ =>
           let i:= fresh in 
           destruct (IH _ _ _ H) as [i []]; clear H
         | _ => solve [eexists; split; [> eauto | ineq_tac]]
         end.
Qed.

Lemma make_se_coercion_total : forall t1 t2 l,
    exists c, make_se_coercion (t1, t2, l) c /\ [|c|] <= max [|t1|] [|t2|].
Proof.
  induction t1; destruct t2; intros;
    repeat match goal with
           | |- context[make_se_coercion (?t, ?g, _) _] =>
             match goal with 
             | H: t <≁> g |- _ => fail 1
             | _ => 
               let H:=fresh in
               assert (t <≁> g); [solve[intros H; inverts H]| eauto] 
             end
           | _ =>
             let f := fresh in
             solve[eexists;
                   split;
                   [econstructor; intro f; (discriminate || inverts f) | ineq_tac]]
           | _ => solve [eauto] 
           end.
  all: match goal with
       | |- exists c, make_se_coercion (?t1 , ?t2, _) _ /\ _ =>
         let e:=fresh in
         destruct (ty_eqdec t1 t2) as [e|e]; [inverts e| idtac]
       end.
  all: eauto. 
  all: repeat match goal with
              | t:ty, l:blame_info, IH: context[make_se_coercion (?g, _, _) _] |- _ =>
                match goal with
                | H: make_se_coercion (g, t, l) _ |- _ => fail 1
                | _ =>
                  let c:=fresh in
                let P1:=fresh in
                let P2:=fresh in
                let x:=fresh in 
                destruct (IH t l) as [c [P1 P2]];
                  destruct (make_se_coercion_symmetry _ _ _ _ P1) as [x []]
                end
              | _ => solve[eexists; split; ineq_tac]
              end.
  Qed. 

Lemma make_se_function' : forall n c1 c2 t1 t2 l,
    [|t1|] <= n ->
    [|t2|] <= n ->
    make_se_coercion (t1, t2, l) c1 ->
    make_se_coercion (t1, t2, l) c2 ->
    c1 = c2.
Proof. induction n.
       - intros c1 c2 [] [] l mk1 mk2; unfold depth in *; simpl in *; omega.  
       - intros c1 c2 [] [] l b1 b2 mk1 mk2.
         all:match goal with
             | H: make_se_coercion _ _, P: make_se_coercion _ _  |- _ =>
               inverts H; inverts P
             end.
         all: try match goal with
                  | H: _ <> _  |- _ => solve[contradiction H; auto]
                  | H: _ <≁> _ |- _ => solve[contradiction H; auto]
                  | H: _ = _ |- _ => discriminate
                  | _ => auto
                  end. 

         all: repeat match goal with 
                | IH: context[make_se_coercion _ _ ->
                              make_se_coercion _ _ ->
                              _ = _],
                      H1: make_se_coercion (?t1, ?t2, _) ?c1,
                          H2: make_se_coercion (?t1, ?t2, _) ?c2 |- _ =>
                  
                  apply (IH c1 c2) in H1;
                    [subst
                    | solve [ineq_tac]
                    | solve [ineq_tac]
                    | assumption]
                | _ => auto
                end.
Qed. 

Lemma make_se_coercion_function : forall h1 h2 t1 t2 l,
    make_se_coercion (t1, t2, l) h1 ->
    make_se_coercion (t1, t2, l) h2 ->
    h1 = h2.
Proof. intros h1 h2 t1 t2 l.
       apply (make_se_function' (max [|t1|] [|t2|]));
       ineq_tac. 
Qed. 


Lemma make_se_coercion_depth : forall t1 t2 l c,
    make_se_coercion (t1, t2, l) c -> [| c |] <= max [|t1|] [|t2|]. 
Proof.
  intros t1 t2 l c1 H1. 
  destruct (make_se_coercion_total t1 t2 l) as [c2 [H2 H3]].
  apply (make_se_coercion_function _ _ _ _ _ H1) in H2.
  subst.
  assumption.
Qed. 
  
Inductive compose_coercions : coercion * coercion -> coercion -> Prop :=
| Comp_Inj_Prj : forall t g c l,
    make_coercion (t, g, l) c -> 
    compose_coercions (Inj_c t, Prj_c t l) c
| Compose_Id_L : forall t c, compose_coercions (ιc t, c) c
| Compose_Id_R : forall t c, compose_coercions (c, ιc t) c
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
    t <≁> g -> compose_coercions (Inj_c t, Prj_c g l) (Fail_c t l g).

Hint Constructors compose_coercions.

Lemma compose_wt : forall c1 c2 t1 t2 t3,
    wt_coercion c1 (t1 ⇒ t2) /\ wt_coercion c2 (t2 ⇒ t3) ->
    exists c3, compose_coercions (c1, c2) c3 /\ wt_coercion c3 (t1 ⇒ t3).
Proof.
  intros c1 c2 t1 t2 t3 [wt_c1 wt_c2].
  inversion wt_c1; inversion wt_c2; subst; eauto. 
Qed. 


