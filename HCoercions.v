Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import General. 
Require Import Types.
Require Import Omega. 
Require Import SolveMax. 
Require Import Coercions. 

Definition lbl := nat.
Hint Unfold lbl.

Definition blame_info : Set := (ty * lbl * ty).
Hint Unfold blame_info. 

Inductive base : ty -> Prop :=
| Base_Int : base Int
| Base_Bool : base Bool. 

Inductive composite : ty -> Prop :=
| Composite_Arr {t1 t2} : composite (t1 → t2)
| Composite_Ref {t1}    : composite (Ref t1). 

Hint Constructors base composite.

Inductive hc_p :=
| prj_mt : hc_p
| prj    : lbl -> hc_p.



Theorem hc_p_eqdec :
  forall x y : hc_p,
    {x = y} + {x <> y}.
Proof. repeat (try unfold blame_info, lbl in *; decide equality). Qed. 

Inductive hc_i :=
| inj_mt : hc_i
| inj    : hc_i.

Theorem hc_i_eqdec : forall x y : hc_i, {x = y} + {x <> y}.
Proof. repeat (try unfold blame_info, lbl in *; decide equality). Qed. 

Inductive hc := 
| HC   : hc_p -> ty -> hc_m -> ty ->  hc_i -> hc
| Fail : hc_p -> ty ->  blame_info -> hc
with
hc_m :=
| Id_hc : hc_m
| Arr_hc : hc -> hc  -> hc_m
| Ref_hc : hc -> hc -> hc_m.

Scheme hc_ind_mut :=
  Induction for hc Sort Prop
  with hcm_ind_mut :=
  Induction for hc_m Sort Prop.

Theorem hc_eqdec : forall x y : hc_i, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Hint Constructors hc hc_m hc_i hc_p. 

Inductive hc_p_wt : hc_p -> cty -> Prop :=
| prj_mt_wt {t} : hc_p_wt prj_mt (t ⇒ t)
| prj_wt   {t l}: t <> Dyn -> hc_p_wt (prj l) (Dyn ⇒ t).

Inductive hc_i_wt : hc_i  -> cty -> Prop :=
| inj_mt_wt {t} : hc_i_wt inj_mt (t ⇒ t)
| inj_c_wt {t}  : t <> Dyn -> hc_i_wt inj (t ⇒ Dyn).


Fixpoint hc_depth h :=
  match h with
  | HC p t1 m t2 i => max (max (ty_depth t1) (ty_depth t2)) (hc_m_depth m)
  | Fail p t1 n => (ty_depth t1)
  end
with
hc_m_depth m :=
  match m with
  | Id_hc => 0
  | Arr_hc c1 c2 => 1 + max (hc_depth c1) (hc_depth c2)
  | Ref_hc c1 c2 => 1 + max (hc_depth c1) (hc_depth c2)
  end.

Open Scope depth_scope.
Instance hc_deep : Deep hc := hc_depth.
Instance hc_m_deep : Deep hc_m := hc_m_depth.
Hint Unfold hc_deep hc_m_deep. 



Inductive hc_wt : hc -> cty -> Prop := 
| hc_wt_HC : forall t1 t2 t3 t4 p m i,
    hc_p_wt p (t1 ⇒ t2) ->
    hc_m_wt m (t2 ⇒ t3) ->
    hc_i_wt i (t3 ⇒ t4) ->
    hc_wt (HC p t2 m t3 i) (t1 ⇒ t4)
| fail_wt : forall t1 t2 t4 p l I1 I2,
    t2 <> Dyn -> I1 <> Dyn -> I2 <> Dyn ->
    hc_p_wt p (t1 ⇒ t2) ->
    t2 !# I1 -> I1 # I2 ->  
    hc_wt (Fail p t2 (I1, l, I2)) (t1 ⇒ t4)
with
hc_m_wt : hc_m -> cty -> Prop :=
| Id_wt {t} : hc_m_wt Id_hc (t ⇒ t)
| Fn_hc_s_wt {t1 t2 t3 t4 c1 c2} :
    hc_wt c1 (t3 ⇒ t1) ->
    hc_wt c2 (t2 ⇒ t4) ->
    hc_m_wt (Arr_hc c1 c2) ((t1 → t2) ⇒ (t3 → t4))
| Ref_hc_s_wt {t1 t2 c1 c2} :
    hc_wt c1 (t2 ⇒ t1) ->
    hc_wt c2 (t1 ⇒ t2) ->
    hc_m_wt (Ref_hc c1 c2) ((Ref t1) ⇒ (Ref t2)).

Scheme hc_wt_ind_mut  := Induction for hc   Sort Prop
  with hcm_wt_ind_mut := Induction for hc_m Sort Prop.

Hint Constructors hc_i_wt hc_p_wt hc_m_wt hc_wt. 

Inductive hc_contains_hc : hc -> hc -> Prop :=
| Contains_Sub {p m i h t1 t2} :
    hc_m_sub_hc m h -> 
    hc_contains_hc (HC p t1 m t2 i) h
| Contains_Trans {p m i h h' t1 t2} : 
    hc_m_sub_hc m h' ->
    hc_contains_hc h' h ->
    hc_contains_hc (HC p t1 m t2 i) h
with
hc_m_sub_hc : hc_m -> hc -> Prop :=
| Contains_Arr_h1 {h1 h2}:
    hc_m_sub_hc (Arr_hc h1 h2) h1
| Contains_Arr_h2 {h1 h2}:
    hc_m_sub_hc (Arr_hc h1 h2) h2
| Contains_Ref_h1 {h1 h2}:
    hc_m_sub_hc (Ref_hc h1 h2) h1
| Contains_Ref_h2 {h1 h2}:
    hc_m_sub_hc (Ref_hc h1 h2) h2.

Hint Constructors hc_contains_hc hc_m_sub_hc.

Ltac rule_out_absurd_hc_contains :=
  solve [
  repeat match goal with
         | H: _ = _ |- _ => inverts H
         end;
  repeat match goal with
         | H: hc_contains_hc (Fail _ _ _) _ |- _ => inverts H
         | H: hc_contains_hc (HC _ (Id_hc _) _) _ |- _ => inverts H
         | H: hc_m_sub_hc Id_hc _  |- _ => inverts H
         | _ => solve [simpl; auto]
         end].

Lemma hc_size_lt_contained_hc : forall h,
    (forall h', hc_contains_hc h h' -> [|h'|] < [|h|]).
Proof.
  intro h. 
  elim h using hc_ind_mut with
    (P := fun h => forall h',
              hc_contains_hc h h' -> [|h'|] < [|h|])
    (P0 := fun m => forall h h',
               hc_m_sub_hc m h ->
               hc_contains_hc h h' -> [|h'|] < [|h|]).
  all: intuition. 
  all: try rule_out_absurd_hc_contains.
  all:
    try 
      solve
      [match goal with
       | H: hc_m_sub_hc _ _ |- _ => inverts keep H
       end;
       match goal with
       | H: hc_contains_hc _ _ , IH: context[_ < _ ] |- ?g =>
         solve [ apply IH; exact H]
       end]. 
  all: 
    match goal with
    | H: hc_contains_hc _ _ |- _ => inverts H
    end;
    match goal with
    | H: hc_m_sub_hc _ _ |- _ => inverts H
    end;
    try match goal with
        | H: hc_contains_hc ?h _ ,
             IH: context[hc_m_sub_hc _ _ -> hc_contains_hc _ _ -> _]
          |- _ =>
          apply IH in H
        end. 
    all: try (eauto; max_tac). 
Qed.

Lemma hc_depth_lt_contained_hc : forall h h',
    hc_contains_hc h h' -> [|h'|] < [|h|].
Proof.
  intro h. 
  elim h using hc_ind_mut with
    (P := fun h => forall h',
              hc_contains_hc h h' -> hc_depth h' < hc_depth h)
    (P0 := fun m =>
             forall h h',
               hc_m_sub_hc m h ->
               hc_contains_hc h h' ->
               hc_depth h' < hc_depth h);
     (* forall h, hc_m_sub_hc m h -> hc_depth h < hc_m_depth m *)
  intuition;
  try rule_out_absurd_hc_contains.
  (* This attempt has to go before the other *)
  all: match goal with
            | H: hc_contains_hc _ _ |- _ => inverts H
            end. 
  all: match goal with
       | H: hc_m_sub_hc _ _ |- _ => inverts keep H
       end.
  all: repeat match goal with
              | IH: context[_ -> _ -> _], 
                    H1: hc_m_sub_hc _ _,
                        H2: hc_contains_hc _ _
                |- _ => apply (IH _ _ H1) in H2
              | _ => solve[simpl in *; eauto] 
              end.
  all: 
    repeat match goal with
           | H: hc_m_sub_hc _ _ |- _ => inverts H
           end;
    match goal with
    | IH: _ -> _ |- _ => apply IH; eauto 
    end. 
Qed.

Hint Resolve hc_depth_lt_contained_hc. 

Lemma hc_contains_hc_depth_help : forall n h1 h2,
    [|h1|] < S n -> hc_contains_hc h1 h2 -> [|h2|] < n.
Proof. intuition. apply hc_depth_lt_contained_hc in H0. max_tac. Qed. 

Ltac contains_tac :=
  match goal with
    | H: [|?h1|] < S ?n |- [|?h2|] < ?n =>
      apply (hc_contains_hc_depth_help n h1 h2);
      [solve [eauto] | solve [eauto] | idtac ..]
  end.

Lemma hc_contains_trans' : forall n h1 h2 h3,
    [|h1|] < n -> 
    hc_contains_hc h1 h2 -> hc_contains_hc h2 h3 -> hc_contains_hc h1 h3.
Proof.
  induction n; intuition; inverts H0; inverts H1; eauto. 
  all: repeat match goal with
              | H: hc_m_sub_hc _ _ |- _ => inverts H
              end.
  all: match goal with
       | H: hc_contains_hc ?h1 ?h2 |- hc_contains_hc _ ?h3 =>
         apply (IHn h1 h2 h3) in H; 
           [solve [eauto] 
           | contains_tac 
           | eauto | idtac ..]
       end.
Qed.

Lemma hc_contains_trans : forall h1 h2 h3,
    hc_contains_hc h1 h2 -> hc_contains_hc h2 h3 -> hc_contains_hc h1 h3.
Proof. 
  introv H1 H2. 
  eapply (hc_contains_trans' (1 + (hc_depth h1)));
    eauto. 
Qed. 





Inductive mk_hc : ty * ty * lbl -> hc -> Prop :=
| Mk_hc_id {l t} :
    mk_hc (t, t, l) (HC prj_mt t Id_hc t inj_mt)
| Mk_hc_dyn_l {t l} :
    t <> Dyn -> mk_hc (Dyn, t, l) (HC (prj l) t Id_hc t inj_mt)
| Mk_hc_dyn_r {t l} :
    t <> Dyn -> mk_hc (t, Dyn, l) (HC prj_mt t Id_hc t inj)
| Mk_hc_arr {t1 t2 t3 t4 l c1 c2} :
    t1 → t2 <> t3 → t4 -> 
    mk_hc (t3, t1, l) c1 -> mk_hc (t2, t4, l) c2 ->
    mk_hc (t1 → t2, t3 → t4, l)
          (HC prj_mt (t1 → t2) (Arr_hc c1 c2) (t3 → t4) inj_mt)
| Mk_hc_ref {t1 t2 l c1 c2} :
    Ref t1 <> Ref t2 -> 
    mk_hc (t2, t1, l) c1 ->
    mk_hc (t1, t2, l) c2 ->
    mk_hc (Ref t1, Ref t2, l)
          (HC prj_mt (Ref t1) (Ref_hc c1 c2) (Ref t2) inj_mt)
(* need to define compatability this includes (t1 -> t2) *) 
| Mk_hc_fail {t g l} :
    t # g -> mk_hc (t, g, l) (Fail prj_mt t (t, l, g)).

Hint Constructors mk_hc. 

Lemma mk_hc_wt' : forall n t1 t2 l h,
    [|h|] < n ->
    mk_hc (t1, t2, l) h -> hc_wt h (t1 ⇒ t2).
Proof.
  induction n; intuition. 
  inverts H0; auto.  
  - eapply IHn in H6; eapply IHn in H7. eauto. 
    contains_tac. 
    contains_tac. 
    contains_tac. 
  - eapply IHn in H6; eapply IHn in H7. eauto. 
    contains_tac. 
    contains_tac. 
    contains_tac. 
  - eauto. 
Qed. 

Lemma mk_hc_wt : forall t1 t2 l h,
    mk_hc (t1, t2, l) h -> hc_wt h (t1 ⇒ t2).
Proof. intuition. eapply (mk_hc_wt' (1 + hc_depth h)); eauto. Qed. 
 
Hint Resolve mk_hc_wt. 

Lemma inconsistent_symetric : forall t1 t2, t1 ≁ t2 -> t2 ≁ t1. 
Proof. auto. Qed.

Hint Resolve inconsistent_symetric. 

Ltac prove_inconsistent :=
  match goal with
  | |- _ ≁ _ => solve [intro h; inversion h]
  | |- _ # _ => solve [intro h; inversion h]
  | |- _ ∼ _ => constructor
  end.

Lemma mk_hc_symetry' : forall n h t1 t2 l,
    [|h|] < n -> 
    mk_hc (t1, t2, l) h -> 
    exists h',
      (mk_hc (t2, t1, l) h' /\ [|h'|] <= max [|t1|] [|t2|]).
Proof.
  induction n; introv bnd mk.
  - intuition. 
  - inverts mk. 
  all:
    repeat match goal with
           | H: mk_hc (?t1, ?t2, ?l) ?h |- _ =>
             let h':=fresh in
             let mk:=fresh in
             let bnd:=fresh in 
             apply (IHn h t1 t2 l) in H;
               [destruct H as [h' [mk bnd]]
               | solve[contains_tac]]
           end.
  all:
    try (eexists; split; [solve[eauto]|max_tac]).  
Qed. 

Lemma mk_hc_symetry : forall h t1 t2 l,
    mk_hc (t1, t2, l) h -> 
    exists h', mk_hc (t2, t1, l) h' /\ [|h'|] <= max [|t1|] [|t2|].
Proof. intuition. eapply (mk_hc_symetry' (S (hc_depth h))); eauto. Qed. 

Hint Resolve mk_hc_symetry.

Lemma mk_hc_function' : forall n h h' t1 t2 l,
    [|t1|] < n ->
    [|t2|] < n -> 
    mk_hc (t1, t2, l) h ->
    mk_hc (t1, t2, l) h' ->
    h = h'.
Proof. induction n; intuition. 
       all: match goal with
            | H1: mk_hc _ _, H2: mk_hc _ _ |- _ => inverts H1; inverts H2
            end.
       all: try match goal with
             | H: _ <> _  |- _ => solve[contradiction H; auto]
             | H: _ # _ |- _ => solve[contradiction H; auto]
             | H: _ = _ |- _ => discriminate
             | _ => auto
             end.
       all: 
         repeat 
           match goal with 
           | IH: context[mk_hc _ _ -> mk_hc _ _ -> _ = _],
                 H1: mk_hc (?t1, ?t2, _) ?c1,
                     H2: mk_hc (?t1, ?t2, _) ?c2 |- _ =>
             apply (IH c1 c2) in H1; 
               [subst 
               | solve [max_tac] 
               | solve [max_tac] 
               | solve [auto] 
               | idtac ..]
           | _ => solve [auto]
           end.
Qed. 

Lemma mk_hc_function : forall h1 h2 t1 t2 l,
    mk_hc (t1, t2, l) h1 ->
    mk_hc (t1, t2, l) h2 ->
    h1 = h2.
Proof. intros h1 h2 t1 t2 l.
       apply (mk_hc_function' (1 + [|t1|] + [| t2 |])).
       max_tac. 
       max_tac. 
Qed.

Hint Resolve mk_hc_function.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.

Program Fixpoint mk_hcf t1 t2 l {measure ((ty_depth t1) + (ty_depth t2))} : hc :=
  if (beq_ty t1 t2) then (HC prj_mt t1 Id_hc t2 inj_mt) else
    match t1, t2 with
    | Dyn, t2  => (HC (prj l) t2 Id_hc t2 inj_mt)
    | t1 , Dyn => (HC prj_mt t1 Id_hc t1 inj)
    | (t11 → t12), (t21 → t22) =>
      (HC prj_mt (t11 → t12)
          (Arr_hc (mk_hcf t21 t11 l)
                  (mk_hcf t12 t22 l))
          (t21 → t22) inj_mt)
    | (Ref t1), Ref t2 =>
      (HC prj_mt (Ref t1)
          (Ref_hc (mk_hcf t2 t1 l) (mk_hcf t1 t2 l))
          (Ref t2) inj_mt)
    | _, _ => Fail prj_mt t1 (t1, l, t2)
    end.


Solve All Obligations with tc_mk_coercion. 
Notation "[ t => l => g ]" := (mk_hcf t g l) (at level 70). 

Lemma mk_hc_total : forall t1 t2 l,
    exists h, mk_hc (t1, t2, l) h /\ hc_depth h <= max (ty_depth t1) (ty_depth t2). 
Proof.
  induction t1; destruct t2; intros.
    (* apply IH when possible *)
  all:
    repeat
      match goal with
      | IH: (forall t l, exists h, mk_hc (?g, t, l) h /\ _),
            T: ty,
               L: lbl |- _ =>
        match goal with
        | H: mk_hc (g, T, L) _ |- _ => fail 1
        | |- context[mk_hc(g → _, T → _, _) _] => destruct (IH T l)
        | |- context[mk_hc(_ → g, _ → T, _) _] => destruct (IH T l)
        | |- context[mk_hc(_ → _, _ → _, _) _] => fail 1 
        | _ => destruct (IH T L)
        end;
        repeat
          match goal with
          | H: exists x, _ |- _ => destruct H
          | H: _ /\ _ |- _ => destruct H
          end
      end.
  all: (* References and Functions need symmetry too *)
    try
      match goal with
      | H: mk_hc (?t1, ?t2, _) _ |- context[mk_hc(Ref ?t1, Ref ?t2, _) _] => 
        destruct (mk_hc_symetry _ _ _ _ H)
      | H: mk_hc (?t1, ?t2, _) _ |- context[mk_hc(?t1 → _, ?t2 → _, _) _] =>
        destruct (mk_hc_symetry _ _ _ _ H)
      end;
    repeat
      match goal with
      | H: exists x, _ |- _ => destruct H
      | H: _ /\ _ |- _ => destruct H
      end.
  
  (* case on whether the types are the same *)
  all: 
    match goal with
    | |- context[mk_hc (?t1, ?t2, _) _] =>
      let H1:=fresh in
      let H2:=fresh in
      destruct (ty_eqdec t1 t2) as [H2 | H2];
        [ try discriminate; inverts H2 |
          try solve [contradiction H2; eauto] ]
          
    end.
  all: 
    match goal with
    | |- context[mk_hc (?t1, ?t2, _) _] =>
      let H1:=fresh in
      destruct (ty_shallow_consistency_dec t1 t2) as [H1 | H1];
        [ try discriminate; inverts H1 |
          try solve [contradiction H1; eauto] ]
    end.
  (* solve by deriving proofs of existance and inequalities *)

  all: 
    try 
      solve [eexists; split; 
             [solve[try (constructor; discriminate); eauto]
             | max_tac]].
Qed. 


Lemma mk_hc_not_dyn : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn ->
    (exists m, mk_hc (t1, t2, l) (HC prj_mt t1 m t2 inj_mt)) \/ 
    (mk_hc (t1, t2, l) (Fail prj_mt t1 (t1, l, t2))).
Proof.
  intros t1 t2 l H1 H2. destruct (mk_hc_total t1 t2 l) as [h [mk_h bound]]. 
  inverts mk_h; eauto.
Qed.

Hint Resolve mk_hc_not_dyn.

Lemma mk_hc_not_dyn_sconsist : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn -> t1 !# t2 ->
    (exists m, mk_hc (t1, t2, l) (HC prj_mt t1 m t2 inj_mt)). 
Proof. intros t1 t2 l H1 H2 H3;
         destruct (mk_hc_not_dyn t1 t2 l H1 H2);
         inverts H3;
         repeat match goal with
                | H: _ <> _ |- _ => solve [contradiction H; reflexivity]
                | H: _ # _ |- _ => solve [contradiction H; eauto]
                | H: mk_hc _ (Fail _ _ _) |- _ => inverts H
                | _ => eauto
                end.
Qed. 

Lemma mk_hc_not_dyn_sinconsist : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn -> t1 # t2 ->
    mk_hc (t1, t2, l) (Fail prj_mt t1 (t1, l, t2)).
Proof.
 intros t1 t2 l H1 H2 H3;
 destruct (mk_hc_not_dyn t1 t2 l H1 H2); eauto. 
Qed. 

Hint Resolve mk_hc_not_dyn_sinconsist mk_hc_not_dyn_sconsist.

Inductive compose_hc : (hc * hc) -> hc -> Prop :=
|Comp_hc_Dyn_L {p i h}:
   (* - Comp_hc_fail_no_prj doesn't overlap here because of the typing rule
        for fail not allowing t2 to be Dyn and the projection is mt
      - Comp_hc_fail_inj_prj doesn't overlap because of the explicit
        inj of the rhs coercion
      - in short the second hyper-coercion may be a failure but 
        doesn't overlap with any of the failure cases for compose *)
   compose_hc (HC p Dyn Id_hc Dyn i, h) h
|Comp_hc_Dyn_R {p1 m1 t1 t2 p2 i2}:
   (* specified as HC so that Comp_hc_fail_L doesn't apply *)
   compose_hc (HC p1 t1 m1 t2 inj, HC p2 Dyn Id_hc Dyn i2)
              (HC p1 t1 m1 t2 inj)
|Comp_hc_no_prj {p1 m1 m2 i2 m3 t11 t22 t}:
   compose_hc_m (m1, m2) m3 ->
   compose_hc (HC p1 t11 m1 t inj_mt, HC prj_mt t m2 t22 i2)
              (HC p1 t11 m3 t22 i2)
|Comp_hc_inj_prj_ok {p1 m1 l m2 i2 t1 t2 t3 t4 m3 m4 m5}:
   t2 <> Dyn ->
   t3 <> Dyn ->
   mk_hc (t2, t3, l) (HC prj_mt t2 m3 t3 inj_mt) ->
   compose_hc_m (m1, m3) m4 ->
   compose_hc_m (m4, m2) m5 ->
   compose_hc (HC p1 t1 m1 t2 inj, HC (prj l) t3 m2 t4 i2)
              (HC p1 t1 m5 t4 i2)
|Comp_hc_inj_prj_fail {p1 m1 l m2 i2 t2 t3 t1 t4 nfo}:
   t2 <> Dyn ->
   t3 <> Dyn ->
   mk_hc (t2, t3, l) (Fail prj_mt t2 nfo) ->
   compose_hc (HC p1 t1 m1 t2 inj, HC (prj l) t3 m2 t4 i2)
              (Fail p1 t1 nfo)
|Comp_hc_fail_L1 {p1 t1 l h}:
   (* doesn't overlap with Comp_hc_Dyn_R *)
   compose_hc (Fail p1 t1 l, h) (Fail p1 t1 l)
(*|Comp_hc_fail_L2 {p1 t1 t2 p2 t3 t4 l1 l2}:
   compose_hc (Fail p1 t1 l1 t2, Fail p2 t3 l2 t4) (Fail p1 t1 l1 t4) *)
|Comp_hc_fail_no_prj {p1 m1 t1 t2 n1}:
   (* doesn't overlap with Comp_hc_Dyn_L because t2 cannot be
      Dyn according to the typing rules and
      there isn't a m1 that would type t1 at Dyn *)
   compose_hc (HC p1 t1 m1 t2 inj_mt, Fail prj_mt t2 n1) (Fail p1 t1 n1)
|Comp_hc_fail_inj_prj_ok {p1 m1 l1 t3 t1 t2 m3 n}:
   (* Don't have to consider inj_mt dyn because that is covered
      via Comp_hc_Dyn_L *)
   mk_hc (t2, t3, l1) (HC prj_mt t2 m3 t3 inj_mt) ->
   compose_hc (HC p1 t1 m1 t2 inj, Fail (prj l1) t3 n) (Fail p1 t1 n)
|Comp_hc_fail_inj_prj_fail {p1 m1 l1 t3 t1 t2 n1 n2}:
   (* Don't have to consider inj_mt dyn because that is covered
      via Comp_hc_Dyn_L *)
   mk_hc (t2, t3, l1) (Fail prj_mt t2 n2) ->
   compose_hc (HC p1 t1 m1 t2 inj, Fail (prj l1) t3 n1) (Fail p1 t1 n2)              
with
(* assuming m1 : t1 => t2 and m2 : t2 => t3 *)
compose_hc_m : (hc_m * hc_m) -> hc_m -> Prop :=
| compose_hc_id_L {m} : compose_hc_m (Id_hc, m) m
| compose_hc_id_R {m} : compose_hc_m (m, Id_hc) m
| compose_Arr {h1 h2 h3 h4 h5 h6}:
    compose_hc (h3, h1) h5 ->
    compose_hc (h2, h4) h6 -> 
    compose_hc_m (Arr_hc h1 h2, Arr_hc h3 h4) (Arr_hc h5 h6)
| compose_Ref {h1 h2 h3 h4 h5 h6} :
    compose_hc (h3, h1) h5 ->
    compose_hc (h2, h4) h6 ->
    compose_hc_m (Ref_hc h1 h2, Ref_hc h3 h4) (Ref_hc h5 h6). 

Hint Constructors compose_hc compose_hc_m. 

Ltac dupH H :=
  let H':=fresh in
  let P :=type of H in
  assert (H' : P); try exact H. 


Lemma mk_hc_id : forall t l, mk_hc (t, t, l) (HC prj_mt t Id_hc t inj_mt).
Proof. intros [] l; auto. Qed. 

Lemma hc_m_le_hc_depth : forall p m i t1 t2,
     [| m |] <= [| HC p t1 m t2 i |]. 
Proof. intros p m i t1 t2. autounfold. simpl. auto. Qed. 

Hint Resolve hc_m_le_hc_depth. 

Lemma max_0_n : forall n, max 0 n = 0 -> n = 0.
Proof. induction n; auto. Qed.

Lemma max_n_0: forall n, max n 0 = 0 -> n = 0.
Proof. induction n; auto. Qed. 

Hint Resolve max_0_n max_n_0 Max.max_lub_l Max.max_lub_r. 


(* Max.max_spec
     : forall n m : nat,
       n < m /\ Nat.max n m = m \/ m <= n /\ Nat.max n m = n *)
Lemma max_n_m_eq_n_le : forall n m,
    max n m = n -> m <= n.
Proof.
  induction n; intros [] H; try (apply max_0_n in H; discriminate); auto.
Qed.

Lemma max_n_m_eq_m_le : forall n m,
    max m n = n -> m <= n.
Proof.
  induction n; intros [] H; try (apply max_0_n in H; discriminate); auto.
Qed.

Hint Resolve max_n_m_eq_n_le max_n_m_eq_m_le.


