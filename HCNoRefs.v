
Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import GTypesNoRefs.
Require Import Omega. 


Inductive base : Ty -> Prop :=
| Base_Int : base Int
| Base_Bool : base Bool. 

Inductive composite : Ty -> Prop :=
| Composite_Arr {t1 t2} : composite (t1 → t2).

Hint Constructors base composite.

Inductive hc_p :=
| prj_mt : hc_p
| prj    : blame_info -> hc_p.

Ltac decide_equality :=
  repeat (try unfold blame_info in *; decide equality).

Theorem hc_p_eqdec :
  forall x y : hc_p,
    {x = y} + {x <> y}.
Proof. decide_equality. Defined.

Inductive hc_i : Type :=
| inj_mt : hc_i
| inj    : hc_i.

Theorem hc_i_eqdec : forall x y : hc_i, {x = y} + {x <> y}.
Proof. decide_equality. Defined.

Inductive hc : Type := 
| HC   : hc_p -> hc_m -> hc_i -> hc
| Fail : hc_p -> Ty -> blame_info -> hc
with
hc_m : Type :=
| Id_hc : Ty -> hc_m
| Arr_hc : Ty -> Ty -> Ty -> Ty -> hc -> hc  -> hc_m.

Scheme hc_ind_mut :=
  Induction for hc Sort Prop
  with hcm_ind_mut :=
  Induction for hc_m Sort Prop.

Theorem hc_eqdec : forall x y : hc_i, {x = y} + {x <> y}.
Proof. decide_equality. Defined.

Hint Constructors hc hc_m hc_i hc_p. 

Inductive hc_p_wt : hc_p -> CTy -> Prop :=
| prj_mt_wt {t} : hc_p_wt prj_mt (t ⇒ t)
| prj_wt   {t l}: t <> Dyn -> hc_p_wt (prj l) (Dyn ⇒ t).

Inductive hc_i_wt : hc_i  -> CTy -> Prop :=
| inj_mt_wt {t} : hc_i_wt inj_mt (t ⇒ t)
| inj_c_wt {t}  : t <> Dyn -> hc_i_wt inj (t ⇒ Dyn).


Inductive hc_wt : hc -> CTy -> Prop := 
| hc_wt_HC : forall t1 t2 t3 t4 p m i,
    hc_p_wt p (t1 ⇒ t2) ->
    hc_m_wt m (t2 ⇒ t3) ->
    hc_i_wt i (t3 ⇒ t4) ->
    hc_wt (HC p m i) (t1 ⇒ t4)
| fail_wt : forall t1 t2 t3 p l,
    hc_p_wt p (CArr t1 t2) ->
    hc_wt (Fail p t2 l) (t1 ⇒ t3)
with
hc_m_wt : hc_m -> CTy -> Prop :=
| Id_wt {t} : hc_m_wt (Id_hc t) (t ⇒ t)
(* | Id_Dyn_wt : hc_m_wt (Id_hc Dyn) (Dyn ⇒ Dyn)
   | Id_base_wt  {t} :
    base t ->
    hc_m_wt (Id_hc t) (t ⇒ t) *)
| Fn_hc_s_wt {t1 t2 t3 t4 c1 c2} :
    hc_wt c1 (t3 ⇒ t1) ->
    hc_wt c2 (t2 ⇒ t4) ->
    hc_m_wt (Arr_hc t1 t2 t3 t4 c1 c2)
            ((t1 → t2) ⇒ (t3 → t4)).

Scheme hc_wt_ind_mut  := Induction for hc   Sort Prop
  with hcm_wt_ind_mut := Induction for hc_m Sort Prop.

Hint Constructors hc_i_wt hc_p_wt hc_m_wt hc_wt. 

Inductive hc_contains_hc : hc -> hc -> Prop :=
| Contains_Sub {p m i h} :
    hc_m_sub_hc m h -> 
    hc_contains_hc (HC p m i) h
| Contains_Trans {p m i h h'} : 
    hc_m_sub_hc m h' ->
    hc_contains_hc h' h ->
    hc_contains_hc (HC p m i) h
with
hc_m_sub_hc : hc_m -> hc -> Prop :=
| Contains_Arr_h1 {t1 t2 t3 t4 h1 h2}:
    hc_m_sub_hc (Arr_hc t1 t2 t3 t4 h1 h2) h1
| Contains_Arr_h2 {t1 t2 t3 t4 h1 h2}:
    hc_m_sub_hc (Arr_hc t1 t2 t3 t4 h1 h2) h2.

(*
Inductive hc_contains_ty : hc -> Ty -> Prop :=
| Contains_Id {p i t} :
    hc_contains_ty (HC p (Id_hc t) i) t
| Contains_Fail {p t i}:
    hc_contains_ty (Fail p t i) t
| Contains_Sub {p m i h t} :
    hc_m_contains_hc m h ->
    hc_contains_ty h t ->
    hc_contains_ty (HC p m i) t. *)

Hint Constructors hc_contains_hc hc_m_sub_hc.

Ltac rule_out_absurd_hc_contains :=
  solve [
  repeat match goal with
         | H: _ = _ |- _ => inverts H
         end;
  repeat match goal with
         | H: hc_contains_hc (Fail _ _ _) _ |- _ => inverts H
         | H: hc_contains_hc (HC _ (Id_hc _) _) _ |- _ => inverts H
         | H: hc_m_sub_hc (Id_hc _) _  |- _ => inverts H
         | _ => solve [simpl; auto]
         end].

Lemma hc_contains_trans : forall h h' h'',
    hc_contains_hc h h' -> hc_contains_hc h' h'' -> hc_contains_hc h h''.
Proof.
  intro h.
  elim h using hc_ind_mut with
  (P := fun h => forall h' h'',
            hc_contains_hc h h' -> hc_contains_hc h' h'' -> hc_contains_hc h h'')
  (P0 := fun m => forall p i h' h'',
   hc_contains_hc (HC p m i) h' -> hc_contains_hc h' h'' ->
   hc_contains_hc (HC p m i) h'');
    intuition; try rule_out_absurd_hc_contains;
      try solve
          [match goal with
           | H: hc_contains_hc _ _ |- _ =>
             inverts H;
             solve [
                 match goal with
                 | H: hc_m_sub_hc _ _ |- _ => inverts H
                 end;
                 eauto
               ]
           end].
Qed.


(*
Inductive hc_wt : hc -> CTy -> Prop :=
| hc_wt_HC_Id : forall t1 t2 t3 p i,
    hc_p_wt p (t1 ⇒ t2) ->
    hc_i_wt i (t2 ⇒ t3) ->
    hc_wt (HC p (Id_hc t2) i) (t1 ⇒ t3)
| hc_wt_HC_Arr : forall t1 t21 t22 t23 t24 t3 p h1 h2 i,
    hc_p_wt p (t1 ⇒ t21 → t22) ->
    hc_wt h1 (t23 ⇒ t21) ->
    hc_wt h2 (t22 ⇒ t24) ->
    hc_i_wt i (t23 → t24 ⇒ t3) ->
    hc_wt (HC p (Arr_hc t21 t22 t23 t24 h1 h2) i) (t1 ⇒ t3)
| hc_wt_HC_Ref : forall t1 t21 t22 t3 p h1 h2 i,
    hc_p_wt p (t1 ⇒ Ref t21) ->
    hc_wt h1 (t21 ⇒ t22) ->
    hc_wt h2 (t22 ⇒ t21) ->
    hc_i_wt i (Ref t22 ⇒ t3) ->
    hc_wt (HC p (Ref_hc t21 t22 h1 h2) i) (t1 ⇒ t3)
| fail_wt : forall t1 t2 t3 p l,
    hc_p_wt p (CArr t1 t2) ->
    hc_wt (Fail p t2 l) (t1 ⇒ t3).

Hint Constructors hc_i_wt hc_p_wt hc_wt. 
*)

Inductive mk_hc : Ty * Ty * blame_info -> hc -> Prop :=
| Mk_hc_id {l t} :
    mk_hc (t, t, l) (HC prj_mt (Id_hc t) inj_mt)
| Mk_hc_dyn_l {t l} :
    t <> Dyn -> mk_hc (Dyn, t, l) (HC (prj l) (Id_hc t) inj_mt)
| Mk_hc_dyn_r {t l} :
    t <> Dyn -> mk_hc (t, Dyn, l) (HC prj_mt (Id_hc t) inj)
| Mk_hc_arr {t1 t2 t3 t4 l c1 c2} :
    t1 → t2 <> t3 → t4 -> 
    mk_hc (t3, t1, l) c1 -> mk_hc (t2, t4, l) c2 ->
    mk_hc (t1 → t2, t3 → t4, l)
          (HC prj_mt (Arr_hc t1 t2 t3 t4 c1 c2) inj_mt)
(* need to define compatability this includes (t1 -> t2) *) 
| Mk_hc_fail {t g l} :
    t <≁> g -> mk_hc (t, g, l) (Fail prj_mt t l).

Hint Constructors mk_hc. 

Lemma mk_hc_wt : forall t1 t2 l h,
    mk_hc (t1, t2, l) h -> hc_wt h (t1 ⇒ t2).
Proof.
  intros t1 t2 l h; gen t1 t2 l.
  Check hc_ind_mut.
  elim h using hc_ind_mut with
  (P := fun h => forall t1 t2 l,
            mk_hc (t1, t2, l) h ->
            hc_wt h (t1 ⇒ t2))
  (P0 := fun m => 
           match m with
           | (Id_hc i) => True
           | (Arr_hc _ _ _ _ h1 h2) =>
             (forall t1 t2 l,
                 mk_hc (t1, t2, l) h1 ->
                 hc_wt h1 (t1 ⇒ t2)) /\
             (forall t1 t2 l,
                 mk_hc (t1, t2, l) h2 ->
                 hc_wt h2 (t1 ⇒ t2))
           end).
  + intros p m IH i t1 t2 l H; destruct m;
      (* Invert and original mk_hc's *)
      repeat match goal with
             | H: Dyn <> Dyn |- _ => contradiction H; reflexivity
             | H: mk_hc _ (HC _ _ _) |- _ => inverts H
             end;
      (* Use sub mk_hc's to derive IH's *)
      repeat match goal with
             | |- _ /\ _ => split 
             | IH: _ /\ _ |- _ => destruct IH
             | IH: context[mk_hc _ ?h -> _],
                   H: mk_hc _ ?h
               |-  _
               => apply IH in H
             | _ => eauto
             end. 
  + intros _1 _2 _3 _4 _5 _6 H. inverts H; auto.
  + trivial.
  + auto.
Qed. 

Hint Resolve mk_hc_wt. 

Lemma inconsistent_symetric : forall t1 t2, t1 ≁ t2 -> t2 ≁ t1. 
Proof. auto. Qed.

Hint Resolve inconsistent_symetric. 

Ltac prove_inconsistent :=
  match goal with
  | |- _ ≁ _ => solve [intro h; inversion h]
  | |- _ <≁> _ => solve [intro h; inversion h]
  | |- _ ∼ _ => constructor
  end.

Fixpoint hc_depth h :=
  match h with
  | HC _ m _ => hc_m_depth m
  | Fail _ t _ => 1
  end
with
hc_m_depth m :=
  match m with
  | Id_hc t => ty_depth t
  | Arr_hc t1 t2 t3 t4 h1 h2 =>
    1 + max (max (hc_depth h1) (max (ty_depth t3) (ty_depth t1)))
            (max (hc_depth h2) (max (ty_depth t2) (ty_depth t4)))
  end. 

(*
Lemma one_le_ty_depth : forall t, 1 <= ty_depth t. 
Proof. induction t;
         simpl;
         try match goal with
             | |- context[max ?t1 ?t2] =>
               destruct (Max.max_dec t1 t2) as [eq | eq];
                 rewrite eq in *
             end;
         eauto.
Qed.

Hint Resolve one_le_ty_depth. 

Lemma one_le_hc_depth : forall h, 1 <= hc_depth h.
Proof. destruct h; simpl; auto using one_le_ty_depth. Qed. 

Lemma one_le_hc_m_depth: forall h, 1 <= hc_m_depth h.
Proof. destruct h; simpl; auto using one_le_hc_depth, one_le_ty_depth. Qed.

Hint Resolve one_le_hc_depth one_le_hc_m_depth one_le_ty_depth. 
 *)

Lemma max_spec_eq_r : forall n m, max n m = n -> m <= n.
Proof.
  intros n m H. destruct (Max.max_spec n m); omega. 
Qed. 

Lemma max_spec_eq_l : forall n m, max n m = m -> n <= m.
Proof. 
  intros n m H. destruct (Max.max_spec n m); try omega.
Qed.

Hint Resolve max_spec_eq_r max_spec_eq_l. 

Ltac omega_max_search depth :=
  match depth with
  | 0 =>  fail
  | S ?n => 
    try match goal with
        | |- context[max ?t1 ?t2] =>
          let e:=fresh in
          destruct (Max.max_dec t1 t2) as [e|e];
          rewrite e in *;
          [ apply max_spec_eq_r in e |
            apply max_spec_eq_l in e ];
          omega_max_search n
        | |- match ?t with _ => _ end =>
          destruct t; omega_max_search n
        end

  end.

Ltac max_dec_tac_context := 
  (* this match leads to exponential blowup :( *) 
  repeat match goal with
         | H: context[max ?t1 ?t2] |- _ =>
           let e:=fresh in
           destruct (Max.max_dec t1 t2) as [e|e];
           rewrite e in *;
           [ apply max_spec_eq_r in e |
             apply max_spec_eq_l in e ]
         end.

Fixpoint hc_size h :=
  match h with
  | HC _ m _ => hc_m_size m
  | Fail _ t _ => 0
  end
with
hc_m_size m :=
  match m with
  | Id_hc t => ty_size t
  | Arr_hc t1 t2 t3 t4 h1 h2 => 1 + hc_size h1 + hc_size h2
  end. 


Lemma one_le_ty_size : forall t, 1 <= ty_size t. 
Proof. induction t; simpl; auto. Qed. 

Hint Resolve one_le_ty_size.

Lemma one_le_hc_m_size : forall m, 1 <= hc_m_size m.
Proof.
  intros []; intros; simpl; auto. Qed. 


Hint Resolve one_le_hc_m_size.


Ltac reveal_minimum_sizes :=
  match goal with
  | t: Ty |- _ => 
    match goal with
    | H: 1 <= ty_size t |- _ => fail 1
    | _ => cut (1 <= ty_size t); [ intro | auto ..]
    end
  | m : hc_m |- _ =>
    match goal with
    | H: 1 <= hc_m_size m |- _ => fail 1
    | _ =>  cut (1 <= hc_m_size m); [ intro | auto ..]
    end
  end.




Ltac expose_depth_min_tac :=
  repeat match goal with
         | t: Ty |- _ => 
           match goal with
           | H: 1 <= ty_depth t |- _ => fail 1
           | _ => cut (1 <= ty_depth t); [ intro | solve [auto] | auto ..]
           end
         (*| h: hc |- _ => 
           match goal with
           | H: 1 <= hc_depth h |- _ => fail 1
           | _ => cut (1 <= hc_depth h); [ intro | solve [auto] | auto ..]
           end
         | h: hc_m |- _ => 
           match goal with
           | H: 1 <= hc_m_depth h |- _ => fail 1
           | _ => cut (1 <= hc_m_depth h); [ intro | solve [auto] | auto ..]
           end *)
         | _ => reveal_minimum_sizes
         end.
Ltac omega_max :=
  simpl in *;
  expose_depth_min_tac;
  repeat
    match goal with
    | e: _ = _ |- _ => rewrite e
    end;
  max_dec_tac_context; 
  omega_max_search 5;
  max_dec_tac_context; 
  omega. 


Lemma mk_hc_symetry_size : forall h t1 t2 l,
    mk_hc (t1, t2, l) h -> exists h', mk_hc (t2, t1, l) h' /\ hc_size h = hc_size h'.
Proof.
  intros h. 
  elim h using hc_ind_mut with
  (P := fun h => forall t1 t2 l,
            mk_hc (t1, t2, l) h ->
            exists h', mk_hc (t2, t1, l) h' /\ hc_size h = hc_size h')
  (P0 := fun m => 
   match m with
   | (Id_hc i) => True
   | (Arr_hc _ _ _ _ h1 h2) =>
     (forall t1 t2 l,
         mk_hc (t1, t2, l) h1 ->
         exists h', mk_hc (t2, t1, l) h' /\ hc_size h1 = hc_size h') /\
     (forall t1 t2 l,
         mk_hc (t1, t2, l) h2 ->
         exists h', mk_hc (t2, t1, l) h'  /\ hc_size h2 = hc_size h')
   end).
  - intros p m P i t1 t2 l H.
    destruct m; inverts H;
      repeat match goal with
             | |- _ /\ _ => split
             | H: exists h, _ |- _ =>
               let h:=fresh in destruct H as [h []]
             | IH: _ /\ _ |- _ => destruct IH
             | IH: (forall t1 t2 l, _ -> _),
                   H: mk_hc _ ?h |-  _
               => apply IH in H
             | _ => intuition (eauto; omega)
             | _ => solve [eexists; split; [> eauto | simpl in *; omega]]
             end.
  - intros p t b t1 t2 l H. inversion H.
    eexists. split. constructor. intro contra.
    inversion contra; subst;  auto. subst. 
    auto. 
  - trivial.
  - auto.
Qed.

(*
Lemma mk_hc_symetry_depth : forall h t1 t2 l,
    mk_hc (t1, t2, l) h -> exists h', mk_hc (t2, t1, l) h' /\ hc_depth h = hc_depth h'.
Proof.
  intros h. 
  elim h using hc_ind_mut with
  (P := fun h => forall t1 t2 l,
            mk_hc (t1, t2, l) h ->
            exists h', mk_hc (t2, t1, l) h' /\ hc_depth h = hc_depth h')
  (P0 := fun m => 
   match m with
   | (Id_hc i) => True
   | (Arr_hc _ _ _ _ h1 h2) =>
     (forall t1 t2 l,
         mk_hc (t1, t2, l) h1 ->
         exists h', mk_hc (t2, t1, l) h' /\ hc_depth h1 = hc_depth h') /\
     (forall t1 t2 l,
         mk_hc (t1, t2, l) h2 ->
         exists h', mk_hc (t2, t1, l) h'  /\ hc_depth h2 = hc_depth h')
   | (Ref_hc _ _ h1 h2) =>
     (forall t1 t2 l,
         mk_hc (t1, t2, l) h1 ->
         exists h', mk_hc (t2, t1, l) h'  /\ hc_depth h1 = hc_depth h') /\
     (forall t1 t2 l,
         mk_hc (t1, t2, l) h2 ->
         exists h', mk_hc (t2, t1, l) h'  /\ hc_depth h2 = hc_depth h')
   end).
  - intros p m P i t1 t2 l H.
    destruct m; inverts H;
      repeat match goal with
             | |- _ /\ _ => split
             | H: exists h, _ |- _ =>
               let h:=fresh in destruct H as [h []]
             | IH: _ /\ _ |- _ => destruct IH
             | IH: (forall t1 t2 l, _ -> _),
                   H: mk_hc _ ?h |-  _
               => apply IH in H
             | _ => intuition (eauto; omega)
             | _ => solve [eexists; split; [> eauto | omega_max]]
             end.
  - intros p t b t1 t2 l H. inversion H.
    eexists. split. constructor. intro contra.
    inversion contra; subst;  auto. subst. 
    auto. 
  - trivial.
  - auto.
  - auto.
Qed. *)

Hint Resolve mk_hc_symetry_size.





Lemma mk_hc_function_size : forall n h h' t1 t2 l,
    ty_size t1 + ty_size t2 <= n -> 
    mk_hc (t1, t2, l) h ->
    mk_hc (t1, t2, l) h' ->
    h = h'.
Proof. induction n.
       - intros h h' [] [] l mk1 mk2; simpl in *; omega.  
       - intros h h' [] [] l bound mk1 mk2;
         match goal with
         | H1: mk_hc _ _, H2: mk_hc _ _ |- _ => inverts H1; inverts H2
         end;
         try match goal with
             | H: _ <> _  |- _ => solve[contradiction H; auto]
             | H: _ <≁> _ |- _ => solve[contradiction H; auto]
             | H: _ = _ |- _ => discriminate
             | _ => auto
             end;
         repeat match goal with 
                | IH: context[mk_hc _ _ -> mk_hc _ _ -> _ = _],
                      H1: mk_hc (?t1, ?t2, _) ?c1,
                          H2: mk_hc (?t1, ?t2, _) ?c2 |- _ =>
                  apply (IH c1 c2) in H1; [subst | solve [simpl in *; omega]
                                           | solve [auto] | idtac ..]
                | _ => auto
                end.
Qed. 

Lemma mk_hc_function : forall h1 h2 t1 t2 l,
    mk_hc (t1, t2, l) h1 ->
    mk_hc (t1, t2, l) h2 ->
    h1 = h2.
Proof. intros h1 h2 t1 t2 l.
       apply (mk_hc_function_size ((ty_size t1) + (ty_size t2))).
       omega. 
Qed. 
  
Hint Resolve mk_hc_function.
  
Lemma mk_hc_total : forall t1 t2 l,
    exists h, mk_hc (t1, t2, l) h /\ hc_size h <= (ty_size t1) + (ty_size t2). 
Proof.
  induction t1; destruct t2; intros;
    (* apply IH when possible *)
    repeat
      match goal with
      | IH: (forall t l, exists h, mk_hc (?g, t, l) h /\ _),
            T: Ty,
               L: blame_info |- _ =>
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
      end;
  (* References and Functions need symmetry too *)
  try match goal with
        | H: mk_hc (?t1, ?t2, _) _ |- context[mk_hc(?t1 → _, ?t2 → _, _) _] =>
          destruct (mk_hc_symetry_size _ _ _ _ H)
      end;
    repeat
      match goal with
      | H: exists x, _ |- _ => destruct H
      | H: _ /\ _ |- _ => destruct H
      end;
  (* case on whether the types are the same *)
  match goal with
  | |- context[mk_hc (?t1, ?t2, _) _] =>
    let H:=fresh in
    destruct (ty_eqdec t1 t2) as [H | H];
      [ try discriminate; inverts H |
        try solve [contradiction H; eauto] ]
  end;
  (* solve by deriving proofs of existance and inequalities *)
  try solve [eexists; split;
             [econstructor; try eassumption; try prove_inconsistent; eauto
             | omega_max]].

Qed. 


Lemma mk_hc_not_dyn : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn ->
    (exists m, mk_hc (t1, t2, l) (HC prj_mt m inj_mt)) \/ 
    (mk_hc (t1, t2, l) (Fail prj_mt t1 l)).
Proof.
  intros t1 t2 l H1 H2. destruct (mk_hc_total t1 t2 l) as [h [mk_h bound]]. 
  inverts mk_h; eauto.
Qed.

Hint Resolve mk_hc_not_dyn.

Lemma mk_hc_not_dyn_sconsist : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn -> t1 <∼> t2 ->
    (exists m, mk_hc (t1, t2, l) (HC prj_mt m inj_mt)). 
Proof. intros t1 t2 l H1 H2 H3;
         destruct (mk_hc_not_dyn t1 t2 l H1 H2);
         inverts H3;
         repeat match goal with
                | H: _ <> _ |- _ => solve [contradiction H; reflexivity]
                | H: _ <≁> _ |- _ => solve [contradiction H; eauto]
                | H: mk_hc _ (Fail _ _ _) |- _ => inverts H
                | _ => eauto
                end.
Qed. 

Lemma mk_hc_not_dyn_sinconsist : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn -> t1 <≁> t2 -> mk_hc (t1, t2, l) (Fail prj_mt t1 l).
Proof.
 intros t1 t2 l H1 H2 H3;
 destruct (mk_hc_not_dyn t1 t2 l H1 H2); eauto. 
Qed. 

Hint Resolve mk_hc_not_dyn_sinconsist mk_hc_not_dyn_sconsist.

Inductive mediating_ty : hc_m -> CTy -> Prop:=
| Med_Ty_Id {t} : mediating_ty (Id_hc t) (t ⇒ t)
| Med_Ty_Arr {t1 t2 t3 t4 h1 h2} :
    mediating_ty (Arr_hc t1 t2 t3 t4 h1 h2)
                 (t1 → t2 ⇒ t3 → t4).

(* Inductive mk_hc' : Ty * Ty * hc_p -> hc -> Prop :=
| mk_hc_cast {t1 t2 l m} : mk_hc (t1, t2, l) m -> mk_hc' (t1, t2, prj l) m
| mk_hc_id {t p} : mk_hc' (t, t, p) (HC prj_mt (Id_hc t) inj_mt). *)

Hint Constructors mediating_ty. 

Lemma mediating_ty_total : forall m, exists t1 t2, mediating_ty m (t1 ⇒ t2).
Proof. intros [];  eauto. Qed. 

Inductive compose_hc : (hc * hc) -> hc -> Prop :=
|Comp_hc_Dyn_L {p i h}:
   (* - Comp_hc_fail_no_prj doesn't overlap here because of the typing rule
        for fail not allowing t2 to be Dyn and the projection is mt
      - Comp_hc_fail_inj_prj doesn't overlap because of the explicit
        inj of the rhs coercion
      - in short the second hyper-coercion may be a failure but 
        doesn't overlap with any of the failure cases for compose *)
   compose_hc (HC p (Id_hc Dyn) i, h) h
|Comp_hc_Dyn_R {p1 m1 i1 p2 i2}:
   (* specified as HC so that Comp_hc_fail_L doesn't apply *)
   compose_hc (HC p1 m1 i1, HC i2 (Id_hc Dyn) p2) (HC p1 m1 i1)
|Comp_hc_no_prj {p1 m1 m2 i2 m3}:
   compose_hc_m (m1, m2) m3 ->
   compose_hc (HC p1 m1 inj_mt, HC prj_mt m2 i2) (HC p1 m3 i2)
|Comp_hc_inj_prj_ok {p1 m1 l m2 i2 t1 t2 t3 t4 m3 m4 m5}:
   mediating_ty m1 (t1 ⇒ t2) ->
   mediating_ty m2 (t3 ⇒ t4) ->
   t2 <> Dyn ->
   t3 <> Dyn ->
   mk_hc (t2, t3, l) (HC prj_mt m3 inj_mt) ->
   compose_hc_m (m1, m3) m4 ->
   compose_hc_m (m4, m2) m5 ->
   compose_hc (HC p1 m1 inj, HC (prj l) m2 i2) (HC p1 m5 i2)
|Comp_hc_inj_prj_fail {p1 m1 l m2 i2 t2 t3 t1 t4}:
   mediating_ty m1 (t1 ⇒ t2) ->
   mediating_ty m2 (t3 ⇒ t4) ->
   t2 <> Dyn ->
   t3 <> Dyn ->
   mk_hc (t2, t3, l) (Fail prj_mt t2 l) ->
   compose_hc (HC p1 m1 inj, HC (prj l) m2 i2) (Fail p1 t1 l)
(* |Comp_hc_fail  {p1 m1 l m2 i2 t1 t2 t3 t4} :
   mediating_ty m1 (t1 ⇒ t2) ->
   mediating_ty m2 (t3 ⇒ t4) ->
   t2 <> Dyn -> t3 <> Dyn ->
   mk_hc (t2, t3, l) (Fail prj_mt t2 l) ->
   compose_hc (HC p1 m1 inj, HC (prj l) m2 i2) (Fail p1 t1 l) *)
|Comp_hc_fail_L {p t l h}:
   (* doesn't overlap with Comp_hc_Dyn_R *)
   compose_hc (Fail p t l, h) (Fail p t l)
|Comp_hc_fail_no_prj {p1 m1 l2 t1 t2}:
   (* doesn't overlap with Comp_hc_Dyn_L because t2 cannot be
      Dyn according to the typing rules and
      there isn't a m1 that would type t1 at Dyn *)
   mediating_ty m1 (t1 ⇒ t2) ->
   compose_hc (HC p1 m1 inj_mt, Fail prj_mt t2 l2) (Fail p1 t1 l2)
|Comp_hc_fail_inj_prj_ok {p1 m1 l1 t3 l2 t1 t2 m3}:
   (* Don't have to consider inj_mt dyn because that is covered
      via Comp_hc_Dyn_L *)
   mediating_ty m1 (t1 ⇒ t2) ->
   mk_hc (t2, t3, l1) (HC prj_mt m3 inj_mt) ->
   compose_hc (HC p1 m1 inj, Fail (prj l1) t3 l2) (Fail p1 t1 l2)
|Comp_hc_fail_inj_prj_fail {p1 m1 l1 t3 l2 t1 t2}:
   (* Don't have to consider inj_mt dyn because that is covered
      via Comp_hc_Dyn_L *)
   mediating_ty m1 (t1 ⇒ t2) ->
   mk_hc (t2, t3, l1) (Fail prj_mt t2 l1) ->
   compose_hc (HC p1 m1 inj, Fail (prj l1) t3 l2) (Fail p1 t1 l1)              
with
(* assuming m1 : t1 => t2 and m2 : t2 => t3 *)
compose_hc_m : (hc_m * hc_m) -> hc_m -> Prop :=
| compose_hc_id_L {t1 m} : compose_hc_m (Id_hc t1, m) m
| compose_hc_id_R {t1 m} : compose_hc_m (m, Id_hc t1) m
| compose_Arr {t11 t12 t21 t22 t31 t32 h1 h2 h3 h4 h5 h6}:
    compose_hc (h3, h1) h5 ->
    compose_hc (h2, h4) h6 -> 
    compose_hc_m (Arr_hc t11 t12 t21 t22 h1 h2,
                  Arr_hc t21 t22 t31 t32 h3 h4)
                 (Arr_hc t11 t12 t31 t32 h5 h6).

Hint Constructors compose_hc compose_hc_m. 

Ltac dupH H :=
  let H':=fresh in
  let P :=type of H in
  assert (H' : P); try exact H. 


Lemma mk_hc_id : forall t l, mk_hc (t, t, l) (HC prj_mt (Id_hc t) inj_mt).
Proof. intros [] l; auto. Qed. 

(*
Lemma mk_hc_id_size : forall t l p m i,
    mk_hc (t, t, l) (HC p m i) -> hc_size (HC p m i)  = ty_size t. 
Proof. intros. cut (mk_hc (t, t, l) (HC prj_mt (Id_hc t) inj_mt)); [intros | idtac ..].
       Check mk_hc_function. apply mk_hc_function enough (H : mk_hc_id t l) by auto. . nverts H; repeat reveal_minimum_sizes; try (simpl; omega).  
       inverts H. (mk_hc_id t l).  intros t l h H. inverts H; reveal_minimum_sizes; simpl; try omega.
       inverts H. eauto. 
       auto. auto. omega. simpl in *.
*)

 


(* Lemma hc_m_contains_trans : forall m m' m'' p p' i i',
    hc_m_contains_hc m  (HC p m' i) ->
    hc_m_contains_hc m' (HC p' m'' i') ->
    hc_m_contains_hc m  (HC p' m'' i'). 
Proof.
  intro m.
  elim m using hcm_ind_mut with
  (P := fun (h : hc) => 
            match h with
            | (HC _ m _ ) =>
              forall m' m'' p p' i i',
              hc_m_contains_hc m  (HC p m' i) ->
              hc_m_contains_hc m' (HC p' m'' i') ->
              hc_m_contains_hc m  (HC p' m'' i')
            | (Fail _ _ _) => True
            end)
    (P0 := fun m => forall m' m'' p p' i i',
       hc_m_contains_hc m  (HC p m' i) ->
       hc_m_contains_hc m' (HC p' m'' i') ->
       hc_m_contains_hc m  (HC p' m'' i'));
  intuition; auto. 
  - inverts H.
  - destruct h; destruct h0.
    inverts keep H1; auto.
     -- inverts keep H10. eauto. 
    -- inverts keep H10. eauto. 
    --  inversion H1; subst.
    * auto.
    * inversion H10. eauto.
    * inversion H10.
    -- inversion H1; subst; auto. 
    * inversion H10.  
    * inversion H10. eauto.
      -- inverts H1; inverts H10.
  - destruct h; destruct h0.
    inverts keep H1; auto. 
     -- inverts keep H8. eauto. 
    -- inverts keep H8. eauto. 
    --  inverts keep H1; try inversion H8; eauto.  
    -- inversion H1; subst; auto; inverts keep H8; eauto. 
    -- inversion H1; subst; auto; inverts keep H8; eauto. 
Qed. 
*)

Lemma hc_contains_self_containment : forall h,
    not (hc_contains_hc h h) /\
    forall p m i, h = (HC p m i) -> not (hc_m_sub_hc m h).
Proof.
  intros h.
  elim h using hc_ind_mut with
  (P := fun h =>
          not (hc_contains_hc h h) /\
          forall p m i, h = (HC p m i) -> not (hc_m_sub_hc m h))
  (P0 := fun m => 
    match m with
    | (Id_hc i) => True
    | (Arr_hc _ _ _ _ h1 h2) =>
      (not (hc_contains_hc h1 h1) /\
       forall p m i, h1 = (HC p m i) -> not (hc_m_sub_hc m h1))
      /\
      (not (hc_contains_hc h2 h2) /\
       forall p m i, h2 = (HC p m i) -> not (hc_m_sub_hc m h2))
    end);
  intuition;
  repeat match goal with
    | H: match ?t with _ => _ end |- _ => destruct t
    | H: _ /\ _ |- _ => destruct H
  end;
  try rule_out_absurd_hc_contains;
  match goal with
  | H: hc_contains_hc _ _ |- _ => inverts H
  | H: HC _ _ _ = HC _ _ _ |- _ => inverts H
  end;
  match goal with
  | H: hc_m_sub_hc _ _ |- _ => inverts H
  end; 
  try match goal with
  | H: hc_contains_hc ?t _, H': hc_contains_hc ?t ?t -> _ |- _ =>
    solve[apply H'; apply (hc_contains_trans _ _ _ H); auto]
  | H: ?t = HC ?p ?m ?i, IH: context[?t = HC _ _ _ -> _ -> False] |- _ =>
    solve [apply IH in H; [ assumption | auto ]]
      end.
Qed. 

Lemma hc_not_cyclic : forall h, not (hc_contains_hc h h).
Proof. intros h. destruct (hc_contains_self_containment h). auto. Qed.

Lemma hcm_not_cyclic : forall m p i, not (hc_m_sub_hc m (HC p m i)).
Proof. intros m p i. destruct (hc_contains_self_containment (HC p m i)). auto. Qed.

Hint Resolve hc_not_cyclic hcm_not_cyclic. 

Lemma hc_m_le_hc_depth : forall p m i,
     hc_m_depth m <= hc_depth (HC p m i). 
Proof. intros p m i. simpl. auto. Qed.

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

Ltac solve_inequality :=
    try match goal with
        | H: hc_m_sub_hc _ _ |- _ => inverts keep H
        | H: hc_contains_hc _ _ |- _ => inverts keep H
    end;
    try match goal with
    | H: hc_contains_hc _ ?h |- _ < _ => inversion H
    end;
    try match goal with
        | H: _ = _ |- _ => inverts keep H
        end;
    try match goal with
        | H: hc_m_sub_hc _ _ |- _ < _ => inverts keep H
        end;                            
    repeat match goal with
      | H: hc_contains_hc _ _ , IH: context[hc_size _ < hc_size _]
        |- _ =>
        apply IH in H; [> idtac | solve [eauto] | idtac ..]
      | H: HC _ _ _ = ?h, IH: context[?h = HC _ _ _] |- hc_size ?h' < _ => 
        symmetry in H;            
        apply (IH _ _ _ h') in H; [> idtac | solve [eauto] | idtac ..] 
    end;
    simpl in *; try omega. 



Lemma hc_size_lt_contained_hc : forall h,
    (forall h', hc_contains_hc h h' -> hc_size h' < hc_size h).
Proof.
  intro h. 
  elim h using hc_ind_mut with
    (P := fun h => forall h',
              hc_contains_hc h h' -> hc_size h' < hc_size h)
    (P0 := fun m => forall h h',
               hc_m_sub_hc m h ->
               hc_contains_hc h h' -> hc_size h' < hc_size h);
  intuition;
  try rule_out_absurd_hc_contains;
  solve [match goal with
         | H: hc_contains_hc _ _ |- _ => inverts H
         end;
         match goal with
         | H: hc_m_sub_hc _ _ |- _ => inverts H
         end;
         match goal with
         | H: hc_contains_hc ?h _ ,
              IH: context[hc_m_sub_hc _ _ -> hc_contains_hc _ _ -> _]
           |- _ =>
           apply IH in H; [> simpl in *; omega | solve [eauto] | idtac ..]
         | _ => solve [simpl in *; omega; solve[auto]]
         end]
  ||
  solve
    [match goal with
     | H: hc_m_sub_hc _ _ |- _ => inverts keep H
     end;
     match goal with
     | H: hc_contains_hc _ _ , IH: context[_ < _ ] |- ?g =>
       solve [ apply IH; exact H]
     end].
Qed.

Lemma hc_depth_lt_contained_hc : forall h,
    (forall h', hc_contains_hc h h' -> hc_depth h' < hc_depth h).
Proof.
  intro h. 
  elim h using hc_ind_mut with
    (P := fun h => forall h',
              hc_contains_hc h h' -> hc_depth h' < hc_depth h)
    (P0 := fun m => forall h h',
               hc_m_sub_hc m h ->
               hc_contains_hc h h' -> hc_depth h' < hc_depth h);
  intuition;
  try rule_out_absurd_hc_contains;
  (* This attempt has to go before the other *)
  try solve
      [match goal with
       | H: hc_m_sub_hc _ _ |- _ => inverts keep H
       end;
       match goal with
       | H: hc_contains_hc _ _ , IH: context[_ < _ ] |- ?g =>
         solve [ apply IH; exact H]
       end];
  (* because the rest of this will diverge *)
  try
    match goal with
    | H: hc_contains_hc _ _ |- _ => inverts H
    end;
  match goal with
    | H: hc_m_sub_hc _ _ |- _ => inverts H
  end;
  match goal with
  | H: hc_contains_hc ?h _ ,
       IH: context[hc_m_sub_hc _ _ -> hc_contains_hc _ _ -> _]
    |- _ =>
    apply IH in H; [> omega_max | solve [eauto] | idtac ..]
  | _ => solve [omega_max; solve[auto]]
  end. 
Qed.


(* Lemma hc_mk_m_depth : forall n h t1 t2 l,
    hc_size h <= n -> 
    mk_hc (t1, t2, l) h ->
    hc_size h <= (ty_size t1) + (ty_size t2). 
Proof. induction n;
       intros h t1 t2 l bound H;
       cut ( 1 <= ty_size t1); 
       cut ( 1 <= ty_size t2);
       intros; eauto. 
       + inverts H; inverts bound. 
 *)

