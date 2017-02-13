
Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import GTypes.
Require Import coercions. 
Require Import Omega. 


Inductive base : Ty -> Prop :=
| Base_Int : base Int
| Base_Bool : base Bool. 

Inductive composite : Ty -> Prop :=
| Composite_Arr {t1 t2} : composite (t1 → t2)
| Composite_Ref {t1}    : composite (Ref t1). 

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
| Arr_hc : Ty -> Ty -> Ty -> Ty -> hc -> hc  -> hc_m
| Ref_hc : Ty -> Ty -> hc -> hc -> hc_m.

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
            ((t1 → t2) ⇒ (t3 → t4))
| Ref_hc_s_wt {t1 t2 c1 c2} :
    hc_wt c1 (t1 ⇒ t2) ->
    hc_wt c2 (t2 ⇒ t1) ->
    hc_m_wt (Ref_hc t1 t2 c1 c2) ((Ref t1) ⇒ (Ref t2)).

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
    hc_m_sub_hc (Arr_hc t1 t2 t3 t4 h1 h2) h2
| Contains_Ref_h1 {t1 t2 h1 h2}:
    hc_m_sub_hc (Ref_hc t1 t2 h1 h2) h1
| Contains_Ref_h2 {t1 t2 h1 h2}:
    hc_m_sub_hc (Ref_hc t1 t2 h1 h2) h2.

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
| Mk_hc_ref {t1 t2 l c1 c2} :
    Ref t1 <> Ref t2 -> 
    mk_hc (t1, t2, l) c1 ->
    mk_hc (t2, t1, l) c2 ->
    mk_hc (Ref t1, Ref t2, l)
          (HC prj_mt (Ref_hc t1 t2 c1 c2) inj_mt)
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
           | (Ref_hc _ _ h1 h2) =>
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
               => idtac IH H h; apply IH in H
             | _ => eauto
             end. 
  + intros _1 _2 _3 _4 _5 _6 H. inverts H; auto.
  + trivial.
  + auto.
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

Lemma one_le_ty_depth : forall t, 1 <= ty_depth t. 
Proof. induction t; simpl; auto. Qed.

Hint Resolve one_le_ty_depth.     


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
  | Ref_hc t1 t2 h1 h2 =>
    1 + max (max (hc_depth h1) (hc_depth h2)) (max (ty_depth t1) (ty_depth t2))
  end. 

Lemma one_le_hc_depth : forall h, 1 <= hc_depth h.
Proof. destruct h as [p [] i | p [] l]; simpl; auto. Qed. 


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

Ltac omega_max :=
  simpl in *;
  repeat
    match goal with
    | t: Ty |- _ => 
      match goal with
      | H: 1 <= ty_depth t |- _ => fail 1
      | _ => cut (1 <= ty_depth t); [ intro | solve [auto] | auto ..]
      end
    | h: hc |- _ => 
      match goal with
      | H: 1 <= hc_depth h |- _ => fail 1
      | _ => cut (1 <= hc_depth h); [ intro | solve [auto] | auto ..]
      end
    end;
  repeat
    match goal with
    | e: _ = _ |- _ => rewrite e
    end;
  max_dec_tac_context; 
  omega_max_search 5;
  max_dec_tac_context; 
  omega. 
  



Lemma mk_hc_symetry : forall h t1 t2 l,
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
             | _ =>
               solve [eexists; split;
                      [> eauto
                      | omega_max]]
             end.
  - intros p t b t1 t2 l H. inversion H.
    eexists. split. constructor. intro contra.
    inversion contra; subst;  auto. subst. 
    auto. 
  - trivial.
  - auto.
  - auto.
Qed.

Hint Resolve mk_hc_symetry.


Fixpoint ty_size t :=
  match t with
  | t1 → t2 => 1 + (ty_size t1 + ty_size t2)
  | Ref t   => 1 + (ty_size t)
  | _ => 1
  end.

Fixpoint hc_size h :=
  match h with
  | HC _ m _ => 1 + hc_m_size m
  | Fail _ t _ => 1 + ty_size t
  end
with
hc_m_size m :=
  match m with
  | Id_hc t => ty_size t
  | Arr_hc t1 t2 t3 t4 h1 h2 =>
    ty_size t1 + ty_size t2 + ty_size t3 + ty_size t4 + hc_size h1 + hc_size h2
  | (Ref_hc t1 t2 h1 h2) =>
    ty_size t1 + ty_size t2 + hc_size h1 + hc_size h2
  end. 

Ltac reveal_minimum_sizes :=
  match goal with
  | t: Ty |- _ => 
    match goal with
    | H: 1 <= ty_size t |- _ => fail 1
    | _ => cut (1 <= ty_size t); [ intro | auto ..]
    end
  | h : hc |- _ =>
    match goal with
    | H: 2 <= hc_size h |- _ => fail 1
    | _ => cut (2 <= hc_size h); [ intro | auto ..]
    end
  | m : hc_m |- _ =>
    match goal with
    | H: 1 <= hc_m_size m |- _ => fail 1
    | _ =>  cut (1 <= hc_m_size m); [ intro | auto ..]
    end
  | ty : hc_m |- _ =>
    match goal with
    | H: 1 <= ty_depth ty |- _ => fail
    | _ =>  cut (1 <= ty_depth ty); [ intro | auto ..]
    end
  end.



Lemma one_le_ty_size : forall t, 1 <= ty_size t. 
Proof. induction t; simpl; auto. Qed. 

Hint Resolve one_le_ty_size.

Lemma two_le_hc_size : forall h, 2 <= hc_size h.
Proof.
  intros [p [] i | p t l]; reveal_minimum_sizes; simpl in *; omega. 
Qed. 

Hint Resolve two_le_hc_size. 

Lemma one_le_hc_m_size : forall m, 1 <= hc_m_size m.
Proof.
  intros []; intros; reveal_minimum_sizes; simpl; omega. 
Qed. 

Hint Resolve one_le_hc_m_size.



Lemma mk_hc_function : forall n h h' t1 t2 l,
    ty_depth t1 + ty_depth t2 <= n -> 
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
                  apply (IH c1 c2) in H1; [subst | solve [omega_max] | solve [auto] | idtac ..]
                | _ => auto
                end.
Qed. 


Hint Resolve mk_hc_function.
  
Lemma mk_hc_total : forall t1 t2 l,
    exists h, mk_hc (t1, t2, l) h /\ hc_depth h <= max (ty_depth t1) (ty_depth t2). 
Proof.
  induction t1; destruct t2; intros;
    (* apply IH when possible *)
    repeat (match goal with
            | IH: (forall t l,
                      exists h, mk_hc (?g, t, l) h /\ _),
                  T: Ty, L: blame_info |- _ =>
              match goal with
              | H: mk_hc (g, T, L) _ |- _ => fail 1
              | |- context[mk_hc(_ → _, _ → _, _) _] => fail 1
              | _ =>
                let h:=fresh in
                let P1:=fresh in
                let P2:=fresh in
                destruct (IH T L) as [h [P1 P2]]
              end
            end);
    (* References and Functions need symmetry too *)
    try match goal with
        | H: mk_hc (?t1, ?t2, _) _ |- _ =>
          match goal with
          | H': mk_hc (t2, t1, _) _ |- _ => fail 1
          | _ =>
            let h:=fresh in
            let P1:=fresh in
            let P2:=fresh in
            destruct (mk_hc_symetry _ _ _ _ H) as [h [P1 P2]]
          end
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
  
  Ltac min_depths_tac :=
        match goal with 
        | t: Ty |- _ =>
          match goal with
          | H: 1 <= ty_depth t |- _ => fail 1
          | _ => cut (1 <= ty_depth t); [> intro | auto ..]
          end
        | h: hc |- _ =>
          match goal with
          | H: 1 <= hc_depth h |- _ => fail 1
          | _ => cut (1 <= hc_depth h); [> intro | auto ..]
          end
        end.
  (* My current tactics cause exponential blowup in the number of cases...
     this is too much for the function case.
     Find a way to search for these automatically *)
  + destruct (IHt1_1 t2_1 l) as [h1 [P11 P12]].
    destruct (IHt1_2 t2_2 l) as [h2 [P21 P22]].
    destruct (mk_hc_symetry _ _ _ _ P11) as [h1r [P11' P12']].
    eexists. split.
    * econstructor; try eassumption; eauto.
    * simpl.
      max_dec_tac_context;
      repeat match goal with
      | H: _ = _ |- _ => rewrite H in *
      end;
      omega_max_search 10; auto;
      max_dec_tac_context;
      try omega. 
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
                 (t1 → t2 ⇒ t3 → t4)
| Med_Ty_Ref {t1 t2 h1 h2} :
    mediating_ty (Ref_hc t1 t2 h1 h2) (Ref t1 ⇒ Ref t2).

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
                 (Arr_hc t11 t12 t31 t32 h5 h6)
| compose_Ref {t1 t2 t3 h1 h2 h3 h4 h5 h6} :
    (* Todo Check that this is correct *)
    compose_hc (h1, h3) h5 ->
    compose_hc (h4, h2) h6 ->
    compose_hc_m (Ref_hc t1 t2 h1 h2,
                  Ref_hc t2 t3 h3 h4)
                 (Ref_hc t1 t3 h5 h6). 

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
    | (Ref_hc _ _ h1 h2) =>
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
  solve
    [match goal with
     | H: hc_contains_hc _ _ |- _ => inverts H
     end;
     match goal with
     | H: hc_m_sub_hc _ _ |- _ => inverts H
       end;
     try match goal with
         | H: hc_contains_hc ?h _ ,
              IH: context[hc_m_sub_hc _ _ -> hc_contains_hc _ _ -> _]
           |- _ =>
             apply IH in H; [> omega_max | solve [eauto] | idtac ..]
         | _ => solve [omega_max; solve[auto]]
         end] ||
    solve
    [match goal with
     | H: hc_m_sub_hc _ _ |- _ => inverts keep H
     end;
     match goal with
     | H: hc_contains_hc _ _ , IH: context[_ < _ ] |- ?g =>
       solve [ apply IH; exact H]
     end].
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

(* well founded induction *)

Theorem compose_hc_total' :
  forall n,
    (forall h1 h2 t1 t2 t3,
        hc_depth h1 + hc_depth h2 <= n ->
        hc_wt h1 (t1 ⇒ t2) ->
        hc_wt h2 (t2 ⇒ t3) ->
        exists h3, compose_hc (h1, h2) h3
                   /\
                   hc_wt h3 (t1 ⇒ t3)
                   /\
                   hc_size h3 <= (hc_size h1) + (hc_size h2))
    /\ 
    (forall m1 m2 t1 t2 t3,
        hc_m_size m1 + hc_m_size m2 <= n ->
        hc_m_wt m1 (t1 ⇒ t2) ->
        hc_m_wt m2 (t2 ⇒ t3) ->
        exists m3,
          compose_hc_m (m1, m2) m3
          /\
          hc_m_wt m1 (t1 ⇒ t3)
          /\
          hc_m_size m3 <= hc_m_size m1 + hc_m_size m2).
Proof. 
  induction n; intuition;
    repeat
    (* There are some base minimums that make trivial case truely trivial *)

  - omega. (* Vacuously True *)
  - omega. (* Vacuously True *)
  - (* case analysis on the typing derivation *)
    match goal with
    | wt1: hc_wt _ _, wt2: hc_wt _ _ |- _ => inverts keep wt1; inverts keep wt2
    end.
    (* further case analysis on m(s) and inner projections and injections *)
    match goal with
    | |- context[compose_hc (HC ?p1 ?m1 ?i1, HC ?p2 ?m2 ?i2) _] =>
      match goal with
      | Hi1: hc_i_wt i1 _,
        Hp1: hc_p_wt p1 _,
        Hp2: hc_p_wt p2 _,
        Hm1: hc_m_wt m1 _,
        Hm2: hc_m_wt m2 _,
        Hi2: hc_i_wt i2 _ |- _ =>
        inverts keep Hm1;
        inverts keep Hi1;
        inverts keep Hp1;
        inverts keep Hp2;
        inverts keep Hm2;
        inverts keep Hi2
      | _ => fail 1
      end
    | |- context[compose_hc (HC _ ?m ?i, Fail ?p ?t _) _] =>
      match goal with
      | Hi: hc_i_wt i _, Hp: hc_p_wt p _, Hm: hc_m_wt m _ |- _ =>
        inverts keep Hm;
        inverts keep Hi;
        inverts keep Hp
      | _ => fail 1
      end
    end;
      try solve [eexists; intuition eauto; simpl in *; omega].  
    (* for merging inj;prj case on whether the types are shallow consistent *)
    + match goal with
      | |- context[compose_hc (HC _ ?m1 inj, HC (prj ?l) ?m2 _) _] =>
        match goal with
        | H1: hc_m_wt m1 (_ ⇒ ?t1),
              H2: hc_m_wt m2 (?t2 ⇒ _) |- _ =>
          let H:=fresh in
          destruct (ty_shallow_consistency_dec t1 t2) as [H | H];
            try (inverts keep H; try discriminate)
        end;
        try match goal with
            | l: blame_info, h: ?t1 <∼> ?t2 |- _ =>
              destruct (mk_hc_not_dyn_sconsist t1 t2 l);
                [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..]
            | l: blame_info, h: ?t1 <≁> ?t2 |- _ =>
              destruct (mk_hc_not_dyn_sconsist t1 t2 l);
                [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..] 
            end 
      end; try solve [eexists; intuition eauto; simpl in *; omega].
      
      * eexists.
        split. 
        eauto.
        split.
        eauto.
        simpl in *. omega. split.apply eauto. 
        
        eauto 7.  intuition. intuition eauto. econstructor; eauto. solve[simpl in *; omega].
    + 
    + eexists; intuition eauto; solve[simpl in *; omega].
    + eexists; intuition eauto; solve[simpl in *; omega].
    + eexists; intuition eauto; solve[simpl in *; omega].
    + eexists; intuition eauto; solve[simpl in *; omega].
    + eexists; intuition eauto; solve[simpl in *; omega].
    + eexists; intuition eauto; solve[simpl in *; omega].



      match goal with
    [compose_hc (HC _ ?m1 ?i, HC _ ? =>
    
      repeat match goal with
               | wt: hc_p_wt _ _ |- _ => inverts wt
               | wt: hc_m_wt _ _ |- _ => inverts wt
               | wt: hc_i_wt _ _ |- _ => inverts wt
               end
    end.
      try solve [eexists; intuition (eauto;omega)].
    + ; try omega.  intuition (try omega; auto). eexists. split. auto.
        split. auto.
        simpl. omega. 
    + 
      match goal with
    | inversion H. omega.  inversion H8.   eauto. 

  * inversion H.  eauto. split; intros; inverts H0; inverts H1; simpl in H;
    inverts H. 
  + destruct IHn as [IHh IHm]. split.
  - intros h1 h2 t1 t2 t3 measure wt_h1 wt_h2.  
    (* case analysis on the typing derivation *)
    inverts keep wt_h1; inverts keep wt_h2; eauto.
    (* further case analysis on m(s) and inner projections and injections *)
    match goal with
    | |- context[compose_hc (HC _ ?m1 ?i, HC ?p ?m2 _) _] =>
      match goal with
      | Hi: hc_i_wt i _, Hp: hc_p_wt p _, Hm1: hc_m_wt m1 _, Hm2: hc_m_wt m2 _ |- _ =>
        inverts keep Hm1;
        inverts keep Hi;
        inverts keep Hp;
        inverts keep Hm2
      | _ => fail 1
      end
    | |- context[compose_hc (HC _ ?m ?i, Fail ?p ?t _) _] =>
      match goal with
      | Hi: hc_i_wt i _, Hp: hc_p_wt p _, Hm: hc_m_wt m _ |- _ =>
        inverts keep Hm;
        inverts keep Hi;
        inverts keep Hp
      | _ => fail 1
      end
    end; eauto; 
    (* case on whether the inner types of the mediating 
       coercions are shallow consistent *)
    try match goal with
        | |- context[compose_hc (HC _ ?m1 _, HC _ ?m2 _) _] =>
          let t21:=fresh in
          let t22:=fresh in
          let t23:=fresh in
          let t24:=fresh in
          let P1:=fresh in
          let P2:=fresh in
          destruct (mediating_ty_total m1) as [t21 [t22 P1]];
            destruct (mediating_ty_total m2) as [t23 [t24 P2]];
            destruct (ty_shallow_consistency_dec t22 t23) as [P3 | nP3];
            inverts keep P1;
            inverts keep P2;
            try (inverts keep P3; try discriminate)
        end; eauto;
      try match goal with
          | l: blame_info, h: ?t1 <∼> ?t2 |- _ =>
            destruct (mk_hc_not_dyn_sconsist t1 t2 l);
              [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..]
          | l: blame_info, h: ?t1 <≁> ?t2 |- _ =>
            destruct (mk_hc_not_dyn_sconsist t1 t2 l);
              [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..] 
          end. 
    eexists. 
    split; [> eauto | idtac ..].
    edestruct (IHm (Id_hc (t0 → t2)) x).
    unfold lt in *. 
    edestruct 

    omega. 
      in 

    
    simpl in *.
    unfold lt in *. 
    repeat rewrite <- plus_n_Sm in *.
    inversion measure.
    inversion H9. 

    Ltac expose_more :=
      repeat match goal with
       | |- context[max ?n1 ?n2] =>
         cut_if_not_hypothesis (n1 <= max n1 n2);
         cut_if_not_hypothesis (n2 <= max n1 n2);
         simpl; intros
      end. 
    expose_more. 
    destruct measure. 

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
    tc_mk_coercion. 
    
    intuition (try omega; eauto).
    
    
 Theorem compose_hc_total : forall h1 h2 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    exists h3, compose_hc (h1, h2) h3.
Proof.
  intros h1.
  elim h1 using hc_ind_mut with
  (P := fun h => forall h2 t1 t2 t3,
            hc_wt h  (t1 ⇒ t2) ->
            hc_wt h2 (t2 ⇒ t3) ->
            exists h3, compose_hc (h, h2) h3)
  (P0 := fun m => 
           match m with
           | (Id_hc i) => True
           | (Arr_hc _ _ _ _ h1 h2) =>
             (forall h2' t1 t2 t3,
                 hc_wt h1   (t1 ⇒ t2) ->
                 hc_wt h2'  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h1, h2') h3) /\
             (forall h2' t1 t2 t3,
                 hc_wt h2   (t1 ⇒ t2) ->
                 hc_wt h2'  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h2, h2') h3)
           | (Ref_hc _ _ h1 h2) =>
             (forall h2' t1 t2 t3,
                 hc_wt h1  (t1 ⇒ t2) ->
                 hc_wt h2'  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h1, h2') h3) /\
             (forall h2' t1 t2 t3,
                 hc_wt h2  (t1 ⇒ t2) ->
                 hc_wt h2'  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h2, h2') h3)
           end);
    eauto.
    intros p [].
    gen p. 
    (* proof showing single induction is not enough *)
    + intros p t_id P i h2 t1 t2 t3 wt_h1 wt_h2. 
      inverts keep wt_h1; inverts keep wt_h2. 
      (* select h2 = (Arr _ _ _ _ _ ) *)
      shelve. 

    * (* use typing info to unify types *)
      match goal with
      | |- context[compose_hc (HC _ _ ?i, HC ?p _ _) _] =>
        match goal with
        | Hi: hc_i_wt i _, Hp: hc_p_wt p _ |- _ =>
          inverts keep Hi;
            inverts keep Hp
        | _ => fail 1
        end
      end;
      (* case on whether t_id in shallow consistent with (t21 → t22) *)
        try match goal with
            | |- context[compose_hc (HC _ ?m1 _, HC _ ?m2 _) _] =>
              let t21:=fresh in
              let t22:=fresh in
              let t23:=fresh in
              let t24:=fresh in
              let P1:=fresh in
              let P2:=fresh in
              destruct (mediating_ty_total m1) as [t21 [t22 P1]];
                destruct (mediating_ty_total m2) as [t23 [t24 P2]];
                destruct (ty_shallow_consistency_dec t22 t23) as [P3 | nP3];
                inverts keep P1;
                inverts keep P2;
                try inverts keep P3
            end;
        (* This may reveal some absurd cases that inversion fails to find *)
        try discriminate;
        eauto;
      (* invoke lemma showing there exists either a HC or Fail *) 
      try match goal with
          | l: blame_info, h: ?t1 <∼> ?t2 |- _ =>
            destruct (mk_hc_not_dyn_sconsist t1 t2 l);
              [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..]
          | l: blame_info, h: ?t1 <≁> ?t2 |- _ =>
            destruct (mk_hc_not_dyn_sconsist t1 t2 l);
              [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..] 
          end; eauto. 

      (* Trying to find the reason this is broken *)
      destruct x; inverts keep H; eauto. 
      eexists.
      eapply Comp_hc_inj_prj_ok; eauto. 
      econstructor. 
      (* Need a pretty general IH on the subcomponents hc *)
      econstructor.
      econstructor.
      assumption.
      assumption. eassumptioneauto.  
      
      (* induction on the well-foundedness of the composition relation *)
  
  (* intros p [] P i h2.
     gen p P i.
     elim h2 using hc_ind_mut *)
             (forall h2' t1 t2 t3,
                 hc_wt h2  (t1 ⇒ t2) ->
                 hc_wt h2'  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h2, h2') h3)
           end);eauto.
  induction

  
  

  eauto. 
  eauto.
  eauto. 
  eauto.. 

  
  intros h . match goal with
    | 
  
  intros h1 h2 cty1 cty2 wt_h1.
  induction wt_h1. 
  intros wt_h2.
  induction wt_h2.
  intros T1 T2 T3 cty1eq cty2eq.
  inverts keep cty1eq. inverts keep cty2eq. 
  shelve. 
  destruct IHwt_h2_1 with t1 t3 t21; auto. 
  
  intros t1 t2
  try match goal with
   | |- context[compose_hc (HC _ _ ?i, HC ?p _ _) _] =>
     match goal with
     | Hi: hc_i_wt i _, Hp: hc_p_wt p _ |- _ =>
       inverts keep Hi;
       inverts keep Hp
     | _ => fail 1
     end
   | |- context[compose_hc (HC _ _ ?i, Fail ?p _ _) _] =>
     match goal with
     | Hi: hc_i_wt i _, Hp: hc_p_wt p _ |- _ => inverts Hi; inverts Hp
     | _ => fail 1
     end
  end;
  try match goal with
   | |- context[compose_hc (HC _ ?m1 _, HC _ ?m2 _) _] =>
     let t21:=fresh in
     let t22:=fresh in
     let t23:=fresh in
     let t24:=fresh in
     let P1:=fresh in
     let P2:=fresh in
     destruct (mediating_ty_total m1) as [t21 [t22 P1]];
     destruct (mediating_ty_total m2) as [t23 [t24 P2]];
     destruct (ty_shallow_consistency_dec t22 t23);
     inverts keep P1;
     inverts keep P2
      end;
  eauto;
  try match goal with
  | l: blame_info, h: ?t1 <∼> ?t2 |- _ =>
    destruct (mk_hc_not_dyn_sconsist t1 t2 l);
      [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..]
  | l: blame_info, h: ?t1 <≁> ?t2 |- _ =>
    destruct (mk_hc_not_dyn_sconsist t1 t2 l);
      [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..]

  end; eauto. 

  
  destruct (mk_hc_not_dyn_sconsist t1 t2 l);
  [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..].

  
  eauto.

  

  
  eexists; eauto. 
  
  destruct IHwt_h2_1; [ > reflexivity | reflexivity | ..].
  
  
  eexists. econstructor. eassumption. eassumption.  
  eassumption. eassumption.
  destruct (
  
  eauto. eexists. econstructor. 
  
  eauto. 
  eauto. 
  .
  (*
    - destructing mediating coercion in the first hyper coercions to
       force the case 
    - destructing all injections in projection to permit easy case analysis
    - destructing second hyper coercion to find easy cases
  *)
  + intros p [t11 | t11 t12 t13 t14 h11 h12 | t11 t12 h11 h12] P []
           [[] [t21 | t21 t22 t23 t24 h21 h22 | t21 t22 h21 h22] i |] 
           t1 t2 t3 wt1 wt2; eauto;   
      destruct (ty_eqdec t2 Dyn);
      match goal with
      | |- context[ compose_hc (HC _ ?m1 _, HC _ ?m2 _) _] =>
        destruct (mediating_ty_total m1) as [lt1 [lt2 MTL]];
          destruct (mediating_ty_total m2) as [rt3 [rt4 MTR]];
          destruct (ty_shallow_consistency_dec lt2 rt3);
          inverts MTL;
          inverts MTR
      | |- context[ compose_hc (HC _ ?m1 _, Fail _ ?rt3 _) _] =>
        destruct (mediating_ty_total m1) as [lt1 [lt2 MTL]];
          destruct (ty_shallow_consistency_dec lt2 rt3);
          inverts MTL
      | |- context[compose_hc (Fail _ _ _, _) _] => eauto
      end;

      inverts wt1; inverts wt2;
    
      time repeat match goal with
     | H: hc_p_wt _ _ |- _ => inverts H
     | H: hc_i_wt _ _ |- _ => inverts H
     | H: hc_m_wt _ _ |- _ => inverts H
    end;
    time subst;
    try match goal with
        | H: ?t <> ?t |- _ => contradiction H; reflexivity
        | _ => discriminate
    end;
    try match goal with
    | H: ?t1 <∼> ?t2 |- _ =>
      solve [destruct (mk_hc_not_dyn_sconsist t1 t2 b) as [];
             intuition (try discriminate; eauto)]
    | H: ?t1 <≁> ?t2 |- _ =>
      solve [destruct (mk_hc_not_dyn_sinconsist t1 t2 b) as [];
             intuition (try discriminate; eauto)]
    end;
    eauto.
  - match goal with
    | l: blame_info, H: ?t1 <∼> ?t2 |- _ =>
      destruct (mk_hc_total t1 t2 l) as [m mk_h1];
      inversion H; subst; eauto
    end.
    inversion mk_h1; subst; eauto. 
    eexists. econstructor.
    econstructor. econstructor. assumption. assumption. econstructor.
    eassumption. eassumption. econstructor. econstructor. 
    destruct (compose_hc_total h21 c1 _ _ _).
    destruct (compose_hc_total c2 c22 _ _ _).
    inverts H0. inverts s. . destruct
  - eexists. econstructor. econstructor. econstructor. eassumption.
    eassumption. destruct s. eauto. destruct mk_hc_totaleconstructor. destruct (mkeauto.
    


    - inverts wt1; inverts wt2;
    destruct (ty_eqdec t5 Dyn);
    destruct (ty_eqdec t6 Dyn);
    time repeat match goal with
     | H: hc_p_wt _ _ |- _ => inverts H
     | H: hc_i_wt _ _ |- _ => inverts H
     | H: hc_m_wt _ _ |- _ => inverts H
    end;
    time subst;
    try match goal with
    | H: ?t <> ?t |- _ => contradiction H; reflexivity
    end;
    eauto. 
      - inverts wt1; inverts wt2;
    destruct (ty_eqdec t5 Dyn);
    destruct (ty_eqdec t6 Dyn);
    time repeat match goal with
     | H: hc_p_wt _ _ |- _ => inverts H
     | H: hc_i_wt _ _ |- _ => inverts H
     | H: hc_m_wt _ _ |- _ => inverts H
    end;
    time subst;
    try match goal with
    | H: ?t <> ?t |- _ => contradiction H; reflexivity
    end;
    eauto. 
 - inverts wt1; inverts wt2. 
    destruct (ty_eqdec t5 Dyn);
    destruct (ty_eqdec t6 Dyn);
    time repeat match goal with
     | H: hc_p_wt _ _ |- _ => inverts H
     | H: hc_i_wt _ _ |- _ => inverts H
     | H: hc_m_wt _ _ |- _ => inverts H
    end;
    time subst;
    try match goal with
    | H: ?t <> ?t |- _ => contradiction H; reflexivity
    end;
    eauto. 
    contradiction n. 
    inverts
    inverts H8. 
    inverts H5.
    eexists.
    econstructor. 

    eauto. 

    * 
    destruct (ty_shallow_consistency_dec t5 t6). 
    
  - eauto.
  - eauto.


    time repeat match goal with
     | |- context[HC _ ?m _] =>
       match goal with 
       | H: mediating_ty m _ |- _ => fail 1
       | _ =>
         let t1:=fresh in
         let t2:=fresh in
         let H:=fresh in
         destruct (mediating_ty_total m) as [t1 [t2 H]];
         inversion H; subst 
       end
    end;
    time (inverts wt1; inverts wt2);
    time repeat match goal with
     | H: hc_p_wt _ _ |- _ => inverts H
     | H: hc_i_wt _ _ |- _ => inverts H
     | H: hc_m_wt _ _ |- _ => inverts H
    end;
    time repeat match goal with
     | H: mediating_ty (Id_hc ?t) _ |- _ => 
       match goal with
       | H: t <> Dyn |- _ => fail 1
       | H: t = Dyn |- _ => fail 1
       | _ => destruct (ty_eqdec t Dyn)
       end
     | H: ?t <> ?t |- _ => contradiction H; reflexivity
    end;
    time repeat match goal with
     | H: mediating_ty _ (_ ⇒ ?t2), H': mediating_ty _ (?t3 ⇒ _) |- _ =>
       match goal with
       | H: t2 <∼> t3 |- _ => fail 1
       | H: t2 <≁> t3 |- _ => fail 1
       | _ => destruct (ty_shallow_consistency_dec t2 t3)
       end
     | H: mediating_ty _ (?t1 ⇒ ?t2) |- context[compose_hc (_, Fail _ ?t3 _) _] =>
       match goal with
       | H: t2 <∼> t3 |- _ => fail 1
       | H: t2 <≁> t3 |- _ => fail 1
       | _ => destruct (ty_shallow_consistency_dec t2 t3)
       end
     | H1: ?t2 <≁> ?t3, H2: ?t2 <∼> ?t3 |- _ => contradiction H1; exact H2
    end;
    time repeat match goal with
     | b: blame_info, H3: ?t2 <∼> ?t3 |- _ =>
       match goal with
       | h: mk_hc (t2, t3, b) _ |- _ => fail 1
       | _ =>
         let m:=fresh in
         let H:=fresh in 
         destruct (mk_hc_not_dyn_sconsist t2 t3 b) as [m H];
         solve [intuition (try discriminate; eauto)]
       end
    end;


    
    eauto. 


    destruct (mk_hc_not_dyn_sconsist (t23 → t24) t5 b); intuition (try discriminate; eauto).

    auto.
    
    eexists. econstructor;
               

               try eassumption. eassumption. eauto. 
    apply (mk_hc_not_dyn_sconsist _ _ b H4 H5) in s0 as [m p]. 
    eauto. eexists. econstructor; eauto. 
    

     

    
    eauto. 
    * 
  - 

    eauto.
  - destruct (mk_hc_not_dyn_sinconsist _ _ b H0 H1 f);
    eauto.
  -  eexists. econstructor. econstructor. econstructor. exact H0.  exact H1. 
    . eassumption.  eauto.
    eexists; 
      match goal with
      | H: _ <> Dyn |- _ <> Dyn => exact H
      | _ => eauto
      end . 

      
    try discriminate;
        try (solve[eauto]).
  - exists (Fail (prj l0) t b). 
    eapply Comp_hc_fail_R_good.
    compose_Fail_R_good. econstructor. 
    eexists. econstructor. 
    exists (HC prj_mt (Arr_hc t21 t22 t23 t24 h21 h22) inj_mt). 
    econstructor. 
    
   (solve [
                  try (solve [exists (HC prj_mt (Id_hc t3) inj_mt);
                                     econstructor;
                                     eauto]).
    * subst. exists (HC prj_mt (Id_hc Dyn) inj_mt). constructor. 
  
      eassumption. eassumption. econstructor. econstructor. econstructor. 
      econstructor. 
  intros p1 [[]| |] P i1 [t' [[] | |] i2 | p2 t1'' l]
         t1' t2' t3' H1 H2.
  try destruct t; try destruct t';
  inversion H1; subst; inversion H2; subst;
  eexists; repeat econstructor;
  repeat (match goal with
          |  H: ?h |- ?h => exact H
          | |- _ <> _ => discriminate
          end).
  

  eapply mk_hc_id. 
  repeat econstructor. 
  repeat (match goal with
          |  H: ?h |- ?h => exact H
          | |- _ <> _ => discriminate
          end).

  
  try discriminate;
          try assumption).
  eexists; repeat econstructor.
  discriminate. discriminate. 

  eexists; repeat econstructor; assumption.
  eexists; repeat econstructor; assumption.
  eexists; repeat econstructor. discriminate. 
  
      eexists; intuition eauto.  
      eexists; eauto. 
    inverts H5. 
    econstructor. 
    econstructor. 
    econstructor. 
    
      intuition eauto.  econstructor. econstructor. econstructor. 

    repeat match goal with
             | IH: _ /\ _ |- _ => destruct IH
             | IH: (forall t1 t2 l, _ -> _),
                   H:  mk_hc _ ?h |-  _
               => apply IH in H
             | _ => eauto
             | |- (exists x, _) => eexists
             | |- _ /\ _ => split 
             end.
                               
eexists. split. repeat econstructor. destruct m. 
eapply Med_Ty_Id. 

|Comp_hc_Fail_L :
   compose_hc (Fail p t l, h) (Fail p t l)
|Comp_hc_Fail_R_Inj_Prj 
|Comp_hc_Fail_R_Id :
   compose_hc (HC p1 (Id_hc t1) i, Fail p2 t2 l, h) (Fail p1 t1 l)
|Comp_hc_Fail_R_Med :
   compose_hc (HC p1 (Id_hc t1) i, Fail p2 t2 l, h) (Fail p1 t1 l)                          
.

                                                        

Theorem comp_pres_wt :
  forall c1 c2 t1 t2 t3,
    (hc_wt c1 (t1 ⇒ t2)) ->
    (hc_wt c2 (t2 ⇒ t3)) ->
    exists c3, compose_hc (c1, c2) c3 /\
               hc_wt c3 (t1 ⇒ t3).
Proof. Admitted.


Definition wt_hc t g := {h | hc_wt h (t ⇒ g)}.  
Arguments wt_hc /. 

Definition wt_se t g := {c | se_coercion c (t ⇒ g)}. 
Arguments wt_se /. 

Record bijection {A B : Type} : Type :=
  mk_bijection
    {
      f : A -> B; 
      g : B -> A;
      Id_a {a} : g (f a) = a;
      Id_b {b} : f (g b) = b
    }.

Theorem hc_se_isomorphism : forall {t g},
    @bijection (wt_hc t g) (wt_se t g).
Proof. Admitted. 

Definition hc2se {t1 t2} : wt_hc t1 t2 -> wt_se t1 t2 :=
  f hc_se_isomorphism.

Definition se2hc {t1 t2} : wt_se t1 t2 -> wt_hc t1 t2 :=
  g hc_se_isomorphism. 

Theorem iso_preserves_composition :
  forall h1 h2 h3,
    compose_se (proj1_sig (hc2se h1), proj1_sig (hc2se h2)) (proj1_sig (hc2se hs)) <->
    compose_hc (proj1_sig h1, proj1_sig h2) h3.
         
Defintion iso_preserves_relation := forall {A B},
    (iso : @bijection A B) ->
    (r1 : A -> B -> Prop) ->
    (r2 : B -> A -> Prop) ->
    (f iso a1 b1) ->
    (f iso a2 b2) ->
    r1 

Theorem hc_c_iso_preserves_composition :
  forall t1 t2 t3
         (h1 : wt_hc t1 t2) (h2 : wt_hc t2 t3) (h3 : wt_hc t1 t3)
         (c2 : wt_se t1 t2) (c2 : wt_se t2 t3) (h3 : wt_hc t1 t3), 
    hc2se c h -> 
    compose_hc (h1, h2) h3 /\ compose_se (c1, c2) c3 -> 
    hc2se h3 = c3. 



(* Fixpoint comp n c1 c2 : hc := *)
(*   match n with *)
(*   | O => Fail prj_mt Dyn 0 *)
(*   | S n' =>  *)
(*     match c1, c2 with *)
(*     | HC prj_mt (ι _) inj_mt, c2 => c2 *)
(*     | c1, HC prj_mt (ι _) inj_mt => c1 *)
(*     (* empty inj/prj no fails *) *)
(*     | HC p1 m1 inj_mt, HC prj_mt m2 i2 => *)
(*       match m1, m2 with *)
(*       | ι t1, ι t2 => HC p1 (ι t1) i2 *)
(*       | Med t1 (c11 →hc c12) _, *)
(*         Med _  (c21 →hc c22) t2 => *)
(*         HC p1 *)
(*            (Med t1 *)
(*                 ((comp n' c21 c11) →hc (comp n' c12 c22)) *)
(*                 t2) *)
(*            i2 *)
(*       | Med t1 (Ref_hc c11 c12) _, *)
(*         Med _  (Ref_hc c21 c22) t2 => *)
(*         HC p1 *)
(*            (Med t1 *)
(*                 (Ref_hc (comp n' c11 c21) *)
(*                         (comp n' c22 c12)) *)
(*                 t2) *)
(*            i2 *)
(*       (* Shouldn't be possible if input is well typed *) *)
(*       | _ , _ => Fail prj_mt Dyn 0 *)
(*       end *)
(*     (* empty inj/prj fails on second *) *)
(*     | HC p1 m inj_mt, Fail prj_mt t2 l => *)
(*       match m with *)
(*       | (ι t1) => Fail p1 t1 l *)
(*       | (Med t1 _ _) => Fail p1 (Static (Composite t1)) l *)
(*       end                                 *)
(*     (* full  inj/prj no failure *)  *)
(*     | HC p1 m1 inj, HC (prj l) m2 i2 => *)
(*       match m1, m2 with *)
(*       | ι t1, ι t2 => *)
(*         if tyd_eq t1 t2 *)
(*         then HC p1 (ι t1) i2 *)
(*         else Fail p1 t2 l *)
(*       | Med t1 _ t2, Med t3 _ t4 =>  *)
(*         comp n' *)
(*              (HC p1 m1 inj_mt) *)
(*              (comp n' *)
(*                    (make_hc (Static (Composite t2)) *)
(*                             (Static (Composite t3)) *)
(*                             l) *)
(*                    (HC prj_mt m2 i2)) *)
(*       (* These rules indicate that composite types have *)
(*          no direct identities *) *)
(*       | Med t1 _ _, _ => *)
(*         Fail p1 (Static (Composite t1)) l *)
(*       | ι t1, _ => Fail p1 t1 l *)
(*       end *)
(*     (* full  inj/prj failure in second *) *)
(*     | HC p1 m inj_mt, Fail (prj l1) t3 l2 => *)
(*       let (t1, t2) := *)
(*           match m with *)
(*           | (ι t1) => (t1, t1) *)
(*           | (Med t1 _ t2) => *)
(*             (Static (Composite t1), Static (Composite t2)) *)
(*           end in *)
(*       if tyd_eq t2 t3 *)
(*       then Fail p1 t1 l2 *)
(*       else Fail p1 t1 l1 *)
               
                            

(*     | Fail p1 t12 l, _ => Fail p1 t12 l *)
(*     (* Everything else not well typed *) *)
(*     | _, _ => Fail prj_mt Dyn 0 *)
(*     end *)
(*   end. *)

(*       (* alternatively with type-constructor identities *)
(*       | Med t1 s1 t2, Med t3 s2 t4 =>  *)
(*         match make_hc_c n t2 t3 l with  *)
(*         | Id        => HC p1 (Med t1 (comp_s n' s1 s2) t4) i2 *)
(*         | Through s => HC p1 (Med t1 (comp_s n' s1 (comp_s n' s s2)) t4) i2 *)
(*         | Failed    => Fail p1 t1 l *)
(*         end     *)
(*       | ι t1, Med t3 s2 t4 => *)
(*         match make_hc_c n t1 t3 l with *)
(*         | Id        => HC p1 (Med t1 s2 t4) i1 *)
(*         | Through s => HC p1 (Med t1 (comp_s n' s s2) t2) i1 *)
(*         | Failed    => Fail p1 t1 l      *)
(*         end *)
(*       | Med t1 s1 t2, ι t4 => *)
(*         match make_hc_c n t2 t3 l with *)
(*         | Id        => HC p1 (Med t1 s1 t4) i1 *)
(*         | Through s => HC p1 (Med t1 (comp_s n' s1 s) t2) i1 *)
(*         | Failed    => Fail p1 t1 l      *)
(*         end *)
(*       *) (* But this is just duplicating code and not compressing identities *) *)
(*       (* *)
(*       | Med t1 s1 t2, Med t3 s2 t4 => *)
(*         fl n' p1 t1 m1 (fr n' (make_hc (Static (Comp t2)) (Static (Comp t4)) l) m2 i2) *)
(*       | Med t1 s1 t2, ι t4         =>  *)
(*         fl n' p1 t1 m1 (make_hc (Static (Comp t2)) (Static (Comp t4)) l) (* this drops i *) *)
(*       | ι t1        , Med t3 s2 t4 => *)
(*         fl n' (make_hc (Static t1) (Static (Comp t4)) l) m2 i2 *)
(*        (*  *)
(*        with  *)
(*        fl (n : Nat) (p : hc_p) (t1 : Ty_c) (m : hc_m) (c : hc) := *)
(*           match c with *)
(*           | HC _ (ι t2) i => HC p (Med t1 s t2) i *)
(*           | HC _ (Med t2 s t3) i => *)
(*             match comp_m n m (Med t2 s t3) with *)
(*             | None => Fail p t1 l *)
(*             | Some (ι t5) => HC p (i t5) i *)
(*             | Some (Med t4 s t5) => HC p (Med t4 s t5) i *)
(*           | Fail _ t2 l => Fail p t1 l *)
(*           end. *)
(*        with *)
(*        f2 (n : Nat) (c : hc) (m : hc_m) (i : hc_i) := *)
(*           match c with *)
(*            | HC p (ι t2) _ =>  HC p (Med t1 s t2) i *)
(*            | HC p (Med t2 s t3) _ => *)
(*              match comp_s n s m with *)
(*              | None => Fail p t1 l *)
(*              | Some (ι t5) => HC p (i t3) i *)
(*              | Some (Med t4 s t5) => HC p (Med t4 s t5) i *)
(*           | Fail p t2 l => Fail p t1 l *)
(*           end. *)
(*        with *)
(*        comp_m n t1 m1 m2 t2 := *)
(*          match *)
(*        *) *)
(*        *) *)


(* Definition compose c1 c2 := *)
(*   comp (2 * (max (hc_ty_depth c1) (hc_ty_depth c2))) *)
(*        c1 c2.  *)

(* Ltac comp_pres_wt_tac := *)
(*   constructor || *)
(*   reflexivity || *)
(*   discriminate ||              *)
(*   match goal with *)
(*     | |- forall x, _ => intro x *)
(*     | |- _ -> _  => intro *)
(*     | |- hc_wt _ _ => *)
(*       eapply hc_wt || *)
(*              eapply fail_wt *)
(*     | |- hc_p_wt _ _ => *)
(*       apply prj_mt_wt || eapply prj_wt *)
(*     | |- hc_i_wt _ _ => *)
(*       apply inj_mt_wt || eapply inj_c_wt *)
(*     | |- hc_m_wt _ _ => *)
(*       apply Id_Dyn_wt || *)
(*             eapply Id_Base_wt || *)
(*             eapply Med_wt *)
(*     | |- hc_s_wt _ _ => *)
(*       apply Ref_hc_s_wt || apply Fn_hc_s_wt *)
(*     | [H: _ |- _ ] => *)
(*       solve[inversion H; subst; discriminate]      *)
(*   end. *)
    

(*   intros c1. *)
(*   elim c1 using hc_ind  *)
(*   with *)
(*   (P0 := fun m:hc_m => *)
(*            forall p i c2 t1 t2 t3, *)
(*              (hc_wt (HC p m i) (t1 ⇒ t2)) -> *)
(*              (hc_wt c2 (t2 ⇒ t3)) -> *)
(*              (hc_wt (compose (HC p m i) c2) (t1 ⇒ t3))) *)
(*   (P1 := fun s:hc_s => *)
(*            forall p t11 t12 i c2 t1 t2 t3, *)
(*              (hc_wt (HC p (Med t11 s t12) i) (t1 ⇒ t2)) -> *)
(*              (hc_wt c2 (t2 ⇒ t3)) -> *)
(*              (hc_wt (compose (HC p (Med t11 s t12) i) c2) (CArr t1 t3))). *)
(*   repeat comp_pres_wt_tac. *)
(*   destruct c2. *)
(*   match goal with *)
(*   | [ |- *)
(*   | [ H1: hc_wt _ _ , *)
(*       H2: hc_wt _ _ *)
(*       |- hc_wt *)
(*            (compose (HC ?p1 ?m1 ?i1) (HC ?p2 ?m2 ?i2)) *)
(*            _ ] => *)
(*     destruct p1; *)
(*       destruct p2; *)
(*       destruct m1; *)
(*       destruct m2; *)
(*       destruct i1; *)
(*       destruct i2; *)
(*       inversion H1; *)
(*       inversion H2 *)
(*   end. *)
(*   destruct t; destruct t0. *)
(*   subst. *)
(*   inversion H5. *)
(*   inversion H7. *)
(*   inversion H8. *)
(*   inversion H13. *)
(*   inversion H15. *)
(*   inversion H16. *)
(*   subst. *)
(*   subst. *)
(*   repeat comp_pres_wt_tac. *)
  
(*   progress destruct (HC h h0 h1). *)
(*   progress destruct (HC h h0 h1). *)


(*   match goal with *)
    
(*   end. *)

(*   comp_pres_wt_tac. *)
(*     intros p m IH1 i c2 t1 t2 t3 wtl wtr.  *)
(*     destruct p; destruct m; destruct i; destruct c2 as [p2 m2 i2 | p2 i2 l2]. *)
(*     destruct p2; destruct m2; destruct i2.  *)
(*     + inversion wtl; inversion wtr. inversion H5. inversion H13.  *)
(*       destruct t1; destruct t3; *)
(*       repeat comp_pres_wt_tac. *)
(*       destruct t1; destruct t3; *)
(*       repeat comp_pres_wt_tac. *)
      

(*       subst.constructor. eapply inj_mt_wt. comp_pres_wt_tac.   *)
      
(* |  : forall t1 t2 s, *)
(*       end. *)
(*       apply (hc_wt Dyn Dyn Dyn).  *)
(*       apply (prj_mt_wt).  *)
(*       apply ( *)
(*       destruct H3. *)
(*       destruct H5. *)
(*       destruct H6.  *)
(*       destruct H13.  *)
(*       destruct H11. *)
(*       destruct H14. *)
(*       compute. *)
(*       exact (hc_wt hc  *)
(*       subst.  *)
(*       exact (hc_wt {t2=Dyn}_ _ _).  *)
(*       inversion wtl. inversion H5. inversion wtr. discriminate h8.  *)
(*     destruct t.  *)
(*     inversion H3.  *)
(*     inversion  *)

(*       match goal with *)
(*       | |- _ /\ *)
(*     end. simpl. *)
    
(*     simpl. *)


(*     constructor. *)
(*     auto.  *)
(*     inversion H6. *)
(*     inversion H5. *)
(*     inversion wtl. *)
(*     apply IH1 in wtl *)
(*                  with p := inj_mt. *)
(*     discriminate. *)
    
(*     case m.  *)



  
      hc_to_c(comp_hc hc1 hc2) = comp_c (hc_to_c hc1) (hc_to_c hc2).

    (* todo implement regular coercions *)
    (* On hold until implementation is done.
     (* todo iso morphism test *)
     (* prove hcs now *)*)


(*b
Prove: 
hyper-coercion = compact-reference = coercions
Under Composition.
(* todo define isomorphism between hcs (hc), coercions (c))
(* hc_to_c_pres_comp hc_to_c(hc1;hc2) = hc_to_c(hc1);hc_to_c(hc2))
*)


(* trash *)
(* Fixpoint mk_hc n t1 t2 l : hc := *)
(*   match n with *)
(*   | 0 => Fail prj_mt Dyn 0 (* This is jiberish *) *)
(*   | S n' => *)
(*     match t1, t2 with *)
(*     | Dyn, Dyn => HC prj_mt (ι Dyn) inj_mt *)
(*     | Dyn, (Static (Base b)) => *)
(*       HC (prj l) (ι (Static (Base b))) inj_mt *)
(*     | Dyn, (Static (Composite ((t21 → t22) as t2_c))) => *)
(*       HC (prj l) *)
(*          (Med t2_c *)
(*               (mk_hc n' t21 t21 l →hc mk_hc n' t22 t22 l) *)
(*               t2_c) *)
(*          inj_mt *)
(*     | Dyn, (Static (Composite ((Ref t21) as t2_c))) => *)
(*       HC (prj l) *)
(*          (Med t2_c *)
(*               (Ref_hc (mk_hc n' t21 t21 l) *)
(*                       (mk_hc n' t21 t21 l)) *)
(*               t2_c) *)
(*          inj_mt *)
(*     | (Static (Base b)), Dyn => *)
(*       HC prj_mt (ι (Static (Base b))) inj *)
(*     | (Static (Composite ((t21 → t22) as t2_c))), Dyn => *)
(*       HC prj_mt *)
(*          (Med t2_c *)
(*               (mk_hc n' t21 t21 l →hc mk_hc n' t22 t22 l) *)
(*               t2_c) *)
(*          inj *)
(*     | (Static (Composite ((Ref t21) as t2_c))), Dyn => *)
(*       HC prj_mt *)
(*          (Med t2_c *)
(*               (Ref_hc (mk_hc n' t21 t21 l) *)
(*                       (mk_hc n' t21 t21 l)) *)
(*               t2_c) *)
(*          inj *)
(*     | (Static (Base b1)), (Static (Base b2)) => *)
(*       if tyb_eq b1 b2 *)
(*       then HC prj_mt (ι (Static (Base b2))) inj_mt *)
(*       else Fail prj_mt (Static (Base b1)) l  *)
(*     | Static (Composite ((t11 → t12) as t1_c)), *)
(*       Static (Composite ((t21 → t22) as t2_c)) => *)
(*       HC prj_mt *)
(*          (Med t1_c *)
(*               (mk_hc n' t12 t11 l →hc mk_hc n' t21 t22 l) *)
(*               t2_c) *)
(*          inj *)
(*     | Static (Composite ((Ref t11) as t1_c)), *)
(*       Static (Composite ((Ref t21) as t2_c)) => *)
(*       HC prj_mt *)
(*          (Med t1_c *)
(*               (Ref_hc (mk_hc n' t11 t21 l) *)
(*                       (mk_hc n' t21 t11 l)) *)
(*               t2_c) *)
(*          inj_mt *)
(*     | _, _ => Fail prj_mt t1 l  *)
(*     end *)
(*   end. *)

(* Definition make_hc (t1 t2 : Ty) l : hc := *)
(*   mk_hc (max (ty_depth t1) (ty_depth t2)) t1 t2 l.  *)

