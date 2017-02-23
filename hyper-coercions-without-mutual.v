
Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import GTypes.
Require Import coercions. 

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
| HC_Id  : hc_p -> Ty -> hc_i -> hc
| HC_Arr : hc_p -> Ty -> Ty -> Ty -> Ty -> hc -> hc -> hc_i -> hc
| HC_Ref : hc_p -> Ty -> Ty -> hc -> hc -> hc_i -> hc
| Fail : hc_p -> Ty -> blame_info -> hc.

Hint Constructors hc. 

Theorem hc_eqdec : forall x y : hc_i, {x = y} + {x <> y}.
Proof. decide_equality. Defined.

Inductive hc_p_wt : hc_p -> CTy -> Prop :=
| prj_mt_wt {t} : hc_p_wt prj_mt (t ⇒ t)
| prj_wt   {t l}: t <> Dyn -> hc_p_wt (prj l) (Dyn ⇒ t).

Inductive hc_i_wt : hc_i  -> CTy -> Prop :=
| inj_mt_wt {t} : hc_i_wt inj_mt (t ⇒ t)
| inj_c_wt {t}  : t <> Dyn -> hc_i_wt inj (t ⇒ Dyn).

Inductive hc_wt : hc -> CTy -> Prop :=
| hc_wt_id : forall t1 t2 t3 p i,
    hc_p_wt p (t1 ⇒ t2) ->
    hc_i_wt i (t2 ⇒ t3) ->
    hc_wt (HC_Id p t2 i) (t1 ⇒ t3)
| hc_wt_arr : forall t1 t21 t22 t31 t32 t4 c1 c2 p i,
    hc_p_wt p (t1 ⇒ (t21 → t22)) ->
    hc_i_wt i ((t31 → t32) ⇒ t4) ->
    hc_wt c1 (t31 ⇒ t21) ->
    hc_wt c2 (t22 ⇒ t32) ->
    hc_wt (HC_Arr p t21 t22 t31 t32 c1 c2 i) (t1 ⇒ t4)
| hc_wt_ref : forall t1 t2 t3 t4 c1 c2 p i,
    hc_p_wt p (t1 ⇒ (Ref t2)) ->
    hc_i_wt i ((Ref t3) ⇒ t4) ->
    hc_wt c1 (t2 ⇒ t3) ->
    hc_wt c2 (t3 ⇒ t2) ->
    hc_wt (HC_Ref p t2 t3 c1 c2 i) (t1 ⇒ t4)
| fail_wt : forall t1 t2 t3 p l,
    hc_p_wt p (CArr t1 t2) ->
    hc_wt (Fail p t2 l) (t1 ⇒ t3). 

Hint Constructors hc_i_wt hc_p_wt hc_wt. 

Inductive mk_hc : Ty * Ty * blame_info -> hc -> Prop :=
| Mk_hc_id {l t} : mk_hc (t, t, l) (HC_Id prj_mt t inj_mt)
| Mk_hc_dyn_l {t l} :
    t <> Dyn -> mk_hc (Dyn, t, l) (HC_Id (prj l) t inj_mt)
| Mk_hc_dyn_r {t l} :
    t <> Dyn -> mk_hc (t, Dyn, l) (HC_Id prj_mt t inj)
| Mk_hc_arr {t1 t2 t3 t4 l c1 c2} :
    mk_hc (t3, t1, l) c1 ->
    mk_hc (t2, t4, l) c2 ->
    mk_hc (t1 → t2, t3 → t4, l) (HC_Arr prj_mt t1 t2 t3 t4 c1 c2 inj_mt)
| Mk_hc_ref {t1 t2 l c1 c2} :
    mk_hc (t1, t2, l) c1 ->
    mk_hc (t2, t1, l) c2 ->
    mk_hc (Ref t1, Ref t2, l) (HC_Ref prj_mt t1 t2 c1 c2 inj_mt)
| Mk_hc_fail {t g l} :
    t <≁> g -> mk_hc (t, g, l) (Fail prj_mt t l).

Hint Constructors mk_hc. 

Lemma mk_hc_wt : forall t1 t2 l h,
    mk_hc (t1, t2, l) h -> hc_wt h (t1 ⇒ t2).
Proof.
  intros t1 t2 l h; gen t1 t2 l.
  induction h; intros;
  match goal with
  | H: mk_hc _ _ |- _ => inverts H
  end;
  repeat match goal with
         | H: mk_hc _ ?t, IH: forall t1 t2 l, mk_hc _ ?t -> _ |- _ =>
           apply IH in H
         end;
  auto.
Qed. 

Hint Resolve mk_hc_wt. 


Ltac prove_inconsistent :=
  match goal with
  | |- _ ≁ _ => solve [intro h; inversion h]
  | |- _ <≁> _ => solve [intro h; inversion h]
  | |- _ ∼ _ => constructor
  end.

Lemma mk_hc_symetry : forall h t1 t2 l,
    mk_hc (t1, t2, l) h -> exists h', mk_hc (t2, t1, l) h'.
Proof.
  intros h. 
  induction h; intros; 
  match goal with
  | H: mk_hc _ _ |- _ => inverts H
  end;
  repeat match goal with
         | H: mk_hc _ ?t, IH: forall t1 t2 l, mk_hc _ ?t -> _ |- _ =>
           apply IH in H
         | H: exists h, _ |- _ => destruct H
         end;
  eauto.
Qed.

Hint Resolve mk_hc_symetry.

Lemma mk_hc_total : forall t1 t2 l,
    exists h, mk_hc (t1, t2, l) h. 
Proof.
  induction t1; destruct t2; intros;
    repeat (match goal with
         | IH: (forall t l,
                   exists h, mk_hc (?g, t, l) h),
            T: Ty, L: blame_info |- _ =>
           match goal with
           | H: mk_hc (g, T, L) _ |- _ =>
             fail 1
           | _ => destruct (IH T L)
           end
         end);
    repeat (match goal with
            | H: mk_hc (?t1, ?t2, _) _ |- _ =>
              match goal with
              | H': mk_hc (t2, t1, _) _ |- _ =>
                fail 1
              | _ => 
                destruct (mk_hc_symetry _ _ _ _ H)
              end
            end);
    eexists;
    econstructor;
    try prove_inconsistent;
    try discriminate;
    try eassumption. 
Qed.

Hint Resolve mk_hc_total.

Lemma mk_hc_not_dyn : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn ->
    (exists t, mk_hc (t1, t2, l) (HC_Id prj_mt t inj_mt)) \/
    (exists t3 t4 t5 t6 c1 c2,
        mk_hc (t1, t2, l) (HC_Arr prj_mt t3 t4 t5 t6 c1 c2 inj_mt)) \/
    (exists t3 t4 c1 c2,
        mk_hc (t1, t2, l) (HC_Ref prj_mt t3 t4 c1 c2 inj_mt)) \/
    (mk_hc (t1, t2, l) (Fail prj_mt t1 l)). 
Proof. intros t1 t2 l H1 H2. destruct (mk_hc_total t1 t2 l) as [h mk_h]. 
       inverts mk_h; subst; eauto 6.
       intuition (try discriminate; eauto).

       
(*     t1 <> Dyn -> t2 <> Dyn -> *)
(*     (exists m, mk_hc (t1, t2, l) (HC prj_mt m inj_mt)) \/ *)
(*     mk_hc (t1, t2, l) (Fail prj_mt t1 l). *)
(* Proof. intros t1 t2 l t1nDyn t2nDyn. *)
(*        destruct (mk_hc_total t1 t2 l).  *)
(*        inversion H; subst; eauto.  *)
(* Qed.  *)


Inductive mediating_ty : hc -> CTy -> Prop:=
| Med_Ty_Id {p t i} : mediating_ty (HC_Id p t i) (t ⇒ t)
| Med_Ty_Arr {p t1 t2 t3 t4 h1 h2 i} :
    mediating_ty (HC_Arr p t1 t2 t3 t4 h1 h2 i) (t1 → t2 ⇒ t3 → t4)
| Med_Ty_Ref {p t1 t2 h1 h2 i} :
    mediating_ty (HC_Ref p t1 t2 h1 h2 i) (Ref t1 ⇒ Ref t2).

Hint Constructors mediating_ty.

(* Lemma mediating_ty_total : forall m, exists t1 t2, mediating_ty m (t1 ⇒ t2). *)
(* Proof. destruct m; eauto. Qed.  *)

Inductive mk_hc' : Ty * Ty * hc_p -> hc -> Prop :=
| mk_hc_cast {t1 t2 l h} : mk_hc (t1, t2, l) h -> mk_hc' (t1, t2, prj l) h
| mk_hc_id {t p} : mk_hc' (t, t, p) (HC_Id prj_mt t inj_mt).

Inductive outer_casts : hc -> hc_p * hc_i -> Prop :=
| OC_Id  {p t i} : outer_casts (HC_Id p t i) (p, i)
| OC_Arr {p t1 t2 t3 t4 h1 h2 i} : outer_casts (HC_Arr p t1 t2 t3 t4 h1 h2 i) (p, i)
| OC_Ref {p t1 t2 h1 h2 i} : outer_casts (HC_Ref p t1 t2 h1 h2 i) (p, i).

Inductive divide_prj : hc -> hc_p * hc -> Prop :=
| DP_Id  {p t i} : divide_prj (HC_Id p t i) (p, HC_Id prj_mt t i)
| DP_Arr {p t1 t2 t3 t4 h1 h2 i} :
    divide_prj (HC_Arr p t1 t2 t3 t4 h1 h2 i)
               (p, HC_Arr prj_mt t1 t2 t3 t4 h1 h2 i)
| DP_Ref {p t1 t2 h1 h2 i} :
    divide_prj (HC_Ref p t1 t2 h1 h2 i)
               (p, HC_Ref prj_mt t1 t2 h1 h2 i).

Inductive divide_inj : hc -> hc * hc_i -> Prop :=
| DI_Id  {p t i} : divide_inj (HC_Id p t i) (HC_Id p t inj_mt, i)
| DI_Arr {p t1 t2 t3 t4 h1 h2 i} :
    divide_inj (HC_Arr p t1 t2 t3 t4 h1 h2 i)
               (HC_Arr p t1 t2 t3 t4 h1 h2 inj_mt, i)
| DI_Ref {p t1 t2 h1 h2 i} :
    divide_inj (HC_Ref p t1 t2 h1 h2 i)
               (HC_Ref p t1 t2 h1 h2 inj_mt, i).

Hint Constructors mk_hc' outer_casts divide_prj divide_inj. 

Inductive compose_hc : (hc * hc) -> hc -> Prop :=
|Comp_hc_Dyn_L {p1 i1 h2}: compose_hc (HC_Id p1 Dyn i1, h2) h2
|Comp_hc_Dyn_R {h1 p2 i2}: compose_hc (h1, HC_Id p2 Dyn i2) h1
|Comp_hc_good {h1 h2 h3 t11 t12 t21 t22 i1 p2 h4 h5 h6 h7}:
   mediating_ty h1 (t11 ⇒ t12) ->
   mediating_ty h2 (t21 ⇒ t22) ->
   divide_inj h1 (h3, i1) ->
   divide_prj h2 (p2, h4) ->
   mk_hc' (t12, t21, p2) h5 ->
   compose_hc_m (h3, h5) h6 ->
   compose_hc_m (h6, h4) h7 ->
   t12 <> Dyn ->
   t21 <> Dyn ->
   compose_hc (h1, h2) h7
with
compose_hc_m : hc * hc -> hc -> Prop :=
| compose_hc_id {t p1 i1 p2 i2} :
    compose_hc_m (HC_Id p1 t i1, HC_Id p2 t i2) (HC_Id p1 t i2)
| compose_Arr {p1 t11 t12 t21 t22 h11 h12 i1
               p2 t31 t32 h21 h22 i2 h31 h32}:
    compose_hc (h21, h11) h31 ->
    compose_hc (h12, h22) h32 -> 
    compose_hc_m (HC_Arr p1 t11 t12 t21 t22 h11 h12 i1,
                  HC_Arr p2 t21 t22 t31 t32 h21 h22 i2)
                 (HC_Arr p1 t11 t12 t31 t32 h31 h32 i2)
| compose_hc_id_arr {p1 t11 t12 i1 p2 t21 t22 h21 h22 i2} :
    compose_hc_m (HC_Id p1 (t11 → t12) i1,
                  HC_Arr p2 t11 t12 t21 t22 h21 h22 i2)
                 (HC_Arr p1 t11 t12 t21 t22 h21 h22 i2)
| compose_hc_arr_id {p1 t11 t12 t21 t22 h11 h12 i1 p2 i2} :
    compose_hc_m (HC_Arr p1 t11 t12 t21 t22 h11 h12 i1,
                  HC_Id p2 (t21 → t22) i2)
                 (HC_Arr p1 t11 t12 t21 t22 h11 h12 i2).

(* | compose_Arr {t11 t12 t21 t22 t31 t32 h1 h2 h3 h4 h5 h6}: *)
(*     compose_hc (h3, h1) h5 -> *)
(*     compose_hc (h2, h4) h6 ->  *)
(*     compose_hc_m (Arr_hc t11 t12 t21 t22 h1 h2, *)
(*                   Arr_hc t21 t22 t31 t32 h3 h4) *)
(*                  (Arr_hc t11 t12 t31 t3                  *)
(* | compose_Ref {t1 t2 t3 h1 h2 h3 h4 h5 h6} : *)
(*     (* Todo Check that this is correct *) *)
(*     compose_hc (h1, h3) h5 -> *)
(*     compose_hc (h4, h2) h6 -> *)
(*     compose_hc_m (Ref_hc t1 t2 h1 h2, *)
(*                   Ref_hc t2 t3 h3 h4) *)
(*                  (Ref_hc t1 t3 h5 h6).  *)
(* | compose_hc_id_R {h1 p1 i1 h2} : compose_hc_m (m, Id_hc t1) m *)


(* |Comp_hc_fail {p1 m1 l m2 i2 t1 t2 t3 t4} : *)
(*    mediating_ty m1 (t1 ⇒ t2) -> *)
(*    mediating_ty m2 (t3 ⇒ t4) -> *)
(*    t2 <> Dyn -> t3 <> Dyn -> *)
(*    mk_hc (t2, t3, l) (Fail prj_mt t2 l) -> *)
(*    compose_hc (HC p1 m1 inj, HC (prj l) m2 i2) (Fail p1 t1 l) *)
(* |Comp_hc_fail_L {p t l h}: *)
(*    compose_hc (Fail p t l, h) (Fail p t l) *)
(* |Comp_hc_fail_R_good {p1 m1 i1 p2 t11 t12 t2 t3 t4 l2 p3 m3 i3}: *)
(*    mediating_ty m1 (t11 ⇒ t12) -> *)
(*    mk_hc' (t12, t2, p2) (HC p3 m3 i3) ->  *)
(*    mediating_ty m3 (t3 ⇒ t4) -> *)
(*    (* shallow consistent prime would work here *) *)
(*    compose_hc (HC p1 m1 i1, Fail p2 t2 l2) (Fail p3 t3 l2) *)
(* |Comp_hc_fail_R_fail {p1 m1 i1 p2 t2 l2 t11 t12 p3 l3}: *)
(*    mediating_ty m1 (t11 ⇒ t12) -> *)
(*    (* shallow consistent prime would work here *) *)
(*    mk_hc' (t12, t2, p2) (Fail p3 t12 l3) -> *)
(*    compose_hc (HC p1 m1 i1, Fail p2 t2 l2) (Fail p1 t11 l3)               *)
(* with *)
(* (* assuming m1 : t1 => t2 and m2 : t2 => t3 *) *)
(* compose_hc_m : (hc_m * hc_m) -> hc_m -> Prop := *)
(* | compose_hc_id_L {t1 m} : compose_hc_m (Id_hc t1, m) m *)
(* | compose_hc_id_R {t1 m} : compose_hc_m (m, Id_hc t1) m *)
(* | compose_Arr {t11 t12 t21 t22 t31 t32 h1 h2 h3 h4 h5 h6}: *)
(*     compose_hc (h3, h1) h5 -> *)
(*     compose_hc (h2, h4) h6 ->  *)
(*     compose_hc_m (Arr_hc t11 t12 t21 t22 h1 h2, *)
(*                   Arr_hc t21 t22 t31 t32 h3 h4) *)
(*                  (Arr_hc t11 t12 t31 t32 h5 h6) *)
(* | compose_Ref {t1 t2 t3 h1 h2 h3 h4 h5 h6} : *)
(*     (* Todo Check that this is correct *) *)
(*     compose_hc (h1, h3) h5 -> *)
(*     compose_hc (h4, h2) h6 -> *)
(*     compose_hc_m (Ref_hc t1 t2 h1 h2, *)
(*                   Ref_hc t2 t3 h3 h4) *)
(*                  (Ref_hc t1 t3 h5 h6).  *)


Hint Constructors compose_hc compose_hc_m. 



Definition id_dyn  := (HC_Id prj_mt Dyn inj_mt).
Definition id_fun  := (HC_Id prj_mt (Int → Int) inj_mt).
Definition id_int  := (HC_Id prj_mt Int inj_mt).
Definition prj_int := (HC_Id (prj 1) Int inj_mt).
Definition inj_int := (HC_Id prj_mt Int inj).
Definition chk_int := (HC_Id (prj 1) Int inj).
Definition prj_fun := (HC_Id (prj 3) (Dyn → Dyn) inj_mt).
Definition inj_fun := (HC_Id prj_mt  (Dyn → Dyn) inj).
Definition chk_fun := (HC_Id (prj 3) (Dyn → Dyn) inj).
Definition fun_hc1 := (HC_Arr prj_mt Dyn Dyn Int Int inj_int prj_int inj_mt).
Definition fun_hc2 := (HC_Arr prj_mt Int Int Dyn Dyn prj_int inj_int inj_mt).
Definition fun_hc3 := (HC_Arr prj_mt Dyn Dyn Int Int inj_int prj_int inj).
Definition fun_hc4 := (HC_Arr (prj 3) Dyn Dyn Int Int inj_int prj_int inj_mt).
Definition fun_hc5 := (HC_Arr prj_mt Int Int Int Int id_int id_int inj_mt).
Definition fun_hc6 := (HC_Arr prj_mt Dyn Dyn Dyn Dyn chk_int chk_int inj_mt).
Definition fun_hc7 := (HC_Arr prj_mt Int Int Int Int id_int id_int inj_mt). 
                        
Hint Unfold id_dyn id_fun id_int 
     prj_int inj_int chk_int
     prj_fun inj_fun chk_fun
     fun_hc1 fun_hc2 fun_hc3 fun_hc4 fun_hc5 fun_hc6.


Ltac hc_infer :=
  autounfold; eexists; eexists;
  repeat (econstructor; intuition; try discriminate; eauto).

Example id_dyn_wt  : exists t1 t2, hc_wt id_dyn (t1 ⇒ t2). 
Proof. hc_infer. Qed. 
Example id_fun_wt  : exists t1 t2, hc_wt id_fun (t1 ⇒ t2).
Proof. hc_infer. Qed. 
Example id_int_wt  : exists t1 t2, hc_wt id_int (t1 ⇒ t2).
Proof. hc_infer. Qed. 
Example prj_int_wt : exists t1 t2, hc_wt prj_int (t1 ⇒ t2).
Proof. hc_infer. Qed. 
Example inj_int_wt : exists t1 t2, hc_wt inj_int (t1 ⇒ t2). 
Proof. hc_infer. Qed. 
Example chk_int_wt : exists t1 t2, hc_wt chk_int (t1 ⇒ t2). 
Proof. hc_infer. Qed.
Example prj_fun_wt : exists t1 t2, hc_wt prj_fun (t1 ⇒ t2). 
Proof. hc_infer. Qed. 
Example inj_fun_wt : exists t1 t2, hc_wt inj_fun (t1 ⇒ t2). 
Proof. hc_infer. Qed. 
Example chk_fun_wt : exists t1 t2, hc_wt chk_fun (t1 ⇒ t2). 
Proof. hc_infer. Qed.
Example fun_hc1_wt : exists t1 t2, hc_wt fun_hc1 (t1 ⇒ t2). 
Proof. hc_infer. Qed. 
Example fun_hc2_wt : exists t1 t2, hc_wt fun_hc2 (t1 ⇒ t2). 
Proof. hc_infer. Qed.
Example fun_hc3_wt : exists t1 t2, hc_wt fun_hc3 (t1 ⇒ t2). 
Proof. hc_infer. Qed.
Example fun_hc4_wt : exists t1 t2, hc_wt fun_hc4 (t1 ⇒ t2). 
Proof. hc_infer. Qed.
Example fun_hc5_wt : exists t1 t2, hc_wt fun_hc5 (t1 ⇒ t2). 
Proof. hc_infer. Qed.
Example fun_hc6_wt : exists t1 t2, hc_wt fun_hc6 (t1 ⇒ t2).  
Proof. hc_infer. Qed.
Example fun_hc7_wt : exists t1 t2, hc_wt fun_hc7 (t1 ⇒ t2).  
Proof. hc_infer. Qed. 

Ltac compute_compose :=
  repeat match goal with
         | _ => progress autounfold
         | _ => apply Comp_hc_Dyn_L
         | _ => apply Comp_hc_Dyn_R
         | _ => eapply compose_Arr
         | _ => eapply Comp_hc_good
         | _ => progress (intuition discriminate)
         | _ => progress auto
         end.

Example e_comp_1 : compose_hc (id_dyn, id_dyn) id_dyn. 
Proof. compute_compose. Qed. 
Example e_comp_2 : compose_hc (id_dyn, prj_fun) prj_fun. 
Proof. compute_compose. Qed. 
Example e_comp_3 : compose_hc (prj_fun, inj_fun) chk_fun. 
Proof. compute_compose. Qed. 
Example e_comp_4 : compose_hc (fun_hc1, fun_hc2) fun_hc6. 
Proof. compute_compose. Qed. 
Example e_comp_5 : compose_hc (fun_hc2, fun_hc1) fun_hc7. 
Proof. compute_compose. Qed. 



Hint Constructors compose_hc compose_hc_m. 

Theorem compose_hc_total : forall h1 h2 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    exists h3, compose_hc (h1, h2) h3.
Proof.
  intros h1 h2 t1 t2 t3 wt1 wt2.
  induction h1; induction h2. 
  inversion wt1; subst; inversion wt2; subst; 
    repeat match goal with
           | H: hc_p_wt _ _ |- _ => inverts H
           | H: hc_i_wt _ _ |- _ => inverts H
           end;
    repeat match goal with
           | _ => try subst; solve[eauto]
           | |- context[compose_hc ((HC_Id _ ?t _), _) _] =>
             match goal with
             | H: t <> Dyn |- _ => fail 1
             | H: t = Dyn |- _ => fail 1
             | _ => destruct (ty_eqdec t Dyn)
             end
           | |- context[compose_hc (_, (HC_Id _ ?t _)) _] =>
             match goal with
             | H: t <> Dyn |- _ => fail 1
             | H: t = Dyn |- _ => fail 1
             | _ => destruct (ty_eqdec t Dyn)
             end
           | H: ?t <> ?t |- _ => contradiction H; reflexivity
           | |- exists x, _ => eexists
           end;
    repeat match goal with
               | H1: ?t1 <> Dyn, H2: ?t2 <> Dyn, l: blame_info |- _ =>
                 match goal with
                   | H: mk_hc (t1, t2, l) _ |- _ => fail 1 
                   | _ => destruct (mk_hc_total t1 t2 l)
                 end
           end.

  repeat intuition (try discriminate; eauto).



    eapply Comp_g
    econstructor. 
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eassumption. 
    econstructor. 
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    eassumption. 
    
    destruct (mk_hc_total. 
    econstructor. 
    
    repeat (try eassumption; econstructor).
    
    auto. 

  
  
               | |- context[(HC _ ?m _)] =>
                 match goal with
                 | H: mediating_ty m _ |- _ => fail 1
                 | _ =>
                   destruct (mediating_ty_total (Id_hc t5)) as [[]];
                   match goal with
                   | H': mediating_ty m _ |- _ => inversion H'; subst
                   end
                 end
               | _ => discriminate
                end).
   - time 
   - time repeat match goal with
               | H1: ?t1 <> Dyn, H2: ?t2 <> Dyn, l: blame_info |- _ =>
                 match goal with
                   | H: mk_hc (t1, t2, l) (HC _ _ _) |- _ => fail 1
                   | H: mk_hc (t1, t2, l) (Fail _ _ _) |- _ => fail 1
                   | _ =>
                     idtac "money" t1 t2;
                       destruct (mk_hc_not_dyn t1 t2 l H1 H2) as [[]|]
                 end
               end; eauto.
   - time repeat match goal with
               | H1: ?t1 <> Dyn, H2: ?t2 <> Dyn, l: blame_info |- _ =>
                 match goal with
                   | H: mk_hc (t1, t2, l) (HC _ _ _) |- _ => fail 1
                   | H: mk_hc (t1, t2, l) (Fail _ _ _) |- _ => fail 1
                   | _ =>
                     idtac "money" t1 t2;
                       destruct (mk_hc_not_dyn t1 t2 l H1 H2) as [[]|]
                 end
               end; eauto. 

    
  inversion wt1; inversion wt2; induction wt1. subst. 
  induction wt1. 
  + eexists. 
  + eexists.  inverts H1. inverts H2.

  ; destruct h2. intuition. eexists. compute_compose.  eauto. 
  elim h1 using hc_ind_mut with
  (P := fun h => forall h2 t1 t2 t3,
            hyper_coercion_wt h  (t1 ⇒ t2) ->
            hyper_coercion_wt h2 (t2 ⇒ t3) ->
            exists h3, compose_hc (h, h2) h3)
  (P0 := fun m => 
           match m with
           | (Id_hc i) => True
           | (Arr_hc _ _ _ _ h1 h2) =>
             (forall h2 t1 t2 t3,
                 hyper_coercion_wt h1  (t1 ⇒ t2) ->
                 hyper_coercion_wt h2  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h1, h2) h3)
             /\
             (forall h1 t1 t2 t3,
                 hyper_coercion_wt h2  (t1 ⇒ t2) ->
                 hyper_coercion_wt h1  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h1, h2) h3)
           | (Ref_hc _ _ h1 h2) =>
             (forall h2 t1 t2 t3,
                 hyper_coercion_wt h1  (t1 ⇒ t2) ->
                 hyper_coercion_wt h2  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h1, h2) h3)
             /\
             (forall h1 t1 t2 t3,
                 hyper_coercion_wt h2  (t1 ⇒ t2) ->
                 hyper_coercion_wt h1  (t2 ⇒ t3) ->
                 exists h3, compose_hc (h1, h2) h3)
           end).
  (*
    - destructing mediating coercion in the first hyper coercions to
       force the case 
    - destructing all injections in projection to permit easy case analysis
    - destructing second hyper coercion to find easy cases
  *)
 + time (time (intros  [] [t11 | t11 t12 t13 t14 h11 h12 | t11 t12 h11 h12] P []
                       [[] [t21 | t21 t22 t23 t24 h21 h22 | t21 t22 h21 h22]   [] |] 
                       t1 t2 t3 wt1 wt2;
               inversion wt1; subst; inversion wt2; subst);
         
     inversion H; eauto. 
     subst. econstructor. econstructor. econstructor. econstructor.
     econstructor. eassumption. eassumption. eassumption.
     econstructor. econstructor. 
     inversion 

   eauto.
   end  .
   idtac "money" t3 t5; destruct (mk_hc_not_dyn t3 t5 b) as [[]|].
        try discriminate;
        try (solve[eauto]).
  - destruct (mediating_ty_total (Id_hc t5)) as [Ht11 [Ht12 Ht1]];
    destruct (mediating_ty_total (Id_hc t3)) as [Ht21 [Ht22 Ht2]].
    inversion Ht1; inversion Ht2; subst. 
    destruct (mk_hc_not_dyn Ht12 Ht22 b); try eassumption.
    destruct H; eauto.  
    eauto. 

    eauto. 
    eexists. econstructor. eassumption. eassumption.
    
    eexists. econstructor. econstructor. econstructor.
    econstructor. destruct (mk_hc_total t5 t3 b). apply
  - exists (Fail (prj l0)  b). 
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
    (hyper_coercion_wt c1 (t1 ⇒ t2)) ->
    (hyper_coercion_wt c2 (t2 ⇒ t3)) ->
    exists c3, compose_hc (c1, c2) c3 /\
               hyper_coercion_wt c3 (t1 ⇒ t3).
Proof. Admitted.


Definition wt_hc t g := {h | hyper_coercion_wt h (t ⇒ g)}.  
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



(* Fixpoint comp n c1 c2 : hyper_coercion := *)
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
(*        fl (n : Nat) (p : hc_p) (t1 : Ty_c) (m : hc_m) (c : hyper_coercion) := *)
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
(*        f2 (n : Nat) (c : hyper_coercion) (m : hc_m) (i : hc_i) := *)
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
(*     | |- hyper_coercion_wt _ _ => *)
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
(*              (hyper_coercion_wt (HC p m i) (t1 ⇒ t2)) -> *)
(*              (hyper_coercion_wt c2 (t2 ⇒ t3)) -> *)
(*              (hyper_coercion_wt (compose (HC p m i) c2) (t1 ⇒ t3))) *)
(*   (P1 := fun s:hc_s => *)
(*            forall p t11 t12 i c2 t1 t2 t3, *)
(*              (hyper_coercion_wt (HC p (Med t11 s t12) i) (t1 ⇒ t2)) -> *)
(*              (hyper_coercion_wt c2 (t2 ⇒ t3)) -> *)
(*              (hyper_coercion_wt (compose (HC p (Med t11 s t12) i) c2) (CArr t1 t3))). *)
(*   repeat comp_pres_wt_tac. *)
(*   destruct c2. *)
(*   match goal with *)
(*   | [ |- *)
(*   | [ H1: hyper_coercion_wt _ _ , *)
(*       H2: hyper_coercion_wt _ _ *)
(*       |- hyper_coercion_wt *)
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
     (* prove hyper_coercions now *)*)


(*b
Prove: 
hyper-coercion = compact-reference = coercions
Under Composition.
(* todo define isomorphism between hyper_coercions (hc), coercions (c))
(* hc_to_c_pres_comp hc_to_c(hc1;hc2) = hc_to_c(hc1);hc_to_c(hc2))
*)


(* trash *)
(* Fixpoint mk_hc n t1 t2 l : hyper_coercion := *)
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

(* Definition make_hc (t1 t2 : Ty) l : hyper_coercion := *)
(*   mk_hc (max (ty_depth t1) (ty_depth t2)) t1 t2 l.  *)

