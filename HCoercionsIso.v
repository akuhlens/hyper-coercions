Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FinFun.
Require Import LibTactics. 
Require Import General. 
Require Import Types. 
Require Import Coercions. 
Require Import HCoercions.
Require Import HCoercionsCompose. 
Require Import Omega. 
Require Import SolveMax.
Open Scope depth_scope. 

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

(* SearchAbout "Bijective". *)

(*

t   := arbitrary types
I J := injectables t ≠ ⋆
l   := blame labels
c   := space efficient coercions | i
i   := ⊥ᴵˡᴶ |
p   := ∈ | l
h   := hyper coercions  | pt⊥ˡt

⊥ᴵˡᴶ  <-> ∈t₁⊥ˡ

Typing rule for failed in regular coercions
pretty much direct translation from Siek et al (PLDI'15).

t₁ ≠ ⋆   t₁ ∼ I    I ≠ J
----------------------------
   ⊢ ⊥ᴵˡᴶ : t₁ => t₂

Typing rule for failed in hyper coercions

 tₚ ≠ ⋆   ⊢ p : t₁ => tₚ
----------------------------
   ⊢ ptₚ⊥ˡ : t₁ => t₂

Notice that here we are always able to reconstruct
the projection side of the type in type judgements.


Say we want to define isomorphic (≡) as the existance
of a bijection between two entities.

h ≡ c : 
 ∃ f : h -> c, g : c -> h -> 
  (∀ h, g (f h) = h) /\ (forall c, f (g c) = c)

But we probably want that bijection
to always produce well typed terms at
the same type that previous derivation
⊢ h : (t₁ => t₂) ->  ⊢ f h : (t₁ => t₂)
/\
⊢ c : (t₁ => t₂) ->  ⊢ g h : (t₁ => t₂)

I think that it is unlikely that it is
possible to find a function g that can
live up to this expectation.
*)

Fixpoint h2c_help h t1 t2 : crcn :=
  match h with 
  | (HC p t1 m t2 i) => 
    let m' :=
        match (m, t1, t2) with
        | (Arr_hc c1 c2, Arr t1 t2, Arr t3 t4) =>
          Arr_c (h2c_help c1 t3 t1) (h2c_help c2 t2 t4)
        | (Ref_hc c1 c2, Ref t1, Ref t2) =>
          Refc (h2c_help c1 t2 t1) (h2c_help c2 t1 t2)
        | (_ , t1 , t2) => Id_c t1
        end
    in
    match p with
    | (prj l) => 
      match i with
      | inj => Prjc t1 l ;c (m' ;c Injc t2)
      | inj_mt => Prjc t1 l ;c m'
      end
    | prj_mt =>
      match i with
      | inj => m' ;c Injc t2
      | inj_mt => m'
      end
    end
  | (Fail p t1 (I1, l, I2)) => 
    match p with
    | (prj l') => Prjc t1 l' ;c (Failc I1 l I2)
    | prj_mt => (Failc I1 l I2)
    end
  end.
 
Fixpoint h2c (hwt : (hc * ty * ty)) : (crcn * ty * ty) :=
  match hwt with
  | (h, t1, t2) => (h2c_help h t1 t2, t1, t2)
 end.

Definition s_wt := se_coercion. 
Hint Unfold s_wt.

Fixpoint c2h_help s t1 t2 : hc :=
    match s with
  | (Prjc t1 l1) ;c i  =>
    match i with
    | g ;c (Injc t2) =>
      (* manually inlining this makes this code a cinch for
         the totality check *)
      let m := match (g, t1, t2) with
               | (Arr_c s1 s2, Arr t1 t2, Arr t3 t4) =>
                 (Arr_hc (c2h_help s1 t3 t1)
                         (c2h_help s2 t2 t4))
               | (Refc s1 s2, Ref t1, Ref t2)  =>
                 (Ref_hc (c2h_help s1 t2 t1)
                         (c2h_help s2 t1 t2))
               | _ => Id_hc
               end
      in HC (prj l1) t1 m t2 inj
    | Failc I1 l2 I2 =>
      Fail (prj l1) t1 (I1, l2, I2)
    | g =>
      (* manually inlining this makes this code a cinch for
         the totality check *)
      let m := match (g, t1, t2) with
               | (Arr_c s1 s2, Arr t1 t2, Arr t3 t4) =>
                 (Arr_hc (c2h_help s1 t3 t1)
                         (c2h_help s2 t2 t4))
               | (Refc s1 s2, Ref t1, Ref t2)  =>
                 (Ref_hc (c2h_help s1 t2 t1)
                         (c2h_help s2 t1 t2))
               | _ => Id_hc
               end
        in HC (prj l1) t1 m t2 inj_mt 
    end
  | i => 
    match i with 
    | g ;c (Injc t2) =>
      (* manually inlining this makes this code a cinch for
         the totality check *)
      let m := match (g, t1, t2) with
               | (Arr_c s1 s2, Arr t1 t2, Arr t3 t4) =>
                 (Arr_hc (c2h_help s1 t3 t1)
                         (c2h_help s2 t2 t4))
               | (Refc s1 s2, Ref t1, Ref t2)  =>
                 (Ref_hc (c2h_help s1 t2 t1)
                         (c2h_help s2 t1 t2))
               | _ => Id_hc
               end
      in HC prj_mt t1 m t2 inj
    | Failc I1 l2 I2 =>
      Fail prj_mt t1 (I1, l2, I2)
    | g => 
      (* manually inlining this makes this code a cinch for
         the totality check *)
      let m := match (g, t1, t2) with
               | (Arr_c s1 s2, Arr t1 t2, Arr t3 t4) =>
                 (Arr_hc (c2h_help s1 t3 t1)
                         (c2h_help s2 t2 t4))
               | (Refc s1 s2, Ref t1, Ref t2)  =>
                 (Ref_hc (c2h_help s1 t2 t1)
                         (c2h_help s2 t1 t2))
               | _ => Id_hc
               end
      in HC prj_mt t1 m t2 inj_mt 
      end
  end.

Fixpoint c2h (cwt : (crcn * ty * ty)) : (hc * ty * ty) :=
  match cwt with
  | (c, t1, t2) => (c2h_help c t1 t2, t1, t2)
  end.

Lemma h2c_help_lemma' : forall n h t1 t2,
    [| h |] < n -> 
    hc_wt h (t1 ⇒ t2) -> 
    c2h_help (h2c_help h t1 t2) t1 t2 = h. 
Proof.
    induction n.
  - intuition.
  - introv bnd wt.
    inverts wt.
    + inverts H1; inverts H3; inverts H4. 
      all: simpl.
      all: repeat match goal with
                  | H: hc_wt _ _ |- _ =>
                    apply IHn in H;
                      [rewrite H | contains_tac]
                  end.
      all: congruence.
    + tc_tac. 
      all: simpl.
      all: reflexivity.
Qed. 

Lemma h2c_help_lemma : forall h t1 t2,
    hc_wt h (t1 ⇒ t2) -> 
    c2h_help (h2c_help h t1 t2) t1 t2 = h.
Proof.
  introv wt.
  apply (h2c_help_lemma' (1 + [|h|])).
  eauto.
  eauto.
Qed.
  
Lemma h2c_lemma' : forall n h t1 t2,
    [| h |] < n -> 
    hc_wt h (t1 ⇒ t2) -> 
    c2h (h2c (h, t1, t2)) = (h, t1, t2).
Proof.
  intros.
  simpl.
  rewrite h2c_help_lemma.
  reflexivity.
  eauto.
Qed.

Lemma h2c_lemma : forall h t1 t2,
    hc_wt h (t1 ⇒ t2) -> 
    c2h (h2c (h, t1, t2)) = (h, t1, t2).
Proof.
  intros.
  apply (h2c_lemma' (1+[|h|])).
  eauto. 
  assumption.
Qed. 

Fixpoint c_depth (c : crcn) : nat :=
  match c with
  | Prjc t1 l => ty_depth t1
  | Injc t2 => ty_depth t2
  | Id_c t => 0
  | Seq_c c1 c2 => max (c_depth c1) (c_depth c2)
  | Arr_c c1 c2 => 1 + max (c_depth c1) (c_depth c2)
  | Refc c1 c2 => 1 + max (c_depth c1) (c_depth c2)
  | Failc _ _ _ => 0
  end.

Instance c_deep : Deep crcn := c_depth.
Hint Unfold c_deep. 

Lemma c2h_help_lemma : forall c t1 t2,
    se_coercion c (t1 ⇒ t2) -> 
    h2c_help (c2h_help c t1 t2) t1 t2 = c. 
Proof.
  intros c.
  match goal with
  | |- ?g =>
    assert (H: forall n, [| c |] < n -> g)
  end.
  { intros n.
    generalize dependent c. 
    induction n. 
    - intuition.
    - introv b w.
      inverts w. 
      all: repeat match goal with
                  | H: se_inj_coercion _ _ |- _ => inverts H
                  | H: se_med_coercion _ _ |- _ => inverts H
                  end.
      all: simpl.
      all: repeat match goal with
               | H: se_coercion _ _ |- _ =>
                 apply IHn in H; [rewrite H | max_tac]
               end.
      all: eauto.
  }
  apply (H (1 + [|c|])).
  max_tac. 
Qed.   

Lemma c2h_lemma : forall c t1 t2,
    se_coercion c (t1 ⇒ t2) -> 
    h2c (c2h (c, t1, t2)) = (c, t1, t2).  
Proof.
  intros.
  simpl.
  rewrite c2h_help_lemma. 
  auto.
  assumption. 
Qed. 




Theorem hc_iso :
  (forall h t1 t2,
      hc_wt h (t1 ⇒ t2) ->
      c2h (h2c (h, t1, t2)) = (h, t1, t2)) 
  /\
  (forall c t1 t2,
      se_coercion c (t1 ⇒ t2) ->
      h2c (c2h (c, t1, t2)) = (c, t1, t2)).
Proof.
  split. 
  apply h2c_lemma.
  apply c2h_lemma.
Qed.

Definition compose_c := compose_coercions. 
Hint Unfold compose_c. 


Theorem hc_iso_help_respects_compose' : forall n h1 h2 h3 c1 c2 c3 t1 t2 t3,
    [| h1 |] < n ->
    [| h2 |] < n -> 
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    compose_hc (h1, h2) h3 ->
    h2c_help h1 t1 t2 = c1 ->
    h2c_help h2 t2 t3 = c2 ->
    h2c_help h3 t1 t3 = c3 ->
    compose_c (c1, c2) c3.
Proof.
  induction n.
  - intuition. 
  - introv b1 b2 w1 w2.
    introv cp e1 e2 e3.
    inverts w1; inverts w2; inverts cp.
    + tc_tac.
      all: simpl in *.
      all: subst. 
      all: eauto. 
    + tc_tac.
      all: simpl in *.
      all: subst. 
      all: eauto. 
    + inverts H16. 
      * tc_tac; simpl in *; subst; eauto. 
      * tc_tac; simpl in *; subst; eauto.
      *
Admitted.

Theorem hc_iso_respects_compose : forall h1 h2 h3 c1 c2 c3 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    compose_hc (h1, h2) h3 ->
    h2c (h1, t1, t2) = (c1, t1, t2) ->
    h2c (h2, t2, t3) = (c2, t2, t3) ->
    h2c (h3, t1, t3) = (c3, t1, t3) ->
    compose_c (c1, c2) c3.
Proof.
  intros.
  simpl in *.
  inversion H2; inversion H3; inversion H4.
  eapply (hc_iso_help_respects_compose' (1 + [|h1|] + [|h2|]) h1 h2).
  omega. 
  omega.
  eassumption. 
  eassumption.
  eassumption.
  congruence.
  congruence.
  congruence.
Qed. 

Lemma h2c_wt_n : forall n h t1 t2,
    [|h|] < n ->
    hc_wt h (t1 ⇒ t2) -> s_wt (h2c_help h t1 t2) (t1 ⇒ t2).
Proof.
  induction n. 
  - intuition. 
  - introv bnd wt. 
    inverts wt.
    + tc_tac. 
      all: repeat match goal with
                  | H: hc_wt _ _ |- _ => apply IHn in H; [idtac | max_tac]
                  end.
      all: solve[simpl; eauto].
    + tc_tac.
      all: simpl.
      all: eauto.
Qed. 

Lemma h2c_wt : forall h t1 t2,
    hc_wt h (t1 ⇒ t2) -> s_wt (h2c_help h t1 t2) (t1 ⇒ t2).
Proof.
  introv wt.
  apply (h2c_wt_n (1 + [|h|])).
  max_tac. 
  assumption.
Qed. 


Lemma c2h_wt_n : forall n c t1 t2,
    [|c|] < n ->
    s_wt c (t1 ⇒ t2) -> hc_wt (c2h_help c t1 t2) (t1 ⇒ t2).
Proof.
  unfold s_wt.
  induction n.
  - intuition.
  - introv bnd wt.
    inverts wt.
    all:
      repeat
        match goal with
        | H: se_inj_coercion _ _ |- _ => inverts H
        | H: se_med_coercion _ _ |- _ => inverts H
        end.
    all:
      repeat
        match goal with
        | H: se_coercion _ _ |- _ =>
          apply IHn in H; [idtac | max_tac]
        end.
    all: simpl; eauto.
    Unshelve.
    all: constructor.
Qed. 

Lemma c2h_wt : forall c t1 t2,
    s_wt c (t1 ⇒ t2) -> hc_wt (c2h_help c t1 t2) (t1 ⇒ t2).
Proof.
  intuition.
  apply (c2h_wt_n (1 + [|c|])).
  max_tac.
  assumption.
Qed. 

Definition h2c' {t1 t2} (h : {h : hc | hc_wt h (t1 ⇒ t2)})
  : {c : crcn | s_wt c (t1 ⇒ t2)} :=
  exist _ (h2c_help (proj1_sig h) t1 t2)
          (h2c_wt (proj1_sig h) t1 t2 (proj2_sig h)).

Definition c2h' {t1 t2} (c : {c : crcn | s_wt c (t1 ⇒ t2)})
  : {h : hc | hc_wt h (t1 ⇒ t2)} :=
  exist _ (c2h_help (proj1_sig c) t1 t2)
          (c2h_wt (proj1_sig c) t1 t2 (proj2_sig c)).
Hint Unfold h2c' c2h'.


Lemma sigma_eq_wt : forall A c c' t1 t2,
    forall (R : A -> cty -> Prop) f g,
      c = c' -> 
      exist (fun c => R c (t1 ⇒ t2)) c  f
      =
      exist (fun c => R c (t1 ⇒ t2)) c' g. 
Proof. 
  intros. 
  subst. 
  f_equal. 
  apply proof_irrelevance. 
Qed. 

Theorem hc_iso' : forall t1 t2, Bijective (@h2c' t1 t2). 
Proof.
  unfold Bijective. 
  intros. 
  exists (@c2h' t1 t2). 
  split. 
  - intros [h hwt]. 
    autounfold.
    simpl.
    assert (h'  : hc_wt h (t1 ⇒ t2)) by assumption.
    apply h2c_help_lemma in h'.
    apply sigma_eq_wt.
    assumption. 
  - intros [c cwt]. 
    autounfold.
    simpl.
    assert (c' : s_wt c (t1 ⇒ t2)) by assumption.
    apply c2h_help_lemma in c'.
    apply sigma_eq_wt.
    assumption. 
Qed.     

Lemma mk_c_lemma : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn ->
    (t1 !# t2 
     /\ 
     (exists m, 
         make_se_coercion (t1, t2, l) m
         /\
         se_med_coercion m (t1 ⇒ t2)
         /\
         c_depth  m <= max [|t1|] [|t2|]))
    \/ 
    (t1 # t2 /\ (make_se_coercion (t1, t2, l) (Failc t1 l t2))).
Admitted. 


 
Inductive compose_s : coercion * coercion -> coercion -> Prop :=
| Comp_Inj_Prj : forall t g l s1 s2 s3 s4 s5 t1 t2,
    make_se_coercion (t, g, l) s3 ->
    se_med_coercion s1 (t1 ⇒ t2) ->
    compose_s (s3, s2) s4 -> 
    compose_s (s1, s4) s5 -> 
    compose_s (s1 ;c Injc t, Prjc t l ;c s2) s5
| Comp_Arr   : forall c1 c2 c3 c4 c5 c6,
    compose_s (c3, c1) c5 ->
    compose_s (c2, c4) c6 ->
    compose_s (c1 →c c2, c3 →c c4) (c5 →c c6)
| Comp_Ref   : forall c1 c2 c3 c4 c5 c6,
    compose_s (c3, c1) c5 ->
    compose_s (c2, c4) c6 ->
    compose_s (Refc c1 c2, Refc c3 c4) (Refc c5 c6)
| Compose_Seq_c_L : forall s1 s2 s3 t l,
    compose_s (s1, s2) s3 -> 
    compose_s (Prjc t l ;c s1, s2) (Prjc t l ;c s3)
| Compose_Seq_c_R : forall t1 t2 t3 t4 s1 s2 s3 t,
    se_med_coercion s1 (t1 ⇒ t2) ->
    se_med_coercion s2 (t3 ⇒ t4) ->
    compose_s (s1, s2) s3 ->
    compose_s (s1, s2 ;c Injc t) (s3 ;c Injc t)
| Compose_Id_L : forall t c,
    compose_s (ιc t, c) c
| Compose_Id_R : forall t c,
    compose_s (c, ιc t) c
| Compose_Fail_R : forall s1 t1 t2 t l g,
    se_med_coercion s1 (t1 ⇒ t2) ->
    compose_s (s1, Failc t l g) (Failc t l g)
| Compose_Fail_L    : forall t g l s,
    compose_s (Failc t l g, s) (Failc t l g).

Hint Constructors compose_s.


Lemma h2c_respects_compose' : forall h1 h2 h3 c1 c2 c3 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    h2c_help h1 t1 t2 = c1 -> 
    h2c_help h2 t2 t3 = c2 -> 
    h2c_help h3 t1 t3 = c3 -> 
    compose_hc (h1, h2) h3 ->
    compose_s (c1, c2) c3.
  Proof. 
    intros h1 h2.
    match goal with
    | |- ?g =>
      assert (H: forall n, [|h1|] < n -> [|h2|] < n -> g)
    end.
    { intros n. gen h1 h2.
      induction n.
      - intuition.
      - introv b1 b2 w1 w2 e1 e2 e3 cp.
        inverts w1; inverts w2; inverts cp. 
        all: tc_tac; simpl in *.
        all:
          repeat
            match goal with
            | H: compose_hc_m _ _ |- _ => inverts H
            end.
        Ltac rem_c h :=
          match goal with
          | |- context[h2c_help h ?t1 ?t2] =>
            remember (h2c_help h t1 t2)
          end.
        all: subst; eauto.
(*        all:
          repeat
            match goal with
            | |- context[h2c_help ?h ?t1 ?t2] =>
              remember (h2c_help h t1 t2)
            end.
        constructor. 
            match goal with
            | H: compose_hc (?h1, ?h2) ?h3 |- _ =>
              rem_c h1; rem_c h2; rem_c h3;
                eapply IHn in H;
                [idtac
                |contains_tac;solve[max_tac]
                |contains_tac;solve[max_tac]
                |solve[eauto] ..]
            end.
            all: subst; eauto. 
            all: 
          repeat match goal with
                 | H: compose_hc (?h1, ?h2) ?h3 |- _ =>
                   rem_c h1; rem_c h2; rem_c h3;
                     eapply IHn in H;
                     [idtac
                     |contains_tac;solve[max_tac]
                     |contains_tac;solve[max_tac]
                     |solve[eauto] ..]
                 end.
        all: subst; eauto. 
        Ltac mk_c_tac t2 t3 l := 
          match goal with
          | H1: t2 <> Dyn, H2: t3 <> Dyn |- _ =>
            let sc:=fresh in 
            let mkhc:=fresh in
            let m:=fresh in
            let sem:=fresh in
            let db:=fresh in 
            let wt:=fresh in
            destruct (mk_c_lemma t2 t3 l H1 H2) as
                [[sc [m [mkhc [sem db]]]]|[sc mkhc]]
          end.
        constructor. 
        subst. 
        subst. constructor. inverts H18.
        autounfold.
        
        try match goal with
            | |- context[compose_c (_ ;c Injc ?t2, Prjc ?t3 ?l ;c _) _] =>
              mk_c_tac t2 t3 l
            | |- context[compose_c (_ ;c (_ ;c Injc ?t2), Prjc ?t3 ?l ;c _) _] =>
              mk_c_tac t2 t3 l
            end.
        


        mk_hc_tac' t5 t3. 
*)
Admitted. 

Theorem h2c_respects_compose : forall t1 t2 t3,
    forall (hwt1 : {h : hc   | hc_wt h (t1 ⇒ t2)})
           (hwt2 : {h : hc   | hc_wt h (t2 ⇒ t3)})
           (hwt3 : {h : hc   | hc_wt h (t1 ⇒ t3)})
           (cwt1 : {c : crcn |  s_wt c (t1 ⇒ t2)})
           (cwt2 : {c : crcn |  s_wt c (t2 ⇒ t3)})
           (cwt3 : {c : crcn |  s_wt c (t1 ⇒ t3)}),
      cwt1 = h2c' hwt1 -> cwt2 = h2c' hwt2 -> cwt3 = h2c' hwt3 -> 
      compose_hc (proj1_sig hwt1, proj1_sig hwt2) (proj1_sig hwt3) ->
      compose_s  (proj1_sig cwt1, proj1_sig cwt2) (proj1_sig cwt3).
Proof.
  introv e1 e2 e3 cp.
  eapply (h2c_respects_compose'  _ _ (proj1_sig hwt3)
                                _ _ _ _ _ _ (proj2_sig hwt1) (proj2_sig hwt2)).
  - unfold h2c' in e1. subst. simpl. congruence. 
  - unfold h2c' in e2. subst. simpl. congruence.
  - unfold h2c' in e3. subst. simpl. congruence. 
  - exact cp. 
Qed. 

