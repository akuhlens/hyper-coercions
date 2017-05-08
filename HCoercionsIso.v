Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FinFun.
Require Import Coq.Logic.ProofIrrelevance.
Require Import LibTactics. 
Require Import General. 
Require Import Types. 
Require Import Coercions. 
Require Import HCoercions.
Require Import HCoercionsCompose. 
Require Import Omega. 
Require Import SolveMax.
Open Scope depth_scope. 


Lemma hc_wt_eq {c c' t1 t2} : 
  forall (p  : hc_wt c  (t1 ⇒ t2))
         (p' : hc_wt c' (t1 ⇒ t2)),
     p = p. 
Proof.
  intros. 
  apply proof_irrelevance.
Qed.


Lemma se_wt_eq {c c' t1 t2} : 
  forall (p  : se_wt c  (t1 ⇒ t2))
         (p' : se_wt c' (t1 ⇒ t2)),
     p = p. 
Proof.
  intros.
  apply proof_irrelevance.
Qed.

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
  | Id_c t => ty_depth t
  | Seq_c c1 c2 => max (c_depth c1) (c_depth c2)
  | Arr_c c1 c2 => 1 + max (c_depth c1) (c_depth c2)
  | Refc c1 c2 => 1 + max (c_depth c1) (c_depth c2)
  | Failc _ _ _ => 0
  end.

Instance c_deep : Deep crcn := c_depth.
Hint Unfold c_deep. 

Lemma c2h_help_lemma : forall c t1 t2,
    se_wt c (t1 ⇒ t2) -> 
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
               | H: se_wt _ _ |- _ =>
                 apply IHn in H; [rewrite H | max_tac]
               end.
      all: eauto.
  }
  apply (H (1 + [|c|])).
  max_tac. 
Qed.   

Lemma c2h_lemma : forall c t1 t2, se_wt c (t1 ⇒ t2) -> 
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
  (forall c t1 t2, se_wt c (t1 ⇒ t2) ->
      h2c (c2h (c, t1, t2)) = (c, t1, t2)).
Proof.
  split. 
  apply h2c_lemma.
  apply c2h_lemma.
Qed.

(*
Theorem hc_iso_help_respects_compose' : forall n h1 h2 h3 c1 c2 c3 t1 t2 t3,
    [| h1 |] < n ->
    [| h2 |] < n -> 
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    compose_hc (h1, h2) h3 ->
    h2c_help h1 t1 t2 = c1 ->
    h2c_help h2 t2 t3 = c2 ->
    h2c_help h3 t1 t3 = c3 ->
    compose_s (c1, c2) c3.
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
 *)
(*
Theorem hc_iso_respects_compose : forall h1 h2 h3 c1 c2 c3 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    compose_hc (h1, h2) h3 ->
    h2c (h1, t1, t2) = (c1, t1, t2) ->
    h2c (h2, t2, t3) = (c2, t2, t3) ->
    h2c (h3, t1, t3) = (c3, t1, t3) ->
    compose_s (c1, c2) c3.
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
*)

Lemma h2c_wt_n : forall n h t1 t2,
    [|h|] < n ->
    hc_wt h (t1 ⇒ t2) -> se_wt (h2c_help h t1 t2) (t1 ⇒ t2).
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
    hc_wt h (t1 ⇒ t2) -> se_wt (h2c_help h t1 t2) (t1 ⇒ t2).
Proof.
  introv wt.
  apply (h2c_wt_n (1 + [|h|])).
  max_tac. 
  assumption.
Qed. 


Lemma c2h_wt_n : forall n c t1 t2,
    [|c|] < n ->
    se_wt c (t1 ⇒ t2) -> hc_wt (c2h_help c t1 t2) (t1 ⇒ t2).
Proof.
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
        | H: se_wt _ _ |- _ =>
          apply IHn in H; [idtac | max_tac]
        end.
    all: simpl; eauto.
    Unshelve.
    all: constructor.
Qed. 

Lemma c2h_wt : forall c t1 t2,
    se_wt c (t1 ⇒ t2) -> hc_wt (c2h_help c t1 t2) (t1 ⇒ t2).
Proof.
  intuition.
  apply (c2h_wt_n (1 + [|c|])).
  max_tac.
  assumption.
Qed. 

Definition h2c' {t1 t2} (h : {h : hc | hc_wt h (t1 ⇒ t2)})
  : {c : crcn | se_wt c (t1 ⇒ t2)} :=
  exist _ (h2c_help (proj1_sig h) t1 t2)
          (h2c_wt (proj1_sig h) t1 t2 (proj2_sig h)).

Definition c2h' {t1 t2} (c : {c : crcn | se_wt c (t1 ⇒ t2)})
  : {h : hc | hc_wt h (t1 ⇒ t2)} :=
  exist _ (c2h_help (proj1_sig c) t1 t2)
          (c2h_wt (proj1_sig c) t1 t2 (proj2_sig c)).
Hint Unfold h2c' c2h'.


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
    assert (c' : se_wt c (t1 ⇒ t2)) by assumption.
    apply c2h_help_lemma in c'.
    apply sigma_eq_wt.
    assumption. 
Qed.     

(*
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
*)


Lemma mk_hc_to_mk_s : forall t1 t2 l h,
    mk_hc (t1, t2, l) h ->
    make_se_coercion (t1, t2, l) (h2c_help h t1 t2). 
Proof.
  intros t1 t2.
  match goal with
  | |- ?g =>
    assert (H: forall n, [|t1|] < n -> [|t2|] < n -> g)
  end.
  {
    intros n. gen t1 t2. 
    induction n.
    - intuition. 
    - introv b1 b2 m.
      inverts m.
      all: simpl.
      all:
        repeat
          match goal with
          | H: mk_hc _ _ |- _ =>
            eapply IHn in H; [idtac | max_tac | max_tac ]
          end.
      all: eauto. 
  }
  apply (H (1 + [|t1|] + [|t2|])).
  all: max_tac.
Qed. 

(*
Lemma mk_s_depth : forall t1 t2 l h,
    make_se_coercion (t1, t2, l) (h2c_help h t1 t2) ->
    [|(h2c_help h t1 t2)|] <= max [|t1|] [|t2|].
Admitted. 
*)

Ltac clear_except H :=
  let H:=type of H in
  repeat match goal with
         | H': ?h |- _ =>
           match h with
           | H => fail 1
           | _ => clear H'
           end
         end.
Ltac clear_unrelated H :=
  repeat match goal with
         | H': ?h |- _ =>
           match h with
           | context[H] => fail 1
           | _ => clear H
           end
         end.
Lemma le_max3 : forall n0 n1 n2 n3,
    n0 <= max n1 (max n2 n3) ->
    n0 <= n1 \/ n0 <= n2 \/ n0 <= n3.
Proof.
  max_tac. 
Qed.
Ltac shortcut_max :=
  repeat
    match goal with
    | H: ?n0 <= max ?n1 (max ?n2 ?n3) |- _ => 
      let h1:=fresh in
      let h2:=fresh in
      eapply le_max3 in H;
      edestruct H as [h1 | [h1 | h1]];
      clear H
    | |- S _ <= S _ => apply le_S 
    | |- max ?c1 ?c2 <= _ => 
      eapply max_le_strategy;
      split
    end.

Lemma h2c_preserves_depth' : forall h t1 t2,
    hc_wt h (t1 ⇒ t2) ->
    [|h2c_help h t1 t2|] <= max [|h|] (max [|t1|] [|t2|]).
Proof.
  intros h.
  match goal with
  | |- ?g => assert (H: forall n, [|h|] < n -> g)
  end.
  { intros n. gen h. 
    induction n; intuition.
    inverts H0. 
    tc_tac.
    all: simpl in *.
    all: repeat
           match goal with
           | H: hc_wt ?c _ |- _ =>
             eapply (IHn c) in H; [idtac | max_tac | idtac ..]
           end.
    all: clear IHn; clear H.
    * max_tac. 
    * max_tac. 
    * max_tac. 
    * max_tac. 
    * autounfold in *; simpl in *. shortcut_max.
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      all: max_tac. 
    * autounfold in *; simpl in *. shortcut_max. 
      tc_tac. all: max_tac. 
    }
  eapply (H (1+[|h|])).
  eauto.
Qed.
   
Lemma h2c_preserves_depth : forall h t1 t2,
    hc_wt h (t1 ⇒ t2) -> [|h2c_help h t1 t2|] <= [|h|]. 
Proof.
  intros h.
  match goal with
  | |- ?g => assert (H: forall n, [|h|] < n -> g)
  end.
  { intros n. gen h. 
    induction n; intuition.
    inverts H0. 
    - tc_tac.
      all: repeat
             match goal with
             | H: hc_wt ?c _ |- _ =>
               eapply (IHn c) in H; [idtac | max_tac | idtac ..]
             end.
      all: try solve[autounfold; simpl in *; max_tac].
    - tc_tac.
      all: autounfold in *.
      all: simpl in *.
      all: max_tac. 
  }
  apply (H (1 + [|h|])).
  auto. 
Qed.

  (* In the next proof we commonly need to have a
   knowledge of the height of calls to h2c_help calls *)
(*
Ltac eq_h2c_help:=
  subst; autounfold in *; simpl in *; 
  repeat match goal with
         | |- context[h2c_help ?h ?t1 ?t2] =>
           idtac h; 
           let c:=fresh "c" in
           let e:=fresh "e" in
           remember (h2c_help h t1 t2) as c eqn:e;
           assert ([|h|] = [|c|]) by (eapply h2c_preserves_depth; eauto)
         | H: context[h2c_help ?h ?t1 ?t2] |- _ =>
           match goal with
           | H: _ = h2c_help h t1 t2 |- _ => fail 1
           | _ =>
             let c:=fresh "c" in
             let e:=fresh "e" in
             remember (h2c_help h t1 t2) as c eqn:e;
             assert ([|h|] = [|c|]) by (eapply h2c_preserves_depth; eauto)
           end
         end.
*)
Lemma L4 : forall h n c t8 t9 t4 t5,
    [|h|] = [|c|] ->
    (S (c_depth c) <= S (ty_depth t8)) \/
    (S (c_depth c) <= S (ty_depth t9)) \/
    (S (c_depth c) <= S (ty_depth t4)) \/
    (S (c_depth c) <= S (ty_depth t5)) ->
    S (S (ty_depth t8)) <= S n ->
    S (S (ty_depth t9)) <= S n -> 
    S (S (ty_depth t4)) <= S n ->
    S (S (ty_depth t5)) <= S n -> 
    S (hc_depth h) <= n. 
Proof.
  max_tac. 
Qed.


(*
Ltac clear_except H :=
  let H:=type of H in
  repeat match goal with
         | H': ?h |- _ =>
           match h with
           | H => fail 1
           | _ => clear H'
           end
         end. 
*)


Ltac one_will_do :=
  repeat
    match goal with
    | |- context[?n] =>
      match goal with
      | H: context[n] |- _ =>
        solve[clear_except H; max_tac]
      end
    end.

Inductive max_contains : nat -> nat -> Prop :=
| MC_here : forall n, max_contains n n
| MC_left : forall n l r,
    max_contains n l -> 
    max_contains n (max l r)
| MC_right : forall n l r,
    max_contains n r -> 
    max_contains n (max l r). 
Hint Constructors max_contains.       
Lemma L1 : forall c m,
    max_contains c m -> c <= m.
Proof.
  intros c m ct. induction ct. 
  - reflexivity. 
  - intuition.
  - intuition. 
Qed.
Hint Resolve L1. 
Lemma L2 : forall c m n,
    S (S m) <= S n -> max_contains c m -> S c <= n.
Proof.
  intros. inverts H0; intuition. 
  - assert (c <= l0). eauto. max_tac. 
  - assert (c <= r). eauto. max_tac. 
Qed.
Hint Resolve L2. 
Lemma L5 {c n}: forall h t1 t2 t3 t4,
          hc_contains_hc h c -> 
          ([|h|] <= S (ty_deep t1))
            \/
            ([|h|] <= S (ty_deep t2))
            \/
            ([|h|] <= S (ty_deep t3))
            \/
          ([|h|] <= S (ty_deep t4)) ->
          S (ty_deep t1) < S n ->
          S (ty_deep t2) < S n ->
          S (ty_deep t3) < S n ->
          S (ty_deep t4) < S n ->
          [|c|] < n.
        Proof.
          introv ct.
          assert ([|c|] < [|h|]). 
          eauto. 
          max_tac. 
        Qed.

Inductive hc_sub_ty : hc -> ty -> Prop :=
| hst_l {p l m r i} : hc_sub_ty (HC p l m r i) l
| hst_r {p l m r i} : hc_sub_ty (HC p l m r i) r
| hst_f {p l i} : hc_sub_ty (Fail p l i) l. 

Hint Constructors hc_sub_ty.

Lemma L6 : forall h t,
    hc_sub_ty h t -> [|t|] <= [|h|].
Proof.
  intros h t c. inverts c; max_tac. 
Qed.
Hint Resolve L6.

Lemma L8 : forall h1 h2,
    hc_contains_hc h1 h2 -> [|h2|] < [|h1|].
Proof.
  assert (forall n h1 h2,
             [|h2|] < n ->
             hc_contains_hc h1 h2 -> [|h2|] < [|h1|]).
  {  induction n; intuition. } 
  intros h1 h2. 
  apply (H (1 + [|h2|])).
  intuition.
Qed.

Hint Resolve L6 L8.

Lemma L7 {c2 n h1 h2 h3 t1 t2} :
  [|h1|] < S n ->
  [|h2|] < S n ->       
  [|h3|] <= max [|t1|] [|t2|] ->
  hc_sub_ty h1 t1 ->
  hc_sub_ty h2 t2 ->
  hc_contains_hc h3 c2 -> 
  [|c2|] < n.
Proof.
 intros. 
 assert ([|t1|] <= [|h1|]).
 eauto. 
 assert ([|t2|] <= [|h2|]).
 eauto. 
 assert ([|c2|] < [|h3|]).
 eauto. 
 max_tac. 
Qed.

Ltac bounds_tac :=
  match goal with
  | _ => assumption
  | _ => contains_tac
  | H: S (S ?m) <= S ?n |- S ?c <= ?n =>
    eapply (L2 _ _ _ H); [solve[eauto] ..]
  | H1: [|?h1|] < S ?n,
        H2: [|?h2|] < S ?n,
            H3: [|?h3|] <= max [|?t1|] [|?t2|]
    |- [|?c|] < ?n =>
    apply (L7 H1 H2 H3);
    [solve[eauto] ..]
  (* | H: _ <= S (max (max (ty_depth ?t8) (ty_depth ?t9)) *)
  (*                  (max (ty_depth ?t4) (ty_depth ?t5))) *)
  (*   |- _ =>  *)
  (*   try solve[eapply (L4 _ _ _ t8 t4 t9 t5); *)
  (*             [eauto | one_will_do ..]] *)
  (* | H: [|?h|] <= S (max (max (ty_deep ?t1) (ty_deep ?t2)) *)
  (*                       (max (ty_deep ?t3) (ty_deep ?t4))) *)
  (*   |- _ => *)
  (*   try solve[apply (L5 h t1 t2 t3 t4); *)
  (*             [idtac | one_will_do ..]] *)
  end.


(* Lemma h2c_respects_compose''' : forall h1 h2 h3 t1 t2 t3, *)
(*     hc_wt h1 (t1 ⇒ t2) -> *)
(*     hc_wt h2 (t2 ⇒ t3) -> *)
(*     compose_hc (h1, h2) h3 -> *)
(*     compose_s (h2c_help h1 t1 t2, *)
(*                h2c_help h2 t2 t3) *)
(*               (h2c_help h3 t1 t3). *)
(* Proof. *)
(*   assert (H: forall n h1 h2 h3 t1 t2 t3, *)
(*              hc_wt h1 (t1 ⇒ t2) -> *)
(*              hc_wt h2 (t2 ⇒ t3) -> *)
(*              compose_hc (h1, h2) h3 -> *)
(*              [|h1|] < n -> [|h2|] < n -> *)
(*              compose_s (h2c_help h1 t1 t2, *)
(*                         h2c_help h2 t2 t3) *)
(*                        (h2c_help h3 t1 t3)). *)
(*   { induction n. *)
(*     - intuition.  *)
(*     - introv hw1 hw2 cp b1 b2. *)
(*       (* assert (cw1 : se_wt (h2c_help h1 t1 t2) (t1 ⇒ t2)). *) *)
(*     (* { apply h2c_wt. assumption. } *) *)
(*     (* assert (cw2 : se_wt (h2c_help h2 t2 t3) (t2 ⇒ t3)). *) *)
(*     (* { apply h2c_wt. assumption. } *) *)
(*     (* assert (hwb3 : hc_wt h3 (t1 ⇒ t3) *) *)
(*     (*                /\ [|h3|] < S n ). *) *)
(*     (* {edestruct (compose_hc_total_deterministic_welltyped (S n) h1 h2) *) *)
(*     (*     as [h3' [cp' [fn [wt b3]]]]. *) *)
(*     (*   eauto.  *) *)
(*     (*   eauto.  *) *)
(*     (*   assumption. *) *)
(*     (*   assumption.  *) *)
(*     (*   rewrite <- (fn h3); [idtac | eauto]. *) *)
(*     (*   split; [assumption | max_tac]. } *) *)
(*     (* destruct hwb3 as [hw3 b3]. *) *)
(*     (* assert (cw3 : se_wt (h2c_help h3 t1 t3) (t1 ⇒ t3)). *) *)
(*     (* { subst. apply h2c_wt. assumption. }         *) *)
(*     (* split; [idtac | split; [exact cw3 | exact b3]]. *)  *)
(*     inverts cp; inverts hw1; inverts hw2. *)
(*     + tc_tac; simpl in *; eauto.  *)
(*     + tc_tac; simpl in *; eauto. *)
(*     + tc_tac; simpl in *; eauto. *)
(*       Ltac compose_h2c_tac := *)
(*       match goal with *)
(*       | IH: context[_ -> _],  *)
(*             H: compose_hc (?h1, ?h2) ?h3 *)
(*         |- ?g =>  *)
(*         (* Derive that h3 must be well-typed*) *)
(*         let h3':= fresh in *)
(*         let wt := fresh in *)
(*         let fn := fresh in *)
(*         let b := fresh in *)
(*         edestruct (compose_hc_total_deterministic_welltyped *)
(*                      (1 + [|h1|] + [|h2|]) h1 h2) as [h3' [_ [fn [wt b]]]]; *)
(*          [solve[eauto] *)
(*          |solve[eauto] *)
(*          |clear_except H; omega *)
(*          |clear_except H; omega *)
(*          |rewrite (fn h3) in wt; *)
(*           [idtac | exact H]]; *)
(*          clear fn; clear h3'; (* clean-up *) *)
(*            let H1:=fresh in *)
(*            let H2:=fresh in *)
(*            let H3:=fresh in *)
(*            eapply (IH h1 h2 h3 _ _ _) in H as [H1 [H2 H3]]; *)
(*              [idtac *)
(*              |solve[eauto] *)
(*              |solve[eauto] *)
(*              |solve[bounds_tac] *)
(*              |solve[bounds_tac] *)
(*              |idtac ..]  *)
(*       end. *)
(*             (*  *)
(*       Ltac compose_h2c_tac :=  *)
(*         match goal with *)
(*         | IHn: context[_ -> _],  *)
(*           H1: compose_hc (?h1, ?h2) ?h3 *)
(*           |- ?g => *)
(*           let H2:=fresh in *)
(*           let H3:=fresh in *)
(*           eapply (IHn h1 h2 h3 _ _ _) in H1 as [H1 [H2 H3]]; *)
(*           [idtac *)
(*           |solve[eauto] *)
(*           |solve[eauto] *)
(*           |solve[bounds_tac] *)
(*           |solve[bounds_tac] *)
(*           |idtac ..] *)
(*         end. *)  *)
(*       Ltac h2c_depth_tac := *)
(*         repeat *)
(*           match goal with *)
(*           | |- context[h2c_help ?h ?t1 ?t2] =>  *)
(*             match goal with *)
(*             | H: [|h|] = [|h2c_help h t1 t2|] |- _ => fail 1 *)
(*             | _ => *)
(*               assert ([|h|] = [|h2c_help h t1 t2|]) by *)
(*                   (solve[eapply h2c_preserves_depth; eauto]) *)
(*             end *)
(*           end. *)
      
(*       Ltac compose_h2c_m_tac := *)
(*         repeat match goal with *)
(*                | H: compose_hc_m _ _ |- _ => *)
(*                  inverts H *)
(*                end. *)
(*     + compose_h2c_m_tac. *)
(*       all: tc_tac; simpl in *. *)
(*       all: *)
(*         repeat *)
(*           match goal with *)
(*           | H: compose_hc (?h1, ?h2) ?h3 |- _ => *)
(*             eapply IHn in H; *)
(*               [idtac *)
(*               |eauto *)
(*               |eauto *)
(*               |bounds_tac *)
(*               |bounds_tac] *)
(*           end. *)
(*       all: eauto. *)
(*       Ltac h2c_mk_hc_tac := *)
(*         match goal with *)
(*         |H: mk_hc _ _ |- _ =>  *)
(*          let H':= fresh in  *)
(*          let H'':= fresh in *)
(*          inverts keep H; *)
(*          eapply mk_hc_to_mk_s in H as H''; *)
(*          (* apply mk_s_depth in H'' as H'; *) *)
(*          eapply mk_hc_depth in H *)
(*         |H: mk_hc _ (Fail _ _ _) |- _ => *)
(*          inverts keep H;  *)
(*          eapply mk_hc_to_mk_s in H *)
(*         end. *)
(*     + match goal with *)
(*       | B: _ < S ?n, *)
(*         H: mk_hc _ ?h |- _ => *)
(*         let H':= fresh in  *)
(*         let H'':= fresh in  *)
(*         eapply mk_hc_to_mk_s in H as H''; *)
(*         idtac *)
(*       end. *)
(*       match goal with *)
(*       | B: _ < S ?n, *)
(*         H: mk_hc  _ ?h |- _ => *)
(*         assert ([|h|] < S n) by *)
(*             (eapply mk_hc_depth in H; *)
(*             max_tac) *)
(*       end. *)
(*       inverts H4; *)
(*       inverts H6. *)
(*         try *)
(*           solve[ *)
(*             tc_tac; *)
(*             simpl in *; *)
(*             repeat *)
(*               match goal with *)
(*               | H: compose_hc (?h1, ?h2) ?h3 |- _ => *)
(*                 eapply IHn in H; *)
(*                 [idtac *)
(*                 |eauto *)
(*                 |eauto *)
(*                 |bounds_tac *)
(*                 |bounds_tac] *)
(*               end; *)
(*             eauto].  *)
(*       repeat *)
       
(*       all: eauto. *)
    
      
      
(*       (* apply mk_s_depth in H'' as H'; *) *)
          
        
      
(*       all: compose_h2c_m_tac.  *)
(*       all: tc_tac. *)
(*       Opaque depth. *)
(*       all: simpl in *.  *)
(*       Transparent depth.  *)
(*       all: h2c_depth_tac.  *)
(*       all: repeat compose_h2c_tac.  *)
(*       all: try solve[tc_tac; simpl in *; clear IHn; eauto 7]. *)
(*     + h2c_mk_hc_tac.                                 *)
(*       all: try solve[tc_tac; simpl in *; clear IHn;  eauto]. *)
(*     + all: try solve[tc_tac; simpl in *; clear IHn;  eauto]. *)
(*     + all: try solve[tc_tac; simpl in *; clear IHn;  eauto]. *)
(*     + all: try solve[tc_tac; simpl in *; clear IHn;  eauto]. *)
(*       Hint Resolve make_se_coercion_wt. *)
(*       Ltac hack_tac := *)
(*         let rec dtr m1 m2 := *)
(*             let cp:=fresh in *)
(*             let fn:=fresh in *)
(*             let wt:=fresh in *)
(*             let m3:=fresh in *)
(*             edestruct (compose_s_total_fun_wt m1 m2) *)
(*               as [m3 [cp [fn wt]]]; [eauto|eauto|idtac] *)
(*         in match goal with *)
(*            | H: make_se_coercion _ ?m2 |- compose_s (Prjc _ _ ;c (?m1 ;c _), _ ) _ => *)
(*              dtr m1 m2 *)
(*            | H: make_se_coercion _ ?m2 |- compose_s (?m1 ;c _, _ ) _ => *)
(*              dtr m1 m2 *)
(*            end. *)

(*     + h2c_mk_hc_tac. *)
(*       * all: try solve[tc_tac; simpl in *; clear IHn; eauto]. *)
(*       * tc_tac. *)
(*         all: simpl in *. *)
(*         all: inverts cw1; inverts cw2; inverts cw3; *)
(*           repeat *)
(*             match goal with *)
(*             | H: se_med_coercion _ _ |- _ => inverts H *)
(*             | H: se_inj_coercion _ _ |- _ => inverts H *)
(*             end. *)
(*         all: hack_tac. *)
(*         all: eauto. *)
(*         all: *)
(*           match goal with *)
(*           | H: se_wt _ _ |- _ => inverts H *)
(*           end; *)
(*           repeat *)
(*             match goal with *)
(*             | H: se_med_coercion _ _ |- _ => inverts H *)
(*             | H: se_inj_coercion _ _ |- _ => inverts H *)
(*             end. *)
(*         all: try match goal with *)
(*                  | H: compose_s _ (Failc _ _ _) |- _ => inverts H *)
(*                  end. *)
(*         all: try match goal with *)
(*                  | H: _ = _ |- _ => inverts H *)
(*                  end.  *)
(*         all: eauto. *)
(*       * tc_tac. *)
(*         all: simpl in *. *)
(*         all: inverts cw1; inverts cw2; inverts cw3; *)
(*           repeat *)
(*             match goal with *)
(*             | H: se_med_coercion _ _ |- _ => inverts H *)
(*             | H: se_inj_coercion _ _ |- _ => inverts H *)
(*             end. *)
(*         all: hack_tac. *)
(*         all: eauto. *)
(*         all: *)
(*           match goal with *)
(*           | H: se_wt _ _ |- _ => inverts H *)
(*           end; *)
(*           repeat *)
(*             match goal with *)
(*             | H: se_med_coercion _ _ |- _ => inverts H *)
(*             | H: se_inj_coercion _ _ |- _ => inverts H *)
(*             end. *)
(*         all: try match goal with *)
(*                  | H: compose_s _ (Failc _ _ _) |- _ => inverts H *)
(*                  end. *)
(*         all: try match goal with *)
(*                  | H: _ = _ |- _ => inverts H *)
(*                  end.  *)
(*         all: eauto 6. *)
(*     + h2c_mk_hc_tac. tc_tac; simpl in *;  eauto.  *)
(* Qed.       *)

Lemma h2c_respects_compose'' : forall n h1 h2 h3 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    compose_hc (h1, h2) h3 ->
    [|h1|] < n -> [|h2|] < n ->
    compose_s (h2c_help h1 t1 t2,
               h2c_help h2 t2 t3)
              (h2c_help h3 t1 t3)
    /\
    se_wt (h2c_help h3 t1 t3)
         (t1 ⇒ t3)
    /\
    [|h3|] < n.
Proof.
  induction n.
  - intuition. 
  - introv hw1 hw2 cp b1 b2.
    assert (cw1 : se_wt (h2c_help h1 t1 t2) (t1 ⇒ t2)).
    { apply h2c_wt. assumption. }
    assert (cw2 : se_wt (h2c_help h2 t2 t3) (t2 ⇒ t3)).
    { apply h2c_wt. assumption. }
    assert (hwb3 : hc_wt h3 (t1 ⇒ t3)
                   /\ [|h3|] < S n ).
    {edestruct (compose_hc_total_deterministic_welltyped (S n) h1 h2)
        as [h3' [cp' [fn [wt b3]]]].
      eauto. 
      eauto. 
      assumption.
      assumption. 
      rewrite <- (fn h3); [idtac | eauto].
      split; [assumption | max_tac]. }
    destruct hwb3 as [hw3 b3].
    assert (cw3 : se_wt (h2c_help h3 t1 t3) (t1 ⇒ t3)).
    { subst. apply h2c_wt. assumption. }        
    split; [idtac | split; [exact cw3 | exact b3]]. 
    inverts cp; inverts hw1; inverts hw2.
    + tc_tac; simpl in *; eauto. 
    + tc_tac; simpl in *; eauto.
    + tc_tac; simpl in *; eauto.
      Ltac compose_h2c_tac :=
      match goal with
      | IH: context[_ -> _], 
            H: compose_hc (?h1, ?h2) ?h3
        |- ?g => 
        (* Derive that h3 must be well-typed*)
        let h3':= fresh in
        let wt := fresh in
        let fn := fresh in

        edestruct (compose_hc_total_deterministic_welltyped
                    (1 + [|h1|] + [|h2|]) h1 h2) as [h3' [_ [fn [wt _]]]];
         [solve[eauto]
         |solve[eauto]
         |clear_except H; omega
         |clear_except H; omega
         |rewrite (fn h3) in wt;
          [idtac | exact H]];
         clear fn; clear h3'; (* clean-up *)
           let H1:=fresh in
           let H2:=fresh in
           let H3:=fresh in
           eapply (IH h1 h2 h3 _ _ _) in H as [H1 [H2 H3]];
             [idtac
             |solve[eauto]
             |solve[eauto]
             |solve[bounds_tac]
             |solve[bounds_tac]
             |idtac ..] 
      end.
      Ltac h2c_depth_tac :=
        repeat
          match goal with
          | |- context[h2c_help ?h ?t1 ?t2] => 
            match goal with
            | H: [|h|] = [|h2c_help h t1 t2|] |- _ => fail 1
            | _ =>
              assert ([|h|] = [|h2c_help h t1 t2|]) by
                  (solve[eapply h2c_preserves_depth; eauto])
            end
          end.
      Ltac compose_h2c_m_tac :=
        repeat match goal with
               | H: compose_hc_m _ _ |- _ =>
                 inverts H
               end.
    + compose_h2c_m_tac.
      all: tc_tac; simpl in *.
      all: h2c_depth_tac.
      all: repeat compose_h2c_tac.
      all: try solve[tc_tac; simpl in *; clear IHn; eauto].
      Ltac h2c_mk_hc_tac :=
        match goal with
        |H: mk_hc _ _ |- _ => 
         let H':= fresh in 
         let H'':= fresh in
         inverts keep H;
         eapply mk_hc_to_mk_s in H as H'';
         (* apply mk_s_depth in H'' as H'; *)
         eapply mk_hc_depth in H
        |H: mk_hc _ (Fail _ _ _) |- _ =>
         inverts keep H; 
         eapply mk_hc_to_mk_s in H
        end.
    + h2c_mk_hc_tac.
      all: compose_h2c_m_tac. 
      all: tc_tac.
      Opaque depth.
      all: simpl in *. 
      Transparent depth. 
      all: h2c_depth_tac. 
      all: repeat compose_h2c_tac. 
      all: try solve[tc_tac; simpl in *; clear IHn; eauto 7].
    + h2c_mk_hc_tac.                                
      all: try solve[tc_tac; simpl in *; clear IHn;  eauto].
    + all: try solve[tc_tac; simpl in *; clear IHn;  eauto].
    + all: try solve[tc_tac; simpl in *; clear IHn;  eauto].
    + all: try solve[tc_tac; simpl in *; clear IHn;  eauto].
    + h2c_mk_hc_tac.
      all: tc_tac. 
      all: simpl in *.
      all: inverts cw1; inverts cw2; inverts cw3;
        repeat
          match goal with
          | H: se_med_coercion _ _ |- _ => inverts H
          | H: se_inj_coercion _ _ |- _ => inverts H
          end.
      all: solve[eauto]. 
    + h2c_mk_hc_tac. tc_tac; simpl in *;  eauto. 
Qed.      

Lemma h2c_respects_compose' : forall h1 h2 h3 c1 c2 c3 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    h2c_help h1 t1 t2 = c1 -> 
    h2c_help h2 t2 t3 = c2 -> 
    h2c_help h3 t1 t3 = c3 -> 
    compose_hc (h1, h2) h3 ->
    compose_s (c1, c2) c3.
Proof.
  introv w1 w2 e1 e2 e3 cp. 
  edestruct (h2c_respects_compose'' (1 + [|h1|] + [|h2|]))
            as [cp' [wt' bnd']].
  exact w1. exact w2. exact cp.
  omega. omega. subst. eauto.
Qed.

Theorem h2c_respects_compose : forall t1 t2 t3,
    forall (hwt1 : {h : hc   | hc_wt h (t1 ⇒ t2)})
           (hwt2 : {h : hc   | hc_wt h (t2 ⇒ t3)})
           (hwt3 : {h : hc   | hc_wt h (t1 ⇒ t3)})
           (cwt1 : {c : crcn | se_wt c (t1 ⇒ t2)})
           (cwt2 : {c : crcn | se_wt c (t2 ⇒ t3)})
           (cwt3 : {c : crcn | se_wt c (t1 ⇒ t3)}),
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

