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
SearchAbout "Bijective".

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
                    apply IHn in H; [rewrite H | contains_tac]
                  end.
      all: congruence.
    + inverts H3. 
      all: destruct l0 as [[I1 l] I2].
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

Lemma c2h_lemma' : forall n c t1 t2,
    [| c |] < n -> 
    se_coercion c (t1 ⇒ t2) -> 
    h2c (c2h (c, t1, t2)) = (c, t1, t2).
Admitted. 

Lemma c2h_lemma : forall c t1 t2,
    se_coercion c (t1 ⇒ t2) -> 
    h2c (c2h (c, t1, t2)) = (c, t1, t2).  
Proof.
  intros.
  apply (c2h_lemma' (1 + [|c|])).
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
