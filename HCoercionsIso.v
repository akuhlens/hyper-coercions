Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FinFun.
Require Import LibTactics. 
Require Import GTypes. 
Require Import coercions. 
Require Import HCoercions.
Require Import Omega. 
Require Import omega_max. 

SearchAbout "Bijection".




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



Fixpoint h2c (t : (hc * ty * ty)) : crcn :=
  match t with
  | (h, t1, t2) => 
    match h with 
    | (HC p t1 m t2 i) => 
      match p with
      | (prj l) => 
        match i with
        | inj => (Prjc t1 l ;c (m2c m t1 t2 ;c Injc t2))
        | inj_mt => (Prjc t1 l ;c m2c m t1 t2)
        end
      | prj_mt =>
        match i with
        | inj => (m2c m t1 t2) ;c Injc t2
        | inj_mt => (m2c m t1 t2)
        end
      end
    | (Fail p t1 l t2) => 
      match p with
      | (prj l) => (Prjc t1 l ;c (Failc t1 l t2))
      | prj_mt => (Failc t1 l t2)
      end
    end
  end
with m2c (m : hc_m) : crcn :=
       match (m, t1, t2) with
       | Arr_hc c1 c2, Arr t11 => (Arr_c (h2c_weak c1) (h2c_weak c2))
       | Ref_hc c1 c2 => (Refc (h2c_weak c1) (h2c_weak c2))
                           
       end.

Fixpoint inf_c (c : crcn) : (ty * ty) :=
  match c with
  | Prjc t1 l => (Dyn, t1)
  | Injc t2   => (t2, Dyn)
  | Id_c t1   => (t1,  t1)
  | c1 ;c c2  =>  
    let (t1, t2) := inf_c c1 in
    let (t3, t4) := inf_c c2 in
    (t1, t4)
  | (Arr_c c1 c2) => 
    let (t3, t1) := inf_c c1 in
    let (t2, t4) := inf_c c2 in
    (t1 → t2, t3 → t4)
  | Refc c1 c2 => 
    let (t2, t1) := inf_c c1 in
    (Ref t1, Ref t2)
  | Failc t1 l t2 =>  (t1, t2)
  end. 

Fixpoint c2h_weak (s : crcn) : hc :=
  match s with
    | (Prjc t1 l1) ;c i  =>
      match i with
      | g ;c (Injc t2) => 
        let (t1', t2') := inf_c g in
        let m := match g with
                 | (Arr_c s1 s2) => (Arr_hc (c2h_weak s1) (c2h_weak s2))
                 | (Refc s1 s2)  => (Ref_hc (c2h_weak s1) (c2h_weak s2))
                 | _ => Id_hc
                 end
        in HC (prj l1) t1' m t2' inj
      | Failc t1' l2 t2' =>
        Fail (prj l1) t1' l2 t2'
      | g => 
        let (t1', t2') := inf_c g in
        let m := match g with
                 | (Arr_c s1 s2) => (Arr_hc (c2h_weak s1) (c2h_weak s2))
                 | (Refc s1 s2)  => (Ref_hc (c2h_weak s1) (c2h_weak s2))
                 | _ => Id_hc
                 end
        in HC (prj l1) t1' m t2' inj_mt 
      end
    | i => 
      match i with 
      | g ;c (Injc t2) => 
        let (t1', t2') := inf_c g in
        let m := match g with
                 | (Arr_c s1 s2) => (Arr_hc (c2h_weak s1) (c2h_weak s2))
                 | (Refc s1 s2)  => (Ref_hc (c2h_weak s1) (c2h_weak s2))
                 | _ => Id_hc
                 end 
        in HC prj_mt t1' m t2' inj
      | Failc t1' l2 t2' =>
        Fail prj_mt t1' l2 t2'
      | g  => 
        let (t1', t2') := inf_c g in
        let m :=  match g with
                  | (Arr_c s1 s2) => (Arr_hc (c2h_weak s1) (c2h_weak s2))
                  | (Refc s1 s2)  => (Ref_hc (c2h_weak s1) (c2h_weak s2))
                  | _ => Id_hc
                  end 
        in HC prj_mt t1' m t2' inj_mt 
      end
  end.


Lemma  h2c_weak_wt' : forall n,
    (forall h t1 t2,
        hc_wt h (t1 ⇒ t2) ->
        hc_depth h < n -> 
        se_coercion (h2c_weak h) (t1 ⇒ t2))
    /\
    (forall m t1 t2, 
        hc_m_wt m (t1 ⇒ t2) -> 
        hc_m_depth m <= n ->
        se_med_coercion (m2c m t1 t2) (t1 ⇒ t2)).
Proof.
  assert (Hh :
            (forall n, 
                (forall m t1 t2, 
                    hc_m_wt m (t1 ⇒ t2) -> 
                    hc_m_depth m <= n ->
                    se_med_coercion (m2c m t1 t2) (t1 ⇒ t2)) ->
                (forall h t1 t2,
                    hc_wt h (t1 ⇒ t2) ->
                    hc_depth h < S n -> 
                    se_coercion (h2c_weak h) (t1 ⇒ t2)))).
  { introv Hm wt db. 
    inverts wt.
    + match goal with
      | H: hc_m_wt ?m _ |- _ => 
        assert (dbm : hc_m_depth m <= n); [eauto | idtac]
      end.
      inverts H1; inverts H4.
        all: simpl.
        all: eauto.
      + inverts H3. all: simpl. all: eauto. }
  assert (Hm :
            (forall n, 
                (forall m t1 t2, 
                    hc_m_wt m (t1 ⇒ t2) -> 
                    hc_m_depth m <= n ->
                    se_med_coercion (m2c m t1 t2) (t1 ⇒ t2)) ->
                (forall h t1 t2,
                    hc_wt h (t1 ⇒ t2) ->
                    1 + hc_depth h <= S n -> 
                    se_coercion (h2c_weak h) (t1 ⇒ t2)))).
  { eauto. }
  induction n. 
  - split. 
    + introv wt db. inverts db. 
    + introv wt db. 
      inverts wt.
      all: inverts db. 
      * simpl. eauto.
  - destruct IHn as [IHh IHm]. 
    split. 
    + apply Hh. assumption. 
    + introv wt db. 
      inverts wt.
      * eauto. 
      * simpl in *. eauto 6. (* apply Hm twice *)
      * simpl in *. eauto 6. (* and again *)
Qed. 
  

Lemma inf_c_wt : forall n c t1 t2,
    crcn_depth c < n ->
    se_coercion c (t1 ⇒ t2) ->
    (t1, t2) = inf_c c.
Proof.
  induction n. 
  all: introv db se.
  - inverts db. 
  - inverts se.
    all: try match goal with 
             | H: se_inj_coercion _ _ |- _ => inverts H
             end. 
    all: try match goal with
             | H: se_med_coercion _ _ |- _ => inverts H
             end.
    all: simpl.
    
 eauto. 


Lemma c2h_wt : 
  (forall n c t1 t2,
      se_coercion c (t1 ⇒ t2) ->
      crcn_depth c < n -> 
      hc_wt (c2h_weak c) (t1 ⇒ t2)).
Proof. 
  induction n.
  all: introv se db.
  all: inverts se. 
  all: try match goal with 
           | H: se_inj_coercion _ _ |- _ => inverts H
           end. 
  all: try match goal with
           | H: se_med_coercion _ _ |- _ => inverts H
           end.
  all: simpl; eauto. 
  

/\
    (forall m t1 t2, 
        hc_m_wt m (t1 ⇒ t2) -> 
        hc_m_depth m <= n ->
        se_med_coercion (m2c m t1 t2) (t1 ⇒ t2))


Lemma h2c_weak_wt : forall t1 t2 h, 
    hc_wt h (t1 ⇒ t2) -> se_coercion (h2c_weak h) (t1 ⇒ t2). 
Proof. introv wt. apply (h2c_weak_wt' (1 + hc_depth h)); eauto. Qed. 

Definition h2c {t1 t2} (h : {h : hc | hc_wt h (t1 ⇒ t2)}) :
  {c : crcn | se_coercion c (t1 ⇒ t2)} :=
  exist _ (h2c_weak (proj1_sig h)) (h2c_weak_wt t1 t2 (proj1_sig h) (proj2_sig h)) .

Lemma c2h_weak_wt : forall t1 t2 c,
    se_coercion c (t1 ⇒ t2) -> hc_wt (c2h_weak c) (t1 ⇒ t2). 
Admitted.

Definition c2h {t1 t2} (c : {c : crcn | se_coercion c (t1 ⇒ t2)}):
  {h : hc | hc_wt h (t1 ⇒ t2)} :=
  exist _ (c2h_weak (proj1_sig c)) (c2h_weak_wt t1 t2 (proj1_sig c) (proj2_sig c)).

Theorem h_isomorphic_c {t1 t2} : Bijective (@h2c t1 t2). 
Proof. 
  unfold Bijective. 
  exists  (@c2h t1 t2). 
  split. 
  - assert (H: forall n c, 
               hc_depth c < n ->
               forall (p : hc_wt c (t1 ⇒ t2)),
               c2h (h2c (exist _ c p)) = (exist _ c p)).
    { - induction n.
        + introv db. intros p. inverts db. 
        + introv db; intros p. 
          inverts keep p. 
          inverts H1; inverts H3; inverts H4. 
          * unfold h2c. unfold c2h.  simpl in *. destruct h; destruct h0; destruct h1. 
            simpl; eauto. 
        
    }
    + intros c. apply (P (1 + hc_depth c) c). 