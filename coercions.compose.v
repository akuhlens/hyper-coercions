Require Import Coq.Init.Datatypes.
Require Import LibTactics.
Require Export General.
Require Import GTypes.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import coercions.
Open Scope depth_scope.



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
         | |- context[max ?m ?n] => spec_max_with_guard m n
         | H: context[max ?m ?n] |- _ => spec_max_with_guard m n
         | |- context[match ?t with _ => _ end] =>
           match goal with
           | |- ?g => destruct t
           end
         end.
Ltac ineq_tac := solve[eauto 7] || solve[omega_max] || unfold depth in *; cbn in *; omega_max.


Inductive se_int : coercion -> Prop :=
| se_int_Id  : forall t, se_int (ιc t)
| se_int_Arr : forall c1 c2, se_int (c1 →c c2)
| se_int_Ref : forall c1 c2, se_int (c1 #c c2).

Hint Constructors se_int.

Inductive  compose_se : coercion * coercion -> coercion -> Prop :=
| Comp_Se_Inj_Prj : forall g t' t l i i' m c,
    make_se_coercion (t, t', l) m ->
    compose_se (g, m) i' ->
    compose_se (i', i) c ->
    compose_se (Seq_c g (Inj_c t), Seq_c (Prj_c t' l) i) c
| Comp_Se_Arr   : forall c1 c2 c3 c4 c5 c6,
    compose_se (c3, c1) c5 ->
    compose_se (c2, c4) c6 ->
    compose_se (c1 →c c2, c3 →c c4) (c5 →c c6)
| Comp_Se_Ref_c   : forall c1 c2 c3 c4 c5 c6,
    compose_se (c3, c1) c5 ->
    compose_se (c2, c4) c6 ->
    compose_se (Ref_c c1 c2, Ref_c c3 c4) (Ref_c c5 c6)
| Comp_Se_Assoc_L : forall t l g c c',
    compose_se (g , c) c' ->
    compose_se ((Prj_c t l);c g, c) ((Prj_c t l);c c')
| Comp_Se_Assoc_R : forall g1 g2 t g3 t1 t2,
    se_med_coercion g1 (t1 ⇒ t2) ->
    compose_se (g1 , g2) g3 ->
    compose_se (g1 , g2 ;c (Inj_c t)) (g3 ;c (Inj_c t))
(* | Comp_Se_Prj : forall t l i t'' s c,
   se_inj_coercion i (t  ⇒ t'') ->
   compose_se (i, s) c ->
   compose_se (Seq_c (Prj_c t l) i, s) (Seq_c (Prj_c t l) c) *)
(* | Comp_Se_Inj : forall g g' t t' t'' c,
   se_inj_coercion g (t ⇒ t') ->
   se_inj_coercion g' (t' ⇒ Dyn) ->
   compose_se (g, g') c ->
   compose_se (g, Seq_c g' (Inj_c t'')) (Seq_c c (Inj_c t'')) *)
| Comp_Se_Id_L : forall t c,
    compose_se (Id_c t, c) c
| Comp_Se_Id_R : forall t c,
    compose_se (c, Id_c t) c
(* Consider compose (Prj t l; (g ;c (Inj t)), ⊥ l') (Prj t l; ⊥ l') *)
(* This example is not well typed  ⊥ l  : t1 => t2 where t1 <> dyn *)
| Compose_Fail_c_R : forall g l t1 t2 t3,
    se_med_coercion g (t1 ⇒ t2) ->
    compose_se (g, Fail_c t2 l t3) (Fail_c t1 l t3)
| Compose_Fail_c_L : forall c l t1 t2 t3,
    se_coercion c (t2 ⇒ t3) ->
    compose_se (Fail_c t1 l t2, c) (Fail_c t1 l t3).

Hint Constructors compose_se.


Inductive subc : coercion -> coercion -> Prop :=
| sc_med_arr1 {c1 c2}: subc c1 (c1 →c c2)
| sc_med_arr2 {c1 c2}: subc c2 (c1 →c c2)
| sc_med_ref1 {c1 c2}: subc c1 (c1 #c c2)
| sc_med_ref2 {c1 c2}: subc c2 (c1 #c c2)
| sc_med_subp {t l i c}: subc c i -> subc c (Prj_c t l ;c i)
| sc_med_subi {t m c}: subc c m -> subc c (m ;c Inj_c t).

Hint Constructors subc.

Inductive subt : ty -> coercion -> Prop :=
| st_prj1 {t l i} : subt t (Prj_c t l ;c i)
| st_prj2 {t' t l i}: subt t' i -> subt t' (Prj_c t l ;c i)
| st_inj1 {t m}: subt t (m ;c Inj_c t)
| st_inj2 {t' t m}: subt t' m -> subt t' (m ;c Inj_c t)
| st_fail1 {t g l}: subt t (Fail_c t l g)
| st_fail2 {t g l}: subt g (Fail_c t l g).

Lemma subc_lt_depth : forall c1 c2 cty, se_coercion c1 cty -> subc c2 c1 -> crcn_depth c2 < crcn_depth c1.
Proof.
  induction c1.
  all: intros c2 cty H1 H2.
  all: inverts H1; inverts H2.
  all: repeat match goal with
              | h: se_inj_coercion _ _ |- _ => inverts h
              | h: se_med_coercion _ _ |- _ => inverts h
              | h: subc _ _ |- _ => inverts h
              end.
  all: try solve [ineq_tac].
Qed.


Lemma subc_le_depth : forall n c1 c2 cty,
    crcn_depth c1 <= S n -> subc c2 c1 ->
    se_coercion c1 cty ->
    crcn_depth c2  <= n.
Proof.
  intros n c1 c2 cty H1 H2 H3.
  apply (subc_lt_depth _ _ _ H3) in H2.
  omega.
Qed.

Hint Resolve subc_lt_depth subc_le_depth.

Lemma le_depth_prj_eq : forall t l1 l2 i1 i2 cty1 cty2,
    crcn_depth i1 <= crcn_depth i2 ->
    se_coercion i1 cty1 ->
    se_coercion i2 cty2 ->
    crcn_depth (Prj_c t l1 ;c i1) <= crcn_depth (Prj_c t l2 ;c i2).
Proof. intuition. ineq_tac. Qed.

Lemma le_depth_inj_eq : forall t m1 m2 cty1 cty2,
    crcn_depth m1 <= crcn_depth  m2 ->
    se_coercion m1 cty1 ->
    se_coercion m2 cty2 ->
    crcn_depth (m1 ;c Inj_c t) <= crcn_depth (m2 ;c Inj_c t).
Proof. intuition. ineq_tac. Qed.

Hint Resolve le_depth_inj_eq le_depth_prj_eq.

Lemma le_depth_s_max_ty :forall s t1 t2,
    se_coercion s (t1 ⇒ t2) ->
    ty_depth t1 <= crcn_depth s  /\  ty_depth t2 <= crcn_depth s.
Proof. induction s; intros t1 t2 H.
       all: inverts H.
       all: splits.
       all: repeat match goal with
                   | H: se_inj_coercion _ _ |- _ => inverts H
                   | H: se_med_coercion _ _ |- _ => inverts H
                   end.
       all: repeat match goal with
                   | H: forall t1 t2, _ -> _ /\ _ |- _ =>
                     edestruct H; [solve [eauto] | idtac]; clear H
                   |H: _ /\ _ |- _ => destruct H
                   end.
       all: try solve[ineq_tac].
Qed.

Lemma le_depth_s_t1 :forall s t1 t2, se_coercion s (t1 ⇒ t2) -> ty_depth t1 <= crcn_depth s.
Proof. intuition. edestruct le_depth_s_max_ty. eassumption. auto. Qed.
Lemma le_depth_s_t2 :forall s t1 t2, se_coercion s (t1 ⇒ t2) -> ty_depth t2  <= crcn_depth s.
Proof. intuition. edestruct le_depth_s_max_ty. eassumption. auto. Qed.

Hint Resolve le_depth_s_t1 le_depth_s_t2.

Lemma le_depth_prj_eq_max : forall t l i1 i2 c2 t1 t2 t3,
    crcn_depth i1 <= crcn_depth i2 ->
    crcn_depth i1 <= crcn_depth c2 ->
    se_coercion (Prj_c t l ;c i1) (t1 ⇒ t3) ->
    se_coercion (Prj_c t l ;c i2) (t1 ⇒ t2) ->
    se_coercion c2 (t2 ⇒ t3) ->
    crcn_depth (Prj_c t l ;c i1) <= max (crcn_depth (Prj_c t l ;c i2)) (crcn_depth c2).
Proof. intuition. induction i2; ineq_tac. Qed.

Hint Resolve le_depth_prj_eq_max.

Lemma le_depth_inj_eq_max : forall m1 m2 t3 c t1,
    crcn_depth m1 <= crcn_depth m2 ->
    crcn_depth m1 <= crcn_depth c  ->
    se_coercion (m1 ;c Inj_c t3) (t3 ⇒ Dyn) ->
    se_coercion (m2 ;c Inj_c t3) (t3 ⇒ Dyn) ->
    se_coercion c (t1 ⇒ t3) ->
    crcn_depth (m1 ;c Inj_c t3) <= max (crcn_depth c) (crcn_depth (m2 ;c Inj_c t3)).
Proof. intuition. induction m2; ineq_tac. Qed.

Hint Resolve le_depth_prj_eq_max.

Lemma depth_med_eq_t1_t2 : forall c t1 t2,
    se_med_coercion c (t1 ⇒ t2) -> (crcn_depth c) = max (ty_depth t1) (ty_depth t2).
Proof. induction c; intros t1 t2 H; inverts H. 
       all: repeat match goal with
                     | H: se_coercion _ _ |- _ => inverts H
                     | H: se_inj_coercion _ _ |- _ => inverts H
                     | H: se_med_coercion _ _, IH: forall t1 t2, _ |- _ => apply IH in H
                   end.
       - ineq_tac. 
       - reflexivity. 
       - simpl in *. 
all: try solve[ineq_tac]. 
       
ineq_tac. 
       

Lemma compose_se_wt : forall n c1 c2 t1 t2 t3,
    [| c1 |] <= n ->
    [| c2 |] <= n ->
    se_coercion c1 (t1 ⇒ t2) ->
    se_coercion c2 (t2 ⇒ t3) ->
    exists c3, compose_se (c1, c2) c3 /\
               se_coercion c3 (t1 ⇒ t3) /\
               [| c3 |] <= max [| c1 |] [| c2 |].
Proof.
  Ltac reconstruct :=
    solve[repeat match goal with
                 | H: _ <> _ |- _ => solve [contradiction H; eauto]
                 | _ =>
                   eexists;
                   split;
                   [solve [eauto 7]
                   | split;
                     [ solve [eauto 7]
                     | solve[ineq_tac]]]
                 end].
  induction n.
  Ltac mk_se_tac t1 t2 l :=
    match goal with
    | H: make_se_coercion (t1, t2, l) _ |- _ => fail 1
    | _ => let x:= fresh  in
           destruct (make_se_coercion_total t1 t2 l) as [x []]
    end.
  Ltac mk_se_tac' :=
    match goal with
    | |- context[compose_se (_ ;c (_ ;c Inj_c ?t), Prj_c ?g ?l ;c _) _] =>
      mk_se_tac t g l
    | |- context[compose_se (_ ;c Inj_c ?t, Prj_c ?g ?l ;c _) _] =>
      mk_se_tac t g l
    end;
    match goal with
    | H: make_se_coercion _ ?c |- _ => inverts keep H
    end;
    repeat
      match goal with
      | H: make_se_coercion _ ?c |- _ =>
        match goal with
        | H: se_coercion c _ |- _ => fail 1
        | _ => let h:=fresh in
               apply make_se_coercion_wt in H as h
        end
      end.
  Ltac IH_tac c1 c2 :=
    match goal with
    | IH: forall c3 c4, _ |- _ =>
      edestruct (IH c1 c2);
      [idtac c1 c2 | idtac | solve[eauto] | solve[eauto] | idtac];
      [ineq_tac | ineq_tac | idtac];
      match goal with
      | H: compose_se _ _ /\ _ |- _ =>
        let P1:=fresh in
        let P2:=fresh in
        let P3:=fresh in
        destruct H as [P1 [P2 P3]]
      end
    end.
  Ltac IH_tac' :=
    repeat match goal with
           | H1: se_coercion ?c1 (_ ⇒ ?t),
                 H2: se_coercion ?c2 (?t ⇒ _)
             |- _ =>
             match goal with
             | H: compose_se (c1, c2) _ |- _ => fail 1
             | IH: forall c1 c2, _ |- _ => IH_tac c1 c2
             end
           end.


  - intuition. exfalso. eauto.
  - intros c1 c2 t1 t2 t3 b1 b2 wt1 wt2.
    inverts wt1; inverts wt2; eauto.
    + inverts H3; inverts H5. 
      * reconstruct. 
      * reconstruct. 
      * inverts H1. 
        ** reconstruct.
        ** exists. split. eauto 6. reconstruct. 
        ** 
    + inverts H3; inverts H5.
      * reconstruct.
      * reconstruct.
      * shelve. 
      * inverts H1; reconstruct. 
      * 
        ** reconstruct. 
        ** reconstruct. 
match goal with
           | |- context[max ?n ?m] => destruct (Max.max_spec n m) as [[iq eq]|[iq eq]]
           end; rewrite eq.
           ineq_tac.
           rapply le_depth_prj_eq.
           

           unfold depth in iq. simpl in iq.
           specialize N.max_lub_iff. intros iff. 
           assert
SearchAbout "max". 
           
           
ineq_tac. 
           ineq_tac. 
           ineq_tac. eauto.
           Check le_depth_s_t2.
           match goal with
           |
           apply le_depth_s_t1.
           ineq_tac.
           reconstruct.
           ++ reconstruct.

           * reconstruexists. split. eauto. split. eauto. ineq_tac.
             ineq_tac.
             ineq_tac.
             inverts H1.
             ineq_tac.
             ineq_tac.
             ineq_tac.
             eauto.


             ineq_tac. apply  eauto. eauto 8.
           * inverts H1. all: reconstruct.
           * inverts H5; inverts H1.
             ++ reconstruct.
             ++ reconstruct.
             ++ reconstruct.
             ++ reconstruct.
             ++ inverts H3.
                ** reconstruct.
                ** IH_tac c3 c1. IH_tac c2 c4. exists.  split. eauto. split. eauto.
                   simpl in *.
             ++ inverts H3.
                ** reconstruct.
                ** IH_tac c2 c4. IH_tac c3 c1. reconstruct.
             ++ reconstruct.
             ++ inverts H3.
                ** reconstruct.
                ** IH_tac c1 c3. IH_tac c4 c0. reconstruct.
             ++ inverts H3.
                ** reconstruct.
                ** IH_tac c3 c1. IH_tac c0 c4. reconstruct.
           + inverts H3.
             * reconstruct.
             * mk_se_tac'.
               ++ inverts H5; inverts H1.
                  ** reconstruct.
                  ** reconstruct.
                  ** reconstruct.
                  ** reconstruct.
                  ** inverts H8.
                     +++ reconstruct.
                     +++ IH_tac c2 c0. IH_tac c4 c3. reconstruct.
                  ** inverts H8.
                     +++ reconstruct.
                     +++ IH_tac c0 c2. IH_tac c3 c4. reconstruct.
                  ** reconstruct.
                  ** inverts H8.
                     +++ reconstruct.
                     +++ IH_tac c1 c0. IH_tac c3 c2. reconstruct.
                  ** inverts H8.
                     +++ reconstruct.
                     +++ IH_tac c0 c1. IH_tac c2 c3. reconstruct.
               ++ reconstruct.
               ++ inverts H1. reconstruct.
               ++ inverts H1; inverts H5.
                  ** reconstruct.
                  ** inverts H10.
                     +++ reconstruct.
                     +++ IH_tac c2 c4. IH_tac c3 c1. reconstruct.
                  ** inverts H10.
                     +++ reconstruct.
                     +++ IH_tac c2 c3. IH_tac c0 c1. reconstruct.
                  ** IH_tac c4 c2. IH_tac c1 c3. reconstruct.
                  ** inverts H10.
                     +++ IH_tac c4 c2. IH_tac c1 c3. reconstruct.
                     +++ IH_tac c1 c3. IH_tac c4 c2. IH_tac c5 x. IH_tac c6 x0.

                         exists. split. econstructor.  eauto. eauto.  split. eauto.
                         unfold depth in *. cbn in *. ineq_tac.

                         reconstruct. prj_inj_IH.  exists. split.  eauto. split. eauto. reconstruct.
                     +++(* I an not sure why prj_inj_IH didn't work here *)
                     +++

                       exists. split. econstructor. eauto. eauto.
                       reconstruct.
                       Ltac mk_se_tac'' :=
                         match goal with
                         | |- context[compose_se (_ ;c (_ ;c Inj_c ?t), Prj_c ?g ?l ;c _) _] =>
                           mk_se_tac t g l
                         | |- context[compose_se (_ ;c Inj_c ?t, Prj_c ?g ?l ;c _) _] =>
                           idtac t g; try mk_se_tac t g l
                         end;
                         match goal with
                         | H: make_se_coercion _ ?c |- _ => inverts keep H
                         end;
                         repeat
                           match goal with
                           | H: make_se_coercion _ ?c |- _ =>
                             match goal with
                             | H: se_coercion c _ |- _ => fail 1
                             | _ => let h:=fresh in
                                    apply make_se_coercion_wt in H as h
                             end
                           end.

                       mk_se_tac''. ** reconstruct. ++ reconstruct. * + ** eauto. exists. split. econstructor.  eauto. eauto. apply econstructor.  econstructor. eauto. reconstruct.
           + inverts H3.
             * reconstruct.
             * mk_se_tac'.
               ** inverts H1.
                  *** prj_inj_IH.
                      eexists. split. econstructor. econstructor.  econstructor. econstructor.
                      eauto. solve[eauto]. split. solve[eauto]. ineq_tac.


                      try reconstruct.

             (*           Lemma l1000 : forall n m p, max n m <= p -> n <= p /\ m <= p.
           Pr           oof. induction n; intros [] [] H; simpl in H; max_tac. Qed.
           Ltac l1000_ta     c :=
             repeat match goal with
                    | H: max _ _ <= _ |- _ => apply l1000 in H; destruct H
                    end.
              *)

             * mk_se_tac'.
               all:
                 match goal with
                 | H: se_med_coercion _ _ |- _ => inverts keep H
                 end.
               all: try reconstruct.
               prj_inj_IH.

               ** - all:
                      all: try reconstruct.
                    * mk_se_tac'.
                      all:
                        repeat match goal with
                               | H: se_med_coercion _ _ |- _ => inverts H
                               end.
                      all: try reconstruct.
                      all: prj_inj_IH.
                      all: try reconstruct.


                      eexists.
                      split.
                      econstructor.
                      econstructor.
                      eauto.
                      econstructor.
                      eauto.
                      econstructor.
                      econstructor.
                      econstructor.
                      eauto.
                      econstructor.
                      eauto. econstructor.
                      econstructor.
                      econstructor.
                      eauto. intuition.

                      reconstruct.
                      all: try solve[prj_inj_IH; reconstruct].

                      all:

                        all: try match goal with
                                 | H: _ <> _ |- _ =>
                                 end.
                      all: try reconstruct.



                      -- prj_inj_IH. reconstruct.
                      -- prj_inj_IH. reconstruct.
                    * mk_se_tac'.
                      inverts keep  H9.

                      inverts keep H2.
                      inverts keep H40;
                        inverts keep H41.
                      all: try reconstruct.
                      all: try match goal with
                               | H: _ <> _ |- _ => solve [contradiction H; congruence]
                               end.

                      exists.
                      split.
                      econstructor.
                      eauto.
                      econstructor.
                      eassumption.
                      econstructor.
                      inverts keep H17.
                      eauto.
                      eauto.
                      econstructor.
                      eauto.
                      eauto.
                      eauto.
                      econstructor.
                      auto.
                      econstructor.
                      eassumption.
                      econstructor.
                      eauto.
                      eauto.
                      eauto.
                      split.
                      eauto.
                      ineq_tac.
                      -- edestruct (IHn c0 c2);
                           [ineq_tac | ineq_tac | eauto | eauto | idtac].
                         eauto. destruct H11 as [P1 [P2 P3]].
                         edestruct (IHn c4 c2);
                           [ineq_tac | ineq_tac | eauto | eauto | idtac].
                         destruct H11 as [P4 [P5 P6]].

                         eexists.
                         split.
                         econstructor.
                         auto.
                         econstructor.
                         eassumption.
                         econstructor.
                         eauto.

                         eauto.
                         eauto.
                         split.
                         eauto.
                         ineq_tac.

                         ineq_tac.
                         ineq_tac.
                         eauto.
                         eauto.

                         eassumption.
                         eauto. jauto.
                         econstructor; eauto.
                         econstructor; eauto.
                         eauto.
                         econstructor; eauto.
                         apply
                           inverts keep H2.
                         inverts keep H9.
                         eauto.
                         split.
                         eauto.
                         ineq_tac.


                         unfold depth in *. simpl in *.
                         remember (Init.Nat.max (ty_deep t2) (ty_deep t5)).
                         SearchAbout "max".

                         omega.
                         omega.
                         omega.
                         omeLemma max_spec' : forall n m p, max n m = p ->
                                                            n < m /\ p = m \/ m <= n /\ p = n.
                         Proof. intros n m. destruct (Max.max_spec n m).
                                ineq_tac.
                                ineq_tac.
                                repeat match goal with
                                       | H: ?t = ?t |- _ => clear H
                                       end.
                                subst H14. rewrite H50 in * . clear H50.
                                ineq_tac.
                                ineq_tac.
                                omega.
                                destruct H13 as [[]|[]].
                                destruct H3.
                                destruct H13.
                                subst.
                                substs.
                                solve_ineq.

                                eauto.
                                inverts

                                  eauto. try solve [econstructor; eauto].
                                eauto
                                  eauto.
                                split.
                                eauto.
                                unfold depth in *.
                                simpl in *.
                                max_tac.
                                max_tac.
                                eexists; split;
                                  [eauto
                                  | split;
                                    [eauto
                                    | eauto; time solve[unfold depth in *; simpl in *; max_tac]]]eexists. split. eauto. split. eauto.
                                unfold depth in *. simpl in *. max_tac.


                                eauto.
                                eauto.


                                econstructor. eauto.
                                edestruct (IHn c1 x).
                                unfold depth in *.
                                simpl in *.
                                l1000_tac.

                                destruct H. max_tac.
                                apply l1000 in max_tac.
                                apply max_tac.
                                eauto. . eautodestruct .


                                eauto. eauto. split. eauto. eauto.
                                ++ eexists.

                                   Lemma compose_se_wt : forall n c1 c2 t1 t2 t3,
                                       [| c1 |] <= n ->
                                       [| c2 |] <= n ->
                                       se_coercion c1 (t1 ⇒ t2) ->
                                       se_coercion c2 (t2 ⇒ t3) ->
                                       exists c3, compose_se (c1, c2) c3 /\
                                                  se_coercion c3 (t1 ⇒ t3) /\
                                                  [| c3 |] <= max [| c1 |] [| c2 |].
                                   Proof. induction n.
                                          - intuition. exfalso. eauto.
                                          - intuition.
                                            inverts H1; inverts H2; eauto.
                                            + inverts keep H7; inverts keep H8; eauto 6.
                                              Ltac mk_se_tac t1 t2 l :=
                                                match goal with
                                                | H: make_se_coercion (t1, t2, l) _ |- _ => fail 1
                                                | _ => let x:= fresh  in
                                                       destruct (make_se_coercion_total t1 t2 l) as [x []]
                                                end.
                                              Ltac mk_se_tac' :=
                                                match goal with
                                                | |- context[compose_se (_ ;c (_ ;c Inj_c ?t), Prj_c ?g ?l ;c _) _] =>
                                                  mk_se_tac t g l
                                                end.
                                              Lemma l1000 : forall n m p, max n m <= p -> n <= p /\ m <= p.
                                              Proof. induction n; intros [] [] H; simpl in H; max_tac. Qed.
                                              Ltac l1000_tac :=
                                                repeat match goal with
                                                       | H: max _ _ <= _ |- _ => apply l1000 in H; destruct H
                                                       end.

                                              Ltac reconstruct :=
                                                solve [eexists; split; [eauto | split; [eauto | solve[ineq_tac]]]].
                                              * mk_se_tac'.
                                                match goal with
                                                | H: make_se_coercion _ ?c |- _ => inverts keep H
                                                end.

                                                all:
                                                  repeat
                                                    match goal with
                                                    | H: make_se_coercion _ ?c |- _ =>
                                                      match goal with
                                                      | H: se_coercion c _ |- _ => fail 1
                                                      | _ => let h:=fresh in
                                                             apply make_se_coercion_wt in H as h
                                                      end
                                                    end.
                                                all: try reconstruct.

                                                all: match goal with
                                                     | H: se_med_coercion _ _ |- _ => inverts keep H3
                                                     end.

                                                all: try match goal with
                                                         | H: _ <> _ |- _ =>  solve [contradiction H; eauto]
                                                         end.
                                                all: try reconstruct.

                                                -- edestruct (IHn c0 c3);
                                                     [ineq_tac | ineq_tac | eauto | eauto | idtac].
                                                   destruct H11 as [P1 [P2 P3]].
                                                   edestruct (IHn c4 c2);
                                                     [ineq_tac | ineq_tac | eauto | eauto | idtac].
                                                   destruct H11 as [P4 [P5 P6]].
                                                   exists.
                                                   split.
                                                   econstructor.
                                                   auto.
                                                   econstructor.
                                                   eassumption.
                                                   econstructor.
                                                   eauto.
                                                   eauto.
                                                   eauto.
                                                   split.
                                                   eauto.
                                                   ineq_tac.
                                                -- edestruct (IHn c0 c3);
                                                     [ineq_tac | ineq_tac | eauto | eauto | idtac].
                                                   destruct H11 as [P1 [P2 P3]].
                                                   edestruct (IHn c4 c2);
                                                     [ineq_tac | ineq_tac | eauto | eauto | idtac].
                                                   destruct H11 as [P4 [P5 P6]].

                                                   eexists.
                                                   split.
                                                   econstructor.
                                                   auto.
                                                   econstructor.
                                                   eassumption.
                                                   econstructor.
                                                   eauto.

                                                   eauto.
                                                   eauto.
                                                   split.
                                                   eauto.
                                                   ineq_tac.

                                                   ineq_tac.
                                                   ineq_tac.
                                                   eauto.
                                                   eauto.

                                                   eassumption.
                                                   eauto. jauto.
                                                   econstructor; eauto.
                                                   econstructor; eauto.
                                                   eauto.
                                                   econstructor; eauto.
                                                   apply
                                                     inverts keep H2.
                                                   inverts keep H9.
                                                   eauto.
                                                   split.
                                                   eauto.
                                                   ineq_tac.


                                                   unfold depth in *. simpl in *.
                                                   remember (Init.Nat.max (ty_deep t2) (ty_deep t5)).
                                                   SearchAbout "max".

                                                   omega.
                                                   omega.
                                                   omega.
                                                   omeLemma max_spec' : forall n m p, max n m = p ->
                                                                                      n < m /\ p = m \/ m <= n /\ p = n.
                                                   Proof. intros n m. destruct (Max.max_spec n m).
                                                          ineq_tac.
                                                          ineq_tac.
                                                          repeat match goal with
                                                                 | H: ?t = ?t |- _ => clear H
                                                                 end.
                                                          subst H14. rewrite H50 in * . clear H50.
                                                          ineq_tac.
                                                          ineq_tac.
                                                          omega.
                                                          destruct H13 as [[]|[]].
                                                          destruct H3.
                                                          destruct H13.
                                                          subst.
                                                          substs.
                                                          solve_ineq.

                                                          eauto.
                                                          inverts

                                                            eauto. try solve [econstructor; eauto].
                                                          eauto
                                                            eauto.
                                                          split.
                                                          eauto.
                                                          unfold depth in *.
                                                          simpl in *.
                                                          max_tac.
                                                          max_tac.
                                                          eexists; split;
                                                            [eauto
                                                            | split;
                                                              [eauto
                                                              | eauto; time solve[unfold depth in *; simpl in *; max_tac]]]eexists. split. eauto. split. eauto.
                                                          unfold depth in *. simpl in *. max_tac.


                                                          eauto.
                                                          eauto.


                                                          econstructor. eauto.
                                                          edestruct (IHn c1 x).
                                                          unfold depth in *.
                                                          simpl in *.
                                                          l1000_tac.

                                                          destruct H. max_tac.
                                                          apply l1000 in max_tac.
                                                          apply max_tac.
                                                          eauto. . eautodestruct .


                                                          eauto. eauto. split. eauto. eauto.
                                                          ++ eexists.