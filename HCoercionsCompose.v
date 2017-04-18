Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import GTypes.
Require Import coercions. 
Require Import Omega. 
Require Import omega_max.
Require Import HCoercions.

(* Well founded induction *)

Lemma mk_hc_depth : forall h t1 t2 l,
    mk_hc (t1, t2, l) h ->
    hc_depth h <= Init.Nat.max (ty_depth t1) (ty_depth t2).
Proof.
  intros h t1 t2 l H.
  destruct (mk_hc_total t1 t2 l) as [x [P1 P2]]. 
  apply (mk_hc_function _ _ _ _ _ P1) in H.
  subst.
  assumption. 
Qed.

Inductive hc_contains_ty : hc -> ty -> Prop :=
| hct1 {p t1 m t2 i}: hc_contains_ty (HC p t1 m t2 i) t1
| hct2 {p t1 m t2 i}: hc_contains_ty (HC p t1 m t2 i) t2
| hcf1 {p t1 t2 l} : hc_contains_ty (Fail p t1 l t2) t1
| hcf2 {p t1 t2 l} : hc_contains_ty (Fail p t1 l t2) t1
| sub {p t1 m t2 i h t}:
    hc_m_sub_hc m h ->
    hc_contains_ty h t -> 
    hc_contains_ty (HC p t1 m t2 i) t.
Hint Constructors hc_contains_ty. 

Lemma hc_contains_ty_depth': forall n c t,
    hc_depth c < n -> 
    hc_contains_ty c t ->
    ty_depth t <= hc_depth c. 
Proof. 
  induction n;
    intuition. 
  inverts H0. 
  - simpl in *. omega_max. 
  - simpl in *. omega_max. 
  - simpl in *. omega_max. 
  - simpl in *. omega_max. 
  - 
    match goal with
    | H: hc_depth ?c < S ?n, H2: hc_m_sub_hc ?m ?h |- _ =>
      let P:=fresh in 
      assert (P : hc_depth h < hc_depth c);
        [ solve [eauto] | idtac ..]
    end.
    apply IHn in H2 as H3. 
    ineq_tac. 
    ineq_tac. 
Qed.
Lemma hc_contains_ty_depth: forall c t,
    hc_contains_ty c t ->
    ty_depth t <= hc_depth c. 
Proof. intros;
         apply (hc_contains_ty_depth' (1 + hc_depth c)).
       eauto. 
       eauto. 
Qed. 

Lemma mk_hc_depth_help : forall n c1 c2 c3 t1 t2 l,
    hc_depth c1 < n ->
    hc_depth c2 < n ->
    hc_contains_ty c1 t1 -> 
    hc_contains_ty c2 t2 ->
    mk_hc (t1, t2, l) c3 ->            
    hc_depth c3 < n.
Proof. 
  intuition. 
  Check hc_contains_ty_depth. 
  apply hc_contains_ty_depth in H1. 
  apply hc_contains_ty_depth in H2.
  apply mk_hc_depth  in H3. 
  simpl in *; omega_max. 
Qed.

Ltac invert_initial_mediating_ty_judgements :=
  match goal with
  | m1: hc_m_wt _ _, m2: hc_m_wt _ _ |- _ => inverts keep m1; inverts keep m2
  | m1: hc_m_wt |- _ => inverts keep m1
  | _ => idtac
  end.

Lemma mk_hc_lemma : forall t1 t2 l,
    t1 <> Dyn -> t2 <> Dyn ->
    (t1 !# t2 
     /\ 
     (exists m, 
         mk_hc (t1, t2, l) (HC prj_mt t1 m t2 inj_mt)
         /\
         hc_depth  (HC prj_mt t1 m t2 inj_mt) <= Init.Nat.max (ty_depth t1) (ty_depth t2)))      
    \/ 
    (t1 # t2
     /\
     (mk_hc (t1, t2, l) (Fail prj_mt t1 l t2))).
Proof. 
  intros t1 t2 l nd1 nd2. 
  destruct (ty_shallow_consistency_dec t1 t2) as [c | c].
  - destruct (mk_hc_not_dyn_sconsist t1 t2 l nd1 nd2 c). 
    left. split. assumption. 
    eexists. split. 
    eassumption. 
    apply (mk_hc_depth _ _ _ l H).
  - eauto. 
Qed.

Lemma help_m_mk_hc : forall p t2 m t3 i l,
    mk_hc (t2, t3, l) (HC p t2 m t3 i) ->
    hc_m_depth m <= max (ty_depth t2) (ty_depth t3).
Proof.
  intuition. 
  apply mk_hc_depth in H. 
  simpl in *. omega_max. 
Qed. 
Lemma help_resolve_compose :
  forall t1 t2 t3 t4 p1 m1 i1 p2 m2 i2 m3 m4 m5 l,
    mk_hc (t2, t3, l) (HC prj_mt t2 m3 t3 inj_mt) ->
    hc_m_depth m4 <= max (hc_m_depth m1) (hc_m_depth m3) -> 
    hc_m_depth m5 <= max (hc_m_depth m4) (hc_m_depth m2) ->
    hc_depth (HC p1 t1 m5 t4 i2) <= 
    max (hc_depth (HC p1 t1 m1 t2 i1))
        (hc_depth (HC p2 t3 m2 t4 i2)).
Proof.
  intuition. 
  apply help_m_mk_hc in H. 
  simpl in *. omega_max. 
Qed.

Hint Resolve help_resolve_compose. 

Ltac IHm_tac m1 m2 m3 :=
  match goal with
  | IH: context[exists (m : hc_m), _] |- _ =>
    let total:=fresh "cmp" in
    let wt:=fresh "wt" in
    let bound:=fresh "db" in
    (edestruct (IH m1 m2) as [m3 [total [wt bound]]];
     [solve[try assumption; eauto]
     |solve[try assumption; eauto]
     |solve[try assumption; simpl in *; omega_max]
     |solve[try assumption; simpl in *; omega_max]
     | idtac ..])
  end.

Ltac reconstruct := 
  solve [eexists; split; 
         [> solve[eauto] 
         | split; 
           [> solve[let e:=fresh in
                    let h:=fresh in
                    intros e h;
                    inverts h; 
                    congruence]
           | split; 
             [> solve[eauto] 
             | try solve[eauto];
               try solve[simpl in *; omega_max];
               ineq_tac]]]]. 

Ltac tc_tac := 
  repeat match goal with
         | H: hc_m_wt _ _ |- _ => inverts H
         | H: hc_i_wt _ _ |- _ => inverts H
         | H: hc_p_wt _ _ |- _ => inverts H
         | _ => solve[contradiction; eauto]
         | _ => solve[discriminate]
         end.

Ltac tc_tac_full :=
  repeat match goal with
           | H: hc_wt _ _ |- _ =>
             inverts H
         end;
  tc_tac. 


Ltac determinism_tac :=
  repeat match goal with
         | H1: mk_hc (?t1, ?t2, _) _,
               H2: mk_hc (?t1, ?t2, _) _ |- _  => 
           apply (mk_hc_function _ _ _ _ _ H2) in H1;
           inverts H1
         | cfn: _ -> compose_hc_m (?c1, ?c2) _ -> ?c3 = _ |- _ =>
           match goal with
           | H1: compose_hc_m (c1, c2) c3,
                 H2: compose_hc_m (c1, c2) ?c4 |- _ =>
             apply cfn in H2;
             rewrite <- H2 in *
           end
         | cfn: _ -> compose_hc (?c1, ?c2) _ -> ?c3 = _ |- _ =>
           match goal with
           | H1: compose_hc (c1, c2) c3,
                 H2: compose_hc (c1, c2) ?c4 |- _ =>
             apply cfn in H2;
             rewrite <- H2 in *
           end
         end.



Lemma compose_total_reconstruct_help :
  forall n p1 t1 m5 t4 i2 m1 t2 i1 p2 t3 m2
         t1' t2' t3' t1'' t3'' p3 i3,
    (forall (m1 m2 : hc_m) (t1 t2 t3 : ty),
        hc_m_wt m1 (t1 ⇒ t2) ->
        hc_m_wt m2 (t2 ⇒ t3) ->
        hc_m_depth m1 <= n ->
        hc_m_depth m2 <= n ->
        exists m3 : hc_m,
          compose_hc_m (m1, m2) m3 /\
          (forall m3',
              compose_hc_m (m1, m2) m3' -> m3 = m3') /\
          hc_m_wt m3 (t1 ⇒ t3) /\
          hc_m_depth m3 <=
          Init.Nat.max (hc_m_depth m1) (hc_m_depth m2)) ->
    hc_wt (HC p1 t1 m1 t2 i1) (t1' ⇒ t2') ->
    hc_wt (HC p2 t3 m2 t4 i2) (t2' ⇒ t3') ->
    hc_depth (HC p1 t1 m1 t2 i1) < S n ->
    hc_depth (HC p2 t3 m2 t4 i2) < S n ->
    compose_hc (HC p1 t1 m1 t2 i1,
                HC p2 t3 m2 t4 i2)
               (HC p3 t1'' m5 t3'' i3) ->
    (forall h3', 
        compose_hc (HC p1 t1 m1 t2 i1, 
                    HC p2 t3 m2 t4 i2)
                   h3' ->
        (HC p3 t1'' m5 t3'' i3) = h3')
    /\
    hc_wt (HC p3 t1'' m5 t3'' i3) (t1' ⇒ t3')
    /\
    hc_depth (HC p3 t1'' m5 t3'' i3) <= 
    max (hc_depth (HC p1 t1 m1 t2 i1))
        (hc_depth (HC p2 t3 m2 t4 i2)).
Proof.
  introv IHm wt1 wt2 db1 db2 cmp12.
  inverts keep cmp12. 
  - split; [idtac | split; [idtac | idtac]].
    + introv cmp12'. 
      inverts cmp12'. 
      all: tc_tac_full. 
      all: try match goal with
               |H: compose_hc_m _ _ |- _ => inverts H
               end.
      all: subst; reflexivity. 
    + tc_tac_full.
      all: eauto.  
    + eauto. 
  - split; [idtac | split; [idtac | idtac]].
    + introv cmp12'. 
      inverts cmp12'.
      all: tc_tac_full.
      all: try match goal with
               | H: compose_hc_m _ _ |- _ => inverts H
               end.
      all: subst; reflexivity. 
    + tc_tac_full; eauto. 
    + eauto. 
  - inverts keep wt1; inverts keep wt2;
      edestruct (IHm m1 m2) as [m3 [cmp3 [cfn [wt3 db3]]]].
    eauto. 
    eauto. 
    clear IHm; simpl in *; omega_max. 
    clear IHm; simpl in *; omega_max. 
    split; [idtac | split; [idtac | idtac]].
    all: determinism_tac. 
    + introv cmp12'.
      inverts cmp12'.
      all: determinism_tac.  (* Inversion introduces more *)
      all: tc_tac_full.
      all: reflexivity. 
    + inverts H3; inverts H12; eauto.  
    + eauto. 
  - apply mk_hc_wt in H16 as H16wt. 
    apply mk_hc_depth in H16 as H16db. 
    inverts H16wt;
      inverts keep wt1;
      inverts keep wt2;
      edestruct (IHm m1 m4) as [m3 [cmp3 [cfn [wt3 db3]]]].
    eauto. 
    eauto. 
    clear IHm; simpl in *; omega_max. 
    clear IHm; simpl in *; omega_max. 
    edestruct (IHm m3 m2) as [m7 [cmp7 [cfn7 [wt7 db7]]]]. 
    eauto. 
    eauto. 
    clear IHm; simpl in *; omega_max. 
    clear IHm; simpl in *; omega_max.
    determinism_tac. 
    split; [idtac | split; [idtac | idtac]].
    + introv cmp12'.
      inverts cmp12'.
      all: determinism_tac. 
      all: congruence. 
    + eauto. 
    + eauto. 
      Unshelve. 
      all: assumption. 
Qed. 

Hint Resolve compose_total_reconstruct_help. 


Ltac mk_hc_tac :=
  let rec mk_hc_tac' t2 t3 l :=
      match goal with
      | H1: t2 <> Dyn, H2: t3 <> Dyn |- _ =>
        let sc:=fresh in 
        let mkhc:=fresh in
        let m:=fresh in
        let db:=fresh in 
        let wt:=fresh in
        destruct (mk_hc_lemma t2 t3 l H1 H2) as
            [[sc [m [mkhc db]]]|[sc mkhc]];
        apply (mk_hc_wt t2 t3 l) in mkhc as wt;
        inverts wt
      end
  in
    match goal with
    | |- context[compose_hc (HC _ _ _ ?t2 inj, HC (prj ?l) ?t3 _ _ _) _] =>
      mk_hc_tac' t2 t3 l
    | |- context[compose_hc (HC _ _ _ ?t2 inj, Fail (prj ?l) ?t3 _ _) _] =>
      mk_hc_tac' t2 t3 l
  end.
Ltac inner_ty_consist_dec_tac :=
  (*      let rec mk_hc_extra :=
            (match goal with
             | H: mk_hc (?t1, ?t2, ?l) ?h |- _ =>
               match goal with
               | H': hc_wt h _ |- _ => fail 1
               | _ => let P:=fresh in
                      apply mk_hc_wt in H as P
               end;
               match goal with
               | H': hc_depth h <= (max (ty_depth ?t1) (ty_depth ?t2)) |- _ => fail 1
               | _ => let P:=fresh in apply mk_hc_depth in H as P
               end
             end)
        in
        (* for merging inj;prj case on whether the types are shallow consistent *)
        let rec mk_hc_tac :=
            repeat match goal with
                   | l: blame_info, h: ?t1 !# ?t2 |- _ =>
                     match goal with
                     | H: mk_hc (t1, t2, l) _ |- _ => fail 1
                     | _ =>
                       inverts keep h;
                       try solve[try discriminate; try contradiction];
                       destruct (mk_hc_not_dyn_sconsist t1 t2 l);
                       [solve [eauto] | solve [eauto] | solve [eauto] | idtac ..];
                       mk_hc_extra
                     end
                   | l: blame_info, h: ?t1 # ?t2 |- _ =>
                     match goal with
                     | H: mk_hc (t1, t2, l) _ |- _ => fail 1
                     | _ => 
                       try solve[contradiction h; eauto];
                         destruct (mk_hc_not_dyn_sinconsist t1 t2 l);
                         [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..];
                         mk_hc_extra
                     end
                end
        in *)
        try match goal with
            | |- context[compose_hc (HC _ _ ?m1 ?t2 inj, HC (prj ?l) ?t3 ?m2 _) _] =>
              destruct (ty_shallow_consistency_dec t2 t3);
              mk_hc_tac
            | |- context[compose_hc (HC _ _ ?m1 ?t1 inj, Fail (prj ?l) ?t2 _ _) _] =>
              destruct (ty_shallow_consistency_dec t1 t2);
              mk_hc_tac
            end.

Lemma compose_correct_recontruct_hcXhc_fail:
  forall p t1 m1 t2 l m2 t3 i t1' t3' t4,
    hc_wt (HC p t1 m1 t2 inj) (t1' ⇒ Dyn) ->
    hc_wt (HC (prj l) t3 m2 t4 i) (Dyn ⇒ t3') ->
    mk_hc (t2, t3, l) (Fail prj_mt t2 l t3) -> 
    (forall h3' : hc,
        compose_hc
          ((HC p t1 m1 t2 inj), (HC (prj l) t3 m2 t4 i)) h3' ->
        Fail p t1 l t4 = h3')
    /\
    hc_wt (Fail p t1 l t4) (t1' ⇒ t3')
    /\
    hc_depth (Fail p t1 l t4) <=
    max (hc_depth (HC p t1 m1 t2 inj))
        (hc_depth (HC (prj l) t3 m2 t4 i)).
Proof.
  introv wt1 wt2 mk23. 
  split; [idtac | split; [idtac | idtac]]. 
  - introv cmp12. 
    inverts cmp12. 
    all: determinism_tac. 
    all: tc_tac_full.
    all: reflexivity. 
  - inverts wt1; tc_tac; eauto;
    constructor; try congruence; eauto. 
  - simpl in *. omega_max.  
Qed. 

Hint Resolve compose_correct_recontruct_hcXhc_fail.


(* This is completely broken *)
Ltac omega_max_d := 
  simpl in *;
  repeat match goal with
         | H: context[match ?c with _ => _ end] |- _ =>
           remember c; destruct c
         | |- context[match ?c with _ => _ end] =>
           remember c; destruct c
         end;
  omega_max. 

Lemma hc_m_depth_mk_hc_help {p1 p2 p3 m1 m2 m3 i1 i2 i3 t1 t2 t3 t4 n}: 
    hc_depth (HC p1 t1 m1 t2 i1) < S n ->
    hc_depth (HC p2 t3 m2 t4 i2) < S n ->
    (hc_depth (HC p3 t2 m3 t3 i3) 
     <= max (ty_depth t2) (ty_depth t3))-> 
    hc_m_depth m3 <= n.
Proof. intuition. simpl in *. omega_max. Qed. 
Hint Resolve hc_m_depth_mk_hc_help. 
Lemma hc_m_depth_compose_help 
      {p1 p2 p3 m1 m2 m3 m4 i1 i2 i3 t1 t2 t3 t4 n}:
  hc_depth (HC p1 t1 m1 t2 i1) < S n ->
  hc_depth (HC p2 t3 m2 t4 i2) < S n ->
  (hc_depth (HC p3 t2 m3 t3 i3) 
   <= max (ty_depth t2) (ty_depth t3)) -> 
  hc_m_depth m4 <= max (hc_m_depth m1) (hc_m_depth m3) ->
  hc_m_depth m4 <= n. 
Proof. intuition. simpl in *. omega_max. Qed. 
Hint Resolve hc_m_depth_compose_help. 


Ltac comp_exists f s c :=
  match goal with
  | H: compose_hc (f,s) _ |- _ => fail 1
        | IH: context[_ -> _ -> _ -> _ -> _] |- _ => 
          let comp:=fresh "cmp" in
          let cfn:=fresh "cfn" in
          let wt:=fresh "wt" in 
          let db:=fresh "dbnd" in
          edestruct (IH f s) as [c [comp [cfn [wt db]]]] ;
          [ solve [eauto] 
          | solve [eauto]
          | clear IH; try solve[eauto]
          | clear IH; try solve[eauto]
          | idtac ..]
  end.
Ltac comp_tac := 
  match goal with
  | H: mk_hc _ (HC _ _ ?m3 _ _)
    |- context[compose_hc (HC _ _ ?m1 _ _, HC _ _ ?m2 _ _) _] =>
    idtac m3 m1 m2;
    let m4:=fresh in
    let m5:=fresh in
    comp_exists m1 m3 m4;
    comp_exists m4 m2 m5
  | |- context[compose_hc (HC _ _ ?m1 _ inj_mt, 
                           HC prj_mt _ ?m2 _ _) _] =>
    idtac m1 m2;
    let m3:=fresh in
    comp_exists m1 m2 m3
  end. 


Theorem compose_hc_mostly_correct :
  forall n h1 h2 t1 t2 t3,
    (forall (m1 m2 : hc_m) (t1 t2 t3 : ty),
        hc_m_wt m1 (t1 ⇒ t2) ->
        hc_m_wt m2 (t2 ⇒ t3) ->
        hc_m_depth m1 <= n ->
        hc_m_depth m2 <= n ->
        exists m3 : hc_m,
          compose_hc_m (m1, m2) m3 /\
          (forall m3' : hc_m,
              compose_hc_m (m1, m2) m3' -> m3 = m3') /\
          hc_m_wt m3 (t1 ⇒ t3) /\
          hc_m_depth m3 <=
          Init.Nat.max (hc_m_depth m1) (hc_m_depth m2)) ->
    hc_wt h1 (t1 ⇒ t2) -> 
    hc_wt h2 (t2 ⇒ t3) -> 
    hc_depth h1 < S n ->
    hc_depth h2 < S n ->
    exists h3 : hc,
      compose_hc (h1, h2) h3 
      /\
      (forall h3' : hc,
          compose_hc (h1, h2) h3' -> h3 = h3') 
      /\
      hc_wt h3 (t1 ⇒ t3) 
      /\
      hc_depth h3 <= Init.Nat.max (hc_depth h1) (hc_depth h2). 
Proof.
  introv IHm wt1 wt2 db1 db2.
  match goal with
  | H1: hc_wt _ _, H2: hc_wt _ _ |- _ => inverts keep H1; inverts keep H2
  end. 
  all: repeat match goal with
              | H: hc_m_wt _ _ |- _ => inverts H
              end.
  all: 
    try 
      match goal with
      | |- context[compose_hc (HC _ _ _ _ ?i, HC ?p _ _ _ _) _] =>
        match goal with
        | H1: hc_i_wt i _, H2: hc_p_wt p _ |- _ =>
          inverts H1; inverts H2; eauto 6
        end
      | |- context[compose_hc (HC _ _ _ _ ?i, Fail ?p _ _ _) _] =>
        match goal with
        | H1: hc_i_wt i _, H2: hc_p_wt p _ |- _ =>
          inverts H1; inverts H2; eauto 6
        end
      end.
  all: 
    repeat 
      match goal with
      | H: _ → _ = _ → _ |- _ => inverts H
      | H: (Ref _) = (Ref _) |- _ => inverts H
      end.
  all: subst. 
  all: try solve [tc_tac;
                  try mk_hc_tac;
                  try comp_tac;
                  eauto 6].
  (* 11 goals left *)
  - tc_tac_full. 
    all: eexists; split; [idtac | split; [idtac | idtac]]. 
    all: eauto. 
    all: introv c; inverts c; eauto. 
    all: contradiction. 
  - tc_tac_full.
    all: eexists; split; [idtac | split; [idtac | idtac]]. 
    all: eauto. 
    introv c; inverts c; eauto. 
  - mk_hc_tac.
    + eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * eauto. 
      * simpl in *. omega_max. 
    + eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * eauto. 
      * simpl in *. omega_max. 
  - eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * simpl in *; destruct (ty_depth t7); omega_max. 
  - mk_hc_tac. 
    + eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      *  tc_tac; constructor; try congruence; eauto. 
      * inverts H; try contradiction;
        simpl in *; destruct (ty_depth t7); omega_max.  
    + eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      *  tc_tac; constructor; try congruence; eauto. 
      * destruct t6.
        all: try solve[contradiction]. 
        all: try solve[contradiction H; eauto].
        all: simpl in *. 
        all: destruct (ty_depth t7). 
        all: omega_max. 
    - eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * simpl in *; destruct (ty_depth t7); omega_max. 
    - mk_hc_tac. 
    + eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      *  tc_tac; constructor; try congruence; eauto. 
      * inverts keep H.
        all: try contradiction.
        all: try solve[contradiction H; eauto].
        all: simpl in *.
        all: clear H6. 
        all: destruct (ty_depth t7).
        all: omega_max.  
    + eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * destruct t6.
        all: try solve[contradiction]. 
        all: try solve[contradiction H; eauto].
        all: simpl in *. 
        all: destruct (ty_depth t7). 
        all: omega_max. 
    - eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * simpl in *; destruct (ty_depth t7); omega_max. 
    -  eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * simpl in *.  omega_max. 
    - eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * simpl in *; omega_max. 
    -  eexists; split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv c; inverts c; try contradiction; eauto; determinism_tac. 
      * tc_tac; constructor; try congruence; eauto. 
      * simpl in *; destruct (ty_depth t7); omega_max. 
Qed.     

Hint Resolve compose_hc_mostly_correct.  

Theorem compose_hc_m_mostly_correct :
  forall n h1 h2 t1 t2 t3,
    (forall (m1 m2 : hc_m) (t1 t2 t3 : ty),
        hc_m_wt m1 (t1 ⇒ t2) ->
        hc_m_wt m2 (t2 ⇒ t3) ->
        hc_m_depth m1 <= n ->
        hc_m_depth m2 <= n ->
        exists m3 : hc_m,
          compose_hc_m (m1, m2) m3 /\
          (forall m3' : hc_m,
              compose_hc_m (m1, m2) m3' -> m3 = m3') /\
          hc_m_wt m3 (t1 ⇒ t3) /\
          hc_m_depth m3 <=
          Init.Nat.max (hc_m_depth m1) (hc_m_depth m2)) ->
    hc_wt h1 (t1 ⇒ t2) -> 
    hc_wt h2 (t2 ⇒ t3) -> 
    1 + hc_depth h1 <= S n ->
    1 + hc_depth h2 <= S n ->
    exists h3 : hc,
      compose_hc (h1, h2) h3 
      /\
      (forall h3' : hc,
          compose_hc (h1, h2) h3' -> h3 = h3') 
      /\
      hc_wt h3 (t1 ⇒ t3) 
      /\
      hc_depth h3 <= Init.Nat.max (hc_depth h1) (hc_depth h2). 
Proof.
  intuition.
  assert (hc_depth h1 <= S n). auto. 
  assert (hc_depth h2 <= S n). auto. 
  eauto. 
Qed.

Hint Resolve compose_hc_m_mostly_correct. 

Theorem compose_hc_correct :
  forall n,
    (forall h1 h2 t1 t2 t3,
        hc_wt h1 (t1 ⇒ t2) ->
        hc_wt h2 (t2 ⇒ t3) ->
        hc_depth h1 < n ->
        hc_depth h2 < n -> 
        exists h3,
          (* Compose is total *)
          compose_hc (h1, h2) h3
          /\
          (* Compose is a function *)
          (forall h3', compose_hc (h1, h2) h3' -> h3 = h3')
          /\
          (* Compose is well-typed *)
          hc_wt h3 (t1 ⇒ t3)
          /\
          (* There is a bound on the depth of coercions
             returned from composition *)
          hc_depth h3 <= max (hc_depth h1) (hc_depth h2))
    /\
    (forall m1 m2 t1 t2 t3,
        hc_m_wt m1 (t1 ⇒ t2) ->
        hc_m_wt m2 (t2 ⇒ t3) ->
        hc_m_depth m1 <= n ->
        hc_m_depth m2 <= n ->
        exists m3,
          compose_hc_m (m1, m2) m3
          /\
          (forall m3', compose_hc_m (m1, m2) m3' -> m3 = m3')
          /\
          hc_m_wt m3 (t1 ⇒ t3)
          /\ 
          hc_m_depth m3 <= max (hc_m_depth m1) (hc_m_depth m2)).
Proof. 
  induction n; split; intuition.
  (* base case for (exist h3, ...) vacuously true *)
  - (* base case for exist m3, ... *)
    match goal with
      | H1: hc_m_wt _ _, H2: hc_m_wt _ _ |- _ =>
        inverts keep H1; inverts keep H2
    end;
    match goal with
      | H1: hc_m_depth _ <= 0, H2: hc_m_depth _ <= 0 |- _ =>
        inverts H1; inverts H2
    end.
    reconstruct. 
  - (* inductive step for exists h3, ... *)
    eapply compose_hc_mostly_correct; eauto. 
  - inverts H1; inverts H2.
    + eauto. 
    + eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv cmp'. inverts cmp'. reflexivity. 
      * eauto. 
      * eauto. 
    + eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv cmp'. inverts cmp'. reflexivity. 
      * eauto. 
      * eauto. 
    + eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv cmp'. inverts cmp'. reflexivity. 
      * eauto. 
      * eauto. 
    + edestruct compose_hc_m_mostly_correct as [m1' [cmp1' [cfn1' [wt1' db1']]]]. 
      eauto. 
      exact H7. 
      exact H8. 
      eauto. 
      eauto. 
      edestruct compose_hc_m_mostly_correct as [m2' [cmp2' [cfn2' [wt2' db2']]]]. 
      eauto.
      exact H9. 
      exact H11.
      eauto.
      eauto. 
      eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv cmp'. inverts cmp'. determinism_tac. reflexivity. 
      * eauto. 
      * simpl in *. omega_max. 
    + eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv cmp'. inverts cmp'. reflexivity. 
      * eauto. 
      * eauto. 
    + edestruct compose_hc_m_mostly_correct as [m1' [cmp1' [cfn1' [wt1' db1']]]]. 
      eauto. 
      exact H7. 
      exact H8. 
      eauto. 
      eauto. 
      edestruct compose_hc_m_mostly_correct as [m2' [cmp2' [cfn2' [wt2' db2']]]]. 
      eauto.
      exact H9. 
      exact H10.
      eauto.
      eauto. 
      eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
      * eauto. 
      * introv cmp'. inverts cmp'. determinism_tac. reflexivity. 
      * eauto. 
      * simpl in *. omega_max. 
Qed.         
