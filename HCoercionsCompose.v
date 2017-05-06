Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import General. 
Require Import Types.
Require Import Coercions. 
Require Import Omega. 
Require Import SolveMax.
Require Import HCoercions.
Open Scope depth_scope.
(* Well founded induction *)

Lemma mk_hc_depth : forall h t1 t2 l,
    mk_hc (t1, t2, l) h ->
    [|h|] <= max [|t1|] [|t2|].
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
| hcf1 {p t1 l} : hc_contains_ty (Fail p t1 l) t1
| sub {p t1 m t2 i h t}:
    hc_m_sub_hc m h ->
    hc_contains_ty h t -> 
    hc_contains_ty (HC p t1 m t2 i) t.
Hint Constructors hc_contains_ty. 

Lemma hc_contains_ty_depth': forall n c t,
    [| c |] < n -> 
    hc_contains_ty c t ->
    [| t |] <= [| c |]. 
Proof. 
  induction n;
    autounfold in *; intuition. 
  inverts H0. 
  - max_tac. 
  - max_tac. 
  - max_tac. 
  - assert (P : hc_depth h < hc_depth (HC p t1 m t2 i)).
    eauto.
    apply IHn in H2.
    max_tac. 
    max_tac. 
Qed.

Lemma hc_contains_ty_depth: forall c t,
    hc_contains_ty c t ->
    ty_depth t <= hc_depth c. 
Proof. intros;
         apply (hc_contains_ty_depth' (1 + [| c |])).
       eauto. 
       eauto. 
Qed. 

Lemma mk_hc_depth_help : forall n c1 c2 c3 t1 t2 l,
    [|c1|] < n ->
    [|c2|] < n ->
    hc_contains_ty c1 t1 -> 
    hc_contains_ty c2 t2 ->
    mk_hc (t1, t2, l) c3 ->            
    hc_depth c3 < n.
Proof. 
  intuition. 
  apply hc_contains_ty_depth in H1. 
  apply hc_contains_ty_depth in H2.
  apply mk_hc_depth  in H3. 
  max_tac. 
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
         hc_depth  (HC prj_mt t1 m t2 inj_mt)
         <= Init.Nat.max (ty_depth t1) (ty_depth t2)))      
    \/ 
    (t1 # t2
     /\
     (mk_hc (t1, t2, l) (Fail prj_mt t1 (t1, l, t2)))).
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
  max_tac. 
Qed. 
Lemma help_resolve_compose :
  forall t1 t2 t3 t4 p1 m1 i1 p2 m2 i2 m3 m4 m5 l,
    mk_hc (t2, t3, l) (HC prj_mt t2 m3 t3 inj_mt) ->
    [|m4|] <= max [|m1|] [|m3|] -> 
    [|m5|] <= max [|m4|] [|m2|] ->
    [|HC p1 t1 m5 t4 i2|] <= 
    max [|HC p1 t1 m1 t2 i1|] [|HC p2 t3 m2 t4 i2|]. 
Proof.
  intuition. 
  apply help_m_mk_hc in H. 
  max_tac. 
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
     |solve[max_tac]
     |solve[max_tac]
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
               max_tac]]]]. 

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
        [|m1|] <= n ->
        [|m2|] <= n ->
        exists m3 : hc_m,
          compose_hc_m (m1, m2) m3 /\
          (forall m3',
              compose_hc_m (m1, m2) m3' -> m3 = m3') /\
          hc_m_wt m3 (t1 ⇒ t3) /\
          [|m3|] <= max [|m1|] [|m2|]) -> 
    hc_wt (HC p1 t1 m1 t2 i1) (t1' ⇒ t2') ->
    hc_wt (HC p2 t3 m2 t4 i2) (t2' ⇒ t3') ->
    [|HC p1 t1 m1 t2 i1|] < S n ->
    [|HC p2 t3 m2 t4 i2|] < S n ->
    compose_hc (HC p1 t1 m1 t2 i1, HC p2 t3 m2 t4 i2)
               (HC p3 t1'' m5 t3'' i3) ->
    (forall h3', 
        compose_hc (HC p1 t1 m1 t2 i1, HC p2 t3 m2 t4 i2) h3' ->
        (HC p3 t1'' m5 t3'' i3) = h3')
    /\
    hc_wt (HC p3 t1'' m5 t3'' i3) (t1' ⇒ t3')
    /\
    [|HC p3 t1'' m5 t3'' i3|]
    <=
    max [|HC p1 t1 m1 t2 i1|] [|HC p2 t3 m2 t4 i2|].
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
    max_tac.
    max_tac. 
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
      edestruct (IHm m4 m2) as [m3 [cmp3 [cfn [wt3 db3]]]].
    eauto. 
    eauto.
    max_tac.
    max_tac.
    determinism_tac. 
    edestruct (IHm m1 m3) as [m7 [cmp7 [cfn7 [wt7 db7]]]]. 
    eauto. 
    eauto. 
    max_tac.
    max_tac. 
    determinism_tac. 
    split; [idtac | split; [idtac | idtac]].
    + introv cmp12'.
      inverts cmp12'.
      all: determinism_tac. 
      all: congruence. 
    + eauto. 
    + clear db1.
      clear db2.
      clear IHm.
      clear H4.
      clear H14.
      max_tac. 
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
    | |- context[compose_hc (HC _ _ _ ?t2 inj, Fail (prj ?l) ?t3 _) _] =>
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

Lemma arr_not_dyn_l : forall t1 t2, t1 → t2 <> Dyn.
Proof. congruence. Qed. 
Lemma arr_not_dyn_r : forall t1 t2, Dyn <> t1 → t2. 
Proof. congruence. Qed. 
Lemma ref_not_dyn_r : forall t1, Dyn <> Ref t1. 
Proof. congruence. Qed. 
Lemma ref_not_dyn_l : forall t2, Ref t2 <> Dyn. 
Proof. congruence. Qed. 
Hint Resolve arr_not_dyn_r arr_not_dyn_l ref_not_dyn_l ref_not_dyn_r.

Lemma compose_correct_recontruct_hcXhc_fail:
  forall p t1 m1 t2 l m2 t3 i t1' t3' t4,
    hc_wt (HC p t1 m1 t2 inj) (t1' ⇒ Dyn) ->
    hc_wt (HC (prj l) t3 m2 t4 i) (Dyn ⇒ t3') ->
    mk_hc (t2, t3, l) (Fail prj_mt t2 (t2, l, t3)) -> 
    (forall h3' : hc,
        compose_hc
          ((HC p t1 m1 t2 inj), (HC (prj l) t3 m2 t4 i)) h3' ->
        Fail p t1 (t2, l, t3)  = h3')
    /\
    hc_wt (Fail p t1 (t2, l, t3)) (t1' ⇒ t3')
    /\
    [|Fail p t1 (t2, l, t3)|]
    <=
    max [|HC p t1 m1 t2 inj|] [|HC (prj l) t3 m2 t4 i|].
Proof.
  introv wt1 wt2 mk23. 
  split; [idtac | split; [idtac | idtac]]. 
  - introv cmp12. 
    inverts cmp12. 
    all: determinism_tac. 
    all: tc_tac_full.
    all: reflexivity. 
  - inverts keep wt1; inverts keep mk23; tc_tac; eauto.
    all: inverts keep wt2; tc_tac; eauto.
  - max_tac.  
Qed. 

Hint Resolve compose_correct_recontruct_hcXhc_fail.


Lemma hc_m_depth_mk_hc_help {p1 p2 p3 m1 m2 m3 i1 i2 i3 t1 t2 t3 t4 n}: 
    [|HC p1 t1 m1 t2 i1|] < S n ->
    [|HC p2 t3 m2 t4 i2|] < S n ->
    [|HC p3 t2 m3 t3 i3|] <= max [|t2|] [|t3|] -> 
    [|m3|] <= n.
Proof. max_tac. Qed. 
Hint Resolve hc_m_depth_mk_hc_help. 
Lemma hc_m_depth_compose_help 
      {p1 p2 p3 m1 m2 m3 m4 i1 i2 i3 t1 t2 t3 t4 n}:
  [|HC p1 t1 m1 t2 i1|] < S n ->
  [|HC p2 t3 m2 t4 i2|] < S n ->
  [|HC p3 t2 m3 t3 i3|] <= max [|t2|] [|t3|] -> 
  [|m4|] <= max [|m1|] [|m3|] ->
  [|m4|] <= n. 
Proof.  max_tac. Qed. 
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
    let m4:=fresh in
    let m5:=fresh in
    comp_exists m3 m2 m4;
    comp_exists m1 m4 m5
  | |- context[compose_hc (HC _ _ ?m1 _ inj_mt, 
                           HC prj_mt _ ?m2 _ _) _] =>
    let m3:=fresh in
    comp_exists m1 m2 m3
  end. 

Lemma sct_arr_trans : forall t1 t2 t1' t2' t3,
    t1 → t2 !# t3 -> t1' → t2' !# t3.
Proof.
  introv sct. 
  destruct t3; inverts sct; eauto. 
Qed.
Lemma sct_ref_trans : forall t1 t2 t1',
    Ref t1 !# t2 -> Ref t1' !# t2. 
Proof.
  introv sct.
  destruct t2; inverts sct; eauto.
Qed.
Lemma sct_refl : forall t1 t2,
    t1 !# t2 -> t2 !# t1. 
Proof.
  introv s. inverts s; eauto.
Qed. 
Hint Resolve sct_arr_trans sct_ref_trans sct_refl.

Lemma sic_refl : forall t1 t2, t1 # t2 -> t2 # t1.
Proof. introv s. intro c. inverts c; contradiction s; eauto. Qed.
Lemma sic_not_dyn_l : forall t1 t2, t1 # t2 -> t1 <> Dyn.
Proof. introv s. intro c. subst. contradiction s; eauto. Qed.
Hint Resolve sic_refl sic_not_dyn_l.
Lemma sic_not_dyn_r : forall t1 t2, t1 # t2 -> t2 <> Dyn.
Proof. eauto. Qed. 
Hint Resolve sic_not_dyn_r. 

Lemma L10 : forall p1 t1 m1 t2 i1 n p2 t3 m2 i2 m3 m4 t4,
    hc_depth (HC p1 t1 m1 t2 i1) < S n -> 
    hc_depth (HC p2 t3 m2 t4 i2) < S n ->
    hc_depth (HC prj_mt t2 m3 t3 inj_mt) <= max (ty_depth t2) (ty_depth t3) ->
    hc_m_depth m4 <= max (hc_m_depth m3) (hc_m_depth m2) ->
    hc_m_depth m4 <= n.
Proof. max_tac. Qed. 
Hint Resolve L10. 


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
  (* all: repeat match goal with
     | H: hc_m_wt _ _ |- _ => inverts H
     end. *)
  all: 
    try 
      match goal with
      | |- context[compose_hc (HC _ _ _ _ ?i, HC ?p _ _ _ _) _] =>
        match goal with
        | H1: hc_i_wt i _, H2: hc_p_wt p _ |- _ =>
          inverts H1; inverts H2; eauto 6
        end
      | |- context[compose_hc (HC _ _ _ _ ?i, Fail ?p _ _) _] =>
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
  - comp_tac. eauto 6. 
  - tc_tac. all: eauto. 
  - tc_tac. all: eauto.
  - mk_hc_tac.
    + comp_tac. eauto 6.
    + eauto. 
  - exists. 
    split. 
    eauto. 
    split. 
    introv c. inverts c; tc_tac; determinism_tac; try congruence. 
    split. 
    tc_tac; eauto. 
    max_tac. 
  - tc_tac; eauto 6. 
    exists. 
    split. 
    eauto. 
    split. 
    introv c. inverts c; tc_tac; determinism_tac; try congruence. 
    eauto. 
  - tc_tac. 
  - mk_hc_tac.
    + exists.
      split.
      eauto.
      split.
      introv c. inverts c; tc_tac; determinism_tac; try congruence. 
      split.
      eauto.
      tc_tac; eauto. 
      max_tac.
    + exists.
      split.
      eauto.
      split.
      introv c. inverts c; tc_tac; determinism_tac; try congruence. 
      split.
      tc_tac; eauto.
      max_tac.
  - exists.
    split.
    eauto. 
    split. 
    introv c. inverts c; tc_tac; determinism_tac; try congruence.
    split.
    tc_tac; eauto. 
    max_tac. 
  - exists.
    split.
    eauto. 
    split. 
    introv c. inverts c; tc_tac; determinism_tac; try congruence. 
    split. 
    eauto. 
    eauto. 
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
  introv IHm w1 w2 b1 b2. 
  assert (bound: forall h n, 1 + hc_depth h <= S n -> hc_depth h < S n). auto.  
  eapply compose_hc_mostly_correct.
  exact IHm.
  exact w1.
  exact w2. 
  apply (bound h1 n b1).
  apply (bound h2 n b2). 
Qed.

Hint Resolve compose_hc_m_mostly_correct. 

Lemma compose_hc_m_type_preserving_deterministic_function: forall n m1 m2 t1 t2 t3,
    hc_m_wt m1 (t1 ⇒ t2) ->
    hc_m_wt m2 (t2 ⇒ t3) ->
    [|m1|] <= n ->
    [|m2|] <= n ->
    exists m3,
      compose_hc_m (m1, m2) m3
      /\
      (forall m3', compose_hc_m (m1, m2) m3' -> m3 = m3')
      /\
      hc_m_wt m3 (t1 ⇒ t3)
      /\ 
      [|m3|] <= max [|m1|] [|m2|].
Proof.
  induction n. 
  (* base case for (exist h3, ...) vacuously true *)
  - (* base case for exist m3, ... *)
    intuition.
    match goal with
      | H1: hc_m_wt _ _, H2: hc_m_wt _ _ |- _ =>
        inverts keep H1; inverts keep H2
      end.
      all: autounfold in *. 
      all: match goal with
           | H1: hc_m_depth _ <= 0, H2: hc_m_depth _ <= 0 |- _ =>
             inverts H1; inverts H2
           end.
      reconstruct. 
    - introv w1 w2 b1 b2. inverts w1; inverts w2.
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
        exact H4. 
        exact H2. 
        eauto. 
        eauto. 
        edestruct compose_hc_m_mostly_correct as [m2' [cmp2' [cfn2' [wt2' db2']]]]. 
        eauto.
        exact H3. 
        exact H6.
        eauto.
        eauto. 
        eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
        * eauto. 
        * introv cmp'. inverts cmp'. determinism_tac. reflexivity. 
        * eauto. 
        * max_tac. 
      + eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
        * eauto. 
        * introv cmp'. inverts cmp'. reflexivity. 
        * eauto. 
        * eauto. 
      + edestruct compose_hc_m_mostly_correct as [m1' [cmp1' [cfn1' [wt1' db1']]]]. 
        eauto. 
        exact H4. 
        exact H2. 
        eauto. 
        eauto. 
        edestruct compose_hc_m_mostly_correct as [m2' [cmp2' [cfn2' [wt2' db2']]]]. 
        eauto.
        exact H3. 
        exact H5.
        eauto.
        eauto. 
        eexists. split; [idtac | split; [idtac | split; [idtac | idtac]]]. 
        * eauto. 
        * introv cmp'. inverts cmp'. determinism_tac. reflexivity. 
        * eauto. 
        * max_tac.
Qed. 

Theorem compose_hc_m_total_deterministic_type_preserving :
    forall m1 m2 t1 t2 t3,
        hc_m_wt m1 (t1 ⇒ t2) ->
        hc_m_wt m2 (t2 ⇒ t3) ->
        exists m3,
          compose_hc_m (m1, m2) m3
          /\
          (forall m3', compose_hc_m (m1, m2) m3' -> m3 = m3')
          /\
          hc_m_wt m3 (t1 ⇒ t3).
  intros. 
  edestruct (compose_hc_m_type_preserving_deterministic_function
               (1+[|m1|]+[|m2|]) m1 m2 t1 t2 t3 H H0) as [m3 [c123 [c12fn [m3wt b3]]]].
  omega. 
  omega.
  eauto. 
Qed.   

Theorem compose_hc_total_deterministic_welltyped :
  forall n,
    (forall h1 h2 t1 t2 t3,
        hc_wt h1 (t1 ⇒ t2) ->
        hc_wt h2 (t2 ⇒ t3) ->
        [|h1|] < n ->
        [|h2|] < n -> 
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
             returned from composition. Needed for IH. *)
          [|h3|] <= max [|h1|] [|h2|]).
Proof. 
  intros. 
  eapply compose_hc_mostly_correct. 
  apply (compose_hc_m_type_preserving_deterministic_function n).
  all: eauto. 
Qed. 

Theorem compose_hc_type_preserving_deterministic_function :
  forall h1 h2 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    exists h3,
      (* Compose is total *)
      compose_hc (h1, h2) h3
      /\
      (* Compose is a function *)
      (forall h3', compose_hc (h1, h2) h3' -> h3 = h3')
      /\
      (* Compose is well-typed *)
      hc_wt h3 (t1 ⇒ t3). 
Proof. 
  intros. 
  edestruct (compose_hc_total_deterministic_welltyped (1 + [|h1|] + [|h2|]))
    as [h3 [cp [fn [wt b]]]]. 
  exact H.
  exact H0.
  all: try max_tac.
  eauto. 
Qed. 

Corollary compose_hc_wt: forall h1 h2 h3 t1 t2 t3,
    hc_wt h1 (t1 ⇒ t2) ->
    hc_wt h2 (t2 ⇒ t3) ->
    compose_hc (h1, h2) h3 ->
    hc_wt h3 (t1 ⇒ t3).
Proof.
  introv w1 w2 c. 
  edestruct compose_hc_type_preserving_deterministic_function as [h3' [c' [cf w3']]].
  exact w1. exact w2.
  rewrite (cf h3) in *.
  all: assumption. 
Qed. 
