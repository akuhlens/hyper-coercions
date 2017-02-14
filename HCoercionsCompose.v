
Require Import Coq.Init.Datatypes.
Require Import LibTactics. 
Require Import GTypes.
Require Import coercions. 
Require Import Omega. 
Require Import HCoercions.

(* well founded induction *)

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


Ltac invert_initial_mediating_ty_judgements :=
  match goal with
  | m1: hc_m_wt _ _, m2: hc_m_wt _ _ |- _ => inverts keep m1; inverts keep m2
  | m1: hc_m_wt |- _ => inverts keep m1
  | _ => idtac
  end.

Ltac inner_ty_consist_dec_tac :=
        let rec mk_hc_extra :=
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
                   | l: blame_info, h: ?t1 <∼> ?t2 |- _ =>
                     match goal with
                     | H: mk_hc (t1, t2, l) _ |- _ => fail 1
                     | _ =>
                       try solve[inverts keep h; try discriminate];
                       idtac l h t1 t2;
                       destruct (mk_hc_not_dyn_sconsist t1 t2 l);
                       [solve [eauto] | solve [eauto] | solve [eauto] | idtac ..];
                       mk_hc_extra
                     end
                   | l: blame_info, h: ?t1 <≁> ?t2 |- _ =>
                     match goal with
                     | H: mk_hc (t1, t2, l) _ |- _ => fail 1
                     | _ => 
                       try solve[contradiction h; eauto];
                         destruct (mk_hc_not_dyn_sconsist t1 t2 l);
                         [ > solve [eauto] | solve [eauto] | solve [eauto] | idtac ..];
                         mk_hc_extra
                     end
                end
        in
        try match goal with
               | |- context[compose_hc (HC _ ?m1 inj, HC (prj ?l) ?m2 _) _] =>
                 match goal with
                 | H1: hc_m_wt m1 (_ ⇒ ?t1),
                       H2: hc_m_wt m2 (?t2 ⇒ _) |- _ =>
                   destruct (ty_shallow_consistency_dec t1 t2);
                   mk_hc_tac         
                 end
            | |- context[compose_hc (HC _ ?m1 inj, Fail (prj ?l) ?t2 _) _] =>
              match goal with
              | H1: hc_m_wt m1 (_ ⇒ ?t1) |- _ => 
                destruct (ty_shallow_consistency_dec t1 t2);
                mk_hc_tac
              end
            | _ => idtac 
            end.

Theorem compose_hc_total :
  forall n,
    (forall h1 h2 t1 t2 t3,
        hc_wt h1 (t1 ⇒ t2) ->
        hc_wt h2 (t2 ⇒ t3) ->
        hc_depth h1 + hc_depth h2 <= n ->
        exists h3, compose_hc (h1, h2) h3
                   /\
                   hc_wt h3 (t1 ⇒ t3)
                   /\
                   hc_depth h3 <= (hc_depth h1) + (hc_depth h2)).
(*  /\ 
  (forall m1 m2 t1 t2 t3,
      hc_m_wt m1 (t1 ⇒ t2) ->
      hc_m_wt m2 (t2 ⇒ t3) ->
      hc_m_depth m1 + hc_m_depth m2 <= 1 + n ->
      exists m3,
        compose_hc_m (m1, m2) m3
        /\
        hc_m_wt m1 (t1 ⇒ t3)
        /\
        hc_m_depth m3 <= hc_m_depth m1 + hc_m_depth m2). *)
Proof. 
  induction n; intuition.
  (* There are some base minimums that make trivial case truely trivial *)
  - omega_max. (* Vacuously True *) 
  - match goal with
    | H1: hc_wt _ _, H2: hc_wt _ _ |- _ => inverts keep H1; inverts keep H2
    end;
    invert_initial_mediating_ty_judgements.


    * repeat match goal with
           | H: hc_i_wt _ _ |- _ => inverts H
           | H: hc_p_wt _ _ |- _ => inverts H
           end;
        try solve
        [eexists; split; [> solve[eauto] | split; [> solve[eauto] | omega_max]]];
        inner_ty_consist_dec_tac;
        repeat match goal with
               | H: hc_wt _ _ |- _ => inverts H
               | H: hc_i_wt _ _ |- _ => inverts H
               | H: hc_p_wt _ _ |- _ => inverts H
               end;
        try solve
        [eexists; split; [> solve[eauto] | split; [> solve[eauto] | omega_max]]].
    * repeat match goal with
           | H: hc_i_wt _ _ |- _ => inverts H
           | H: hc_p_wt _ _ |- _ => inverts H
           end.
      all: try discriminate. 
      all:
        try solve
            [eexists; split; [> solve[eauto] | split; [> solve[eauto] | omega_max]]].
      all: inner_ty_consist_dec_tac.


      
      inverts H3.
      inverts H18. 
      inverts keep H17. 
      try solve
          [eexists; split; [> solve[eauto] | split; [> solve[eauto] | omega_max]]].
      
      inverts H2.
      eexists. 
      split.
      econstructor.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto. 
      econstructor. 
      destruct (IHn _ _ _ _ _ H11 H13) as [c5 [P1 P2]]. 

      repeat match goal with
      | |- context[hc_depth ?c] =>
        match goal with
        | H: hc_depth c < _ |-  _ => fail 1
        | H: context[(HC ?p ?m ?i)] |- _ =>
          cut (hc_contains_hc (HC p m i) c);
            [ intros | solve[eauto] | idtac ..];
            match goal with
            | H: (hc_contains_hc (HC p m i) c) |- _ =>
              apply hc_depth_lt_contained_hc in H
            end
        end
      end.
      simpl in * .
      expose_depth_min_tac. 
      repeat
        match goal with
        | e: _ = _ |- _ => rewrite e
        end. 

      SearchAbout "max".
      SearchAbout "ex".

      (*
        Max.max_lub_l: forall n m p : nat, Nat.max n m <= p -> n <= p
        Max.max_lub_r: forall n m p : nat, Nat.max n m <= p -> m <= p
       *)
      
      repeat match goal with
      | H: context[(max ?n ?m)] |- _ =>
        match goal with
        | H: (max n m) = _ |- _ => fail 1
        | _ =>
          let x:=fresh in
          let eq:=fresh in
          let ieq1:=fresh in
          let ieq2:=fresh in
          let ieq3:=fresh in
          remember (max n m) as x eqn:eq;
            symmetry in eq;
            assert (ieq1 : (max n m) <= x) by (rewrite eq; reflexivity);
            apply Max.max_lub_l in ieq1 as ieq2;
            apply Max.max_lub_r in ieq1 as ieq3
        end
       end.

      
      do 3 match goal with
                  | H: context[max ?t1 ?t2] |- _ =>
                    match goal with
                    | H: max t1 t2 = t1 |- _ => fail 1
                    | H: max t1 t2 = t2 |- _ => fail 1
                    | _ =>
                      let H:=fresh in
                      assert (H: (max t1 t2 = t1)) by (apply Max.max_l; omega);
                        rewrite H in *;
                        try time "branch 1" omega
                    | _ =>
                      let H:=fresh in
                      assert (H: (max t1 t2 = t1)) by (apply Max.max_r; omega);
                        rewrite H in *;
                        try time "branch 2" omega
                    | _ =>
                      let e:=fresh in
                      destruct (Max.max_dec t1 t2) as [e|e];
                        rewrite e in *;
                        [ apply max_spec_eq_r in e |
                          apply max_spec_eq_l in e ];
                        try time "branch 3" omega
                    end
            end.
      
      
      subst.
                 end
             end.

      Ltac max_dec_tac_context := 
        (* this match leads to exponential blowup :( *) 
        repeat match goal with
               | H: context[max ?t1 ?t2] |- _ =>
          
         end.


      omega_max_search 5;
  max_dec_tac_context; 
  omega. 
      
      omega_max. 
      Check hc_size_lt_contained_hc .

      destruct 
      destruct (H0 _ _ _ _ _ H19 H11). 
      simpl in *. 
      omega_max. 
      split.

      constructor. apply 
      eauto. 
      
      try solve
            [eexists; split; [> solve[eauto] | split; [> solve[eauto] | omega_max]]].
    

             discriminate. 
      eauto. 
      eauto. 
      eauto. 
      eauto.
      eauto.
      eauto. 
      eauto. 
      split.
      econstructor.
      2: eauto. 
      constructor.
      eauto.
      eauto. 
      omega_max. econstructor. 
      econstructor. 
      econstructor. 
    try match goal with
         | |- context[compose_hc (HC _ _ ?i, HC ?p _ _) _] =>

         | |- context[compose_hc (HC _ _ ?i, Fail ?p _ _)] =>
           repeat match goal with
                  | H: hc_i_wt i _ |- _ => inverts H
                  | H: hc_p_wt p _ |- _ => inverts H
                  end
         end.
    






    (* mk_hc (t1, t2, l) h -> hc_wt h (t1 ⇒ t2) /\ hc_depth h = max (ty_depth t1) (ty_depth t2) *)
        all: try 


        all:
          time try solve
          [eexists; split; [> solve[eauto] | split; [> solve[eauto] | omega_max]]].


    * eexists. 
      split.
      solve[eauto].
      split.
      solve[eauto]. 
      omega_max. 
      [>  | split; [> solve[eauto] | omega_max]].
          
        
    * eexists; 
        all:
          repeat match goal with
                 | H: hc_wt _ _ |- _ => inverts H
                 | H: hc_p_wt _ _ |- _ => inverts H
                 | H: hc_i_wt _ _ |- _ => inverts H
                 end;
          repeat match goal with
               | H: hc_m_wt _ _ |- _ => inverts keep H
               end;
          repeat match goal with
                 | H: _ <> _ |- _ => solve [contradiction H; auto]
                 end;
        

        


        
          
        try solve[  
        eexists; split;
          [> solve [try solve [repeat (try eassumption; econstructor)] ; eauto]
          | split;
            [> repeat (econstructor + eassumption + eauto) | omega_max]]].
                                                                             

                        end.  
    

    
    (* further case analysis on m(s) and inner projections and injections *)
    (* compose HC, HC *)
    time "all"
     (
      end; 
    
    
        (* mk_hc (t1, t2, l) h -> hc_wt h (t1 ⇒ t2) /\ hc_depth h = max (ty_depth t1) (ty_depth t2) *)
        repeat
          try match goal with
              | H: mk_hc (?t1, ?t2, ?l) ?h |- _ =>
                match goal with
                | H': hc_wt h _ |- _ => fail 1
                | _ => 
                  cut (hc_wt h (t1 ⇒ t2)); [intro | apply (mk_hc_wt _ _ _ _ H)]
                end;
                  match goal with
                  | H': hc_depth h <= (max (ty_depth t1) (ty_depth t2)) |- _ => fail 1
                  | _ => let P:=fresh in apply mk_hc_depth in H as P
                  end
              end;
        


        try
        time "solve"  
        solve
        [eexists; split;
         [> solve [try solve [repeat (try eassumption; econstructor)] ; eauto]
         | split;
           [> repeat (econstructor + eassumption + eauto) | omega_max]]]).
      
      

      repeat match goal with
             | H: hc_wt _ _ |- _ => inverts H
             | H: hc_p_wt _ _ |- _ => inverts H
             | H: hc_i_wt _ _ |- _ => inverts H
             end;
        do 2 match goal with
             | H: hc_m_wt _ _ |- _ => inverts keep H
             end.


      


      
      
      eexists. 
      split. 
      eauto.
      split. 
      eauto.

      simpl in *. omega_max. 
      eauto. 

      split.
      econstructor. 
      eassumption.
      eassumption. eauto. 

      
      match goal with
      | H: mk_hc (?t1, ?t2, ?l) ?h |- _ =>
        match goal with
        | H': hc_wt h _ |- _ => fail 1
        | _ =>
          let P:=fresh in
          let x:=fresh in
          let y:=fresh in
          let z:=fresh in
          let w1:=fresh in
          let w2:=fresh in
          let w2:=fresh in
          apply mk_hc_wt in H as P;
            inverts keep P as [x y z w1 w2 w3 | x y z w1];
            [inverts w1; inverts keep w2; inverts w3 |
             inverts w1]
        end;
          match goal with
          | H': hc_depth h <= (max (ty_depth ?t1) (ty_depth ?t2)) |- _ => fail 1
          | _ => let P:=fresh in apply mk_hc_depth in H as P
          end

          
      end.
      
      eexists. 
      split.
      eauto. 
      split.
      econstructor.
      eassumption.
      eassumption. 
      eauto. 
      
      inverts H13.
      inverts H19.
      inverts H22. 
      inverts keep H21.
      eauto. 
      econstructor. 
      eassumption. eauto. 
      apply mk_hc_wt in H3 as H42.  
      assumption.
      destruct (mk_hc_total t3 t3 l0) as [x' [Px'1 Px'2]]. 
      Check mk_hc_function. 
      apply (mk_hc_function _ _ _ _ _  Px'1) in H3 as H3eq. 
      subst. 
      
      omega_max. 
      
      eassumption. 
      match goal with
    | |- context[compose_hc (HC ?p1 ?m1 ?i1, HC ?p2 ?m2 ?i2) _] =>
              Hi2: hc_i_wt i2 _ |- _ =>

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

