Require Import Coq.Init.Datatypes.
Require Import LibTactics.
Require Export General.
Require Import GTypes. 
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import coercions.
Open Scope depth_scope. 


Inductive  compose_se : coercion * coercion -> coercion -> Prop :=
| Comp_Se_Inj_Prj : forall g t' t l i i' m c,
    make_se_coercion (t, t', l) m ->
    compose_se (g, m) i' ->
    compose_se (i', i) c ->
    compose_se (Seq_c g (Inj_c t), Seq_c (Prj_c t' l) i) c
| Comp_Se_Prj : forall t l i t'' s c,
    se_inj_coercion i (t  ⇒ t'') ->
    compose_se (i, s) c ->
    compose_se (Seq_c (Prj_c t l) i, s) (Seq_c (Prj_c t l) c)
| Comp_Se_Inj : forall g g' t t' t'' c,
    se_inj_coercion g (t ⇒ t') ->
    se_inj_coercion g' (t' ⇒ Dyn) ->
    compose_se (g, g') c ->
    compose_se (g, Seq_c g' (Inj_c t'')) (Seq_c c (Inj_c t''))              
| Comp_Se_Arr   : forall c1 c2 c3 c4 c5 c6,
    compose_se (c3, c1) c5 ->
    compose_se (c2, c4) c6 ->
    compose_se (c1 →c c2, c3 →c c4) (c5 →c c6)
| Comp_Se_Ref_c   : forall c1 c2 c3 c4 c5 c6,
    compose_se (c3, c1) c5 ->
    compose_se (c2, c4) c6 ->
    compose_se (Ref_c c1 c2, Ref_c c3 c4) (Ref_c c5 c6)
| Comp_Se_Id_L : forall t c,
    compose_se (Id_c t, c) c
| Comp_Se_Id_R : forall t c,
    compose_se (c, Id_c t) c
| Compose_Fail_c_R : forall g t t' l,
    se_med_coercion g (t ⇒ t') ->
    compose_se (g, Fail_c l) (Fail_c l)
| Compose_Fail_c_L : forall c l,
    compose_se (Fail_c l, c) (Fail_c l).

Hint Constructors compose_se. 

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
             solve [eexists; split; [eauto 7 | split; [eauto 7 | solve[ineq_tac]]]].
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

             Ltac prj_inj_IH :=
               repeat match goal with
                      | H1: se_coercion ?c1 (_ ⇒ ?t),
                            H2: se_coercion ?c2 (?t ⇒ _)
                        |- _ =>
                        match goal with
                        | H: compose_se (c1, c2) _ /\ _ |- _ => fail 1
                        | IH: forall c1 c2, _ |- _ =>
                          time (edestruct (IH c1 c2);
                                [idtac | idtac | solve[eauto] | solve[eauto] | idtac];
                                [ineq_tac | ineq_tac | idtac])
                        end
                      end;
               repeat match goal with
                      | H: compose_se _ _ /\ _ |- _ =>
                        let P1:=fresh in
                        let P2:=fresh in
                        let P3:=fresh in
                        destruct H as [P1 [P2 P3]]
                      end.
                        
             -- prj_inj_IH. reconstruct. 
             -- prj_inj_IH.

                
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