Require Import L3.well_boundness L3.well_typedness L3.semantics prop_fold sub.

Instance FH : @FrameHeap V.
Proof. econstructor. Defined.

(* Value typing *)
Inductive vtyp' {G: @WCGAT T} (h: @H V FH) : V -> T -> Prop :=
| vtyp'_n : forall z, vtyp' h (NumV z) Tint
| vtyp'_b : forall b, vtyp' h (BoolV b) Tbool
| vtyp'_f :
    forall
      ds s e f tas tr sp
      (FS: scopeofFrame V FH h f sp)
      (TD: typofDecls T G s ds tas)
      (DS: declsofScopeP wc s ds)
      (NOIMP: linksofScopeP wc s [(P, [sp])])
      (WT: @wt_exp G (E s tr e))
      (WB: @wb_exp G (E s tr e)),
      vtyp' h (ClosV ds (E s tr e) f) (Tarrow tas tr)
| vtyp'_df :
    forall
      ts t v
      (VT: vtyp' h v t),
      vtyp' h (DefFunV v) (Tarrow ts t)
| vtyp'_r :
    forall
      f d sd s
      (SF: scopeofFrame V FH h f s)
      (ASC: assocScope T G sd d s),
      vtyp' h (ObjectV f) (Tclass sd d)

(* Class constructors: *)
| vtyp_cc : forall
    s0 d rss es optr f s sp ds ts
    (ASC: assocScope T G s0 d s)
    (DS: declsofScopeP wc s ds)
    (TS: typofDecls T G s ds ts)
    (FS: scopeofFrame V FH h f sp)
    (OPTR: match optr with
           | Some (sr, r) =>
             sr = sp /\
             scopeofRefP wc r sp /\
             exists p spar dpar,
               rlookup wc sr r p sp dpar /\
               assocScope T G sp dpar spar /\
               dynamicDecl sp dpar /\
               typofDecl T G sp dpar (TclassDef sp dpar) /\
               linksofScopeP wc s [(P, [sp]); (I, [spar])]
           | None =>
             linksofScopeP wc s [(P, [sp])]
           end)
    (SRS: forall sr r, In (sr, r) rss -> sr = s /\ scopeofRefP wc r s)
    (WBE: forall e, In e es -> wb_exp e /\ expScope e = s)
    (WTE: Forall2 (fun e rs =>
                     match rs with
                     | (sr, r) =>
                       exists p s'' d' t',
                       rlookup wc sr r p s'' d' /\
                       typofDecl T G s'' d' t' /\ sub' (expType e) t' /\ wt_exp e
                     end) es rss),
    vtyp' h (ConstructorV s0 d optr (rss, es) f) (TclassDef s0 d)

(* Null values are typed by records: *)
| vtyp'_nr : forall sd d, vtyp' h NullV (Tclass sd d)
(* Applying or reading a null value throws a NullPointer exception,
which is allowed in any context: *)
| vtyp'_q : forall t, vtyp' h (AbortV NullPointer) t
.

Hint Constructors vtyp' : sgraph.

Lemma setSlot_vtyp' :
  forall
    (G: @WCGAT T) h0 f d v h1 v0 t0
    (SET: setSlot V FH h0 f d v h1)
    (VT: vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv SET; induction VT; sgauto.
  - econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
    rewrite H1 in H0; inv H0. econstructor; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst.
    econstructor. rewrite get_set_same.
    rewrite H1 in H0; inv H0; eauto.
    econstructor. rewrite get_set_other; eauto.
  - econstructor; eauto. inv FS. destruct (FrameIdDec f0 f); subst.
    econstructor; rewrite H1 in H0; inv H0; eauto; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
Qed.

Lemma newFrame_vtyp' :
  forall
    (G: @WCGAT T) h0 s f h1 ks v0 t0
    (NF: newFrame V FH h0 s ks f h1)
    (VT: vtyp' h0 v0 t0),
    vtyp' h1 v0 t0.
Proof.
  intros; inv NF; induction VT; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - apply keys_in in H0; contradiction.
  - econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst. apply keys_in in H0. contradiction.
    econstructor. rewrite get_set_other; eauto.
  - econstructor; eauto. inv FS. destruct (FrameIdDec f0 f); subst.
    eapply keys_in in H0; contradiction.
    econstructor; rewrite get_set_other; eauto.
Qed.

Lemma fillFrame_vtyp' :
  forall
    (G: @WCGAT T) slots f h1 h2 v0 t0
    (FF: fillFrame V FH f h1 slots h2)
    (VT: vtyp' h1 v0 t0),
    vtyp' h2 v0 t0.
Proof.
  intros; destruct FF as [? [? [? [? ?]]]]; subst; induction VT; sgauto.
  econstructor; sgauto. inv FS. destruct (FrameIdDec f f0); subst.
  - rewrite H in H0; inv H0. econstructor; rewrite get_set_same; eauto.
  - econstructor; rewrite get_set_other; eauto.
  - econstructor; sgauto.
    inv SF. destruct (FrameIdDec f0 f); subst.
    econstructor. rewrite get_set_same.
    rewrite H0 in H; inv H; eauto.
    econstructor. rewrite get_set_other; eauto.
  - econstructor; eauto. inv FS. destruct (FrameIdDec f0 f); subst.
    econstructor; rewrite H0 in H; inv H; eauto; rewrite get_set_same; eauto.
    econstructor; rewrite get_set_other; eauto.
Qed.

Hint Resolve setSlot_vtyp' : sgraph.
Hint Resolve newFrame_vtyp' : sgraph.
Hint Resolve fillFrame_vtyp' : sgraph.


(* Default values for different types *)
Inductive default : T -> V -> Prop :=
| def_n : default Tint (NumV 0)
| def_b : default Tbool (BoolV false)
| def_df : forall ts t v,
    default t v ->
    default (Tarrow ts t) (DefFunV v)
| def_r : forall sd d, default (Tclass sd d) NullV
.

Hint Constructors default : sgraph.

Lemma default_vtyp' :
  forall (G: @WCGAT T) v t,
    default t v ->
    forall h,
      @vtyp' G h v t.
Proof.
  induction 1; intros; sgauto.
Qed.


Instance VT {G: @WCGAT T} : @VTyp T V :=
  { fh := FH }.
Proof.
  apply vtyp'.
  apply setSlot_vtyp'.
  apply newFrame_vtyp'.
  apply fillFrame_vtyp'.
Defined.

Instance DVT {G: @WCGAT T} : @DefaultVTyp T V VT.
Proof.
  econstructor.
  instantiate (1:=default).
  apply default_vtyp'.
Qed.

Hint Constructors sub' : sgraph.
Hint Constructors sub1 : sgraph.
Hint Constructors upcast : sgraph.

Lemma sub'_trans :
  forall {G: @WCGAT T} t1 t2 t3,
    sub' t1 t2 ->
    sub' t2 t3 ->
    sub' t1 t3.
Proof.
  induction 1; intros; sgauto.
Qed.

Lemma sub'_refl :
  forall {G: @WCGAT T} t,
    sub' t t.
Proof. sgauto. Qed.

Hint Resolve sub'_trans : sgraph.
Hint Resolve sub'_refl : sgraph.

Instance ST {G: @WCGAT T} : SubTyping T.
Proof.
  econstructor.
  eapply (@sub'_refl G).
  eapply (@sub'_trans G).
Defined.

Hint Unfold sub : sgraph.

Section Subtyping.

  Context {G: @WCGAT T}.

  (* Facts about subtyping *)

  Lemma sub_int :
    forall
      t t'
      (SUB: sub' t t')
      (TEQ: t' = Tint),
      t = Tint.
  Proof.
    induction 1; intros; eauto; try discriminate.
    rewrite IHSUB in SUB1; auto. inv SUB1.
  Qed.

  Lemma sub_bool :
    forall
      t t'
      (SUB: sub' t t')
      (TEQ: t' = Tbool),
      t = Tbool.
  Proof.
    induction 1; intros; eauto; try discriminate.
    rewrite IHSUB in SUB1; auto. inv SUB1.
  Qed.

  Lemma sub_tarrow :
    forall
      t t'
      (SUB: sub' t t')
      t1s' t2'
      (TEQ: t' = Tarrow t1s' t2'),
    exists t1s t2,
      t = Tarrow t1s t2 /\
      (Forall2 (fun t1 t1' => sub' t1 t1') t1s' t1s) /\
      sub' t2 t2'.
  Proof.
    induction 1; intros; subst; eauto; try discriminate.
    - do 2 eexists; split; eauto.
      split; sgauto. clear t2'.
      induction t1s'; sgauto.
    - edestruct IHSUB as [t1s [t2 [TEQ [ARGS SUB']]]]; subst; eauto.
      inv SUB1.
      do 2 eexists; split; eauto.
      split; eauto using sub'_trans.
      clear - ARGS ARGS0.
      generalize dependent ARGS0. generalize dependent t1s0.
      induction ARGS; intros. inv ARGS0. constructor.
      inv ARGS0; eauto using sub'_trans.
  Qed.

  Lemma sub_tclass :
    forall
      t t'
      (SUB: sub' t t')
      s d'
      (TEQ: t' = Tclass s d')
      s'
      (ASC: assocScope T G s d' s'),
    exists s0 d s,
      t = Tclass s0 d /\
      assocScope T G s0 d s.
  Proof.
    induction 1; intros; subst; sgauto; try discriminate.
    edestruct IHSUB; eauto. destruct H as [? [? [TEQ ASC']]]. subst. inv SUB1; sgauto.
  Qed.

  Lemma sub_tclassdef :
    forall
      t t'
      (SUB: sub' t t')
      s d'
      (TEQ: t' = TclassDef s d'),
    exists s0 d,
      t = TclassDef s0 d.
  Proof.
    induction 1; intros; subst; eauto; try discriminate.
    edestruct IHSUB as [? [? EQ]]; eauto. subst. inv SUB1.
  Qed.

  Lemma forall2_sub_trans :
    forall
      es ts P
      (P1: Forall2 (fun e t => sub' (expType e) t /\ P e)
                   es ts)
      ts'
      (P2: Forall2 (fun t t' => sub' t t') ts ts'),
      Forall2 (fun e t => sub' (expType e) t /\ P e) es ts'.
  Proof.
    induction 1; intros; eauto; try inv P2; eauto using Forall2.
    destruct H. sgauto.
  Qed.

  Lemma upcast_scopeofFrame :
    forall h rf srec rf',
      upcast h rf srec rf' ->
      scopeofFrame V fh h rf' srec.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma forall2_in :
    forall
      X xs (x:X) Y (ys:list Y) P
      (IN: In x xs),
      Forall2 (fun y x => P y x) ys xs ->
      exists y, P y x /\ In y ys.
  Proof.
    induction xs; intros; inversion IN; subst; inv H; eauto.
    eexists; split; eauto. econstructor; eauto.
    eapply IHxs in H5; eauto. destruct H5 as [? [PY INY]].
    eexists; split; eauto. econstructor 2; eauto.
  Qed.

  (* Key subtyping lemma: if a record has a supertype, then it can be
  safely upcast at runtime *)
  Lemma sub_class_upcast :
    forall
      t t'
      (SUB: sub' t t')
      s d
      (TEQ: t = Tclass s d)
      s' d'
      (TEQ': t' = Tclass s' d')
      h1 srec
      (GH: good_sub_heap h1)
      (ASC: assocScope T G s' d' srec)
      rf
      (VT: vtyp h1 (ObjectV rf) (Tclass s d)),
      exists rf', upcast h1 rf srec rf'.
  Proof.
    induction 1; intros; subst.
    - inv TEQ'. inv VT0. eapply assocScopeDet in ASC; eauto; subst.
      sgauto.
    - inv SUB1. inv VT0.
      assert (frame h1 rf) by sgauto.
      generalize (GH _ H); intro GFRF; destruct GFRF as [WB WT]. inv WB.
      eapply scopeofFrameDet in SF; eauto; subst.
      eapply assocScopeDet in ASC0; eauto; subst.
      assert (llinksofScopeP (@g gat wc) s1 I ims).
      { inv IMS; sgauto. econstructor; split; sgauto. simpl.
        destruct (ELdec I I); intuition. }
      destruct (LNS _ _ H0) as [? [IMF [EQ FSF]]]. subst.
      eapply FSF in IN_IMS. destruct IN_IMS as [? [EQ SF']].
      assert (vtyp h1 (ObjectV x0) (Tclass s d'0)).
      econstructor; sgauto.
      eapply IHSUB in H1; eauto. destruct H1.
      sgauto.
  Qed.

End Subtyping.

Hint Resolve forall2_sub_trans : sgraph.

Section TypeSoundness.

  Context (G: @WCGAT T).

  Lemma eval_exp_scopeofFrame_aux :
    (forall h0 f0 e v h1,
        eval_exp h0 f0 e v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 f1 ds es v h1,
        fill_slots_par h0 f0 f1 ds es v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 ds es v h1,
        fill_slots_seq h0 f0 ds es v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 ds es v h1,
        fill_slots_rec h0 f0 ds es v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 e v h1,
        eval_lhs h0 f0 e v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          scopeofFrame V fh h1 f s) /\
  (forall h0 f0 s r v h1,
     eval_objinit h0 f0 s r v h1 ->
     forall f s,
       scopeofFrame V fh h0 f s ->
       scopeofFrame V fh h1 f s) /\
  (forall h0 f0 f1 rs es v h1,
     assign_refs h0 f0 f1 rs es v h1 ->
     forall f s,
       scopeofFrame V fh h0 f s ->
       scopeofFrame V fh h1 f s).
  Proof.
    apply eval_exp_ind3; sgauto.
  Qed.

  Definition eval_exp_scopeofFrame     := proj1 eval_exp_scopeofFrame_aux.
  Definition fill_par_scopeofFrame     := proj1 (proj2 eval_exp_scopeofFrame_aux).
  Definition fill_seq_scopeofFrame     := proj1 (proj2 (proj2 eval_exp_scopeofFrame_aux)).
  Definition fill_rec_scopeofFrame     := proj1 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).
  Definition eval_lhs_scopeofFrame     := proj1 (proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux)))).
  Definition eval_objinit_scopeofFrame := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))))).
  Definition assign_refs_scopeofFrame  := proj2 (proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux)))).

  Hint Resolve eval_exp_scopeofFrame : sgraph.
  Hint Resolve fill_par_scopeofFrame : sgraph.
  Hint Resolve fill_seq_scopeofFrame : sgraph.
  Hint Resolve fill_rec_scopeofFrame : sgraph.
  Hint Resolve eval_lhs_scopeofFrame : sgraph.
  Hint Resolve eval_objinit_scopeofFrame : sgraph.
  Hint Resolve assign_refs_scopeofFrame : sgraph.
  Hint Unfold abort : sgraph.
  Hint Constructors vtyp' : sgraph.
  Hint Constructors wb_lhs : sgraph.
  Hint Constructors wt_lhs : sgraph.

  Lemma exp_preservation:
    (forall
        h0 f e v h1
        (EVAL: eval_exp h0 f e v h1)
        s t pe
        (UNPACK: e = (E s t pe))
        (FS: scopeofFrame V fh h0 f s)
        (GH: good_sub_heap h0)
        (WT: wt_exp (E s t pe))
        (WB: wb_exp (E s t pe)),
        (good_sub_heap h1 /\ exists t', vtyp h1 v t' /\ sub' t' t))
    /\
    (forall
        h0 f f1 ds e2s v h1
        (FSPAR: fill_slots_par h0 f f1 ds e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        s1
        (FS: scopeofFrame V fh h0 f1 s1)
        (GH: good_sub_heap h0)
        t2s
        (TYPDECS: typofDecls T G s1 ds t2s)
        (WB: forall e,
            In e e2s ->
            expScope e = s /\ wb_exp e)
        (WT: Forall2 (fun (e : exp) (t : T) => sub' (expType e) t /\ wt_exp e) e2s
                     t2s),
        good_sub_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
    /\
    (forall
        h0 f dss e2s v h1
        (FSSEQ: fill_slots_seq h0 f dss e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (GH: good_sub_heap h0)
        t2s
        (TYPDECS: typofSDecls T G dss t2s)
        s'
        (WB1: ForallFold2 (fun ds e ps newPs =>
                             (linksofScopeP wc newPs [(P, [ps])]) /\
                             declsofScopeP wc newPs [(snd ds)] /\
                             newPs = fst ds /\
                             dynamicDecl newPs (snd ds) /\
                             (expScope e) = ps /\
                             wb_exp e)
                          dss e2s s s')
        (WT: Forall2 (fun (e : exp) (t : T) => sub' (expType e) t /\ wt_exp e) e2s
                     t2s),
        good_sub_heap h1 /\
        ((exists f, v = FrameAV f /\ scopeofFrame V fh h1 f s') \/
         v = AbortAV NullPointer))
    /\
    (forall
        h0 f ds e2s v h1
        (FSREC: fill_slots_rec h0 f ds e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (GH: good_sub_heap h0)
        t2s
        (TYPDEC: Forall2 (typofDecl T G s) ds t2s)
        (WB: forall e,
            In e e2s ->
            expScope e = s /\ wb_exp e)
        (WT: Forall2 (fun (e : exp) (t : T) =>
                        is_val e /\
                        match t with
                        | Tarrow _ _ => sub' (expType e) t
                        | _ => False
                        end /\
                        wt_exp e) e2s
                     t2s),
        good_sub_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
    /\
    (forall
        h0 f lhs v h1
        (EVAL: eval_lhs h0 f lhs v h1)
        s t
        (FS: scopeofFrame V fh h0 f s)
        (WB: wb_lhs s lhs)
        (WT: wt_lhs t lhs)
        (GH: good_sub_heap h0),
        good_sub_heap h1 /\ match v with
                            | AddrAV (Addr_ ff d) =>
                              exists s' ds,
                              scopeofFrame V fh h1 ff s' /\
                              declsofScopeP (@wc T dwc) s' ds /\
                              In d ds /\
                              typofDecl T G s' d t /\
                              good_sub_frame h1 ff
                            | AbortAV NullPointer => True
                            | _ => False
                            end) /\
    (forall
        h0 f s r v h1
        (EVAL: eval_objinit h0 f s r v h1)
        p' s' d
        (DR: rlookup wc s r p' s' d)
        (* (DR: dynamicDecl s' d) *)
        (DR: typofDecl T G s' d (TclassDef s' d))
        (FS: scopeofFrame V fh h0 f s)
        (FS: scopeofRefP wc r s)
        (GH: good_sub_heap h0),
        good_sub_heap h1 /\ match v with
                            | FrameAV rf =>
                              vtyp h1 (ObjectV rf) (Tclass s' d)
                            | AbortAV NullPointer => True
                            | _ => False
                            end) /\
    (forall
        h0 f0 f1 rss es v h1
        (ASREF: assign_refs h0 f0 f1 rss es v h1)
        s
        (FS: scopeofFrame V fh h0 f0 s)
        (WBE: forall e, In e es -> wb_exp e /\ expScope e = s)
        (WTE: Forall2 (fun e rs =>
                         match rs with
                         | (sr, r) =>
                           exists p s'' d' t',
                           rlookup wc sr r p s'' d' /\
                           typofDecl T G s'' d' t' /\ sub' (expType e) t' /\ wt_exp e
                         end) es rss)
        (GH: good_sub_heap h0)
        s'
        (FS: scopeofFrame V fh h0 f1 s')
        (SR: forall s0 r,
            In (s0, r) rss ->
            s0 = s' /\ scopeofRefP wc r s'),
        good_sub_heap h1 /\ (v = UnitAV \/ v = AbortAV NullPointer)).
  Proof.
    apply eval_exp_ind3; intros; simpl; try (inv UNPACK; inv WT; inv WB); subst; try (sgauto; fail).
    - (* plus good case *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
    - (* plus bad case 1 *)
      edestruct H; sgauto.
      destruct H1 as [? [VT SUB]]. eapply sub_int in SUB; subst; sgauto.
      inv VT0; sgauto; edestruct ABORTL; sgauto.
    - (* plus bad case 2 *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
      destruct H2 as [? [VT SUB]]. eapply sub_int in SUB; subst; sgauto.
      inv VT0; sgauto; edestruct ABORTR; sgauto.
    - (* gt good case *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
    - (* gt bad case 1 *)
      edestruct H; sgauto.
      destruct H1 as [? [VT SUB]]. eapply sub_int in SUB; subst; sgauto.
      inv VT0; sgauto; edestruct ABORTL; sgauto.
    - (* gt bad case 2 *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
      destruct H2 as [? [VT SUB]]. eapply sub_int in SUB; subst; sgauto.
      inv VT0; sgauto; edestruct ABORTR; sgauto.
    - (* lhs good case *)
      edestruct H as [? [? [? [SF [DS [IN [TD GF]]]]]]]; sgauto.
      inv GF. inv H2. eapply scopeofFrameDet in SF; eauto; subst.
      eapply declsofScopeDet in DS; eauto; subst.
      split; sgauto.
      edestruct WT as [? [VT' SUB']]; eauto.
    - (* lhs bad case 1 *)
      edestruct H; sgauto.
      destruct q; inv H1; sgauto.
    - (* lhs bad case 2 *)
      edestruct H as [? [? [? [? [SF [DS [IN [TD GF]]]]]]]]; eauto.
      intuition eauto.
      inv GF.
      eapply scopeofFrameDet in H1; eauto; subst.
      eapply declsofScopeDet in SF; eauto; subst.
      edestruct well_bound_get as [v P]; eauto.
      exfalso; eapply GET; eauto.
    - (* app good case *)
      edestruct H; sgauto. destruct H3 as [? [VT SUB]]. inv VT.
      eapply sub_tarrow in SUB; sgauto. destruct SUB as [? [? [EQ [FA SUB]]]]; inv EQ.
      eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H0; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. sgauto.
      edestruct H1 as [? [? [VT' SUB']]]; sgauto.
        eapply initNewDefaultFrameSame in NF. destruct NF. sgauto.
    - (* app default fun *)
      edestruct H; sgauto. destruct H1 as [? [VT SUB]].
      eapply sub_tarrow in SUB; sgauto. destruct SUB as [? [? [EQ [FA SUB]]]]; subst.
      inv VT0; sgauto.
    - (* app bad case 1 *)
      edestruct H; sgauto. destruct H1 as [? [VT SUB]].
      eapply sub_tarrow in SUB; sgauto. destruct SUB as [? [? [EQ [FA SUB]]]]; subst.
      inv VT0; inv ABORT1; sgauto.
    - (* app bad case 2 *)
      edestruct H; sgauto. destruct H2 as [? [VT SUB]]. inv VT.
      eapply sub_tarrow in SUB; sgauto. destruct SUB as [? [? [EQ [FA SUB]]]]; inv EQ.
      eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H0; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. sgauto.
      destruct H3 as [contra|contra]; inv contra; sgauto.
    - (* letpar good case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s1).
      { eapply scopeofFrameDet; sgauto. inv FS. econstructor.
        eapply initNewDefaultFrameDiff; sgauto. }
      subst.
      edestruct H; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. simpl in *. sgauto.
      edestruct H0; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. simpl in *. sgauto.
      destruct H4 as [? [VT SUB']]. sgauto.
    - (* letpar bad case 1 *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s1).
      { eapply scopeofFrameDet; sgauto. inv FS. econstructor.
        eapply initNewDefaultFrameDiff; sgauto. }
      subst.
      edestruct H; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. simpl in *. sgauto.
      destruct H1; inv H1; sgauto.
    - (* letseq good case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      edestruct H; sgauto. destruct H2. 2: inv H2. destruct H2 as [? [FEQ SF]]. inv FEQ.
      edestruct H0; sgauto.
      destruct H3 as [? [VT SUB']]. sgauto.
    - (* letseq bad case 1 *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      edestruct H; sgauto. destruct H1. destruct H1 as [? [FEQ SF]]. inv FEQ.
      inv H1; sgauto.
    - (* letrec good case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s0).
      { eapply scopeofFrameDet; sgauto. inv FS. econstructor.
        eapply initNewDefaultFrameDiff; sgauto. }
      subst.
      edestruct H; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. simpl in *. sgauto.
      edestruct H0; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. simpl in *. sgauto.
      destruct H4 as [? [VT SUB']]. sgauto.
    - (* letrec bad case 1 *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s0).
      { eapply scopeofFrameDet; sgauto. inv FS. econstructor.
        eapply initNewDefaultFrameDiff; sgauto. }
      subst.
      edestruct H; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. simpl in *. sgauto.
      destruct H1; inv H1; sgauto.
    - (* asgn good case *)
      edestruct H; sgauto. destruct H2 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0 as [? [? [VT SUB']]]; sgauto.
      split; sgauto. eapply setSlot_good_heap_sub; sgauto. simpl; sgauto.
    - (* asgn bad case 1 *)
      edestruct H; sgauto. destruct q; inv H1; sgauto.
    - (* asgn bad case 2 *)
      edestruct H; sgauto. destruct H2 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0 as [? [? [VT SUB']]]; sgauto.
    - (* asgn bad case 3 *)
      edestruct H; sgauto. destruct H2 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0 as [? [? [VT SUB']]]; sgauto.
      eapply eval_exp_scopeofFrame in SF; sgauto.
      assert (good_sub_frame h2 ff).
      { inv SF. eapply keys_in in H3. assert (frame h2 ff) by sgauto. eapply H2; auto. }
      eapply good_frame_setSlot_sub in H3; sgauto.
      destruct H3. eapply SET in H3; contradiction.
    - (* if good case t *) subst.
      edestruct H; sgauto.
    - (* if good case f *) subst.
      edestruct H; sgauto.
    - (* if bad case *) subst.
      edestruct H as [? [? [VT SUB']]]; sgauto.
      eapply sub_bool in SUB'; eauto; subst.
      destruct v1; inv VT0; sgauto.
      edestruct ABORT1; eauto.
    - (* seq good case *)
      edestruct H; sgauto.
    - (* seq bad case 1 *)
      edestruct H as [? [? [VT SUB']]]; sgauto.
      inv VT; sgauto.
    - (* new good case *)
      eapply rlookupDet in RL; sgauto. destruct RL as [? [? ?]]; subst.
      eapply assocScopeDet in ASC; eauto; subst.
      edestruct H; sgauto.
    - (* new bad case 1 *)
      eapply rlookupDet in RL; sgauto. destruct RL as [? [? ?]]; subst.
      eapply assocScopeDet in ASC; eauto; subst.
      edestruct H; sgauto. destruct av; try destruct H1, BAD.
      destruct e; sgauto; contradiction.
    - (* fill_par nil bad case 1 *)
      inv WT. inv TYPDECS. intuition.
    - (* fill_par nil bad case 2 *)
      inv TYPDECS. inv WT. intuition.
    - (* fill_par cons good case *)
      inv WT. destruct H3. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H3; subst.
      edestruct H as [? [? [VT SUB']]]; sgauto. simpl in *.
      eapply setSlot_good_heap_sub in H3; sgauto. Focus 2. simpl. sgauto.
      edestruct H0; sgauto.
    - (* fill_par cons bad case 1 *)
      inv WT. destruct H2. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H2; subst.
      edestruct H as [? [? [VT SUB]]]; sgauto.
      eapply eval_exp_scopeofFrame in FS0; sgauto.
      assert (good_sub_frame h1 fc).
      { inv FS0. eapply keys_in in H5. assert (frame h1 fc) by sgauto. eapply H; auto. }
      assert (exists ds, declsofScopeP wc s1 ds /\ In d ds).
      { inv H6. eexists; split. econstructor. split; sgauto. eapply keys_in in H9. assumption. }
      destruct H7 as [? [DS IN]].
      eapply good_frame_setSlot_sub in H5; sgauto.
      destruct H5. eapply SS in H5; contradiction.
    - (* fill_par cons bad case 2 *)
      inv WT. destruct H2. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H2; subst.
      edestruct H as [? [? [VT SUB]]]; sgauto. destruct q; inv VT; sgauto.
    - (* fill_seq nil good case *)
      inv WB1. sgauto.
    - (* fill_seq nil bad case 1 *)
      inv WB1. intuition.
    - (* fill_seq nil bad case 2 *)
      inv WB1. intuition.
    - (* fill_seq cons good case *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H3; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H as [? [? [VT SUB]]]; sgauto. inv FS. eapply initNewDefaultFrameDiff in NF; sgauto.
      assert (scopeofFrame V FH h2 fc sd).
      { eapply initNewDefaultFrameSame in NF. destruct NF.
        assert (scopeofFrame V FH h1 fc sd) by sgauto.
        eapply eval_exp_scopeofFrame in H6. 2: sgauto. auto. }
      edestruct H0; sgauto.
      eapply setSlot_good_heap_sub; sgauto. simpl; sgauto.
    - (* fill_seq cons bad case 1 *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H as [? [? [VT SUB]]]; sgauto. inv FS. eapply initNewDefaultFrameDiff in NF; sgauto.
      destruct q; inv VT; sgauto.
    - (* fill_seq cons bad case 2 *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H as [? [? [VT SUB]]]; sgauto. inv FS. eapply initNewDefaultFrameDiff in NF; sgauto.
      assert (scopeofFrame V FH h2 fc sd).
      { eapply initNewDefaultFrameSame in NF. destruct NF.
        assert (scopeofFrame V FH h1 fc sd) by sgauto.
        eapply eval_exp_scopeofFrame in H5. 2: sgauto. auto. }
      assert (frame h2 fc) by sgauto.
      specialize (H2 _ H5).
      eapply good_frame_setSlot_sub in H2; sgauto. 2: left; reflexivity.
      destruct H2; apply SS in H2; contradiction.
    - (* fill_rec nil bad case 1 *)
      inv WT. inv TYPDEC. intuition.
    - (* fill_rec nil bad case 2 *)
      inv TYPDEC. inv WT. intuition.
    - (* fill_rec cons good case *)
      inv WT. destruct H3 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H1; subst.
      assert (exists ts0 ts1, y = Tarrow ts0 ts1).
      { destruct y; inv ISFUN; eauto. } destruct H1 as [? [? EQ]]; subst. simpl in *.
      edestruct H as [? [? [VT SUB]]]; sgauto.
      edestruct H0; sgauto.
      eapply setSlot_good_heap_sub; sgauto. simpl; sgauto.
    - (* fill_rec cons bad case 1 *)
      inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      assert (exists ts0 ts1, y = Tarrow ts0 ts1).
      { destruct y; inv ISFUN; eauto. } destruct H0 as [? [? EQ]]; subst. simpl in *.
      edestruct H as [? [? [VT SUB]]]; sgauto.
      destruct q; inv VT; sgauto.
    - (* fill_rec cons bad case 2 *)
      inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      assert (exists ts0 ts1, y = Tarrow ts0 ts1).
      { destruct y; inv ISFUN; eauto. } destruct H0 as [? [? EQ]]; subst. simpl in *.

      edestruct H; sgauto.
      assert (good_sub_frame h1 frm).
      { eapply eval_exp_scopeofFrame in FS; sgauto. }
      assert (exists ds, declsofScopeP wc s0 ds /\ In d ds).
      { inv H3. eexists; split. econstructor. split; sgauto. eapply keys_in in H8. assumption. }
      destruct H7 as [? [DS IN]].
      eapply good_frame_setSlot_sub in H5; sgauto.
      destruct H5. eapply SS in H5; contradiction.
    - (* eval_lhs var good case *)
      split; sgauto. destruct a. inv WB; inv WT.
      eapply scopeofRefDet in SR; eauto; subst.
      eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
      simpl in *. eapply (good_addr_sub T ST V VT) in SR1; sgauto.
      destruct SR1. destruct H. eapply getAddrDet in ADDR; eauto; inv ADDR.
      assert (TD'':=TD).
      inv TD. eapply keys_in in H2.
      assert (SFF:=H0).
      eapply scopeofFrameFrame in H0. specialize (GH _ H0). inv GH.
      do 2 eexists; split; sgauto. split; sgauto.
      split; sgauto. split; sgauto. econstructor; sgauto.
    - (* eval_lhs var bad case *)
      split; sgauto. inv WB; inv WT.
      eapply scopeofRefDet in SR; eauto; subst.
      eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
      simpl in *. eapply (good_addr_sub T ST V VT) in SR1; sgauto.
      destruct SR1. destruct H. eapply ADDR; eauto.
    - (* eval_lhs field good case *)
      destruct a. inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? [VT SUB']]]; sgauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      eapply sub_tclass in SUB; eauto. destruct SUB as [? [? [? [EQ ASC']]]]; subst.
      inv VT.
      eapply upcast_scopeofFrame in UPCAST.
      assert (sd = rec_s).
      { destruct IMP as [? [? ?]]. inv LS0. rewrite H4 in H1; inv H1. inv H2.
        destruct (ELdec I I); intuition. inv H3; auto. } subst.
      split; sgauto.
      assert (scopeofFrame V FH h2 imp_f s').
      { eapply initNewDefaultFrameSame in SCF; sgauto. destruct SCF. sgauto. }
      eapply (good_addr_sub T ST V VT) in SR1. 3: eassumption. 2: sgauto.
      destruct SR1 as [? [ADDR' SF']]. eapply getAddrDet in ADDR; eauto; inv ADDR.
      assert (TD'':=TD).
      inv TD. eapply keys_in in H3.
      assert (SFF:=H3).
      do 2 eexists; split; sgauto. split; sgauto.
      split; sgauto. split; sgauto.
      eapply scopeofFrameFrame in SF'.
      assert (good_sub_heap h2); sgauto.
    - (* eval_lhs field good null case *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H; sgauto.
    - (* eval_lhs field bad case 1 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? [VT SUB']]]; sgauto.
      eapply sub_tclass in SUB; eauto. destruct SUB as [? [? [? [EQ ASC']]]]; subst.
      eapply sub_tclass in SUB'; eauto. destruct SUB' as [? [? [? [EQ ASC'']]]]; subst.
      destruct v; inv BAD; inv VT0; simpl; sgauto.
    - (* eval_lhs field bad case 2 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? [VT SUB']]]; sgauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      inversion VT; subst.
      assert (sub' (Tclass sd1 d) (Tclass sc sd0)) by sgauto.
      assert (sd = rec_s).
      { destruct IMP as [? [? ?]]. inv LS0. rewrite H5 in H2; inv H2. inv H3.
        destruct (ELdec I I); intuition. inv H4; auto. } subst.
      eapply sub_class_upcast in H1; sgauto. destruct H1.
      edestruct UPCAST; sgauto.
    - (* eval_lhs field bad case 3 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? [VT SUB']]]; sgauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      eapply sub_tclass in SUB; eauto. destruct SUB as [? [? [? [EQ ASC']]]]; subst.
      inv VT.
      eapply upcast_scopeofFrame in UPCAST.
      assert (sd = rec_s).
      { destruct IMP as [? [? ?]]. inv LS0. rewrite H4 in H1; inv H1. inv H2.
        destruct (ELdec I I); intuition. inv H3; auto. } subst.
      assert (scopeofFrame V FH h2 imp_f s').
      { eapply initNewDefaultFrameSame in SCF; sgauto. destruct SCF. sgauto. }
      assert (good_sub_heap h2). eapply initNewDefaultFrame_good_heap1_sub; sgauto.
      eapply (good_addr_sub T ST V VT) in SR1. 3: eassumption. 2: sgauto.
      destruct SR1 as [? [ADDR' SF']]. apply ADDR in ADDR'; contradiction.
    - (* eval_objinit good case 1 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      destruct ASR as [? [? [? [DR2 AS2]]]].
      eapply rlookupDet in DR2; sgauto. destruct DR2 as [? [? ?]]; subst.
      simpl in *. destruct SUBF. inv H4. eapply scopeofFrameDet in SF'; eauto; subst.
      eapply declsofScopeDet in DS'; eauto; subst.
      specialize (WT d (TclassDef x2 x3)). assert (IN':=IN). eapply WT in IN; eauto.

      destruct IN as [? [VT SUB]].
      inv VT. destruct OPTR as [? [SR [? [? [? [DR' [ASCR [DDR [TDR IMSR]]]]]]]]]; subst.
      eapply scopeofFrameDet in SF.
      2: eapply eval_objinit_scopeofFrame; sgauto. subst.
      edestruct H0 as [GH2 VT2]; sgauto.
      inv VT2.
      eapply assocScopeDet in ASCR; eauto; subst.
      eapply scopeofFrameDet in SFP; eauto; subst.
      inv SUB. 2: inv SUB1.

      eapply assocScopeDet in AS2; eauto; subst.
      assert (scopeofFrame V FH h3 rf s0).
      { eapply initNewDefaultFrameSame in RECF. destruct RECF. sgauto. }
      edestruct H1; sgauto.
      destruct H6; inv H6; sgauto. split; sgauto.
      econstructor; sgauto.
      eapply assign_refs_scopeofFrame; sgauto.
    - (* eval_objinit bad case 1 *)
      edestruct H as [GH' VT]; sgauto. destruct v; inv BAD; try inv VT.
      destruct e; sgauto.
    - (* eval_objinit bad case 2 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      inv LHS.
      eapply getAddr_getSlot_sub in ADDR; sgauto.
      destruct ADDR as [? [? [? [GS' [VT SUB]]]]].
      eapply GS in GS'; contradiction.
    - (* eval_objinit bad case 3 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      simpl in *. destruct SUBF. inv H2. eapply scopeofFrameDet in SF'; eauto; subst.
      eapply declsofScopeDet in DS'; eauto; subst.
      specialize (WT d (TclassDef s' d0)). assert (IN':=IN). eapply WT in IN; eauto.

      destruct IN as [? [VT SUB]].
      eapply sub_tclassdef in SUB; eauto. destruct SUB as [? [? EQ]]. subst.
      inv VT0; inv BAD; simpl; sgauto.
    - (* eval_objinit bad case 4 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      simpl in *. destruct SUBF. inv H3. eapply scopeofFrameDet in SF'; eauto; subst.
      eapply declsofScopeDet in DS'; eauto; subst.
      specialize (WT d (TclassDef s' d0)). assert (IN':=IN). eapply WT in IN; eauto.

      destruct IN as [? [VT SUB]].
      inv VT. destruct OPTR as [? [SR [? [? [? [DR' [ASCR [DDR [TDR IMSR]]]]]]]]]; subst.
      edestruct H0 as [GH2 VT2]; sgauto.
      destruct v; try inv VT2; sgauto.
    - (* eval_objinit bad case 5 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      destruct ASR as [? [? [? [DR2 AS2]]]].
      eapply rlookupDet in DR2; sgauto. destruct DR2 as [? [? ?]]; subst.
      simpl in *. destruct SUBF. inv H4. eapply scopeofFrameDet in SF'; eauto; subst.
      eapply declsofScopeDet in DS'; eauto; subst.
      specialize (WT d (TclassDef x2 x3)). assert (IN':=IN). eapply WT in IN; eauto.

      destruct IN as [? [VT SUB]].
      inv VT. destruct OPTR as [? [SR [? [? [? [DR' [ASCR [DDR [TDR IMSR]]]]]]]]]; subst.
      eapply scopeofFrameDet in SF.
      2: eapply eval_objinit_scopeofFrame; sgauto. subst.
      edestruct H0 as [GH2 VT2]; sgauto.
      inv VT2.
      eapply assocScopeDet in ASCR; eauto; subst.
      eapply scopeofFrameDet in SFP; eauto; subst.
      inv SUB. 2: inv SUB1.

      eapply assocScopeDet in AS2; eauto; subst.
      assert (scopeofFrame V FH h3 rf s0).
      { eapply initNewDefaultFrameSame in RECF. destruct RECF. sgauto. }
      edestruct H1; sgauto.
      destruct H6; inv H6; sgauto.
    - (* eval_objinit no parent good case *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      destruct ASR as [? [? [? [DR2 AS2]]]].
      eapply rlookupDet in DR2; sgauto. destruct DR2 as [? [? ?]]; subst.
      simpl in *. destruct SUBF. inv H3. eapply scopeofFrameDet in SF'; eauto; subst.
      eapply declsofScopeDet in DS'; eauto; subst.
      specialize (WT d (TclassDef x2 x3)). assert (IN':=IN). eapply WT in IN; eauto.

      destruct IN as [? [VT SUB]].

      simpl in *.
      inv VT.
      inv SUB. 2: inv SUB1.
      eapply assocScopeDet in AS2; eauto; subst.
      eapply scopeofFrameDet in SF; eauto; subst.
      assert (scopeofFrame V FH h2 rf s0).
      { eapply initNewDefaultFrameSame in RECF. destruct RECF. sgauto. }
      edestruct H0 as [GH2 VT2]; sgauto.
      split; sgauto; destruct VT2. econstructor; sgauto.
      eapply assign_refs_scopeofFrame; sgauto. inv H4.
    - (* eval_objinit no parent bad case 1 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      inv LHS.
      eapply getAddr_getSlot_sub in ADDR; sgauto.
      destruct ADDR as [? [? [? [GS' [VT SUB]]]]].
      eapply GS in GS'; contradiction.
    - (* eval_objinit no parent bad case 2 *)
      edestruct H as [? [? [? [SF' [DS' [IN [TD SUBF]]]]]]]; sgauto.
      destruct ASR as [? [? [? [DR2 AS2]]]].
      eapply rlookupDet in DR2; sgauto. destruct DR2 as [? [? ?]]; subst.
      simpl in *. destruct SUBF. inv H3. eapply scopeofFrameDet in SF'; eauto; subst.
      eapply declsofScopeDet in DS'; eauto; subst.
      specialize (WT d (TclassDef x2 x3)). assert (IN':=IN). eapply WT in IN; eauto.

      destruct IN as [? [VT SUB]].

      simpl in *.
      inv VT.
      inv SUB. 2: inv SUB1.
      eapply assocScopeDet in AS2; eauto; subst.
      eapply scopeofFrameDet in SF; eauto; subst.
      assert (scopeofFrame V FH h2 rf s0).
      { eapply initNewDefaultFrameSame in RECF. destruct RECF. sgauto. }
      edestruct H0 as [GH2 VT2]; sgauto.
      split; sgauto; destruct VT2; subst; simpl; sgauto.
    - (* assign_refs good case *)
      edestruct WBE; [econstructor; reflexivity|].
      inv WTE. destruct H6 as [? [? [? [? [RL [TD [SUB WT]]]]]]].
      destruct e; simpl in *; subst.
      edestruct H as [? [? [VT' SUB']]]; sgauto.
      edestruct H0; sgauto.
      edestruct SR; eauto; subst.
      eapply (good_addr_sub T ST V VT) in RL.
      3: eauto. 2: eauto.
      destruct RL as [? [GA SF]].
      eapply getAddrDet in ADDR; eauto. inv ADDR.
      eapply setSlot_good_heap_sub; sgauto. simpl; sgauto.
    - (* assign_refs bad case 1 *)
      inv WTE. destruct H; auto.
    - (* assign_refs bad case 2 *)
      inv WTE. destruct H; auto.
    - (* assign_refs bad case 3 *)
      edestruct WBE; [econstructor; reflexivity|].
      inv WTE. destruct H5 as [? [? [? [? [RL [TD [SUB WT]]]]]]].
      destruct e; simpl in *; subst.
      edestruct H as [? [? [VT' SUB']]]; sgauto.
      inv VT'; sgauto.
  Qed.

  Lemma init_decls_sound :
    forall
      h0 frm ds h1
      (IDs: init_decls h0 frm ds h1)
      s
      (WT: wt_decls ds)
      (WB: wb_decls s ds)
      (GH: good_sub_heap h0)
      (SF: scopeofFrame V fh h0 frm s),
      good_sub_heap h1 /\ scopeofFrame V fh h1 frm s.
  Proof.
    induction 1; intros; eauto.
    inv WT; inv WB. rewrite <- EQ in EQ0. inv EQ0.
    assert (vtyp h0 (ConstructorV s rd optr (unzipfs fds) frm) (TclassDef s rd)).
    rewrite <- EQ. eapply assocScopeDet in SD; eauto; subst.
    econstructor; sgauto.
    destruct optr. destruct p.
    destruct PARENT0 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]. subst.
    split; eauto 10. assumption.
    eapply IHIDs; eauto using setSlotScope, setSlot_good_heap.
    eapply setSlot_good_heap_sub; sgauto. simpl. constructor.
  Qed.

  Lemma prog_sound :
    forall
      p v
      (WT: wt_prog p)
      (WB: wb_prog p)
      (EVAL: eval_prog p v),
      ~ v = AbortV Wrong.
  Proof.
    intros. inv EVAL.
    inv WT. simpl in TOPFRM.
    inv WB.
    assert (scopeofFrame V fh h0 f s).
    { eapply initNewDefaultFrameSame in TOPFRM. destruct TOPFRM; sgauto. }
    assert (good_sub_heap h0).
    { intros f0 FR.
      assert (f0 = f).
      inv TOPFRM.
      inv NF.
      eapply fillFrameFrames in FF. apply FF in FR.
      pose proof (newFrameFrames _ _ _ _ _ _ _ NF0 f0). apply H0 in FR. inv FR.
      auto. exfalso. eapply emptyHeapNoFrames; eauto.
      inversion TOPFRM; subst.
      inv NF. inv NF0. eapply declsofScopeDet in DS; eauto; subst.
      econstructor.
      + econstructor; sgauto.
        * intros. inv DS0. destruct H2. inv H1. simpl in *; rewrite H5 in H2; inv H2.
          inv FF. inv H1. inv H2. destruct H1. subst.
          eexists; split; sgauto. econstructor.
          rewrite get_set_same. reflexivity. rewrite H3.
          split; auto.
        * inv FF. inv H1. inv H2. destruct H1. subst.
          intros. inv H1. destruct (FrameIdDec f f); intuition. inv H4.
          inv H2. rewrite get_set_same in H1. inv H1. inv DS0. destruct H1. rewrite H2.
          eexists; split; sgauto. split; auto.
        * intros. inv H1. inv H2. inv LS. simpl in *. rewrite H4 in H1; inv H1. inv H3.
        * intros.
          inv FF. inv H2. inv H3. destruct H2. subst. inv H1. inv H3.
          rewrite get_set_same in H2. inv H2.
          rewrite get_set_same in H1. inv H1. inv H4.
      + econstructor; sgauto.
        intros.
        inv H3.
        inv FF. destruct H3 as [? [? [GET H']]]. subst.
        rewrite get_set_same in H4. inv H4. rewrite get_set_same in GET. inv GET.
        eapply defaults_vtyp' in DF; sgauto.
        eexists; split; eauto. simpl; sgauto.
        eapply keys_in; eauto.
    }
    edestruct init_decls_sound as [ID _]; eauto.
    destruct exp_preservation as [expP _].
    edestruct expP; sgauto.
    intro; subst v. destruct H2 as [? [? _]]. inv H2.
  Qed.

End TypeSoundness.
