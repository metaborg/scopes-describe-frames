Require Import L2.semantics prop_fold.

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
      vtyp' h (RecordV f) (Trecord sd d)
(* Null values are typed by both records: *)
| vtyp'_nr : forall sd d, vtyp' h NullV (Trecord sd d)
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
| def_r : forall sd d, default (Trecord sd d) NullV
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
          scopeofFrame V fh h1 f s).
  Proof.
    apply eval_exp_ind3; sgauto.
  Qed.

  Definition eval_exp_scopeofFrame     := proj1 eval_exp_scopeofFrame_aux.
  Definition fill_par_scopeofFrame     := proj1 (proj2 eval_exp_scopeofFrame_aux).
  Definition fill_seq_scopeofFrame     := proj1 (proj2 (proj2 eval_exp_scopeofFrame_aux)).
  Definition fill_rec_scopeofFrame     := proj1 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).
  Definition eval_lhs_scopeofFrame     := proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).

  Hint Resolve eval_exp_scopeofFrame : sgraph.
  Hint Resolve fill_par_scopeofFrame : sgraph.
  Hint Resolve fill_seq_scopeofFrame : sgraph.
  Hint Resolve fill_rec_scopeofFrame : sgraph.
  Hint Resolve eval_lhs_scopeofFrame : sgraph.
  Hint Unfold abort : sgraph.
  Hint Constructors vtyp' : sgraph.

  Lemma exp_preservation:
    (forall
        h0 f e v h1
        (EVAL: eval_exp h0 f e v h1)
        s t pe
        (UNPACK: e = (E s t pe))
        (FS: scopeofFrame V fh h0 f s)
        (GH: good_heap T V VT h0)
        (WT: wt_exp (E s t pe))
        (WB: wb_exp (E s t pe)),
        (good_heap T V VT h1 /\ vtyp h1 v t))
    /\
    (forall
        h0 f f1 ds e2s v h1
        (FSPAR: fill_slots_par h0 f f1 ds e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        s1
        (FS: scopeofFrame V fh h0 f1 s1)
        (GH: good_heap T V VT h0)
        t2s
        (TYPDECS: typofDecls T G s1 ds t2s)
        (WB: forall e,
            In e e2s ->
            expScope e = s /\ wb_exp e)
        (WT: Forall2 (fun (e : exp) (t : T) => expType e = t /\ wt_exp e) e2s
                     t2s),
        good_heap T V VT h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
    /\
    (forall
        h0 f dss e2s v h1
        (FSSEQ: fill_slots_seq h0 f dss e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (GH: good_heap T V VT h0)
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
        (WT: Forall2 (fun (e : exp) (t : T) => expType e = t /\ wt_exp e) e2s
                     t2s),
        good_heap T V VT h1 /\ ((exists f, v = FrameAV f /\ scopeofFrame V fh h1 f s') \/
                                v = AbortAV NullPointer))
    /\
    (forall
        h0 f ds e2s v h1
        (FSREC: fill_slots_rec h0 f ds e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (GH: good_heap T V VT h0)
        t2s
        (TYPDEC: Forall2 (typofDecl T G s) ds t2s)
        (WB: forall e,
            In e e2s ->
            expScope e = s /\ wb_exp e)
        (WT: Forall2 (fun (e : exp) (t : T) =>
                        is_val e /\
                        match t with
                        | Tarrow _ _ => t = expType e
                        | _ => False
                        end /\
                        wt_exp e) e2s
                     t2s),
        good_heap T V VT h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
    /\
    (forall
        h0 f lhs v h1
        (EVAL: eval_lhs h0 f lhs v h1)
        s t
        (FS: scopeofFrame V fh h0 f s)
        (WB: wb_lhs s lhs)
        (WT: wt_lhs t lhs)
        (GH: good_heap T V VT h0),
        good_heap T V VT h1 /\ match v with
                               | AddrAV (Addr_ ff d) =>
                                 exists s' ds,
                                 scopeofFrame V fh h1 ff s' /\
                                 declsofScopeP (@wc T dwc) s' ds /\
                                 In d ds /\
                                 typofDecl T G s' d t /\
                                 good_frame T V VT h1 ff
                               | AbortAV NullPointer => True
                               | _ => False
                               end).
  Proof.
    apply eval_exp_ind3; intros; simpl; try (inv UNPACK; inv WT; inv WB); subst; try (sgauto; fail).
    - (* plus good case *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
    - (* plus bad case 1 *)
      edestruct H; sgauto.
      inv H1; sgauto; edestruct ABORTL; sgauto.
    - (* plus bad case 2 *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
      inv H2; sgauto; edestruct ABORTR; sgauto.
    - (* gt good case *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
    - (* gt bad case 1 *)
      edestruct H; sgauto.
      inv H1; sgauto; edestruct ABORTL; sgauto.
    - (* gt bad case 2 *)
      edestruct H0; sgauto.
      edestruct H; sgauto.
      inv H2; sgauto; edestruct ABORTR; sgauto.
    - (* lhs good case *)
      edestruct H as [? [? [? [SF [DS [IN [TD GF]]]]]]]; sgauto.
      inv GF. inv H2. eapply scopeofFrameDet in SF; eauto; subst.
      eapply declsofScopeDet in DS; eauto; subst.
      split; sgauto. eapply WT; sgauto.
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
      edestruct H; sgauto. inv H3. eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H0; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. sgauto.
      edestruct H1; sgauto. eapply initNewDefaultFrameSame in NF. destruct NF. sgauto.
    - (* app bad case 1 *)
      edestruct H; sgauto. inv H1; sgauto.
    - (* app bad case 2 *)
      edestruct H; sgauto.
      destruct v1; inv ABORT1; inv H1; sgauto.
    - (* app bad case 3 *)
      edestruct H; sgauto. inv H2. eapply scopeofFrameDet in SF; eauto; subst.
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
      edestruct H0; sgauto.
    - (* asgn bad case 1 *)
      edestruct H; sgauto. destruct q; inv H1; sgauto.
    - (* asgn bad case 2 *)
      edestruct H; sgauto. destruct H2 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0; sgauto.
    - (* asgn bad case 3 *)
      edestruct H; sgauto. destruct H2 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0; sgauto.
      eapply eval_exp_scopeofFrame in SF; sgauto.
      assert (good_frame T V VT h2 ff).
      { inv SF. eapply keys_in in H4. assert (frame h2 ff) by sgauto. eapply H2; auto. }
      eapply good_frame_setSlot in H4; sgauto.
      destruct H4. eapply SET in H4; contradiction.
    - (* if good case t *) subst.
      edestruct H; sgauto.
      edestruct H0; sgauto.
    - (* if good case f *) subst.
      edestruct H; sgauto.
      edestruct H0; sgauto.
    - (* if bad case *) subst.
      edestruct H; sgauto.
      destruct v1; inv H1; sgauto.
      edestruct ABORT1; eauto.
    - (* seq good case *)
      edestruct H; sgauto.
      edestruct H0; sgauto.
    - (* seq bad case 1 *)
      edestruct H; sgauto.
      inv H1; sgauto.
    - (* new good case *)
      eapply rlookupDet in RLOOK; eauto. destruct RLOOK as [? [? ?]]; subst.
      eapply rlookupDet in RL; eauto. destruct RL as [? [? ?]]; subst.
      eapply assocScopeDet in ASC; eauto; subst.
      split.
      + eapply initNewDefaultFrame_good_heap; sgauto.
        intros. inv H. destruct H0.
        inv PS. simpl in *. rewrite H2 in H; inv H. inv H0. intros. inv H.
      + econstructor; sgauto. eapply initNewDefaultFrameSame in RECF; sgauto.
        destruct RECF. sgauto.
    - (* new bad case 1 *)
      edestruct RLOOK; sgauto.
    - (* fill_par nil bad case 1 *)
      inv WT. inv TYPDECS. intuition.
    - (* fill_par nil bad case 2 *)
      inv TYPDECS. inv WT. intuition.
    - (* fill_par cons good case *)
      inv WT. destruct H3. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H1; subst.
      edestruct H; sgauto.
      edestruct H0; sgauto. intros. eapply WB. right; auto.
    - (* fill_par cons bad case 1 *)
      inv WT. destruct H2. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      edestruct H; sgauto.
      eapply eval_exp_scopeofFrame in FS0; sgauto.
      assert (good_frame T V VT h1 fc).
      { inv FS0. eapply keys_in in H5. assert (frame h1 fc) by sgauto. eapply H0; auto. }
      assert (exists ds, declsofScopeP wc s1 ds /\ In d ds).
      { inv H6. eexists; split. econstructor. split; sgauto. eapply keys_in in H9. assumption. }
      destruct H7 as [? [DS IN]].
      eapply good_frame_setSlot in H5; sgauto.
      destruct H5. eapply SS in H5; contradiction.
    - (* fill_par cons bad case 2 *)
      inv WT. destruct H2. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      edestruct H; sgauto. destruct q; inv H3; sgauto.
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
      edestruct H; sgauto. inv FS. eapply initNewDefaultFrameDiff in NF; sgauto.
      assert (scopeofFrame V FH h2 fc sd).
      { eapply initNewDefaultFrameSame in NF. destruct NF.
        assert (scopeofFrame V FH h1 fc sd) by sgauto.
        eapply eval_exp_scopeofFrame in H7. 2: sgauto. auto. }
      edestruct H0; sgauto.
    - (* fill_seq cons bad case 1 *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H; sgauto. inv FS. eapply initNewDefaultFrameDiff in NF; sgauto.
      destruct q; inv H2; sgauto.
    - (* fill_seq cons bad case 2 *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      edestruct H; sgauto. inv FS. eapply initNewDefaultFrameDiff in NF; sgauto.
      assert (scopeofFrame V FH h2 fc sd).
      { eapply initNewDefaultFrameSame in NF. destruct NF.
        assert (scopeofFrame V FH h1 fc sd) by sgauto.
        eapply eval_exp_scopeofFrame in H6. 2: sgauto. auto. }
      assert (frame h2 fc) by sgauto.
      specialize (H0 _ H6).
      eapply good_frame_setSlot in H0; sgauto. 2: left; reflexivity.
      destruct H0; apply SS in H0; contradiction.
    - (* fill_rec nil bad case 1 *)
      inv WT. inv TYPDEC. intuition.
    - (* fill_rec nil bad case 2 *)
      inv TYPDEC. inv WT. intuition.
    - (* fill_rec cons good case *)
      inv WT. destruct H3 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H1; subst.
      destruct y; inv ISFUN. simpl in *; subst.
      edestruct H; sgauto.
      edestruct H0; sgauto.
    - (* fill_rec cons bad case 1 *)
      inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      destruct y; inv ISFUN. simpl in *; subst.
      edestruct H; sgauto.
      destruct q; inv H2; sgauto.
    - (* fill_rec cons bad case 2 *)
      inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      destruct y; inv ISFUN. simpl in *; subst.
      edestruct H; sgauto.
      assert (good_frame T V VT h1 frm).
      { eapply eval_exp_scopeofFrame in FS; sgauto.
        inv FS. eapply keys_in in H5. assert (frame h1 frm) by sgauto. eapply H0; auto. }
      assert (exists ds, declsofScopeP wc s0 ds /\ In d ds).
      { inv H3. eexists; split. econstructor. split; sgauto. eapply keys_in in H8. assumption. }
      destruct H7 as [? [DS IN]].
      eapply good_frame_setSlot in H5; sgauto.
      destruct H5. eapply SS in H5; contradiction.
    - (* eval_lhs var good case *)
      split; sgauto. destruct a. inv WB; inv WT.
      eapply scopeofRefDet in SR; eauto; subst.
      eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
      simpl in *. eapply (good_addr T V VT) in SR1; sgauto.
      destruct SR1. destruct H. eapply getAddrDet in ADDR; eauto; inv ADDR.
      assert (TD'':=TD).
      inv TD. eapply keys_in in H2.
      assert (SFF:=H0).
      eapply scopeofFrameFrame in H0. specialize (GH _ H0). inv GH.
      do 2 eexists; split; sgauto. split; sgauto.
    - (* eval_lhs var bad case *)
      split; sgauto. inv WB; inv WT.
      eapply scopeofRefDet in SR; eauto; subst.
      eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
      simpl in *. eapply (good_addr T V VT) in SR1; sgauto.
      destruct SR1. destruct H. eapply ADDR; eauto.
    - (* eval_lhs field good case *)
      destruct a. inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H; sgauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      inv H1. eapply scopeofFrameDet in SF; eauto; subst. eapply assocScopeDet in ASC; eauto; subst.
      assert (good_heap T V VT h2) by sgauto.
      assert (scopeofFrame V FH h2 scf s').
      { eapply initNewDefaultFrameSame in SCF; sgauto. destruct SCF. sgauto. }
      eapply (good_addr T V VT) in H2; sgauto.
      destruct H2. destruct H2. eapply getAddrDet in ADDR; eauto; inv ADDR.
      assert (TD'':=TD).
      inv TD. eapply keys_in in H5.
      assert (SFF:=H3).
      eapply scopeofFrameFrame in H3. split; auto. specialize (H1 _ H3). inv H1.
      do 2 eexists; split; sgauto. split; sgauto.
    - (* eval_lhs field good null case *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H; sgauto.
    - (* eval_lhs field bad case 1 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H; sgauto.
      destruct v; inv BAD; inv H1; simpl; sgauto.
    - (* eval_lhs field bad case 2 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H; sgauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      inv H1. eapply scopeofFrameDet in SF; eauto; subst. eapply assocScopeDet in ASC; eauto; subst.
      assert (good_heap T V VT h2) by sgauto.
      assert (scopeofFrame V FH h2 scf s').
      { eapply initNewDefaultFrameSame in SCF; sgauto. destruct SCF. sgauto. }
      eapply (good_addr T V VT) in H2; sgauto.
      destruct H2. destruct H2. apply ADDR in H2; contradiction.
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
    assert (good_heap T V VT h0).
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
        intros. eapply defaults_vtyp' in DF; sgauto. inv H3.
        inv FF. destruct H3 as [? [? [GET H']]]. subst.
        rewrite get_set_same in H4. inv H4. rewrite get_set_same in GET. inv GET.
        symmetry; auto.
    }
    destruct exp_preservation as [expP _].
    edestruct expP; sgauto.
    intro; subst v. inv H2.
  Qed.

End TypeSoundness.
