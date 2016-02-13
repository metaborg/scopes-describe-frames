Require Import L2.GCsemantics prop_fold.


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

Lemma removeFrames_vtyp:
  forall
    (G: @WCGAT T) fs h1 h2 v0 t0
    (RF: removeFrames V FH h1 fs h2)
    (NR: forall f, vrefers v0 f -> ~ In f fs)
    (VT: vtyp h1 v0 t0),
    vtyp h2 v0 t0.
Proof.
  intros. induction RF. auto.
  apply IHRF.  intros. intro. eapply NR; eauto.  right;auto.
  clear IHRF RF.
  induction VT0; try constructor. 

  intros. econstructor; eauto. 
  eapply removeFrameScope; eauto.  split; auto. 
  intro. subst.  eapply NR.  eapply vr_clos; eauto. left; auto.

  eapply IHVT0.  intros.  apply NR. eapply vr_deffun; eauto.

  econstructor; eauto.
  eapply removeFrameScope; eauto.  split; auto.
  intro. subst. eapply NR. eapply vr_record. eauto. left; auto.
Qed.

(* A Hint database for list membership operations. *)
Hint Resolve in_eq : ins.  
Hint Resolve in_cons : ins.

Lemma in_2 : forall {A:Type} (x1 x2 y: A) (xs:list A), In y (x1::xs) -> In y (x1::x2::xs).
Proof.
  intros. inv H; eauto with ins. 
Qed.

Hint Resolve in_2 : ins. 

Section TypeSoundness.

  Context (G: @WCGAT T).

  Lemma eval_exp_scopeofFrame_aux :
    (forall h0 f0 roots e v h1,
        @eval_exp G VT DVT h0 f0 roots e v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          In f (f0::roots) -> 
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 roots e v h1,
        @eval_lhs G VT DVT h0 f0 roots e v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          In f (f0::roots) -> 
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 roots f1 ds es v h1,
        @fill_slots_par G VT DVT h0 f0 roots f1 ds es v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          In f (f0::roots) -> 
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 roots ds es v h1,
        @fill_slots_seq G VT DVT h0 f0 roots ds es v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          In f (f0::roots) -> 
          scopeofFrame V fh h1 f s) /\
    (forall h0 f0 roots ds es v h1,
        @fill_slots_rec G VT DVT h0 f0 roots ds es v h1 ->
        forall f s,
          scopeofFrame V fh h0 f s ->
          In f (f0::roots) -> 
          scopeofFrame V fh h1 f s).
  Proof.
    apply eval_exp_ind3; [| (eauto 7 using initNewDefaultFrameScope, setSlotScope with ins)  ..].
    intros. eapply H3; eauto. eapply removeFramesScope; intuition eauto.
  Qed.

  Definition eval_exp_scopeofFrame     := proj1 eval_exp_scopeofFrame_aux.
  Definition eval_lhs_scopeofFrame     := proj1 (proj2 eval_exp_scopeofFrame_aux).
  Definition fill_par_scopeofFrame     := proj1 (proj2 (proj2 eval_exp_scopeofFrame_aux)).
  Definition fill_seq_scopeofFrame     := proj1 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).
  Definition fill_rec_scopeofFrame     := proj2 (proj2 (proj2 (proj2 eval_exp_scopeofFrame_aux))).

  Hint Resolve eval_exp_scopeofFrame : sgraph.
  Hint Resolve eval_lhs_scopeofFrame : sgraph.
  Hint Resolve fill_par_scopeofFrame : sgraph.
  Hint Resolve fill_seq_scopeofFrame : sgraph.
  Hint Resolve fill_rec_scopeofFrame : sgraph.
  Hint Unfold abort : sgraph.
  Hint Constructors vtyp' : sgraph.


  Definition good_roots (h: H) (fs: list FrameId) : Prop := (forall f, In f fs -> frame h f). 



  Lemma removeFrame_good_roots: forall h0 fs h1 f,
                                  removeFrame V FH h0 f h1 ->
                                  good_roots h0 fs ->
                                  ~In f fs ->
                                  good_roots h1 fs.
  Proof. 
    unfold good_roots; intros.
    eapply removeFrameFrames; eauto. 
    intuition (try subst; auto). 
  Qed.

  Lemma removeFrames_good_roots : forall h0 rs h1 fs,
                                    removeFrames V FH h0 fs h1 -> 
                                    good_roots h0 rs -> 
                                    (forall f, In f fs -> ~ In f rs) -> 
                                    good_roots h1 rs. 
  Proof.
    intros. induction H.  auto.
    eauto 7 using removeFrame_good_roots with ins. 
  Qed.

  Lemma initNewDefaultFrame_good_roots: forall h0 fs h1 default ks s f,
                                          initNewDefaultFrame default h0 s ks f h1 -> 
                                          good_roots h0 fs -> 
                                          good_roots h1 (f::fs).
  Proof.
    unfold good_roots; intros.
    eapply initNewDefaultFrameFrames; eauto.  inv H1. left; auto. right; eauto. 
  Qed.

  Lemma setSlot_good_roots: forall h0 fs f d v h1,
                              setSlot V FH h0 f d v h1 -> 
                              good_roots h0 fs -> 
                              good_roots h1 fs.
  Proof.
    unfold good_roots; intros.
    erewrite <- setSlotFrames; eauto.
  Qed.


  (* Some silly utility lemmas to improve automation *)

Lemma good_roots_swap: 
    forall h f1 f2 r, 
      good_roots h (f1::f2::r) ->
      good_roots h (f2::f1::r).
  Proof.
    unfold good_roots; intros.
    apply H. inv H0.  right;left;auto.
    inv H1. left; auto. right; right; auto.
  Qed.
    
  Lemma good_roots_drop:
    forall h f r,
      good_roots h (f::r) -> 
      good_roots h r.
  Proof.
    unfold good_roots; intros.
    apply H.  right; auto.
  Qed.


  Lemma good_roots_drop2:
    forall h f1 f2 r,
      good_roots h (f1::f2::r) -> 
      good_roots h (f2::r).
  Proof.
    unfold good_roots; intros.
    apply H. inv H0.  right;left;auto. right;right;auto.
  Qed.

  Lemma good_roots_decomp:
    forall h f r,
      frame h f -> 
      good_roots h r ->
      good_roots h (f::r).
  Proof.
    unfold good_roots; intros.
    inv H1. auto. 
    apply H0; auto. 
  Qed.


  (* An alternative, more selective hint database for this proof. *)
  Hint Constructors vtyp' : pres. 
  Hint Resolve eval_exp_scopeofFrame : pres.
  Hint Resolve fill_par_scopeofFrame : pres.
  Hint Resolve fill_seq_scopeofFrame : pres.
  Hint Resolve fill_rec_scopeofFrame : pres.
  Hint Resolve eval_lhs_scopeofFrame : pres.
  Hint Resolve initNewDefaultFrameScope : pres.
  Hint Resolve eval_exp_scopeofFrame : pres.
  Hint Resolve initNewDefaultFrame_good_roots : pres.
  Hint Resolve initNewDefaultFrameSame_scopeofFrame : pres.
  Hint Resolve initNewDefaultFrame_good_heap1 : pres.
  Hint Resolve setSlot_good_roots : pres. 
  Hint Resolve setSlot_good_heap : pres.
  Hint Resolve setSlot_vtyp' : pres.
  Hint Resolve setSlotScope : pres.     
  Hint Resolve scopeofFrameFrame : pres.
  Hint Resolve good_roots_swap : pres. 
  Hint Resolve good_roots_drop : pres.
  Hint Resolve good_roots_drop2 : pres.
  Hint Resolve good_roots_decomp : pres.

  Ltac peauto := eauto with pres ins.

  Lemma exp_preservation:
    (forall
        h0 f roots e v h1
        (EVAL: @eval_exp G VT DVT h0 f roots e v h1)
        s t pe
        (UNPACK: e = (E s t pe))
        (FS: scopeofFrame V fh h0 f s)
        (GR: good_roots h0 (f::roots))
        (GH: good_heap T V VT h0)
        (WT: wt_exp (E s t pe))
        (WB: wb_exp (E s t pe)),
        (good_roots h1 (f::roots) /\ good_heap T V VT h1 /\ vtyp h1 v t))
    /\
    (forall
        h0 f roots lhs v h1
        (EVAL: eval_lhs h0 f roots lhs v h1)
        s t
        (FS: scopeofFrame V fh h0 f s)
        (WB: wb_lhs s lhs)
        (WT: wt_lhs t lhs)
        (GR: good_roots h0 (f::roots))
        (GH: good_heap T V VT h0),
        good_roots h1 (f::roots) /\
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
                               end)
    /\
    (forall
        h0 f roots f1 ds e2s v h1
        (FSPAR: fill_slots_par h0 f roots f1 ds e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (FCR: In f1 roots)   (* maybe better ways to handle this *)
        (GR: good_roots h0 (f::roots))
        s1
        (FS1: scopeofFrame V fh h0 f1 s1)
        (GH: good_heap T V VT h0)
        t2s
        (TYPDECS: typofDecls T G s1 ds t2s)
        (WB: forall e,
            In e e2s ->
            expScope e = s /\ wb_exp e)
        (WT: Forall2 (fun (e : exp) (t : T) => expType e = t /\ wt_exp e) e2s
                     t2s),
        good_roots h1 (f::roots) /\ good_heap T V VT h1 /\ (v = UnitAV \/ v = AbortAV NullPointer))
    /\
    (forall
        h0 f roots dss e2s v h1
        (FSSEQ: fill_slots_seq h0 f roots dss e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (GR: good_roots h0 (f::roots))
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
        good_roots h1 (f::roots) /\
        good_heap T V VT h1 /\ ((exists f, v = FrameAV f /\ scopeofFrame V fh h1 f s') \/
                                v = AbortAV NullPointer))
    /\
    (forall
        h0 f roots ds e2s v h1
        (FSREC: fill_slots_rec h0 f roots ds e2s v h1)
        s
        (FS: scopeofFrame V fh h0 f s)
        (GR: good_roots h0 (f::roots))
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
        good_roots h1 (f::roots) /\ good_heap T V VT h1 /\ (v = UnitAV \/ v = AbortAV NullPointer)).
  Proof.
      apply eval_exp_ind3; intros; [| (simpl; try (inv UNPACK; inv WT; inv WB); subst) ..].  
    - (* GC case *)
      eapply H3; eauto.
      eapply removeFramesScope; eauto. split; auto. intro; subst.  eapply H1. eauto. left; auto.
      eapply removeFrames_good_roots; eauto. 
      eapply good_heap_drop_safely; eauto. intros. eapply removeFrames_vtyp; eauto.
      econstructor; eauto. 
    - (* cnum *)
      peauto.
    - (* true *)
      peauto.
    - (* false *)
      peauto.
    - (* plus good case *)
      edestruct H as [? [? ?]]; eauto.  
      edestruct H0 as [? [? ?]]; peauto.
    - (* plus bad case 1 *)
      edestruct H as [? [? VT1]]; eauto. 
      intuition auto. 
      inv VT1; simpl; eauto with ins pres. 
      edestruct ABORTL; eauto.
    - (* plus bad case 2 *)
      edestruct H as [? [? ?]]; eauto.
      edestruct H0 as [? [? VT2]]; peauto.
      intuition auto.
      inv VT2; eauto with ins pres. 
      edestruct ABORTR; eauto. 
    - (* gt good case *)
      edestruct H as [? [? ?]]; eauto.
      edestruct H0 as [? [? ?]]; peauto.
    - (* gt bad case 1 *)
      edestruct H as [? [? VT1]]; eauto. 
      intuition auto. 
      inv VT1; simpl; peauto. 
      edestruct ABORTL; eauto.
    - (* gt bad case 2 *)
      edestruct H as [? [? ?]]; eauto.
      edestruct H0 as [? [? VT2]]; peauto.
      intuition auto.
      inv VT2; peauto. 
      edestruct ABORTR; eauto. 
    - (* lhs good case *)
      edestruct H as [? [? [? [? [SF [DS [IN [TD GF]]]]]]]]; eauto.  
      intuition auto. 
      inv GF. inv H3.  eapply scopeofFrameDet in SF; eauto; subst.
      eapply declsofScopeDet in DS; eauto; subst.
      eapply WT; eauto. 
    - (* lhs bad case 1 *)
      edestruct H; eauto.  
      destruct q; inv H1; intuition peauto.
    - (* lhs bad case 2 *)
      edestruct H as [? [? [? [? [SF [DS [IN [TD GF]]]]]]]]; eauto.
      intuition eauto.
      inv GF.  edestruct well_bound_get as [v P]; eauto.
      exfalso; eapply GET; eauto. 
    - (* fn *)
      peauto.
    - (* app good case *)
      edestruct H as [? [? VT]]; peauto. inv VT. 
      eapply scopeofFrameDet in SF; eauto; subst. 
      edestruct H0 as [? [? _]]; peauto. 
      edestruct H1 as [? [? ?]]; peauto. 
    - (* app dfun case *)
      edestruct H as [? [? VT]]; peauto. inv VT. eauto. 
    - (* app bad case 1 *)
      edestruct H as [? [? VT]]; peauto. 
      inv VT; simpl; peauto; contradiction. 
    - (* app bad case 2 *)
      edestruct H as [? [? VT]]; peauto. inv VT.
      eapply scopeofFrameDet in SF; eauto; subst. 
      edestruct H0 as [? [? X]]; peauto. 
      intuition (peauto); inv H5; econstructor. 
    - (* letpar good case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s1).
      { eapply scopeofFrameDet; eauto. inv FS. econstructor.
        eapply initNewDefaultFrameDiff; eauto. }
      subst.
      edestruct H as [? [? _]]; peauto.  
      edestruct H0 as [? [? ?]]; peauto.  
    - (* letpar bad case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s1).
      { eapply scopeofFrameDet; peauto. replace FH with fh by auto. (* ugh *) peauto. }
      subst.
      edestruct H as [? [? ?]]; peauto. 
      destruct H2; inv H2. 
      intuition peauto.
    - (* letseq good case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      edestruct H as [? [? ?]]; peauto. destruct H3. 2: inv H3. 
      destruct H3 as [ff [FEQ SF]]. inv FEQ.
      edestruct H0 as [? [? ?]]; peauto.
    - (* letseq bad case 1 *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      edestruct H as [? [? ?]]; peauto. destruct H2. destruct H2 as [? [FEQ SF]]. inv FEQ.
      inv H2; peauto.
    - (* letrec good case *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s0).
      { eapply scopeofFrameDet; peauto. replace FH with fh by auto. (* ugh *) peauto. }
      subst.
      edestruct H as [? [? _]]; peauto.  
      edestruct H0 as [? [? ?]]; peauto. 
    - (* letrec bad case 1 *)
      rewrite UNZIP1 in UNZIP0; inv UNZIP0.
      rewrite UNZIP1 in UNZIP; inv UNZIP.
      assert (sf = s0).
      { eapply scopeofFrameDet; peauto. replace FH with fh by auto. (* ugh *) peauto. }
      subst.
      edestruct H as [? [? ?]]; peauto. 
      inv H2; inv H3. 
      peauto.
    - (* asgn good case *)
      edestruct H as [? [? ?]]; peauto. 
      destruct H3 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0 as [? [? ?]]; peauto. 
      intuition peauto. 
    - (* asgn bad case 1 *)
      edestruct H as [? [? ?]]; peauto. destruct q; inv H2; peauto.
    - (* asgn bad case 2 *)
      edestruct H as [? [? ?]]; peauto. destruct H3 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0 as [? [? ?]]; peauto. 
    - (* asgn bad case 3 *)
      edestruct H as [? [? ?]]; peauto. destruct H3 as [? [? [SF [DS [IN [TD GF]]]]]].
      edestruct H0 as [? [? ?]]; peauto. 
      exfalso. 
      eapply eval_exp_scopeofFrame in SF; peauto.
      assert (good_frame T V VT h2 ff).
      { inv SF. eapply keys_in in H6. assert (frame h2 ff) by eauto. eapply H4; auto. }
      eapply good_frame_setSlot in H6; peauto. destruct H6. 
      eapply SET; eauto. 
    - (* if good case t *) subst.
      edestruct H as [? [? ?]]; peauto. 
      edestruct H0 as [? [? ?]]; peauto. 
    - (* if good case f *) subst.
      edestruct H as [? [? ?]]; peauto. 
      edestruct H0 as [? [? ?]]; peauto. 
    - (* if bad case *) subst.
      edestruct H as [? [? ?]]; peauto.
      destruct v1; inv H2; peauto.
      edestruct ABORT1; eauto.
    - (* seq good case *)
      edestruct H as [? [? ?]]; peauto.
      edestruct H0 as [? [? ?]]; peauto.
    - (* seq bad case 1 *)
      edestruct H as [? [? ?]]; peauto.
      inv H2; peauto.
    - (* new good case *)
      eapply rlookupDet in RLOOK; eauto. destruct RLOOK as [? [? ?]]; subst.
      eapply rlookupDet in RL; eauto. destruct RL as [? [? ?]]; subst.
      eapply assocScopeDet in ASC; eauto; subst.
      split. peauto.
      split.
      + eapply initNewDefaultFrame_good_heap; peauto.
        intros. inv H. destruct H0.
            inv PS.  simpl in H (*ugh*); rewrite H2 in H; inv H. inv H0. 
        intros. inv H.
      + econstructor; peauto.  replace FH with fh by eauto. (* ugh *)
        peauto. 
    - (* new bad case 1 *)
      edestruct RLOOK; peauto. 
    - (* eval_lhs var good case *)
      intuition eauto.
      destruct a. 
      inv WB; inv WT.
      eapply scopeofRefDet in SR; eauto; subst.
      eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
      simpl in *. eapply (good_addr T V VT) in SR1; eauto. 
      destruct SR1. destruct H. eapply getAddrDet in ADDR; eauto; inv ADDR.
      assert (TD'':=TD).
      inv TD. eapply keys_in in H2.
      assert (SFF:=H0).
      eapply scopeofFrameFrame in H0. 
      assert (GH':= GH).
      specialize (GH' _ H0). inv GH'.
      exists sd. exists (keys ds). split; auto.
      split. econstructor; eauto. split; auto. 
    - (* eval_lhs var bad case *)
      intuition eauto.
      inv WB; inv WT.
      eapply scopeofRefDet in SR; eauto; subst.
      eapply rlookupDet in SR0; eauto; subst. destruct SR0 as [? [? ?]]; subst.
      simpl in *. eapply (good_addr T V VT) in SR1; eauto.
      destruct SR1. destruct H. eauto. 
    - (* eval_lhs field good case *)
      destruct a. inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? ?]]; peauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      inv H2. eapply scopeofFrameDet in SF; eauto; subst. eapply assocScopeDet in ASC; eauto; subst.
      assert (good_heap T V VT h2) by peauto. 
      assert (scopeofFrame V fh h2 scf s') by peauto.  
      assert (GH' := H2).
      eapply (good_addr T V VT) in H2; peauto.
      destruct H2. destruct H2. eapply getAddrDet in ADDR; eauto; inv ADDR.
      assert (TD'':=TD).
      inv TD. eapply keys_in in H6.
      assert (SFF:=H3).
      eapply scopeofFrameFrame in H3. 
      split.  peauto. 
      split;  eauto.  
      exists sd. exists (keys ds).  split; auto. split.
      econstructor; eauto. 
      split; auto.  split; peauto.  
    - (* eval_lhs field good null case *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? ?]]; peauto.
    - (* eval_lhs field bad case 1 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? ?]]; peauto.
      destruct v; inv BAD;  inv H2; simpl; eauto.
    - (* eval_lhs field bad case 2 *)
      inv WB; inv WT. destruct e; simpl in *; subst.
      edestruct H as [? [? ?]]; peauto.
      eapply scopeofRefDet in SCR; eauto; subst.
      eapply scopeofRefDet in SR0; eauto; subst.
      eapply linksofScopeDet in LS; eauto; inv LS.
      eapply rlookupDet in SR; eauto. destruct SR as [? [? ?]]; subst.
      inv H2. eapply scopeofFrameDet in SF; eauto; subst. eapply assocScopeDet in ASC; eauto; subst.
      assert (good_heap T V VT h2) by peauto. 
      assert (scopeofFrame V fh h2 scf s') by peauto.
      assert (GH' := H2).
      eapply (good_addr T V VT) in H2; peauto.
      destruct H2. destruct H2. apply ADDR in H2; contradiction.
    - (* fill_par good case *)
      peauto. 
    - (* fill_par nil bad case 1 *)
      inv WT. inv TYPDECS. intuition.
    - (* fill_par nil bad case 2 *)
      inv TYPDECS. inv WT. intuition.
    - (* fill_par cons good case *)
      inv WT. destruct H3. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H1; subst.
      edestruct H as [? [? ?]];  peauto.
      edestruct H0 as [? [? ?]]; peauto. 
    - (* fill_par cons bad case 2 *)
      inv WT. destruct H2. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      edestruct H as [? [? ?]]; peauto. destruct q; inv H5; auto.
    - (* fill_par cons bad case 1 *)
      inv WT. destruct H2. inv TYPDECS. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      edestruct H as [? [? ?]]; peauto.
      exfalso.
      eapply eval_exp_scopeofFrame in FS; peauto. 
      assert (good_frame T V VT h1 fc).
      { inv FS. eapply keys_in in H7. peauto. }
      assert (exists ds, declsofScopeP wc s1 ds /\ In d ds).
      { inv H6. eexists; split. econstructor. 
        split; eauto. eapply keys_in in H10. assumption. }
      destruct H9 as [? [DS IN]].
      eapply good_frame_setSlot in H7; peauto. 
      destruct H7. eapply SS in H7; contradiction.
    - (* fill_seq nil good case *)
      inv WB1. intuition eauto. 
    - (* fill_seq nil bad case 1 *)
      inv WB1. intuition.
    - (* fill_seq nil bad case 2 *)
      inv WB1. intuition.
    - (* fill_seq cons good case *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H3; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      replace FH with fh in * by auto. (* ugh *)
      edestruct H as [? [? ?]]; peauto. 
      assert (scopeofFrame V FH h2 fc sd) by peauto.
      edestruct H0 as [? [? ?]]; peauto.
    - (* fill_seq cons bad case 1 *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      replace FH with fh in * by auto. (* ugh *)
      edestruct H as [? [? ?]]; peauto. 
      destruct q; inv H3; peauto.
      intuition peauto.
    - (* fill_seq cons bad case 2 *)
      inv WB1. destruct REL as [LKS [DS [FSTEQ [DD [ESEQ WB]]]]]. subst.
      inv WT. destruct H2; subst. inv TYPDECS. simpl in *.
      destruct e. simpl in *. subst. eapply scopeofFrameDet in SF; eauto; subst.
      replace FH with fh in * by auto. (* ugh *)
      edestruct H as [? [? ?]]; peauto. 
      assert (scopeofFrame V FH h2 fc sd) by peauto.
      assert (frame h2 fc) by peauto. 
      specialize (H2 _ H8).
      eapply good_frame_setSlot in H2; peauto. 
      destruct H2; apply SS in H2; contradiction.
    - (* fill_rec nil good case *)
      intuition eauto.  
    - (* fill_rec nil bad case 1 *)
      inv WT. inv TYPDEC. intuition.
    - (* fill_rec nil bad case 2 *)
      inv TYPDEC. inv WT. intuition.
    - (* fill_rec cons good case *)
      inv WT. destruct H3 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H1; subst.
      destruct y; inv ISFUN. simpl in *; subst.
      edestruct H as [? [? ?]]; peauto. 
      edestruct H0 as [? [? ?]]; peauto.
    - (* fill_rec cons bad case 1 *)
      inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      destruct y; inv ISFUN. simpl in *; subst.
      edestruct H as [? [? ?]]; peauto.
      destruct q; inv H5; eauto. 
    - (* fill_rec cons bad case 2 *)
      inv WT. destruct H2 as [ISV [ISFUN WT]]. inv TYPDEC. destruct e.
      assert (s = s0 /\ wb_exp (E s0 t p)).
      { edestruct WB. left. reflexivity. simpl in H1; auto. } destruct H0; subst.
      destruct y; inv ISFUN. simpl in *; subst.
      edestruct H as [? [? ?]]; peauto.
      assert (good_frame T V VT h1 frm) by peauto.
      assert (exists ds, declsofScopeP wc s0 ds /\ In d ds).
      { inv H3. eexists; split. econstructor. split; eauto. eapply keys_in in H9. assumption. } 
      destruct H8 as [? [DS IN]]. 
      eapply good_frame_setSlot in H7; peauto. 
      destruct H7. eapply SS in H7; contradiction.
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
    assert (scopeofFrame V fh h0 f s) by peauto.
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
      + econstructor; eauto.
        * intros. inv DS0. destruct H2. inv H1. simpl in *; rewrite H5 in H2; inv H2.
          inv FF. inv H1. inv H2. destruct H1. subst.
          eexists; split; eauto. econstructor.
          rewrite get_set_same. reflexivity. unfold DomEq. rewrite H3.
          split; auto.
        * inv FF. inv H1. inv H2. destruct H1. subst.
          intros. inv H1. destruct (FrameIdDec f f); intuition. inv H4.
          inv H2. rewrite get_set_same in H1. inv H1. inv DS0. destruct H1. unfold DomEq. rewrite H2.
          eexists; split; peauto. split; auto.
        * intros. inv H1. inv H2. inv LS. simpl in *. rewrite H4 in H1; inv H1. inv H3.
        * intros.
          inv FF. inv H2. inv H3. destruct H2. subst. inv H1. inv H3.
          rewrite get_set_same in H2. inv H2.
          rewrite get_set_same in H1. inv H1. inv H4.
      + econstructor; eauto.
        intros. eapply defaults_vtyp' in DF; peauto. inv H3.
        inv FF. destruct H3 as [? [? [GET H']]]. subst.
        rewrite get_set_same in H4. inv H4. rewrite get_set_same in GET. inv GET.
        symmetry; auto.
    }
    destruct exp_preservation as [expP _].
    edestruct expP; peauto. 
      eapply initNewDefaultFrame_good_roots; eauto. 
      unfold good_roots; intros. inv H1. 
    intro; subst v. inv H2. inv H4.
  Qed.


End TypeSoundness.
