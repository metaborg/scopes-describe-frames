Require Export scopes maps.

(** * Frames and Heaps *)

Definition FrameId := nat.
Lemma FrameIdDec : forall (frm1 frm2:FrameId), {frm1 = frm2} + {frm1 <> frm2}.
Proof.
  repeat (decide equality).
Qed.

(**
A heap [H] is represented as a finite map from [FrameId]s to [Frame]s.

A [Frame] consists of:

- A [ScopeId].

- A set of linked scopes, represented as a (curried) finite map from [EdgeLabel]s and [ScopeId]s to [FrameId]s.

- A set of slots, represented as a finite map from [D]eclarations to [V]alues.

We use a type class to package [Frame] and [H] so that Coq can automatically
infer the [V] type from the context; this provides similar type inference convenience
as Canonical Structures. *)

Class FrameHeap {V : Type} :=
  { Frame := ((ScopeId * (map EdgeLabel (map ScopeId FrameId)))%type * map D V)%type ;
    H := map FrameId Frame
  }.

Section FrameHeapProperties.

  Context `{FH : FrameHeap}.

  (** ** Frame Operations *)

  (** [frame h f] says that [f] is a frame in heap [h]. *)
  Definition frame (h: H) (f: FrameId) : Prop :=
    In f (keys h).


  (** ** Extracting frame components *)

  (** [scopeofFrame h f s] says that [s] is the scope of frame [f] in
  heap [h]. (Corresponds to (S_h(f)) in the Fig. 12 in the paper.) *)

  Inductive scopeofFrame (h: H) (f: FrameId) (s: ScopeId) : Prop :=
  | scopeofFrame_ :
      forall ks slots,
        get FrameIdDec h f = Some (s, ks, slots) ->
        scopeofFrame h f s.

  Lemma scopeofFrameDet :
    forall h f s,
      scopeofFrame h f s ->
      forall s',
        scopeofFrame h f s' ->
        s = s'.
  Proof.
    do 2 inversion 1. rewrite H3 in H1. inv H1; auto.
  Qed.

  Lemma scopeofFrameFrame :
    forall h f s,
      scopeofFrame h f s ->
      frame h f.
  Proof.
    inversion 1; unfold frame; eauto using keys_in.
  Qed.


  (** [linksofFrame h f ks] says that [ks] is the finite map of links
  from frame [f] in heap [h]. (Corresponds to (K_h(f)) in the Fig. 12
  in the paper.) *)

 Inductive linksofFrame (h: H) (f: FrameId) (ks: map EdgeLabel (map ScopeId FrameId)) : Prop :=
  | linksofFrame_ :
      forall s slots,
        get FrameIdDec h f = Some (s, ks, slots) ->
        linksofFrame h f ks.

  Lemma linksofFrameDet :
    forall ks ks' h f ,
      linksofFrame h f ks ->
      linksofFrame h f ks' -> ks = ks'.
  Proof.
    induction ks; intros.
    - inv H0. inv H1. rewrite H0 in H2. inv H2; eauto.
    - inv H0. inv H1. rewrite H0 in H2. inv H2; eauto.
  Qed.


  (** [llinksofFrame h f l ks] says that [ks] is the finite map of
  links for edge label [l] from frame [f] in heap [h]. *)

  Inductive llinksofFrame (h: H) (f: FrameId) (l: EdgeLabel) (lks: map ScopeId FrameId) : Prop :=
  | llinksofFrame_ :
      forall ks,
        linksofFrame h f ks ->
        get ELdec ks l = Some lks ->
        llinksofFrame h f l lks.

  Lemma llinksofFrameDet :
    forall ks ks' h f l,
      llinksofFrame h f l ks ->
      llinksofFrame h f l ks' -> ks = ks'.
  Proof.
    induction ks; intros.
    - inv H0. inv H1.
      eapply linksofFrameDet in H2; eauto; subst.
      rewrite H4 in H3. inv H3; eauto.
    - inv H0. inv H1.
      eapply linksofFrameDet in H2; eauto; subst.
      rewrite H4 in H3. inv H3; eauto.
  Qed.


  (** Getting all slots of a frame. (Corresponds to (D_h(f)) in the
  Fig. 12 in the paper.) *)
  Inductive slotsofFrame (heap: H) (f: FrameId) (slots:map D V) : Prop :=
  | getSlots_ : forall
      scope links,
      get FrameIdDec heap f = Some (scope, links, slots) ->
      slotsofFrame heap f slots.

  Lemma slotsofFrameDet:
    forall h f slots1 slots2,
      slotsofFrame h f slots1 ->
      slotsofFrame h f slots2 ->
      slots1 = slots2.
  Proof.
    intros. inv H0.  inv H1.
    rewrite H0 in H2; inv H2; auto.
  Qed.

  (** Getting value from a slot. (Corresponds to the [[GetSlot]] rule
  in Fig. 12 in the paper.) *)
  Inductive getSlot (heap: H) (f: FrameId) (d: D) (v: V) : Prop :=
  | getSlot_ : forall
      scope links slots,
      get FrameIdDec heap f = Some (scope, links, slots) ->
      Some v = get Ddec slots d ->
      getSlot heap f d v.

  Lemma getSlotDet:
    forall h f d v1 v2,
      getSlot h f d v1 ->
      getSlot h f d v2 ->
      v1 = v2.
  Proof.
    intros. inv H0. inv H1.
    rewrite H0 in H2; inv H2. rewrite <- H4 in H3; inv H3; auto.
  Qed.

  Lemma getSlotFrame :
    forall h f d v,
      getSlot h f d v ->
      frame h f.
  Proof.
    intros. inv H0. eapply keys_in; eauto.
  Qed.

  (** ** Heap Operations *)

  (** Empty heaps. *)

  Definition emptyHeap : H := empty.

  Lemma emptyHeapNoFrames :
    forall f,
      ~ frame emptyHeap f.
  Proof.
    intros. intro. unfold frame, emptyHeap in H0. simpl in H0. auto.
  Qed.


  (** Adding a new frame, whose [FrameId] is required to be fresh,
      with no slots. *)
  Definition newFrame
            (h: H)
            (s: ScopeId)
            (ks: map EdgeLabel (map ScopeId FrameId))
            (f: FrameId)
            (h': H) : Prop :=
    ~ In f (keys h) /\
    h' = set FrameIdDec h f (s, ks, empty).

  Lemma newFrameNew :
    forall h0 s ks f h1,
      newFrame h0 s ks f h1 ->
      ~ frame h0 f.
  Proof.
    intros. inv H0. auto.
  Qed.

  Lemma newFrameFrames :
    forall h0 s ks f0 h1,
      newFrame h0 s ks f0 h1 ->
      forall f,
        frame h1 f <-> f = f0 \/ frame h0 f.
  Proof.
    intros. inv H0. split; intros.
    unfold frame in H1.
    eapply in_keys_set; eauto.
    eapply set_in_keys; eauto.
  Qed.

  Lemma newFrameSame :
    forall h0 s ks frm h1,
      newFrame h0 s ks frm h1 ->
      get FrameIdDec h1 frm = Some (s, ks, []).
  Proof.
    intros. inv H0. eapply get_set_same.
  Qed.

  Lemma newFrameDiff :
    forall h0 f0 s0 ks0 slots0 s ks f h1,
      get FrameIdDec h0 f0 = Some (s0, ks0, slots0) ->
      (* NB. Do not require frm0 <> frm1 *)
      newFrame h0 s ks f h1 ->
      get FrameIdDec h1 f0 = Some (s0, ks0, slots0).
  Proof.
    intros. inv H1. inv H0. rewrite get_set_other; eauto.
    intro; subst. eapply keys_in in H3. contradiction.
  Qed.

  Lemma newFrameDiff' :
    forall h0 s frm0 frm1 h1 ks ds s' ks',
      get FrameIdDec h1 frm0 = Some (s, ks, ds) ->
      frm0 <> frm1 ->
      newFrame h0 s' ks' frm1 h1 ->
      get FrameIdDec h0 frm0 = Some (s, ks, ds).
  Proof.
    intros. inv H2. rewrite get_set_other in H0; eauto.
  Qed.

  Lemma newFrameSlotSame :
    forall s frm h0 h1 d v ks,
      newFrame h0 s ks frm h1 ->
      ~ getSlot h1 frm d v.
  Proof.
    intros. inv H0. intro. inv H0. rewrite get_set_same in H2. inv H2. inv H3.
  Qed.

  Lemma newFrameSlotDiff :
    forall s frm0 frm1 h0 h1 d v ks,
      getSlot h0 frm0 d v ->
      newFrame h0 s ks frm1 h1 ->
      getSlot h1 frm0 d v .
  Proof.
    intros. inv H1. inv H0. econstructor; eauto. rewrite get_set_other; eauto.
    eapply keys_in in H1. intro; subst; contradiction.
  Qed.

  Lemma newFrameSlotDiff':
    forall s frm0 frm1 h0 h1 d v ks,
      getSlot h1 frm0 d v ->
      newFrame h0 s ks frm1 h1 ->
      frm0 <> frm1 ->
      getSlot h0 frm0 d v .
  Proof.
    intros. inv H1. inv H0. rewrite get_set_other in H1; auto.
    econstructor; eauto.
  Qed.


  (** Filling all slots of a frame at once. *)
  Definition fillFrame (f: FrameId) (h0: H) (slots: map D V) (h1: H) : Prop :=
    exists s ks slots0,
      get FrameIdDec h0 f = Some (s, ks, slots0) /\
      h1 = set FrameIdDec h0 f (s, ks, slots).

  Lemma fillFrameFrames :
    forall f0 h0 slots h1,
      fillFrame f0 h0 slots h1 ->
      forall f, frame h0 f <-> frame h1 f.
  Proof.
    intros. destruct H0 as [? [? [? [GF SF]]]]. subst.
    split; unfold frame; intro. simpl.
    destruct (FrameIdDec f0 f); auto. right.
    eapply remove_in_keys; eauto.
    destruct (FrameIdDec f0 f); auto.
    simpl in H0. inv H0. eapply keys_in; eauto. eapply keys_in; eauto.
    simpl in H0. inv H0; [intuition|]. eapply in_keys_remove; eauto.
  Qed.

  Hint Resolve fillFrameFrames : sgraph.

  Lemma fillFrameSame :
    forall
      h0 f slots h1
      (FF: fillFrame f h0 slots h1)
      scope links slots0
      (GF: get FrameIdDec h0 f = Some (scope, links, slots0)),
      get FrameIdDec h1 f = Some (scope, links, slots).
  Proof.
    intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
    rewrite get_set_same. rewrite GF in GF'. inv GF'; auto.
  Qed.

  Lemma fillFrameSame' :
    forall
      h0 f slots h1
      (FF: fillFrame f h0 slots h1)
      scope links slots
      (GF: get FrameIdDec h1 f = Some (scope, links, slots)),
    exists slots', get FrameIdDec h0 f = Some (scope, links, slots').
  Proof.
    intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
    rewrite get_set_same in GF. inv GF. eauto.
  Qed.

  Hint Resolve fillFrameSame' : sgraph.

  Lemma fillFrameDiff :
    forall
      h0 f1 slots h1
      (FF: fillFrame f1 h0 slots h1)
      f0 scope links slots
      (NEQ: f0 <> f1)
      (GF: get FrameIdDec h0 f0 = Some (scope, links, slots)),
      get FrameIdDec h1 f0 = Some (scope, links, slots).
  Proof.
    intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
    rewrite get_set_other; auto.
  Qed.

  Lemma fillFrameDiff' :
    forall
      h0 f1 slots h1
      (FF: fillFrame f1 h0 slots h1)
      f0 scope links slots
      (NEQ: f0 <> f1)
      (GF: get FrameIdDec h1 f0 = Some (scope, links, slots)),
      get FrameIdDec h0 f0 = Some (scope, links, slots).
  Proof.
    intros; destruct FF as [? [? [? [GF' SF]]]]. subst.
    rewrite get_set_other in GF; auto.
  Qed.

  Lemma fillFrameSlotDiff :
    forall h0 f0 d v f1 h1 slots,
      fillFrame f1 h0 slots h1 ->
      getSlot h0 f0 d v ->
      f0 <> f1 ->
      getSlot h1 f0 d v.
  Proof.
    intros. inversion H0 as [? [? [? [GF' SF]]]]. subst.
    inv H1. econstructor. rewrite get_set_other; eauto. assumption.
  Qed.

  Lemma fillFrameSlotDiff' :
    forall h0 f0 d v f1 h1 slots,
      fillFrame f1 h0 slots h1 ->
      getSlot h1 f0 d v ->
      f0 <> f1 ->
      getSlot h0 f0 d v.
  Proof.
    intros; inversion H0 as [? [? [? [GF' SF]]]]. subst.
    inv H1. rewrite get_set_other in H3; eauto. econstructor; eauto.
  Qed.


  (** Create and fully initialize a frame from a list of
  values. (Corresponds to [[initFrame]] defined in Fig. 12 in the
  paper.) *)
  Inductive initFrame
            (h1: H)
            (s: ScopeId)
            (ks: map EdgeLabel (map ScopeId FrameId))
            (slots: map D V)
            (f: FrameId)
            (h3: H) : Prop :=
  | initFrame_ : forall
      h2
      (NF: newFrame h1 s ks f h2)
      (FF: fillFrame f h2 slots h3),
      initFrame h1 s ks slots f h3.

  Lemma initFrameFrames :
    forall h0 s ks vs f0 h1,
      initFrame h0 s ks vs f0 h1 ->
      forall f, f = f0 \/ frame h0 f  <-> frame h1 f.
  Proof.
    intros. inv H0. eapply iff_trans.
    eapply iff_sym. eapply newFrameFrames; eauto.
    eapply fillFrameFrames; eauto.
  Qed.

  Lemma initFrameSame :
    forall h0 s ks vs f0 h1,
      initFrame h0 s ks vs f0 h1 ->
      exists slots, get FrameIdDec h1 f0 = Some (s, ks, slots).
  Proof.
    intros. inversion H0.
    eapply newFrameSame in NF; eauto. inv NF.
    eapply fillFrameSame in FF; eauto.
  Qed.

  Lemma initFrameDiff :
    forall h0 f0 s ks slots f h1 s' ks' vs',
      initFrame h0 s' ks' vs' f h1 ->
      get FrameIdDec h0 f0 = Some (s, ks, slots) ->
      get FrameIdDec h1 f0 = Some (s, ks, slots).
  Proof.
    intros. inv H0.
    assert (get FrameIdDec h2 f0 = Some (s, ks, slots)).
    eapply newFrameDiff; eauto. inv NF.
    eapply fillFrameDiff; eauto.
    intro. subst. eapply keys_in in H1. contradiction.
  Qed.

  Lemma initFrameDiff' :
    forall h0 f0 s ks slots f h1 s' ks' vs',
      initFrame h0 s' ks' vs' f h1 ->
      get FrameIdDec h1 f0 = Some (s, ks, slots) ->
      f <> f0 ->
      get FrameIdDec h0 f0 = Some (s, ks, slots).
  Proof.
    intros. inv H0.
    eauto using fillFrameDiff', newFrameDiff'.
  Qed.

  Lemma initFrameSlotDiff' :
    forall f0 d v f h1 vs ks s h0,
      initFrame h0 s ks vs f h1 ->
      getSlot h1 f0 d v ->
      f0 <> f ->
      getSlot h0 f0 d v.
  Proof.
    intros. inv H0.
    eapply newFrameSlotDiff'. 2: eauto. 2: auto. eapply fillFrameSlotDiff'; eauto.
  Qed.

  Lemma initFrameSame_scopeofFrame :
    forall h0 s ks vs f0 h1,
      initFrame h0 s ks vs f0 h1 ->
      scopeofFrame h1 f0 s.
  Proof.
    intros. eapply initFrameSame in H0. inv H0; econstructor; eauto.
  Qed.

  Lemma initFrameDiff_scopeofFrame :
    forall h0 f0 s f h1 s' ks' vs',
      initFrame h0 s' ks' vs' f h1 ->
      scopeofFrame h0 f0 s ->
      scopeofFrame h1 f0 s.
  Proof.
    intros. inv H1. eapply initFrameDiff in H2; eauto; inv H2; econstructor; eauto.
  Qed.

  (** Setting a slot that already has a value. (Corresponding to
  [[SetSlot]] in Fig. 20 in the paper.) *)
  Inductive setSlot (h: H) (f:FrameId) (d:D) (v:V) (h': H) : Prop :=
  | setSlot_ :
      forall
        scope links slots slots',
        In d (keys slots) ->
        get FrameIdDec h f = Some (scope, links, slots) ->
        slots' = set Ddec slots d v ->
        h' = set FrameIdDec h f (scope, links, slots') ->
        setSlot h f d v h'.

  Lemma setSlotFrame :
    forall h0 f d v h1,
      setSlot h0 f d v h1 ->
      frame h0 f.
  Proof.
    intros. inv H0. apply keys_in in H2. auto.
  Qed.

  Lemma setSlotFrames :
    forall h0 d v h1 f0,
      setSlot h0 f0 d v h1 ->
      forall f,
        frame h0 f <-> frame h1 f.
  Proof.
    intros. split; intros.
      inv H0. eapply set_in_keys. auto.
      inv H0.
       unfold frame in H1; apply in_keys_set in H1. inv H1; subst.
       eapply keys_in; eauto.
       auto.
  Qed.

  Lemma setSlotSlotSame:
    forall frm d v h0 h1,
      setSlot h0 frm d v h1 ->
      getSlot h1 frm d v.
  Proof.
    intros. inv H0. econstructor.
    rewrite get_set_same; eauto.
    rewrite get_set_same; auto.
  Qed.

  Lemma setSlotSlotDiff :
    forall frm0 frm1 d0 d1 v0 v1 h0 h1,
      getSlot h0 frm0 d0 v0 ->
      setSlot h0 frm1 d1 v1 h1 ->
      frm1 <> frm0 \/  d1 <> d0 ->
      getSlot h1 frm0 d0 v0.
  Proof.
    intros. inv H0. inv H1. destruct H2.
      econstructor; eauto. rewrite get_set_other; eauto.
      destruct (FrameIdDec frm1 frm0); subst.
        rewrite H3 in H5; inv H5.
        econstructor. rewrite get_set_same; eauto.
          rewrite get_set_other; eauto.
        econstructor; eauto. rewrite get_set_other; eauto.
  Qed.

  Lemma setSlotSlotDiff' :
    forall frm0 frm1 d0 d1 v0 v1 h0 h1,
      setSlot h0 frm1 d1 v1 h1 ->
      getSlot h1 frm0 d0 v0 ->
      frm1 <> frm0 \/  d1 <> d0 ->
      getSlot h0 frm0 d0 v0.
  Proof.
    intros. inv H0. inv H1. destruct H2.
    rewrite get_set_other in H0.
    econstructor; eauto.  intro. subst. apply H1; auto.
    destruct (FrameIdDec frm1 frm0); subst.
    rewrite get_set_same in H0. inv H0; subst.
    econstructor; eauto.
    rewrite get_set_other in H5.  eauto. intro. subst. apply H1; auto.
    rewrite get_set_other in H0. econstructor; eauto.
    intro. subst. apply n; auto.
  Qed.

  Lemma setSlotSame :
    forall h0 frm0 frm1 d v h1 scope links slots,
      setSlot h0 frm1 d v h1 ->
      get FrameIdDec h0 frm0 = Some (scope, links, slots) ->
      exists slots, get FrameIdDec h1 frm0 = Some (scope, links, slots).
  Proof.
    intros. inv H0.
    destruct (FrameIdDec frm1 frm0); subst.
      unfold Frame in *; rewrite H1 in H3; inv H3. rewrite get_set_same. eexists; eauto.
      rewrite get_set_other. eexists; eauto. intuition.
  Qed.

  Lemma setSlotScope :
    forall
      h0 frm0 frm1 s d v h1,
      setSlot h0 frm1 d v h1 ->
      scopeofFrame h0 frm0 s ->
      scopeofFrame h1 frm0 s.
  Proof.
    inversion 1; intros; subst.
    eapply setSlotSame in H0; eauto.
    destruct H0. inv H5. destruct (FrameIdDec frm0 frm1). subst.
    rewrite H3 in H2; inv H2. econstructor; eauto.
    econstructor. rewrite get_set_other; eauto.
  Qed.

  (** Removing a frame. *)
  Definition removeFrame (h0: H) (f:FrameId) (h1: H) : Prop :=
    h1 = remove FrameIdDec h0 f.

  Lemma removeFrameFrames0:
    forall h0 f h1 f0,
      removeFrame h0 f h1 ->
      (frame h1 f0 <-> (f <> f0 /\ frame h0 f0)).
  Proof.
    intros. unfold frame. inv H0. split; intros. apply in_keys_remove in H0. intuition.
    eapply remove_in_keys; intuition.
  Qed.

  Lemma removeFrameFrames:
    forall h0 f h1 f0,
      removeFrame h0 f h1 ->
      f <> f0 ->
      frame h0 f0 ->
      frame h1 f0.
  Proof.
    unfold frame; intros. inv H0. eapply remove_in_keys; eauto.
  Qed.

  Lemma removeFrameFrames':
    forall h0 f h1 f0,
      removeFrame h0 f h1 ->
      frame h1 f0 ->
      (f <> f0 /\ frame h0 f0).
  Proof.
    unfold frame; intros. inv H0. apply in_keys_remove in H1. intuition.
  Qed.

  Lemma removeFrameSame :
    forall h0 frm0 s0 ks0 slots0 h1 frm,
      removeFrame h0 frm h1 ->
      (get FrameIdDec h1 frm0 = Some (s0, ks0, slots0) <->
       (get FrameIdDec h0 frm0 = Some (s0, ks0, slots0) /\ frm <> frm0)).
  Proof.
    intros. split; intros.
      inv H1. inv H0.
        destruct (FrameIdDec frm frm0); subst.
          rewrite get_remove_same in H3. inv H3.
          rewrite get_remove_other in H3; eauto.
        erewrite get_remove_other; eauto.
      inv H0. inv H1; eauto.
      rewrite get_remove_other; eauto.
  Qed.

  Lemma removeFrameScope:
    forall h0 frm0 s0 h1 frm,
      removeFrame h0 frm h1 ->
      (scopeofFrame h1 frm0 s0 <-> (scopeofFrame h0 frm0 s0 /\ frm <> frm0)).
  Proof.
    intros. split;intros.
      inv H1. eapply removeFrameSame in H2; eauto. destruct H2. split; eauto.
        econstructor; eauto.
      destruct H1. inv H1.  econstructor. eapply removeFrameSame; eauto.
  Qed.


  Lemma removeFrameSlot :
    forall h0 f0 d v f h1,
      removeFrame h0 f h1 ->
      (getSlot h1 f0 d v <-> (getSlot h0 f0 d v /\ f <> f0)).
  Proof.
    intros. inv H0. split; intros.
      inv H0. inv H1. destruct (FrameIdDec f f0); subst.
        rewrite get_remove_same in H3; inv H3.
        rewrite get_remove_other in H3; eauto. split; eauto.
    inv H3. inv H2; econstructor; eauto.
    inv H0. inv H1.
    econstructor; eauto. erewrite get_remove_other; eauto.
  Qed.

  (** Removing multiple frames. *)
  Inductive removeFrames : H -> list FrameId -> H -> Prop :=
  | rfs_nil :
      forall h0, removeFrames h0 [] h0
  | rfs_cons :
      forall h0 h1 h2 f fs,
        removeFrame h0 f h1 ->
        removeFrames h1 fs h2 ->
        removeFrames h0 (f::fs) h2.

  Lemma removeFramesFrames :
    forall h0 fs h1 f0,
      removeFrames h0 fs h1 -> (frame h1 f0 <-> (~ In f0 fs /\ frame h0 f0)).
  Proof.
    intros.
    induction H0; intros.
    intuition.
    eapply removeFrameFrames0 with (f0:=f0) in H0.
    split; intros.
    rewrite IHremoveFrames in H2.  destruct H2.  rewrite H0 in H3.  destruct H3.
    split; auto.  intro; exfalso. inv H5. eapply H3; eauto. eapply H2; contradiction.
    rewrite IHremoveFrames. destruct H2. split.  intro. apply H2. right; auto.
    eapply H0. split; auto. intro; eapply H2; left; auto.
  Qed.

  Lemma removeFramesSame :
    forall h0 frm0 s0 h1 frms ks0 slots0,
      removeFrames h0 frms h1 ->
      (get FrameIdDec h1 frm0 = Some (s0, ks0, slots0) <->
       (~ In frm0 frms /\ get FrameIdDec h0 frm0 = Some (s0, ks0, slots0))).
  Proof.
    intros. induction H0; intros.
    intuition.
    eapply removeFrameSame with (frm0:=frm0) (s0:=s0) in H0.
    split; intros.
    eapply IHremoveFrames in H2.  inv H2.  eapply H0 in H4. inv H4.
    split.  intro. inv H4. apply H5; auto. contradiction. auto.

    inv H2. eapply IHremoveFrames; eauto. split.
    intro. eapply H3; right; auto.
    erewrite H0. split; auto.
    intro; subst; eapply H3; left; auto.
  Qed.

  Lemma removeFramesScope: forall h0 frm0 s0 h1 frms,
                            removeFrames h0 frms h1 ->
                            (scopeofFrame h1 frm0 s0 <-> (~ In frm0 frms /\ scopeofFrame h0 frm0 s0)).
  Proof.
    intros. induction H0; intros.
    intuition.
    eapply removeFrameScope with (frm0 := frm0) (s0:=s0) in H0.
    split; intros.
    eapply IHremoveFrames in H2.  inv H2.  eapply H0 in H4. inv H4.
    split.  intro. inv H4. apply H5; auto. contradiction. auto.

    inv H2. eapply IHremoveFrames; eauto. split.
    intro. eapply H3; right; auto.
    erewrite H0.  split; auto.
    intro; subst; eapply H3; left; auto.
  Qed.

  Lemma removeFramesSlot :
    forall h0 f0 d v fs h1,
      removeFrames h0 fs h1 ->
      (getSlot h1 f0 d v <-> (~ In f0 fs /\ getSlot h0 f0 d v)).
  Proof.
    intros.
    induction H0.
    intuition.
    eapply removeFrameSlot with (h0:= h0) (f := f) (h1:=h1) in H0.
    split; intros.
    eapply IHremoveFrames in H2.  inv H2.  eapply H0 in H4. inv H4.
    split.  intro. inv H4. apply H5; auto. contradiction. auto.

    inv H2. eapply IHremoveFrames; eauto. split.
    intro. eapply H3; right; auto.
    erewrite H0.  split; auto.
    intro; subst; eapply H3; left; auto.
  Qed.

  (** ** Dynamic lookup by path. *)

  (** [lookup h f p f'] says that [p] traces a dynamic path from frame
  [f] to frame [f'] in heap [h]. (Corresponds to [[DLookupD]] and
  [[DLookupE]] in Fig. 12 in the paper.) *)

  Inductive lookup (h: H) : FrameId -> path -> D -> FrameId -> Prop :=
  | lookupD : forall f d,
      (exists v, getSlot h f d v) ->
      lookup h f (Dp d) d f
  | lookupI : forall
      f p f' f'' l s ks d
      (IMS: llinksofFrame h f l ks)
      (S: get ScopeIdDec ks s = Some f')
      (REST: lookup h f' p d f''),
      lookup h f (Ep l s p) d f''
  .

  Lemma lookupDet :
    forall h f p d1 f1,
      lookup h f p d1 f1 ->
      forall d2 f2,
        lookup h f p d2 f2 -> d1 = d2 /\ f1 = f2.
  Proof.
    induction 1; intros.
    - inv H1; auto.
    - inv H1. eapply llinksofFrameDet in IMS; eauto; subst.
      rewrite S in S0; inv S0; eauto.
  Qed.


  (** * Combining Static and Dynamic Properties. *)

  Section CombiningStaticAndDynamic.

    Context `{G: Graph}.

    (** [Addr FrameId D] defines an address within a frame. *)
    Inductive Addr :=
    | Addr_ : FrameId -> D -> Addr.

    (** [getAddr h f r addr] says that [addr] is the address of the
        slot to which reference [r] resolves, starting from frame [f]. *)

    Inductive getAddr (h: H) (f: FrameId) (r: R) : Addr -> Prop :=
    | getAddr_ :
        forall
          p f' d
          (PATH: pathofRefP r p)
          (LK: lookup h f p d f'),
        getAddr h f r (Addr_ f' d).

    Lemma getAddrDet :
      forall h f r a1 a2,
        getAddr h f r a1 ->
        getAddr h f r a2 ->
        a1 = a2.
    Proof.
      intros. inv H0.  inv H1.
      pose proof (pathofRefDet _ _ PATH _ PATH0). subst p0. clear PATH0.
      eapply lookupDet in LK; eauto. destruct LK; subst; eauto.
    Qed.

    (** [getRef h f r v] says that [v] is the value in the slot
        address to which reference [r] resolves, starting from frame [f]. *)
    Inductive getRef (h: H) (f:FrameId) (r: R) (v: V) : Prop :=
    | getRef_ : forall
        ff d
        (ADDR: getAddr h f r (Addr_ ff d))
        (SLOT: getSlot h ff d v),
        getRef h f r v.

    Lemma getRefDet :
      forall h f r v1 v2,
        getRef h f r v1 -> getRef h f r v2 -> v1 = v2.
    Proof.
      intros. inv H0. inv H1.
      pose proof (getAddrDet _ _ _ _ _ ADDR ADDR0). inv H0. clear ADDR0.
      eapply getSlotDet; eauto.
    Qed.

  End CombiningStaticAndDynamic.

End FrameHeapProperties.

Hint Constructors Addr : sgraph.
Hint Constructors getAddr : sgraph.
Hint Constructors slotsofFrame : sgraph.
Hint Constructors getSlot : sgraph.
Hint Constructors typofDecl : sgraph.
Hint Constructors scopeofFrame : sgraph.
Hint Constructors linksofFrame : sgraph.
Hint Constructors llinksofFrame : sgraph.
Hint Constructors lookup : sgraph.

Hint Resolve scopeofFrameFrame : sgraph.
Hint Resolve setSlotSlotSame : sgraph.
Hint Resolve getAddrDet : sgraph.
Hint Resolve getRefDet : sgraph.
Hint Resolve fillFrameSame : sgraph.
Hint Resolve fillFrameDiff : sgraph.
Hint Resolve fillFrameDiff : sgraph.

Hint Resolve initFrameSame_scopeofFrame : sgraph.
Hint Resolve initFrameSame : sgraph.
Hint Resolve initFrameDiff_scopeofFrame : sgraph.
Hint Resolve initFrameDiff : sgraph.
Hint Resolve initFrameSlotDiff' : sgraph.
Hint Resolve setSlotScope : sgraph.


(** * Definition of value typing.

This class is parameterized by [T], the type of types. We will
actually instantiate it for different languages.

[vtyp h v t] says that value [v] has type [t] in heap [h].

We require that value typing is invariant under [setSlot],
[newFrame] and [fillFrame] operations.

*)

Class VTyp {T: Type} `{dwc: Graph (@AT T)} `{fh: FrameHeap} :=
  { vtyp : H -> V -> T -> Prop ;
    setSlot_vtyp :
      forall
        h0 f d v h1 v0 t0
        (SET: setSlot h0 f d v h1)
        (VT: vtyp h0 v0 t0),
        vtyp h1 v0 t0 ;
    newFrame_vtyp :
      forall
        h0 s f h1 ks v0 t0
        (NF: newFrame h0 s ks f h1)
        (VT: vtyp h0 v0 t0),
        vtyp h1 v0 t0 ;
    fillFrame_vtyp :
      forall
        slots f h1 h2 v0 t0
        (FF: fillFrame f h1 slots h2)
        (VT: vtyp h1 v0 t0),
        vtyp h2 v0 t0;
  }.


Section VTypProperties.

  Context `{VT : VTyp}.

  Lemma initFrame_vtyp :
    forall
      h0 s ks slots f h1 v0 t0
      (INF: initFrame h0 s ks slots f h1)
      (VTYP: vtyp h0 v0 t0),
      vtyp h1 v0 t0.
  Proof.
    inversion 1; intros. eapply fillFrame_vtyp; eauto. eapply newFrame_vtyp; eauto.
  Qed.


End VTypProperties.


(** * Good frame and good heap  properties *)

(** These are the properties defined in Fig. 15 in the paper. *)

Section Goodness.

  Context `{VT : VTyp}.

  (** ** Well-Bound and Well-Typed Frames and Heaps *)

  (* Ideally, [well_bound] should not depend on value typing;
     this is just an artifact of the way we abstracted over
     scope declaration data. *)
  Inductive well_bound (h: H) (f: FrameId) : Prop :=
  | well_bound_ :
      forall
        s
        (SC: scopeofFrame h f s)
        (** WellBound declarations *)
        (DSS: forall ds,
            ddataofScopeP s ds ->
            exists slots, slotsofFrame h f slots /\ DomEq slots ds)
        (DSF: forall slots,
            slotsofFrame h f slots ->
            exists ds, ddataofScopeP s ds /\ DomEq slots ds)
        (** WellBound links: *)
        (LNS: forall l ss,
            llinksofScopeP s l ss ->
            exists ks,
              llinksofFrame h f l ks /\
              keys ks = ss /\
              forall s,
                In s ss ->
                exists f', get ScopeIdDec ks s = Some f' /\
                           scopeofFrame h f' s)
        (LNF: forall l ks,
            llinksofFrame h f l ks ->
            llinksofScopeP s l (keys ks)),
        well_bound h f.

  Inductive well_typed (h: H) (f: FrameId) : Prop :=
  | well_typed_ :
      forall
        s
        (SC: scopeofFrame h f s)
        ds
        (DS: declsofScopeP s ds)
        (WT: forall d t v,
            In d ds ->
            typofDecl d t ->
            getSlot h f d v ->
            vtyp h v t),
        well_typed h f.

  Definition good_frame h f := well_bound h f /\ well_typed h f.

  Definition good_heap h := forall f, frame h f -> good_frame h f.

  (** ** Good Frame Properties *)

  Hint Constructors well_bound : sgraph.
  Hint Constructors well_typed : sgraph.

  Lemma well_bound_get :
    forall h f s d ds
           (WB: well_bound h f)
           (SF: scopeofFrame h f s)
           (DS: declsofScopeP s ds)
           (IN: In d ds),
    exists v, getSlot h f d v.
  Proof.
    intros. inv WB.
    eapply scopeofFrameDet in SF; eauto; subst.
    inv DS. inv H0.
    edestruct DSS as [slots [GS DE]]; eauto.
    inv GS.
    assert (In d (keys slots)) by (apply DE; auto).
    eapply in_keys in H2. destruct H2 as [v P].
    exists v; econstructor; eauto.
  Qed.

  Lemma well_bound_set:
    forall
      h f s ds d
      (WB: well_bound h f)
      (SC: scopeofFrame h f s)
      (DS: declsofScopeP s ds)
      (IN: In d ds),
    forall v,
    exists h', setSlot h f d v h'.
  Proof.
    intros. inv WB. eapply scopeofFrameDet in SC; eauto; subst.
    inv DS. destruct H0. subst. inv H0.
    assert (ddataofScopeP s x) by sgauto.
    eapply DSS in H0. destruct H0 as [? [? ?]].
    destruct H0. inv SC0.  erewrite H3 in H0; inv H0.
    eexists. econstructor; sgauto. eapply H1. assumption.
  Qed.

  Lemma setSlot_well_bound :
    forall
      h0 f d v h1
      (SET: setSlot h0 f d v h1)
      (WB: well_bound h0 f),
      well_bound h1 f.
  Proof.
    intros; inv WB; sgauto.
    inversion SET; subst. inversion SC. rewrite H2 in H1; inv H1.
    econstructor.
    - econstructor; eauto. rewrite get_set_same; eauto.
    - intros. eapply DSS in H1. inv H1. inv H3.
      eexists; split. econstructor. simpl. destruct (FrameIdDec f f); [|intuition]. clear e.
      eauto. eapply DomEq_set; eauto.
      inv H1. rewrite H3 in H2. inv H2. auto.
    - intros. inv H1. rewrite get_set_same in H3. inv H3.
      assert (slotsofFrame h0 f slots). econstructor; eauto.
      eapply DSF in H1. inv H1. inv H3. eexists; split; eauto.
      eapply DomEq_set; eauto.
    - intros. eapply LNS in H1; eauto.
      destruct H1 as [? [LLN [KS SS]]]. subst. inv LLN.
      eexists; split; eauto. econstructor; eauto. inv H1. rewrite H4 in H2. inv H2.
      econstructor. rewrite get_set_same; eauto.
      split; auto. intros. apply SS in H4. destruct H4 as [? [? ?]].
      eexists; split; eauto. inv H5.
      destruct (FrameIdDec f x0). subst.
      rewrite H2 in H6. inv H6.
      econstructor. rewrite get_set_same; eauto.
      econstructor. rewrite get_set_other; eauto.
    - intros. inv H1. inv H3. rewrite get_set_same in H1. inv H1.
      assert (llinksofFrame h0 f l ks).
      econstructor; eauto. econstructor; eauto.
      eapply LNF in H1. auto.
  Qed.

  Lemma setSlot_well_typed :
    forall
      h0 f d v h1 t s
      (SET: setSlot h0 f d v h1)
      (SF: scopeofFrame h0 f s)
      (TD: typofDecl d t)
      (VT': vtyp h0 v t)
      (WT: well_typed h0 f),
      well_typed h1 f.
  Proof.
    intros; inv WT; sgauto.
    inversion SET; subst. inversion SC. rewrite H2 in H1; inv H1.
    econstructor; eauto.
    - econstructor; eauto. rewrite get_set_same; eauto.
    - intros. inv H4. rewrite get_set_same in H5. inv H5.
      eapply setSlot_vtyp; eauto. simpl in H6. eapply scopeofFrameDet in SF; eauto; subst.
      destruct (Ddec d0 d); subst. inv H6. simpl in H3. eapply typofDeclDet in TD; eauto; subst; eauto.
      eapply WT0 in H1; eauto. econstructor; eauto. assert (d <> d0). intuition.
      apply get_remove_other with (Kdec:=Ddec) (m:=slots) in H4.
      rewrite H4 in H6. auto.
  Qed.

  Hint Resolve setSlot_well_bound : sgraph.
  Hint Resolve setSlot_well_typed : sgraph.
  Hint Unfold good_frame : sgraph.

  Lemma setSlot_good_frame :
    forall
      h0 f d v h1 s t
      (SET: setSlot h0 f d v h1)
      (SF: scopeofFrame h0 f s)
      (TD: typofDecl d t)
      (VT': vtyp h0 v t)
      (WT: good_frame h0 f),
      good_frame h1 f.
  Proof.
    intros. inv WT. sgauto.
  Qed.

  Hint Resolve setSlot_good_frame : sgraph.

  Lemma setSlot_other_well_bound :
    forall
      h0 f d v h1 f0
      (SET: setSlot h0 f d v h1)
      (WB: well_bound h0 f0)
      (DIFF: f <> f0),
      well_bound h1 f0.
  Proof.
    intros; inv WB; sgauto. inv SC; inv SET.
    econstructor.
    - econstructor; eauto. rewrite get_set_other; eauto.
    - intros. eapply DSS in H3. destruct H3 as [? [? ?]]. inv H3. rewrite H5 in H0; inv H0.
      eexists; split; eauto. econstructor; rewrite get_set_other; eauto.
    - intros. inv H3. rewrite get_set_other in H4; [|intuition]. rewrite H4 in H0; inv H0.
      assert (slotsofFrame h0 f0 slots). econstructor; eauto. eauto.
    - intros. eapply LNS in H3. destruct H3 as [? [? [? ?]]]; subst.
      inv H3. inv H4. rewrite H3 in H0; inv H0.
      eexists; split; eauto. econstructor; sgauto. econstructor; rewrite get_set_other; eauto.
      split; eauto. intros. eapply H5 in H0. destruct H0 as [? [? ?]].
      inv H4.
      eexists; split; eauto. destruct (FrameIdDec x0 f); subst.
      rewrite H7 in H2; inv H2. econstructor; rewrite get_set_same; sgauto.
      econstructor; rewrite get_set_other; sgauto.
    - intros. inv H3. inv H4. rewrite get_set_other in H3; auto. rewrite H3 in H0; inv H0.
      assert (llinksofFrame h0 f0 l ks0); sgauto.
  Qed.

  Lemma setSlot_other_well_typed :
    forall
      h0 f d v h1 t s f0
      (SET: setSlot h0 f d v h1)
      (SF: scopeofFrame h0 f s)
      (TD: typofDecl d t)
      (VT': vtyp h0 v t)
      (WT: well_typed h0 f0)
      (DIFF: f <> f0),
      well_typed h1 f0.
  Proof.
    intros; inv WT. inv SC; inv SET.
    econstructor; eauto.
    - econstructor; rewrite get_set_other; eauto.
    - intros. inv H5. rewrite get_set_other in H6; eauto.
      eapply setSlot_vtyp. econstructor; eauto. eapply WT0; eauto. econstructor; eauto.
  Qed.

  Hint Resolve setSlot_other_well_bound : sgraph.
  Hint Resolve setSlot_other_well_typed : sgraph.

  Lemma setSlot_other_good_frame :
    forall
      h0 f d v h1 t s f0
      (SET: setSlot h0 f d v h1)
      (SF: scopeofFrame h0 f s)
      (TD: typofDecl d t)
      (VT': vtyp h0 v t)
      (WT: good_frame h0 f0)
      (DIFF: f <> f0),
      good_frame h1 f0.
  Proof.
    intros; inv WT; sgauto.
  Qed.

  Lemma getAddr_scopeofFrame :
    forall
      h f r ff d
      (GH: good_heap h)
      (FH: frame h f)
      (ADDR: getAddr h f r (Addr_ ff d)),
    exists sf, scopeofFrame h ff sf.
  Proof.
    inversion 3; subst. clear PATH ADDR.
    induction LK; eauto.
    - unfold frame in FH. eapply in_keys in FH. destruct FH. destruct x. destruct p.
      eexists; try econstructor; eauto.
    - generalize (GH _ FH); intro GF. inv GF. inv H0.
      specialize (LNF _ _ IMS).
      specialize (LNS _ _ LNF).
      destruct LNS as [? [LLF [KS WBL]]].
      eapply llinksofFrameDet in IMS; eauto; subst.
      assert (S':=S).
      apply keys_in in S. specialize (WBL _ S).
      destruct WBL as [? [SCF' SFF']].
      apply scopeofFrameFrame in SFF'.
      rewrite SCF' in S'; inv S'.
      eapply IHLK; eauto.
  Qed.

  Hint Resolve getAddr_scopeofFrame : sgraph.

  Lemma initFrame_other_well_bound :
    forall
      h0 s ks vs f h1
      (INIT: initFrame h0 s ks vs f h1)
      f'
      (WB: well_bound h0 f'),
      well_bound h1 f'.
  Proof.
    intros; inv WB. inv INIT.
    assert (NF':=NF); eapply newFrameSame in NF'.
    assert (FF':=FF); eapply fillFrameSame in FF; eauto. inv FF.
    inv NF. rewrite get_set_same in NF'. inv NF'.
    inv SC.
    assert (f' <> f). intro. subst. apply H0. eapply keys_in; eauto.
    assert (FF'':=FF').
    eapply fillFrameDiff in FF'; eauto. Focus 2.
    apply get_set_other with (Kdec:=FrameIdDec) (m:=h0) (v:=(s, ks, empty)) in H3.
    rewrite H3. eauto.
    econstructor; sgauto.
    - intros. eapply DSS in H4. destruct H4 as [? [GS DE]].
      eexists; split; sgauto. inv GS. rewrite H4 in H2. inv H2. auto.
    - intros. inversion H4. rewrite H5 in FF'. inv FF'.
      assert (slotsofFrame h0 f' slots). econstructor; eauto.
      eauto.
    - intros. eapply LNS in H4. destruct H4 as [? [LL [KS GS]]].
      inv LL. inv H4. rewrite H6 in H2. inv H2.
      eexists; split. econstructor; eauto. econstructor; eauto.
      split; eauto. intros. eapply GS in H2.
      destruct H2 as [? [? ?]]; eexists; split; eauto.
      inv H4.
      destruct (FrameIdDec x0 f). subst. destruct H0. eapply keys_in in H7; auto.
      destruct (FrameIdDec x0 f'). subst.
      rewrite H7 in H6; inv H6.
      econstructor; eauto.
      eapply fillFrameDiff in FF''; eauto.
      econstructor. eauto. rewrite get_set_other; eauto.
    - intros.
      assert (llinksofFrame h0 f' l ks1).
      inv H4. inv H5. rewrite H4 in FF'. inv FF'. econstructor; sgauto.
      eapply LNF in H5; eauto.
  Qed.

  Lemma initFrame_other_well_typed :
    forall
      h0 s ks slots f h1
      (INIT: initFrame h0 s ks slots f h1)
      slots
      (TDs: declsofScopeP s (@keys D V slots))
      f'
      (WT: well_typed h0 f'),
      well_typed h1 f'.
  Proof.
    intros. inv INIT.
    assert (NF':=NF); eapply newFrameSame in NF'.
    assert (FF':=FF); eapply fillFrameSame in FF; eauto. inv FF.
    inversion NF; subst. rewrite get_set_same in NF'. inv NF'. inv WT. inv SC.
    assert (f' <> f). intro. subst. apply H0. eapply keys_in; eauto.
    assert (FF'':=FF').
    eapply fillFrameDiff in FF'; eauto. Focus 2.
    apply get_set_other with (Kdec:=FrameIdDec) (m:=h0) (v:=(s, ks, empty)) in H3.
    rewrite H3. eauto.
    econstructor; sgauto. intros.
    eapply fillFrame_vtyp in FF''; eauto.
    eapply newFrame_vtyp in NF; eauto.
    inv H6. rewrite H7 in FF'; inv FF'.
    eapply WT0; eauto. econstructor; eauto.
  Qed.

  Hint Resolve initFrame_other_well_bound : sgraph.
  Hint Resolve initFrame_other_well_typed : sgraph.

  Lemma initFrame_other_good_frame :
    forall
      h0 s ks slots f h1
      (INIT: initFrame h0 s ks slots f h1)
      (TDs: declsofScopeP s (keys slots))
      f'
      (GF: good_frame h0 f'),
      good_frame h1 f'.
  Proof.
    intros; inv GF; sgauto.
  Qed.

  Lemma initFrame_well_bound :
    forall
      h0 s ks slots f h1
      (INIT: initFrame h0 s ks slots f h1)
      (TDs: declsofScopeP s (keys slots))
      (* WellBound links: *)
      (LNS: forall l ss,
          llinksofScopeP s l ss ->
          exists m,
            get ELdec ks l = Some m /\
            keys m = ss /\
            forall s,
              In s ss ->
              exists f', get ScopeIdDec m s = Some f' /\
                         scopeofFrame h0 f' s)
      (LNF: forall l m,
          get ELdec ks l = Some m ->
          llinksofScopeP s l (keys m)),
      well_bound h1 f.
  Proof.
    intros; inv INIT. inv NF. assert (FF':=FF).
    eapply fillFrameSame in FF; try rewrite get_set_same; eauto.
    eexists; sgauto.
    - intros.
      assert (declsofScopeP s (keys ds)) by (econstructor; eauto).
      eapply declsofScopeDet in TDs; eauto; subst.
      eexists; split; sgauto. split; rewrite <- TDs; auto.
    - intros. inv H1. rewrite H2 in FF; inv FF. inv TDs. inv H1.
      eexists; split; sgauto. split; rewrite <- H4; auto.
    - intros. eapply LNS in H1. destruct H1 as [? [M [KS SF]]]. subst.
      eexists; split. econstructor; eauto. econstructor; eauto.
      split; eauto. intros. apply SF in H1. destruct H1 as [? [GS SF']]. inv SF'.
      assert (x0 <> f). intro. subst. apply keys_in in H1. contradiction.
      eapply fillFrameDiff in FF'; eauto. Focus 2. rewrite get_set_other; eauto.
      eexists; split; sgauto.
    - intros. inv H1. inv H2. rewrite H1 in FF; inv FF.
      apply LNF in H3; auto.
  Qed.

  Lemma initFrame_well_bound1 :
    forall
      h0 s  slots f h1 l sl fl
      (INIT: initFrame h0 s [(l, [(sl, fl)])] slots f h1)
      (TDs: declsofScopeP s (keys slots))
      (* WellBound links: *)
      (LNS: linksofScopeP s [(l, [sl])])
      (SL: scopeofFrame h0 fl sl),
      well_bound h1 f.
  Proof.
    intros; eapply initFrame_well_bound; eauto.
    intros. inv H0. inv H1. eapply linksofScopeDet in LNS; eauto; subst.
    destruct (ELdec l0 l). subst; simpl in *. destruct (ELdec l l); [|intuition].
    inv H2. eexists; split; eauto. split; eauto. intros. inv H1.
    eexists; split; eauto. simpl. destruct (ScopeIdDec s0 s0); intuition.
    inv H2. simpl in H2. destruct (ELdec l0 l); intuition. inv H2.
    intros. simpl in H0. destruct (ELdec l0 l); intuition. subst. inv H0.
    inv LNS. econstructor; split; eauto. simpl. destruct (ELdec l l); intuition.
    inv H0.
  Qed.

  Lemma initFrame_well_bound2 :
    forall
      h0 s  slots f h1 l sl fl l' sl' fl'
      (INIT: initFrame h0 s [(l, [(sl, fl)]); (l', [(sl', fl')])] slots f h1)
      (TDs: declsofScopeP s (keys slots))
      (* WellBound links: *)
      (LNS: linksofScopeP s [(l, [sl]); (l', [sl'])])
      (SL: scopeofFrame h0 fl sl)
      (SL: scopeofFrame h0 fl' sl'),
      well_bound h1 f.
  Proof.
    intros; eapply initFrame_well_bound; eauto.
    intros. inv H0. inv H1. eapply linksofScopeDet in LNS; eauto; subst.
    destruct (ELdec l0 l). subst; simpl in *. destruct (ELdec l l); [|intuition].
    inv H2. eexists; split; eauto. split; eauto. intros. inv H1.
    eexists; split; eauto. simpl. destruct (ScopeIdDec s0 s0); intuition.
    inv H2. simpl in H2. simpl.
    destruct (ELdec l0 l); intuition.
    destruct (ELdec l0 l'); intuition.
    subst. inv H2. eexists; split; simpl; sgauto. split; sgauto. intros.
    destruct H1; inv H1. simpl. destruct (ScopeIdDec s0 s0); [|intuition].
    sgauto. inv H2.
    intros. simpl in H0.
    eexists; split; sgauto. simpl.
    destruct (ELdec l0 l); intuition. subst. inv H0.
    inv LNS. econstructor; split; eauto. simpl. destruct (ELdec l l); intuition.
    destruct (ELdec l0 l'); intuition. inv H0.
    eexists; split; sgauto. inv H0.
  Qed.

  Hint Resolve initFrame_well_bound : sgraph.
  Hint Resolve initFrame_well_bound1 : sgraph.
  Hint Resolve initFrame_well_bound2 : sgraph.

  Lemma initFrame_well_typed :
    forall
      h0 s ks slots f h1
      (INIT: initFrame h0 s ks slots f h1)
      (TDs: declsofScopeP s (keys slots))
    (* WellTyped slots: *)
    (TYP: forall d t v,
            In d (keys slots) ->
            typofDecl d t ->
            get Ddec slots d = Some v -> vtyp h0 v t),
      well_typed h1 f.
  Proof.
    intros; inversion INIT. inv NF. assert (FF':=FF).
    eapply fillFrameSame in FF; try rewrite get_set_same; eauto.
    eexists; sgauto.
    intros. eapply declsofScopeDet in TDs; eauto; subst.
    inv H3. rewrite H4 in FF; inv FF.
    eapply TYP in H1; eauto. eapply initFrame_vtyp; eauto.
  Qed.

  Hint Resolve initFrame_well_typed : sgraph.

  Lemma initFrame_good_frame :
    forall
      h0 s ks slots f h1
      (INIT: initFrame h0 s ks slots f h1)
      (TDs: declsofScopeP s (keys slots))
    (* WellTyped slots: *)
    (TYP: forall d t v,
            In d (keys slots) ->
            typofDecl d t ->
            get Ddec slots d = Some v -> vtyp h0 v t)
    (* WellBound links: *)
    (LNS: forall l ss,
            llinksofScopeP s l ss ->
            exists m,
              get ELdec ks l = Some m /\
              keys m = ss /\
              forall s,
                In s ss ->
                exists f', get ScopeIdDec m s = Some f' /\
                           scopeofFrame h0 f' s)
    (LNF: forall l m,
            get ELdec ks l = Some m ->
            llinksofScopeP s l (keys m)),
      good_frame h1 f.
  Proof.
    intros; sgauto.
  Qed.

  Hint Resolve initFrame_good_frame : sgraph.

  (** ** Public Good Heap and Frame Properties *)

  (** These are the public lemmas that provide structure to type
soundness proofs. *)

  (** In a good heap, for each path that is statically consistent, looking
      up the path dynamically leads to a corresponding frame and declaration.
      (This is Lemma 1 of the paper.) *)
  Lemma good_path :
    forall
      h
      (GH: good_heap h)
      p f s d s'
      (SF: scopeofFrame h f s)
      (SLK: slookup s p s' d),
    exists f', lookup h f p d f' /\ scopeofFrame h f' s'.
  Proof.
    induction p; intros.
    - destruct SLK as [? [? [? [? ?]]]]; subst.
      eexists; split; eauto. econstructor.
      edestruct GH as [WB _]; sgauto.
      eapply well_bound_get; eauto. econstructor; eauto.
    - destruct SLK as [? [? [LL [GL [IN SL]]]]].
      assert (GF: good_frame h f) by (eapply GH; eauto using scopeofFrameFrame).
      inv GF. inv H0. eapply scopeofFrameDet in SF; eauto; subst.
      assert (llinksofScopeP s0 e x0) by (econstructor; eauto).
      eapply LNS in H0.
      destruct H0 as [? [IMF [KEYS IMSC]]]; subst.
      eapply IMSC in IN. inv IN. inv H0.
      eapply IHp in SL; eauto.
      destruct SL as [? [LOOK SF]].
      eexists; split; sgauto.
  Qed.

  (** In practice, we use this corollary of [good_path]:
      In a good heap, each static lookup starting from a reference
      scope corresponds to a dynamic lookup to the address of
      a corresponding scope and declaration. *)

  Corollary good_addr :
    forall
      h r p f s d s'
      (SR: scopeofRefP r s)
      (SLK: rlookup r p s' d)
      (GH: good_heap h)
      (SF: scopeofFrame h f s),
    exists ff, getAddr h f r (Addr_ ff d) /\
               scopeofFrame h ff s' /\
               exists ds,
                 declsofScopeP s' ds /\
                 In d ds.
  Proof.
    intros. destruct SLK as [? [? [? ?]]].
    eapply scopeofRefDet in SR; eauto; subst.
    assert (H2':=H2).
    eapply good_path in H2; eauto.
    destruct H2. destruct H2.
    eexists; split; sgauto. econstructor; sgauto.
    inv H0.
    edestruct path_connectivity' as [? [? SL]]; eauto.
    eapply slookupDet in H2'; eauto. destruct H2'; subst.
    edestruct slookup_ddata as [dd [P1 P2]]; eauto.
  Qed.


  (** It is possible to get any declared field in a good frame. *)
  Corollary good_frame_getSlot :
    forall h f s d ds
           (GF: good_frame h f)
           (SF: scopeofFrame h f s)
           (DS: declsofScopeP s ds)
           (IN: In d ds),
    exists v, getSlot h f d v.
  Proof.
    intros. inv GF. eapply well_bound_get; eauto.
  Qed.

  (** It is possible to set any declared field in a good frame. *)
  Corollary good_frame_setSlot :
    forall
      h f s ds d
      (GF: good_frame h f)
      (SC: scopeofFrame h f s)
      (DS: declsofScopeP s ds)
      (IN: In d ds),
    forall v,
    exists h', setSlot h f d v h'.
  Proof.
    intros. inv GF. eapply well_bound_set; eauto.
  Qed.

  (** Setting a correctly typed value in a slot
      maintains heap goodness. *)
  Lemma setSlot_good_heap :
    forall
      h0 f d v h1 s t
      (SET: setSlot h0 f d v h1)
      (SF: scopeofFrame h0 f s)
      (TD: typofDecl d t)
      (VT': vtyp h0 v t)
      (WT: good_heap h0),
      good_heap h1.
  Proof.
    intros. intro. intro. destruct (FrameIdDec f f0); subst.
    - eapply setSlot_good_frame; eauto. eapply WT. unfold frame. inv SET; eapply keys_in; eauto.
    - eapply setSlot_other_good_frame; eauto. eapply WT.
      inv SET. unfold frame in H0. eapply in_keys in H0. rewrite get_set_other in H0; auto.
      destruct H0. eapply keys_in; eauto.
  Qed.


  (** Initializing a new frame with well-typed slots and well-bound links
      maintains heap goodness. *)
  Lemma initFrame_good_heap :
    forall
      h0 s ks slots f h1
      (GH: good_heap h0)
      (INIT: initFrame h0 s ks slots f h1)
      (TDs: declsofScopeP s (keys slots))
      (* WellTyped slots: *)
      (TYP: forall d t v,
          In d (keys slots) ->
          typofDecl d t ->
          get Ddec slots d = Some v -> vtyp h0 v t)
      (* WellBound links: *)
      (LNS: forall l ss,
          llinksofScopeP s l ss ->
          exists m,
            get ELdec ks l = Some m /\
            keys m = ss /\
            forall s,
              In s ss ->
              exists f', get ScopeIdDec m s = Some f' /\
                         scopeofFrame h0 f' s)
      (LNF: forall l m,
          get ELdec ks l = Some m ->
          llinksofScopeP s l (keys m)),
      good_heap h1.
  Proof.
    intros. unfold good_heap. intros.
    pose proof (initFrameFrames _ _ _ _ _ _ INIT f0). destruct H1.
    apply H2 in H0. destruct H0. subst. eauto using initFrame_good_frame.
    eapply initFrame_other_good_frame in INIT; eauto.
  Qed.

  (** Specialization to a new frame with no links or slots *)
  Corollary initFrame_good_heap0 :
    forall
      h0 s f h1
      (GH: good_heap h0)
      (DS: declsofScopeP s [])
      (PS: linksofScopeP s [])
      (INIT: initFrame h0 s [] [] f h1),
      good_heap h1.
  Proof.
    intros. unfold good_heap. intros.
    eapply initFrame_good_heap; eauto.
    + intros. inv H1.
    + intros. inv H1. destruct H2 as [P1 P2]. eapply linksofScopeDet in PS; eauto; subst. inv P2.
    + intros. inv H1.
  Qed.

  (** Specialization to a new frame with exactly one link *)
  Corollary initFrame_good_heap1 :
    forall
      h0 s slots f h1 l sl fl
      (GH: good_heap h0)
      (INIT: initFrame h0 s [(l, [(sl, fl)])] slots f h1)
      (TDs: declsofScopeP s (keys slots))
      (* WellTyped slots: *)
      (TYP:
         forall
           d t v
           (IN: In d (keys slots))
           (TD: typofDecl d t)
           (GET: get Ddec slots d = Some v),
           vtyp h0 v t)
      (* WellBound links: *)
      (LNS: linksofScopeP s [(l, [sl])])
      (SL: scopeofFrame h0 fl sl),
      good_heap h1.
  Proof.
    intros. unfold good_heap. intros.
    pose proof (initFrameFrames _ _ _ _ _ _ INIT f0). destruct H1.
    apply H2 in H0. destruct H0. subst.
    split; eauto using initFrame_well_typed, initFrame_well_bound1.
    eapply initFrame_other_good_frame in INIT; eauto.
  Qed.

  (* Specialization to a new frame with exactly two links *)
  Lemma initFrame_good_heap2 :
    forall
      h0 s slots f h1 l sl fl l' sl' fl'
      (GH: good_heap h0)
      (INIT: initFrame h0 s [(l, [(sl, fl)]); (l', [(sl', fl')])] slots f h1)
      (TDs: declsofScopeP s (keys slots))
      (* WellTyped slots: *)
      (TYP:
         forall
           d t v
           (IN: In d (keys slots))
           (TD: typofDecl d t)
           (GET: get Ddec slots d = Some v),
           vtyp h0 v t)
      (* WellBound links: *)
      (LNS: linksofScopeP s [(l, [sl]); (l', [sl'])])
      (SL: scopeofFrame h0 fl sl)
      (SL': scopeofFrame h0 fl' sl'),
      good_heap h1.
  Proof.
    intros. unfold good_heap. intros.
    pose proof (initFrameFrames _ _ _ _ _ _ INIT f0). destruct H1.
    apply H2 in H0. destruct H0. subst.
    split; eauto using initFrame_well_typed, initFrame_well_bound2.
    eapply initFrame_other_good_frame in INIT; eauto.
  Qed.

End Goodness.

Hint Resolve setSlot_good_heap : sgraph.
Hint Resolve getAddr_scopeofFrame : sgraph.
Hint Resolve good_addr : sgraph.
Hint Resolve initFrame_good_frame : sgraph.
Hint Resolve initFrame_good_heap : sgraph.
Hint Resolve initFrame_good_heap1 : sgraph.
Hint Resolve initFrame_good_heap2 : sgraph.

(** * Defaults

This class defines a [default] value for each type.
*)

Class DefaultVTyp `{VT: VTyp} :=
  { default : T -> V -> Prop ;
    default_vtyp :
      forall v t,
        default t v -> forall h, vtyp h v t

  }.

Section DefaultVTypProperties.

  Context `{DVT : DefaultVTyp}.

  (** ** Defaults for Slots *)

  Inductive defaults (s: ScopeId) : map D V -> Prop :=
  | defaults_nil : defaults s []
  | default_cons :
      forall
        d slots t v
        (TD: typofDecl d t)
        (DF: default t v)
        (TAIL: defaults s slots),
        defaults s ((d,v) :: slots).

  Lemma defaults_vtyp :
    forall
      s slots
      (DF: defaults s slots)
      ts
      (TDs: typofDecls (keys slots) ts)
      h,
      Forall2 (fun dv t =>
                 match dv, t with
                 | (_, v), t =>
                   vtyp h v t
                 end) slots ts.
  Proof.
    induction 1; intros. inv TDs; eauto.
    inv TDs. eapply typofDeclDet in TD; eauto; subst.
    eapply default_vtyp in DF; eauto.
  Qed.

  Lemma defaults_vtyp' :
    forall
      s slots
      (DF: defaults s slots),
    forall d t v,
      In d (keys slots) ->
      typofDecl d t ->
      get Ddec slots d = Some v ->
      forall h,
        vtyp h v t.
  Proof.
    induction 1; intros.
    - inv H0.
    - simpl in *. destruct (Ddec d d0); subst.
      eapply typofDeclDet in H1; eauto; subst.
      destruct (Ddec d0 d0); inv H2; auto. apply default_vtyp; auto. intuition.
      destruct H0; [contradiction|]. destruct (Ddec d0 d); subst; [intuition|].
      eauto.
  Qed.

  Hint Resolve defaults_vtyp' : sgraph.

  (** ** Defaults for Frames *)

  (** Corresponds to Fig. 20 in the paper. *)

  Inductive initDefault
            (h0: H)
            (s: ScopeId) (ks: map EdgeLabel (map ScopeId FrameId))
            (f: FrameId) (h1: H) : Prop :=
  | initDefault_ : forall
      slots
      (DS: declsofScopeP s (keys slots))
      (DF: defaults s slots)
      (NF: initFrame h0 s ks slots f h1),
      initDefault h0 s ks f h1.

  Lemma initDefaultFrames :
    forall h0 s ks f0 h1,
      initDefault h0 s ks f0 h1 ->
      forall f, f = f0 \/ frame h0 f <-> frame h1 f.
  Proof.
    inversion 1; eauto using initFrameFrames.
  Qed.

  Lemma initDefaultDiff_scopeofFrame :
    forall h0 f0 s0 s ks f h1,
      initDefault h0 s ks f h1 ->
      scopeofFrame h0 f0 s0 ->
      scopeofFrame h1 f0 s0.
  Proof.
    intros. inv H0. eapply initFrameDiff_scopeofFrame; eauto.
  Qed.

  Lemma initDefaultSame_scopeofFrame :
    forall h0 s ks f0 h1,
      initDefault h0 s ks f0 h1 ->
      scopeofFrame h1 f0 s.
  Proof.
    intros. inv H0. eapply initFrameSame_scopeofFrame; eauto.
  Qed.

  Lemma initDefault_vtyp: forall
      h0 s ks f h1 v0 t0
      (INF: initDefault h0 s ks f h1)
      (VT: vtyp h0 v0 t0),
      vtyp h1 v0 t0.
  Proof.
    inversion 1; intros; eauto using initFrame_vtyp.
  Qed.

  Lemma initDefault_good_frame :
    forall h0 s ks f h1
      (INIT: initDefault h0 s ks f h1)
    (* WellBound links: *)
    (LNS: forall l ss,
            llinksofScopeP s l ss ->
            exists m,
              get ELdec ks l = Some m /\
              keys m = ss /\
              forall s,
                In s ss ->
                exists f', get ScopeIdDec m s = Some f' /\
                           scopeofFrame h0 f' s)
    (LNF: forall l m,
            get ELdec ks l = Some m ->
            llinksofScopeP s l (keys m)),
      good_frame h1 f.
  Proof.
    intros. inv INIT. eapply initFrame_good_frame;  sgauto.
  Qed.

  (** ** Public Good Heap Properties for Defaults *)

  (** These are the public lemmas that provide structure to type
soundness proofs.  *)

  (** Initializing a new frame with default slot values nd well-bound links
      maintains heap goodness. *)
  Lemma initDefault_good_heap :
    forall h0 s ks f h1
      (GH: good_heap h0)
      (INIT: initDefault h0 s ks f h1)
    (* WellBound links: *)
    (LNS: forall l ss,
            llinksofScopeP s l ss ->
            exists m,
              get ELdec ks l = Some m /\
              keys m = ss /\
              forall s,
                In s ss ->
                exists f', get ScopeIdDec m s = Some f' /\
                           scopeofFrame h0 f' s)
    (LNF: forall l m,
            get ELdec ks l = Some m ->
            llinksofScopeP s l (keys m)),
      good_heap h1.
  Proof.
    inversion 2; intros; sgauto.
  Qed.

  (* Specialization for frames with no links *)
  Corollary initDefault_good_heap0 :
    forall h0 s f h1
      (GH: good_heap h0)
      (PS: linksofScopeP s [])
      (INIT: initDefault h0 s [] f h1),
      good_heap h1.
  Proof.
    intros. unfold good_heap. intros.
    eapply initDefault_good_heap; sgauto.
    + intros. inv H1. destruct H2.
      inv PS. rewrite H1 in H4; inv H4.  inv H2.
    + intros. inv H1.
  Qed.

  (* Specialization for frames with one link. *)
  Lemma initDefault_good_heap1 :
    forall h0 s f h1 l sl fl
      (GH: good_heap h0)
      (INIT: initDefault h0 s [(l, [(sl, fl)])] f h1)
    (* WellBound links: *)
    (LNS: linksofScopeP s [(l, [sl])])
    (SL: scopeofFrame h0 fl sl),
      good_heap h1.
  Proof.
    intros. unfold good_heap. intros. inv INIT.
    pose proof (initFrameFrames _ _ _ _ _ _ NF f0). destruct H1.
    apply H2 in H0. destruct H0. subst.
    split; eauto using initFrame_well_bound1, initFrame_well_typed, defaults_vtyp'.
    eapply initFrame_other_good_frame in NF; eauto.
  Qed.

End DefaultVTypProperties.

Hint Resolve defaults_vtyp' : sgraph.
Hint Resolve initDefaultSame_scopeofFrame : sgraph.
Hint Resolve initDefaultDiff_scopeofFrame : sgraph.
Hint Resolve initDefault_good_frame : sgraph.
Hint Resolve initDefault_good_heap : sgraph.
Hint Resolve initDefault_good_heap0 : sgraph.
Hint Resolve initDefault_good_heap1 : sgraph.
