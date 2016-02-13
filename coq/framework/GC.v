Require Import maps scopes frames.

Class VRefers {V: Type} :=
 { vrefers : V -> FrameId -> Prop (* (vrefers v f) means v refers directly to f *)
 }.

Section VRefersProperties.

    Context {V:Type} {VR: @VRefers V} {FH: @FrameHeap V}.


    (* (frefers f f') means f refers directly to f' *)
    Inductive frefers (h: H) : FrameId -> FrameId -> Prop :=
    | fr_link : forall f links,
              linksofFrame V FH h f links -> 
              forall m, In m (values links) ->
              forall f', In f' (values m) -> 
              frefers h f f'
    | fr_slot : forall f slots,
              getSlots V FH h f slots -> 
              forall v, In v (values slots) -> 
              forall f', vrefers v f' ->
              frefers h f f'.

    Hint Constructors frefers : sgraph.

    Lemma removeFrame_frefers: 
      forall h0 h1 f0 f1 f2, 
      removeFrame V FH h0 f0 h1 ->
      (frefers h1 f1 f2 <-> (frefers h0 f1 f2 /\ f0 <> f1)).
    Proof.
     intros. 
     split; intros. 
     + inv H0.  
       - inv H1. erewrite removeFrameSame in H0; eauto. inv H0; sgauto.
       - inv H1. erewrite removeFrameSame in H0; eauto. inv H0; sgauto. 
     + inv H0. inv H1.          
       - inv H0. econstructor; eauto. econstructor. erewrite removeFrameSame; sgauto.  
       - inv H0. eapply fr_slot; eauto. econstructor. erewrite removeFrameSame; sgauto.
    Qed.  

    Lemma removeFrames_frefers: forall h0 h1 fs f1 f2, 
                         removeFrames V FH h0 fs h1 ->
                         (frefers h1 f1 f2 <-> (frefers h0 f1 f2 /\ ~ In f1 fs)).
    Proof.
     intros. induction H. intuition.
     split; intros.  
     + rewrite IHremoveFrames in H1. inv H1. 
       eapply removeFrame_frefers in H.  rewrite H in H2.  inv H2. split; auto. 
         intro. inv H2; auto. 
     + rewrite IHremoveFrames. inv H1.  split.
       - eapply removeFrame_frefers; eauto.  split; eauto. intro. subst. apply H3. left; auto.
       - intro; apply H3; right; auto. 
    Qed.
 
  (* Possible extension to reachability. Not used at the moment. *)
  (* (reachable f f') means f' is reachable from f *)
  (* Just the reflexive transitive closure of frefers *)
  Inductive reachable (h: H) : FrameId -> FrameId -> Prop :=
  | re_refl : forall f, reachable h f f
  | re_fref: forall f f' f'', frefers h f f' -> reachable h f' f'' -> reachable h f f''.
            
  Definition unreferenced (h: H) (f: FrameId) : Prop :=
    forall f0, frame h f0 -> ~ frefers h f0 f.

  (* It is "safe" to drop a set of frames from the heap
     if doing so does not result in any new dangling pointers. 
     This gives a very high-level notion of safe garbage collection. *)

  Inductive drop_safely (h0 h1 : H) : Prop :=
  | ds : forall fs,
           removeFrames V FH h0 fs h1 -> 
           (forall f, In f fs -> unreferenced h1 f) -> 
           drop_safely h0 h1. 

  (* Simulating non-deterministic, incomplete reference counting. *)
  (* Drop an unreferenced frame. *)
  Inductive drop_unreferenced (h0 h1 : H) : Prop :=
  | dunr : forall f,
             unreferenced h0 f -> 
             removeFrame V FH h0 f h1 -> 
             drop_unreferenced h0 h1. 

  Lemma drop_unreferenced_safe : forall h0 h1, drop_unreferenced h0 h1 -> drop_safely h0 h1. 
  Proof.
    intros.  inv H. econstructor. 
    econstructor.  eauto. econstructor. 
    intros. inv H. 
    unfold unreferenced in *. intros. intro. eapply H0. eapply removeFrameFrames0 in H1.  apply H1 in H.  inv H.  apply H4.  
    rewrite (removeFrame_frefers h0) in H2. inv H2; auto.   eauto.  
    inv H2. 
  Qed.

  (* Simulating complete reference counting. *)
  (* Drop exactly the unreferenced frames. *)
  Inductive drop_all_unreferenced (h0 h1 : H) : Prop :=
  | daunr: forall fs,
             (forall f, unreferenced h0 f <-> In f fs) ->
             removeFrames V FH h0 fs h1 -> 
             drop_all_unreferenced h0 h1. 
  

  Lemma drop_all_unreferenced_safe : forall h0 h1, drop_all_unreferenced h0 h1 -> drop_safely h0 h1. 
  Proof.
    intros. inv H. econstructor; eauto. 
    intros. rewrite <- H0 in H.  unfold unreferenced in *. 
    intros.  intro. eapply (H f0). 
    eapply removeFramesFrames in H2; eauto. intuition.
    erewrite removeFrames_frefers in H3; eauto. intuition.
  Qed.

  (* Simulating reachability-based gc with respect to a root set. *)
  (* Drop exactly the frames unreachable from some (arbitrary) root set. *)
  Inductive drop_all_unreachable (h0 : H) (roots: list FrameId) (h1: H): Prop :=
  | dunreach : forall fs,
                 (forall f, In f fs <-> (forall f0, In f0 roots -> ~ reachable h0 f0 f)) -> 
                 removeFrames V FH h0 fs h1 -> 
                 drop_all_unreachable h0 roots h1. 

  Lemma drop_all_unreachable_safe : 
    forall h0 h1 roots, 
      drop_all_unreachable h0 roots h1 -> 
      drop_safely h0 h1.
  Proof.
    intros.
    inv H. econstructor; eauto. 
    intros. rewrite H0 in H. 
    unfold unreferenced. intros. intro.
    erewrite removeFrames_frefers in H3; eauto. inv H3.  
    apply H5.
    rewrite H0. 
    intros. 
    intro.
    eapply H. 
    eauto.
    clear - H4 H6.
    induction H6.
    econstructor.  eauto. econstructor.
    econstructor. eauto. eauto.
  Qed.      


End VRefersProperties.


Section VTypRefers.

  Context {T V: Type} {VT: @VTyp T V} {VR:@VRefers V}.

  (* Ideally this should be in a suitable class. *)
  Hypothesis removeFrames_vtyp :
      forall h1 fs h2 v0 t0
        (RM: removeFrames V fh h1 fs h2)
        (NR: forall f, vrefers v0 f -> ~ In f fs)
        (VT: vtyp h1 v0 t0),
        vtyp h2 v0 t0.


  Lemma good_heap_drop_safely : 
    forall h1, 
      good_heap T V VT h1 -> 
      forall h2, drop_safely h1 h2 -> 
                 good_heap T V VT h2. 
  Proof.
    intros. inv H0. 
    unfold good_heap in *.  intros. 
    eapply removeFramesFrames in H0; eauto. destruct H0. 
    pose proof (H f H3).
    inv H4. 
    econstructor. 
    
    inv H5. econstructor.

    eapply removeFramesScope; eauto. 

    intros. destruct (DSS ds0 H4) as [slots [P1 P2]].
    exists slots. split. inv P1. econstructor. eapply removeFramesSame; eauto.  auto.

    intros. inv H4. eapply removeFramesSame in H5; eauto. destruct H5. 
    edestruct (DSF slots) as [ds [P1 P2]]. econstructor; eauto.
    exists ds; eauto.

    intros. destruct (LNS l ss H4) as [ks [P1 [P2 P3]]]. subst ss. 
    inv P1. inv H5. exists ks. split. econstructor. econstructor. eapply removeFramesSame; eauto.
    auto. split; auto. intros.  destruct (P3 s1 H5) as [f' [Q1 Q2]]. exists f'; split; eauto.
    eapply removeFramesScope; eauto. split; eauto.

    intro. apply H2 in H9. eapply H9.  
    eapply removeFramesFrames; eauto.
    econstructor. 
    econstructor. eapply removeFramesSame; eauto.
    eapply values_in; eauto. 
    eapply values_in; eauto.

    intros. eapply LNF. inv H4. inv H5. econstructor; eauto.  econstructor. 
    eapply removeFramesSame in H4; eauto. destruct H4; eauto.

    inv H6. econstructor; eauto. 

    eapply removeFramesScope; eauto.

    intros.
    eapply removeFrames_vtyp; eauto.  intros. 
    intro.  apply H2 in H9. eapply H9. 
    eapply removeFramesFrames; eauto.
    inv H7. 
    eapply fr_slot.
    econstructor; eauto. 
    eapply values_in; eauto. eauto.
    eapply WT; eauto. inv H7. econstructor; eauto. 
    eapply removeFramesSame in H8; eauto. destruct H8; eauto.
  Qed.

  Corollary good_heap_drop_unreferenced:
    forall (h1: H),
      good_heap T V VT h1 ->
      forall h2, drop_unreferenced h1 h2 -> 
                 good_heap T V VT  h2.                                                     
  Proof.
    intros.  eapply good_heap_drop_safely; eauto. 
    eapply drop_unreferenced_safe; eauto.
  Qed.


  Corollary good_heap_drop_unreachable:
    forall (h1: H),
      good_heap T V VT h1 ->
      forall rs h2, drop_all_unreachable h1 rs h2 -> 
                    good_heap T V VT h2.                                                     
  Proof.
    intros.  eapply good_heap_drop_safely; eauto. 
    eapply drop_all_unreachable_safe; eauto.
  Qed.

End VTypRefers.