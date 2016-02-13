Require Export List maps.
Export ListNotations.
Ltac inv H := (inversion H; subst; clear H).

(** Globally available definitions *)
Section ScopeGlobals.

  (** We use nat for identifiers. *)
  Definition ident := nat.
  Inductive R :=
    Re: ident -> nat -> R. (* name, AST position *)
  Lemma Rdec: forall (r1 r2:R), {r1 = r2} + {r1 <> r2}.
  Proof.
    repeat (decide equality).
  Qed.

  Inductive D :=
    De : ident -> nat -> D.
  Lemma Ddec: forall (d1 d2:D), {d1 = d2} + {d1 <> d2}.
  Proof.
    repeat (decide equality).
  Qed.

  Definition ScopeId := nat.
  Lemma ScopeIdDec: forall (s1 s2:ScopeId), {s1 = s2} + {s1 <> s2}.
  Proof.
    repeat (decide equality).
  Qed.

  (** Utility definition for disjointness of list members *)
  Definition Disjoint {X:Type} (l1 l2: list X) :=
    forall (x:X), In x l1 -> ~ In x l2.

  (** ** Labels *)

  (** The following definitions of labels suffices for current
  purposes: *)
  Inductive EdgeLabel := P | I.
  Lemma ELdec : forall (l1 l2: EdgeLabel), {l1 = l2} + {l1 <> l2}.
  Proof.
    repeat (decide equality).
  Qed.

  (** ** Paths *)
  Inductive path :=
  | Dp : D -> path
  | Ep : EdgeLabel -> ScopeId -> path -> path
  .

  Fixpoint declofPath (p:path) : D :=
    match p with
    | Dp d => d
    | Ep _ _ p => declofPath p
    end.

End ScopeGlobals.

Class Graph :=
  { DData : Type ;
    Scope := (((map R path) * (map D DData))%type * (map EdgeLabel (list ScopeId)))%type ;
    graph := map ScopeId Scope ;

    (** Projection functions *)
    ddataofScope (g: graph) : ScopeId -> option (map D DData) :=
      fun (s: ScopeId) =>
        match get ScopeIdDec g s with
        | Some dd => Some (snd (fst  dd))
        | None => None
        end ;
    refsofScope (g: graph) : ScopeId -> option (map R path) :=
      fun (s: ScopeId) =>
        match get ScopeIdDec g s with
        | Some dd => Some (fst (fst dd))
        | None => None
        end ;
    linksofScope (g: graph) : ScopeId -> option (map EdgeLabel (list ScopeId)) :=
      fun (s: ScopeId) =>
        match get ScopeIdDec g s with
        | Some dd => Some (snd dd)
        | None => None
        end ;
    llinksofScopeP (g: graph) (s: ScopeId) (l: EdgeLabel) (ss: list ScopeId) : Prop :=
      exists ks, linksofScope g s = Some ks /\ get ELdec ks l = Some ss ;
    slookup (g: graph) : ScopeId -> path -> ScopeId -> D -> Prop :=
      fix slook s p s' d :=
        match p with
        | Dp d' => d = d' /\ s = s'
        | Ep l s'' p' =>
          exists ss, llinksofScopeP g s l ss /\
                     In s'' ss /\
                     slook s'' p' s' d
        end ;
    scopeofRef : graph -> R -> option ScopeId :=
      fix sref (g': graph) r :=
        match g' with
        | [] => None
        | (s,(rs,_,_)) :: g'' =>
          match get Rdec rs r with
          | Some _ => Some s
          | _ => sref g'' r
          end
        end ;
    scopeofDecl : graph -> D -> option ScopeId :=
      fix sdec (g': graph) d :=
        match g' with
        | [] => None
        | (s,(_,ds,_)) :: g'' =>
          match get Ddec ds d with
          | Some _ => Some s
          | _ => sdec g'' d
          end
        end ;
    pathofRef (g: graph) : R -> option path :=
      fun r =>
        match scopeofRef g r with
        | Some s =>
          match refsofScope g s with
          | Some m => get Rdec m r
          | _ => None
          end
        | _ => None
        end
  }.

(* Describes well-connected graph instances: *)
Class WellConnected (sg : Graph) :=
  { g : graph ;
    path_connectivity :
      (forall r p s,
          pathofRef g r = Some p ->
          scopeofRef g r = Some s ->
          (exists d sd dd, slookup g s p sd d /\ ddataofScope g sd = Some dd /\ In d (keys dd))) ;
    path_unicity :
      (forall r s p sd d sd' d',
          pathofRef g r = Some p ->
          slookup g s p sd d ->
          slookup g s p sd' d' ->
          sd = sd' /\ d = d') }.

Section GraphProperties.
  Context {G : Graph} (C : WellConnected G).

  (** Predicate wrappers: *)
  Definition ddataofScopeP (s: ScopeId) (ds: map D DData) : Prop :=
    ddataofScope g s = Some ds.
  Definition declsofScopeP (s: ScopeId) (ds: list D) : Prop :=
    exists dd, ddataofScope g s = Some dd /\ ds = keys dd.
  Definition refsofScopeP (s: ScopeId) (rs: list R) : Prop :=
    exists m, refsofScope g s = Some m /\ rs = keys m.
  Definition linksofScopeP (s: ScopeId) (ks: map EdgeLabel (list ScopeId)) :=
    linksofScope g s = Some ks.
  Definition scopeofDeclP (d: D) (s: ScopeId) : Prop :=
    scopeofDecl g d = Some s.
  Definition scopeofRefP (r: R) (s: ScopeId) : Prop :=
    scopeofRef g r = Some s.
  Definition pathofRefP (r: R) (p: path) : Prop :=
    pathofRef g r = Some p.

  Definition rlookup (s: ScopeId) (r: R) (p: path) (s': ScopeId) (d': D) :=
    scopeofRefP r s /\ pathofRefP r p /\ slookup g s p s' d'.

  Lemma ddataofScopeDet :
    forall s ds1 ds2,
      ddataofScopeP s ds1 ->
      ddataofScopeP s ds2 ->
      ds1 = ds2.
  Proof.
    intros. inv H. inv H0. rewrite H1 in H2. inv H2; auto.
  Qed.

  Lemma declsofScopeDet :
    forall s ds1 ds2,
      declsofScopeP s ds1 ->
      declsofScopeP s ds2 ->
      ds1 = ds2.
  Proof.
    intros. destruct H as [? [DD DS]]. destruct H0 as [? [DD' DS']].
    rewrite DD' in DD; inv DD; auto.
  Qed.

  Lemma scopeofDeclDet :
    forall d s s',
      scopeofDeclP d s ->
      scopeofDeclP d s' ->
      s = s'.
  Proof.
    intros. inv H. inv H0. rewrite H1 in H2; inv H2; auto.
  Qed.

  Lemma linksofScopeDet : forall s ims ims',
      linksofScopeP s ims ->
      linksofScopeP s ims' ->
      ims = ims'.
  Proof.
    intros. inv H. inv H0. rewrite H1 in H2; inv H2; auto.
  Qed.

  Lemma llinksofScopeDet : forall s l ims ims',
      llinksofScopeP g s l ims ->
      llinksofScopeP g s l ims' ->
      ims = ims'.
  Proof.
    intros. inv H. destruct H1. inv H0.  destruct H2.
    rewrite H0 in H; inv H.
    rewrite H1 in H2; inv H2; auto.
  Qed.


  (** Extracting the associated declaration data: *)
  Inductive assocData (d: D) : (@DData G) -> Prop :=
  | assocData_ :
      forall s ds p,
        scopeofDecl g d = Some s ->
        ddataofScope g s = Some ds ->
        get Ddec ds d = Some p ->
        assocData d p.

  Lemma assocDataDet :
    forall d dd,
      assocData d dd ->
      forall dd',
        assocData d dd' ->
        dd = dd'.
  Proof.
    intros. inv H. inv H0.
    eapply scopeofDeclDet in H1; eauto; subst.
    eapply ddataofScopeDet in H2; eauto; subst.
    rewrite H5 in H3. inv H3; auto.
  Qed.

  Lemma refsofScopeDet :
    forall s rs1 rs2,
      refsofScopeP s rs1 ->
      refsofScopeP s rs2 ->
      rs1 = rs2.
  Proof.
    intros. destruct H as [? [? ?]]. destruct H0 as [? [? ?]]. subst.
    rewrite H0 in H; inv H; auto.
  Qed.

  Lemma scopeofRefDet :
    forall d s s',
      scopeofRefP d s ->
      scopeofRefP d s' ->
      s = s'.
  Proof.
    intros. inv H. inv H0.
    destruct (ScopeIdDec s s'); auto. destruct G. rewrite H2 in H1; inv H1; auto.
  Qed.

  Lemma pathofRefDet :
    forall r p1,
      pathofRefP r p1 ->
      forall p2,
        pathofRefP r p2 ->
        p1 = p2.
  Proof.
    intros. unfold pathofRefP in H, H0. rewrite H0 in H; inv H; auto.
  Qed.

  (** TODO: What to do about dynamic declarations...? *)

  (* Dynamic: the declaration has a dynamic frame entry (e.g is a variable). *)
  Parameter dynamicDecl : ScopeId -> D -> Prop.
  Definition dynamicDecls (s: ScopeId) (ds:list D) : Prop :=
    forall d, In d ds -> dynamicDecl s d.

  Inductive declofRef (r:R) (d:D) : Prop :=
  | declofRef_ : forall
      p
      (PR: pathofRefP r p),
      d = declofPath p ->
      declofRef r d.

  Lemma declofRefDet :
    forall r d1 d2,
      declofRef r d1 -> declofRef r d2 -> d1 = d2.
  Proof.
    intros. inv H. inv H0. rewrite (pathofRefDet _ _ PR _ PR0). reflexivity.
  Qed.

  Definition declsofRefs (rs: list R) (ds: list D) : Prop :=
    Forall2 declofRef rs ds.

  (* Results of resolution.
     We expect every R in the graph to appear in this relation.
     Resolutions are unique. *)
  Definition assocDataofRef r s :=
    exists d, declofRef r d /\ assocData d s.
  Lemma assocDataofRefDet :
    forall r dd dd',
      assocDataofRef r dd ->
      assocDataofRef r dd' ->
      dd = dd'.
  Proof.
    intros.
    destruct H as [? [DR1 ASC1]]. destruct H0 as [? [DR2 ASC2]].
    eapply declofRefDet in DR1; eauto; subst.
    eapply assocDataDet in ASC1; eauto.
  Qed.

  Lemma slookup_declofPath :
    forall p g s d sd,
      slookup g s p sd d ->
      d = declofPath p.
  Proof.
    induction p; inversion 1; subst; eauto.
    destruct H0 as [? [? ?]]. eauto.
  Qed.

  (** Deprecated: *)
  Definition parentofScope (s:ScopeId) (p:option ScopeId) :=
    exists ps, llinksofScopeP g s P ps /\
               match p, ps with
               | None, nil => True
               | Some s, _ => In s ps
               | _, _ => False
               end.

End GraphProperties.

(* Graph with Associated scopes and Types. *)

Instance GAT {T : Type} : Graph :=
  { DData := ((option ScopeId) * T)%type  }.

(* Well-Connected Graph with Associated scopes and Types *)
Class WCGAT {T : Type} :=
  { gat := @GAT T ;
    wc : WellConnected gat
  }.

Section RGATProperties.

  Context (T : Type) (G : @WCGAT T).

  Inductive typofDecl (s: ScopeId) (d: D) (t: T) : Prop :=
  | typofDecl_ :
      forall ds (dd : ((option ScopeId) * T)),
        ddataofScope (@g gat wc) s = Some ds ->
        get Ddec ds d = Some dd ->
        t = snd dd ->
        typofDecl s d t.

  Lemma typofDeclDet :
    forall d s t1 t2,
      typofDecl d s t1 ->
      typofDecl d s t2 ->
      t1 = t2.
  Proof.
    intros. inv H. inv H0. rewrite H1 in H; inv H. rewrite H2 in H3; inv H3.
    reflexivity.
  Qed.

  (** TODO: What to do about dynamic decls...? *)
  Parameter dynamicDeclHasType :
    forall s d,
      dynamicDecl s d ->
      exists t, typofDecl s d t.

  Definition typofDecls (s: ScopeId) (ds: list D) (ts: list T) : Prop :=
    Forall2 (typofDecl s) ds ts.

  Definition typofSDecls (dss: list (ScopeId * D)) (ts: list T) : Prop :=
    Forall2 (fun ds t => match ds with (s, d) => typofDecl s d t end) dss ts.

  Lemma typofDeclsDet :
    forall s ds t1s t2s,
      typofDecls s ds t1s -> typofDecls s ds t2s -> t1s = t2s.
  Proof.
    induction ds; intros.
    inversion H0; subst; inversion H; eauto.
    inversion H0; subst; inversion H; subst.
    f_equal; eauto using typofDeclDet, IHds.
  Qed.

  Lemma typofSDeclsDet :
    forall dss t1s t2s,
      typofSDecls dss t1s -> typofSDecls dss t2s -> t1s = t2s.
  Proof.
    induction dss; intros.
    inversion H0; subst; inversion H; eauto.
    inversion H0; subst; inversion H; subst. destruct a.
    eapply typofDeclDet in H3; eauto; subst.
    f_equal; eauto.
  Qed.

  Lemma rlookupDet :
    forall s r p s' d' p' s'' d'',
      rlookup wc s r p s' d' ->
      rlookup wc s r p' s'' d'' ->
      p = p' /\ s' = s'' /\ d' = d''.
  Proof.
    do 2 destruct 1 as [? [? ?]].
    eapply pathofRefDet in H0; eauto; subst.
    eapply path_unicity in H1; eauto. destruct H1; subst. auto.
  Qed.

  (** TODO: What to do dynamic decls...? *)
  Lemma dynamicDeclsHaveTypes :
    forall s ds,
      dynamicDecls s ds ->
      exists ts, Forall2 (typofDecl s) ds ts.
  Proof.
    induction ds; intros. eexists; eauto.
    assert (dynamicDecls s ds). intro. intro. specialize (H d).
    apply H. destruct (Ddec d a). subst. constructor; auto. constructor 2. auto.
    apply IHds in H0. inv H0.
    specialize (H a).
    eapply dynamicDeclHasType in H. inv H. eexists; econstructor; eauto.
    econstructor; auto.
  Qed.

  (** ** Associated scopes *)
  Inductive assocScope (s: ScopeId) (d: D) (s': ScopeId) : Prop :=
  | assocScope_ :
      forall ds dd,
        ddataofScope (@g gat wc) s = Some ds ->
        get Ddec ds d = Some dd ->
        Some s' = fst dd ->
        assocScope s d s'.

  (* To consider for the future: label each associated scope (using the existing label set) *)

  Lemma assocScopeDet :
    forall s d s1 s2,
      assocScope s d s1 ->
      assocScope s d s2 ->
      s1 = s2.
  Proof.
    intros. inv H. inv H0. rewrite H in H1; inv H1. rewrite H4 in H2; subst; inv H2.
    rewrite <- H5 in H3; inv H3. reflexivity.
  Qed.

  (* Definition assocScopeofRef s r s' := *)
  (*   exists d, declofRef wc r d /\ assocScope s d s'. *)
  (* Lemma assocScopeofRefDet : *)
  (*   forall s r s' s'', *)
  (*     assocScopeofRef s r s' -> *)
  (*     assocScopeofRef s r s'' -> *)
  (*     s' = s''. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct H as [? [DR1 ASC1]]. destruct H0 as [? [DR2 ASC2]]. *)
  (*   eapply declofRefDet in DR1; eauto; subst. *)
  (*   eapply assocScopeDet in ASC1; eauto. *)
  (* Qed. *)

  Definition assocScopeofRef s r s'' :=
    exists p' s' d, rlookup wc s r p' s' d /\ assocScope s' d s''.
  Lemma assocScopeofRefDet :
    forall s r s' s'',
      assocScopeofRef s r s' ->
      assocScopeofRef s r s'' ->
      s' = s''.
  Proof.
    intros.
    destruct H as [? [? [? [DR1 ASC1]]]].
    destruct H0 as [? [? [? [DR2 ASC2]]]].
    eapply rlookupDet in DR1; eauto. destruct DR1 as [? [? ?]]; subst.
    eapply assocScopeDet in ASC1; eauto.
  Qed.

End RGATProperties.
