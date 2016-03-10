Require Export List maps.
Export ListNotations.

Ltac inv H := (inversion H; subst; clear H).

Ltac sgauto := autounfold with sgraph; eauto with sgraph.

(** * Basic Definitions *)

(** We define scope identifiers, declarations, and labels used in the
definition of scope graphs below (corresponding to the definition in
Fig. 5 in the paper) *)

Definition ident := nat.

(** [R]eferences, given by a name [ident]ifier and an AST position. *)
Inductive R :=
  Re: ident -> nat -> R.
Lemma Rdec: forall (r1 r2:R), {r1 = r2} + {r1 <> r2}.
Proof.
  repeat (decide equality).
Qed.

(** [D]eclarations, given by a name [ident]ifier and an AST
position. *)
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

(** [EdgeLabel]s (corresponds to _Label_ in Fig. 5 in the paper). *)

Inductive EdgeLabel := P | I.  (* for now *)

Lemma ELdec : forall (l1 l2: EdgeLabel), {l1 = l2} + {l1 <> l2}.
Proof.
  repeat (decide equality).
Qed.

(** [path]s (corresponding to Fig. 6 in the paper). *)

Inductive path :=
| Dp : D -> path
| Ep : EdgeLabel -> ScopeId -> path -> path
.

(** Extracting the target declaration from a path. *)

Fixpoint declofPath (p:path) : D :=
  match p with
  | Dp d => d
  | Ep _ _ p => declofPath p
  end.

(** * Scope graphs.

We use a type class to package [Scope] and [graph] so that Coq can
automatically infer the [DData] type from the context; this provides
similar type inference convenience as Canonical Structures.

The [DData] type will be instantiated with pairs of optional
associated scopes and types later. Having [DData] as a type parameter
is a generalization that we expect to exploit in future work. *)

Class Graph {DData: Type} :=
  {
(** A [Scope] consists of:

- A finite map from [R]eferences to their resolution [path]s.

- A finite map from [D]eclarations to associated [DData], which is a
  kept as a parameter of this definition.

- A finite map from [EdgeLabel]s to sets of [ScopeId]s, representing
  the labeled links from this scope to other scopes. *)
    Scope := (((map R path) * (map D DData))%type * (map EdgeLabel (list ScopeId)))%type ;

(** A scope graph is compactly represented as a finite map from
[ScopeId]s to [Scope]s.  *)
    graph := map ScopeId Scope ;

    g: graph ;

(**
Projecting the paths out of a scope.
*)
    pathsofScope (s: ScopeId) : option (map R path) :=
      match get ScopeIdDec g s with
      | Some dd => Some (fst (fst dd))
      | None => None
      end ;
(** References occur in exactly one scope in a scope graph. *)
    uniqueRefs :
      forall r s1 s2 m1 m2 p1 p2,
        pathsofScope s1 = Some m1 ->
        pathsofScope s2 = Some m2 ->
        get Rdec m1 r = Some p1 ->
        get Rdec m2 r = Some p2 ->
        s1 = s2 ;

(** Projecting auxiliary data out of a scope (such as type
information, associated scopes -- we provide instantiations of this
[DData] later). *)
    ddataofScope (s: ScopeId) : option (map D DData) :=
      match get ScopeIdDec g s with
      | Some dd => Some (snd (fst  dd))
      | None => None
      end ;
(** Declarations occur in exactly one scope in a scope graph. *)
    uniqueDecls: forall d s1 s2 m1 m2 dd1 dd2,
        ddataofScope s1 = Some m1 ->
        ddataofScope s2 = Some m2 ->
        get Ddec m1 d = Some dd1 ->
        get Ddec m2 d = Some dd2 ->
        s1 = s2 ;

(** Projecting the links from a scope (K(s) om Fig. 5 in the
paper): *)
    linksofScope (s: ScopeId) : option (map EdgeLabel (list ScopeId)) :=
      match get ScopeIdDec g s with
      | Some dd => Some (snd dd)
      | None => None
      end ;

(** The containing scope for a reference is the (sole) one that
    has a path associated with that reference. *)
    scopeofRef (r:R) : option ScopeId :=
      (fix f ss :=
         match ss with
         | s::ss' =>
           match pathsofScope s with
           | Some mp =>
             match get Rdec mp r with
             | Some _ => Some s
             | _ => f ss'
             end
           | _ => f ss'
           end
         | [] => None
         end) (keys g) ;

(** Returns the path of a reference, if the reference exists in the
scope graph: *)
    pathofRef (r: R) : option path :=
      match scopeofRef r with
      | Some s =>
        match pathsofScope s with
        | Some m => get Rdec m r
        | _ => None
        end
      | _ => None
      end ;

(** The containing scope for a declaration is the (sole) one that has [DData]
    associated associated with that declaration: *)
    scopeofDecl (d:D) : option ScopeId :=
      (fix f ss :=
         match ss with
         | s::ss' =>
           match ddataofScope s with
           | Some mp =>
             match get Ddec mp d with
             | Some _ => Some s
             | _ => f ss'
             end
           | _ => f ss'
           end
         | [] => None
         end) (keys g) ;

(** [slookup g s p s' d] means that in graph [g], path [p] leads from
    scope [s] to scope [s'] and declaration [d]. (This corresponds to the
    definition of consistent path in Fig. 6 of the paper.) *)
    slookup : ScopeId -> path -> ScopeId -> D -> Prop :=
      fix f (s: ScopeId) (p: path) (s': ScopeId) (d: D) :=
        match p with
        | Dp d' => exists dd, ddataofScope s = Some dd /\ In d' (keys dd) /\  s = s' /\ d = d'
        | Ep l s'' p' =>
          exists ks ss, linksofScope s = Some ks /\
                        get ELdec ks l = Some ss /\
                        In s'' ss /\
                        f s'' p' s' d
        end ;

(** All paths recorded in a scope graph correspond to actual,
    well-connected paths. *)
    path_connectivity :
      forall s m, pathsofScope s = Some m -> forall r p, get Rdec m r = Some p -> exists sd d, slookup s p sd d ;
  }.

(** ** Derived Properties *)

(** We prove prove some sanity lemmas establishing how the different
ways of retrieving information from a scope graph are equivalent. *)

Section SanityChecks.

  Context `{Graph}.

  (** For [scopeofRef]: *)

  Lemma scopeofRef_sanity1: forall s m r p,
    pathsofScope s = Some m ->
    get Rdec m r = Some p ->
    scopeofRef r = Some s.
  Proof.
    intros.
    unfold scopeofRef.
    unfold pathsofScope in H0.
    destruct (get ScopeIdDec g s) eqn:?.
    2: inv H0.
    generalize Heqo; intro P0.  apply keys_in in P0.
    remember (keys g) as ks.
    assert (P: forall k, In k ks -> In k (keys g)).
      intros. rewrite Heqks in H2. auto.
    clear Heqks.
    induction ks.
    + inv P0.
    + inv P0.
      - simpl.
        destruct (pathsofScope s) eqn:?.
        destruct (get Rdec m0 r) eqn:?.
        auto.
        unfold pathsofScope in Heqo0.
        rewrite Heqo in Heqo0.
        rewrite Heqo0 in H0.  inv H0.
        rewrite Heqo1 in H1; inv H1.

        unfold pathsofScope in Heqo0.
        rewrite Heqo in Heqo0.
        inv Heqo0.
     - destruct (pathsofScope a) eqn:?.
       destruct (get Rdec m0 r) eqn:?.
       f_equal. eapply uniqueRefs.
        eauto.
        unfold pathsofScope. rewrite Heqo; eauto.  eauto.
        eauto.
       eapply IHks; auto; intros; apply P; right; auto.
       eapply IHks; auto; intros; apply P; right; auto.
  Qed.

  Lemma scopeofRef_sanity2: forall s r,
    scopeofRef r = Some s ->
    exists m p, pathsofScope s = Some m /\ get Rdec m r = Some p.
  Proof.
    intros.
    unfold scopeofRef in H0.
    remember (keys g) as ks.
    assert (P: forall k, In k ks -> In k (keys g)).
      intros. rewrite Heqks in H1. auto.
    clear Heqks.
    induction ks.
    + inv H0.
    + destruct (pathsofScope a) eqn:?.
      destruct (get Rdec m r) eqn:?.
      inv H0.
      eexists; eauto.
      eapply IHks; eauto. intros; eapply P; right; auto.
      eapply IHks; eauto. intros; eapply P; right; auto.
  Qed.

  (** For [scopeofDecl]: *)

  Lemma scopeofDecl_sanity1: forall s m d dd,
     ddataofScope s = Some m ->
     get Ddec m d = Some dd ->
     scopeofDecl d = Some s.
  Proof.
    intros.
    unfold scopeofDecl.
    unfold ddataofScope in H0.
    destruct (get ScopeIdDec g s) eqn:?.
    2: inv H0.
    generalize Heqo; intro P0.  apply keys_in in P0.
    remember (keys g) as ks.
    assert (P: forall k, In k ks -> In k (keys g)).
      intros. rewrite Heqks in H2. auto.
    clear Heqks.
    induction ks.
    + inv P0.
    + inv P0.
      - simpl.
        destruct (ddataofScope s) eqn:?.
        destruct (get Ddec m0 d) eqn:?.
        auto.
        unfold ddataofScope in Heqo0.
        rewrite Heqo in Heqo0.
        rewrite Heqo0 in H0.  inv H0.
        rewrite Heqo1 in H1; inv H1.

        unfold ddataofScope in Heqo0.
        rewrite Heqo in Heqo0.
        inv Heqo0.
     - destruct (ddataofScope a) eqn:?.
       destruct (get Ddec m0 d) eqn:?.
       f_equal. eapply uniqueDecls.
        eauto.
        unfold ddataofScope. rewrite Heqo; eauto.  eauto.
        eauto.
       eapply IHks; auto; intros; apply P; right; auto.
       eapply IHks; auto; intros; apply P; right; auto.
  Qed.

  Lemma scopeofDecl_sanity2: forall s d,
    scopeofDecl d = Some s ->
    exists m dd, ddataofScope s = Some m /\ get Ddec m d = Some dd.
  Proof.
    intros.
    unfold scopeofDecl in H0.
    remember (keys g) as ks.
    assert (P: forall k, In k ks -> In k (keys g)).
      intros. rewrite Heqks in H1. auto.
    clear Heqks.
    induction ks.
    + inv H0.
    + destruct (ddataofScope a) eqn:?.
      destruct (get Ddec m d) eqn:?.
      inv H0.
      eexists; eauto.
      eapply IHks; eauto. intros; eapply P; right; auto.
      eapply IHks; eauto. intros; eapply P; right; auto.
  Qed.

  (** Straightforward corollary for use in proofs: *)

  Corollary ddataofScope_scopeofDecl :
    forall dd s,
      ddataofScope s = Some dd ->
      forall d,
        In d (keys dd) ->
        scopeofDecl d = Some s.
  Proof.
    intros. eapply in_keys in H1. destruct H1. eapply scopeofDecl_sanity1; eauto.
  Qed.


End SanityChecks.


(** ** Predicate forms. *)

(** We provide predicates for reasoning about scope graphs. Most are
wrappers for the functions in [Graph]. We prove determinism for each
predicate.

The reason for using these predicate forms, instead of their
functional counterparts defined in [Graph], is mainly historical. We
expect to deprecate many of these in future work, and use the
functions in [Graph] instead. *)

Section PredicateForms.

  Context `{Graph}.

  Definition ddataofScopeP (s: ScopeId) (ds: map D DData) : Prop :=
    ddataofScope s = Some ds.
  Lemma ddataofScopeDet :
    forall s ds1 ds2,
      ddataofScopeP s ds1 ->
      ddataofScopeP s ds2 ->
      ds1 = ds2.
  Proof.
    intros. inv H0. inv H1. rewrite H3 in H2. inv H2; auto.
  Qed.

  (** Gets the declarations of a scope (D(s) in Fig. 5 in the
  paper). *)
  Definition declsofScopeP (s: ScopeId) (ds: list D) : Prop :=
    exists dd, ddataofScope s = Some dd /\ ds = keys dd.
  Lemma declsofScopeDet :
    forall s ds1 ds2,
      declsofScopeP s ds1 ->
      declsofScopeP s ds2 ->
      ds1 = ds2.
  Proof.
    intros. destruct H0 as [? [DD DS]]. destruct H1 as [? [DD' DS']].
    rewrite DD' in DD; inv DD; auto.
  Qed.

  Lemma declsofScope_scopeofDecl :
    forall s ds,
      declsofScopeP s ds ->
      forall d,
        In d ds ->
        scopeofDecl d = Some s.
  Proof.
    intros. destruct H0 as [? [? ?]]. subst.
    eapply ddataofScope_scopeofDecl; eauto.
  Qed.

  (** Gets the declarations of a scope (R(s) in Fig. 5 in the
  paper). *)
  Definition refsofScopeP (s: ScopeId) (rs: list R) : Prop :=
    exists m, pathsofScope s = Some m /\ rs = keys m.
  Lemma refsofScopeDet :
    forall s rs1 rs2,
      refsofScopeP s rs1 ->
      refsofScopeP s rs2 ->
      rs1 = rs2.
  Proof.
    intros. destruct H0 as [? [? ?]]. destruct H1 as [? [? ?]]. subst.
    rewrite H0 in H1; inv H1; auto.
  Qed.

  Definition linksofScopeP (s: ScopeId) (ks: map EdgeLabel (list ScopeId)) :=
    linksofScope s = Some ks.
  Lemma linksofScopeDet : forall s ims ims',
      linksofScopeP s ims ->
      linksofScopeP s ims' ->
      ims = ims'.
  Proof.
    intros. inv H0. inv H1. rewrite H3 in H2; inv H2; auto.
  Qed.

  Definition scopeofDeclP (d: D) (s: ScopeId) : Prop :=
    scopeofDecl d = Some s.
  Lemma scopeofDeclDet :
    forall d s s',
      scopeofDeclP d s ->
      scopeofDeclP d s' ->
      s = s'.
  Proof.
    intros. inv H0. inv H1. rewrite H3 in H2; inv H2; auto.
  Qed.

  Definition scopeofRefP (r: R) (s: ScopeId) : Prop :=
    scopeofRef r = Some s.
  Lemma scopeofRefDet :
    forall d s s',
      scopeofRefP d s ->
      scopeofRefP d s' ->
      s = s'.
  Proof.
    intros. inv H0. inv H1.
    destruct (ScopeIdDec s s'); auto. rewrite H3 in H2; inv H2; auto.
  Qed.

  Definition pathofRefP (r: R) (p: path) : Prop :=
    pathofRef r = Some p.
  Lemma pathofRefDet :
    forall r p1,
      pathofRefP r p1 ->
      forall p2,
        pathofRefP r p2 ->
        p1 = p2.
  Proof.
    intros. unfold pathofRefP in H0, H1. rewrite H0 in H1; inv H1; auto.
  Qed.

  (** For retrieving data associated with declarations (such as
  associated scopes and types). *)
  Inductive assocData (d: D) : DData -> Prop :=
  | assocData_ :
      forall s ds p,
        scopeofDecl d = Some s ->
        ddataofScope s = Some ds ->
        get Ddec ds d = Some p ->
        assocData d p.
  Lemma assocDataDet :
    forall d dd,
      assocData d dd ->
      forall dd',
        assocData d dd' ->
        dd = dd'.
  Proof.
    intros. inv H0. inv H1.
    eapply scopeofDeclDet in H2; eauto; subst.
    eapply ddataofScopeDet in H3; eauto; subst.
    rewrite H6 in H4. inv H4; auto.
  Qed.

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
    intros. inv H0. inv H1. rewrite (pathofRefDet _ _ PR _ PR0). reflexivity.
  Qed.

  Definition declsofRefs (rs: list R) (ds: list D) : Prop :=
    Forall2 declofRef rs ds.

  Definition assocDataofRef r s :=
    exists d, declofRef r d /\ assocData d s.
  Lemma assocDataofRefDet :
    forall r dd dd',
      assocDataofRef r dd ->
      assocDataofRef r dd' ->
      dd = dd'.
  Proof.
    intros.
    destruct H0 as [? [DR1 ASC1]]. destruct H1 as [? [DR2 ASC2]].
    eapply declofRefDet in DR1; eauto; subst.
    eapply assocDataDet in ASC1; eauto.
  Qed.


  Definition llinksofScopeP (s: ScopeId) (l: EdgeLabel) (ss: list ScopeId) : Prop :=
    exists ks, linksofScopeP s ks /\ get ELdec ks l = Some ss.
  Lemma llinksofScopeDet : forall s l ims ims',
      llinksofScopeP s l ims ->
      llinksofScopeP s l ims' ->
      ims = ims'.
  Proof.
    intros. inv H0. destruct H2. inv H1.  destruct H3.
    eapply linksofScopeDet in H0; eauto; subst.
    rewrite H3 in H2; inv H2; auto.
  Qed.

End PredicateForms.

Hint Unfold DomEq : sgraph.
Hint Unfold declsofScopeP : sgraph.
Hint Unfold pathofRefP : sgraph.

(** ** Lookup Predicate Properties *)

Section LookupPredicates.

  Context `{Graph}.

  Lemma slookupDet :
    forall p s s' d' s'' d'',
      slookup s p s' d' ->
      slookup s p s'' d'' ->
      s' = s'' /\ d' = d''.
  Proof.
    induction p; intros.
    - destruct H0 as [? [? [? [? ?]]]].
      destruct H1 as [? [? [? [? ?]]]]. subst. auto.
    - destruct H0 as [? [? [? [? [? ?]]]]].
      destruct H1 as [? [? [? [? [? ?]]]]].
      eauto.
  Qed.

  Lemma slookup_declofPath :
    forall p s d sd,
      slookup s p sd d ->
      d = declofPath p.
  Proof.
    induction p; intros.
       destruct H0 as [? [? [? [? ?]]]]; subst; auto.
       destruct H0 as [? [? [? [? [? ?]]]]]; eauto.
  Qed.


  Lemma path_connectivity' :
    forall r p s,
      pathofRef r = Some p ->
      scopeofRef r = Some s ->
      exists sd d, slookup s p sd d .
  Proof.
   intros. unfold pathofRef in H0.  rewrite H1 in H0.
   destruct (pathsofScope s) eqn:?. 2:inv H0.
   eapply path_connectivity; eauto.
  Qed.


  Lemma slookup_ddata :
    forall p s sd d,
      slookup s p sd d ->
      exists dd, ddataofScope sd = Some dd /\ In d (keys dd).
  Proof.
    induction p; intros.
       destruct H0 as [? [? [? [? ?]]]]; subst. exists x; auto.
       destruct H0 as [? [? [? [? [? ?]]]]]; eauto.
  Qed.

  (** [rlookup r p s' d] means that reference [r] via path [p] leads
     to scope [s'] and declaration [d]. *)
  Definition rlookup (r: R) (p: path) (s': ScopeId) (d': D) : Prop :=
    exists s, scopeofRefP r s /\ pathofRefP r p /\ slookup s p s' d'.

  Lemma rlookupDet :
    forall r p s' d' p' s'' d'',
      rlookup r p s' d' ->
      rlookup r p' s'' d'' ->
      p = p' /\ s' = s'' /\ d' = d''.
  Proof.
    do 2 destruct 1 as [? [? [? ?]]].
    eapply scopeofRefDet in H0; eauto; subst.
    eapply pathofRefDet in H1; eauto; subst.
    eapply slookupDet in H2; eauto; subst.
    destruct H2 as [? ?]; subst; auto.
  Qed.

End LookupPredicates.

(** * Scope Graphs with Associated scopes and Types. *)

(** Here we specialize declaration data to be optional associated
scope and type. *)

Section RGATProperties.

  Context {T: Type}.
  Definition AT := ((option ScopeId) * T)%type.
  Context `{G : Graph AT}.

  (** ** Types *)

  Inductive typofDecl (d: D) (t: T) : Prop :=
  | typofDecl_ :
      forall (dd : ((option ScopeId) * T)),
        assocData d dd ->
        t = snd dd ->
        typofDecl d t.

  Lemma typofDeclDet :
    forall d t1 t2,
      typofDecl d t1 ->
      typofDecl d t2 ->
      t1 = t2.
  Proof.
    intros. inv H. inv H0. eapply assocDataDet in H1; eauto; subst. reflexivity.
  Qed.

  Definition typofDecls (ds: list D) (ts: list T) : Prop :=
    Forall2 typofDecl ds ts.

  Lemma typofDeclsDet :
    forall ds t1s t2s,
      typofDecls ds t1s -> typofDecls ds t2s -> t1s = t2s.
  Proof.
    induction ds; intros.
    inversion H0; subst; inversion H; eauto.
    inversion H0; subst; inversion H; subst.
    f_equal; eauto using typofDeclDet, IHds.
  Qed.

  (** ** Associated scopes *)

  Inductive assocScope (d: D) (s': ScopeId) : Prop :=
  | assocScope_ :
      forall dd,
        assocData d dd ->
        Some s' = fst dd ->
        assocScope d s'.

  Lemma assocScopeDet :
    forall d s1 s2,
      assocScope d s1 ->
      assocScope d s2 ->
      s1 = s2.
  Proof.
    intros. inv H. inv H0. eapply assocDataDet in H1; eauto; subst.
    rewrite <- H3 in H2; inv H2. reflexivity.
  Qed.

  Definition assocScopeofRef r s'' : Prop :=
    exists p' s' d, rlookup r p' s' d /\ assocScope d s''.

  Lemma assocScopeofRefDet :
    forall r s' s'',
      assocScopeofRef r s' ->
      assocScopeofRef r s'' ->
      s' = s''.
  Proof.
    intros.
    destruct H as [? [? [? [DR1 ASC1]]]].
    destruct H0 as [? [? [? [DR2 ASC2]]]].
    eapply rlookupDet in DR1; eauto. destruct DR1 as [? [? ?]]; subst.
    eapply assocScopeDet in ASC1; eauto.
  Qed.

End RGATProperties.
