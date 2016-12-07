Require Import Denotation.
Require Import SQLSemantics.
Require Import List.
Import ListNotations.
Require Import Program.
Require Import FunctionalExtensionality.
Require Import ClassicalFacts.
Axiom prop_ext : prop_extensionality.
Require Import Basic.
Require Import Full.
Require Import Precise.

Open Scope type.

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Inductive index {A} : list A -> Type :=
| found a l : index (a::l)
| next  a l : index l -> index (a::l).

Fixpoint lookup {A} {l:list A} (i:index l) :=
  match i with
  | found a _ => a
  | next _ _ i' => lookup i'
  end.

Arguments found [_ _ _].
Arguments next [_ _ _] _.

Module ConjuctiveQueryData (T : Types) (S : Schemas T) (R : Relations T S).
  Import T S R.
  Module SQL_TSR := SQL T S R.
  Import SQL_TSR.

  Arguments namedProduct {_ _ _} _.

  Section ConjunctiveQuery.
    Variable SQLType : Type.
    Variable TableName : Type.
    Variable columnName : SQLType -> TableName -> Type.
    Variable projectionTypes : list SQLType.

    Definition Access (TableAlias : TableName -> Type) (t:SQLType) := {tn : TableName & (TableAlias tn * columnName t tn)}.

    Record ConjunctiveQuery := {
      (* NOTE we originally had:
      `TableAlias : Type` and `from : TableAlias -> TableName`
      instead of 
      `TableAlias : TableName -> Type`
      this was less convenient to work with, 
      because enumerating all Aliases to the same table was harder.
      *)
      TableAlias : TableName -> Type;
      selections :  list {t:SQLType & (Access TableAlias t * Access TableAlias t)};
      projection (i:index projectionTypes) : Access TableAlias (lookup i)
    }.

    Variable Γ:Schema.
    Variable s:TableName -> Schema.
    Variable t:SQLType -> type.
    Variable c:forall (st:SQLType) (tn:TableName) (cn:columnName st tn), Column (t st) (s tn).
    Variable q:forall (tn:TableName), SQL Γ (s tn).
    Variable cq:ConjunctiveQuery.

    Definition projSchema : Schema.
      refine ((fix rec (sts:list _) := _) projectionTypes).
      refine (match sts with
      | [] => SQLSemantics.empty
      | st::sts => node (leaf (t st)) (rec sts)
      end).
    Defined. 

    Definition fromSchema := namedNode TableName (fun tn => namedNode (TableAlias cq tn) (const (s tn))).

    Definition access {st} (a : Access (TableAlias cq) st) : Column (t st) (Γ ++ fromSchema).
      unfold Access in a.
      refine (right ⋅ _).
      refine (name (a.1) ⋅ _).
      refine (name (fst a.2) ⋅ _).
      refine (c _ _ (snd a.2)).
    Defined.
 
    Definition denoteFrom : SQL Γ fromSchema.
      refine (namedProduct (fun tn : TableName => _)).
      refine (namedProduct (fun _ : TableAlias cq tn => _)).
      refine (q tn).
    Defined.

    Definition denoteSelection : Pred (Γ ++ fromSchema).
      refine ((fix rec (sels:list _) := _) (selections cq)).
      refine (match sels with
      | [] => TRUE
      | sel::sels => _ AND rec sels
      end).
      refine (equal (variable _) (variable _)).
      - exact (access (fst sel.2)).
      - exact (access (snd sel.2)).
    Defined.

    Definition denoteProjection : Proj (Γ ++ fromSchema) projSchema.
      specialize (projection cq); intros proj.
      unfold projSchema.
      induction (projectionTypes) as [|st sts rec].
      - exact erase.
      - refine (combine _ _).
        + exact (access (proj found)).
        + exact (rec (fun i => proj (next i))).
    Defined.          

    Definition denoteConjunctiveQuery : SQL Γ projSchema :=
      SELECT1 denoteProjection 
      FROM1 denoteFrom 
      WHERE denoteSelection.
  End ConjunctiveQuery.
 
  Record ConjunctiveQueryRewrite := {
    SQLType : Type;
    TableName : Type;
    columnName : SQLType -> TableName -> Type;
    projectionTypes : list SQLType;
    query0 : ConjunctiveQuery SQLType TableName columnName projectionTypes; 
    query1 : ConjunctiveQuery SQLType TableName columnName projectionTypes
  }.

  Definition denoteConjunctiveQueryRewriteContainment (r:ConjunctiveQueryRewrite) : Type.
    refine (forall (Γ:Schema), _).
    refine (forall (s:TableName r -> Schema), _).
    refine (forall (T:SQLType r -> type), _).
    refine (forall (c:forall (st:SQLType r) (tn:TableName r) (cn:columnName r st tn), Column (T st) (s tn)), _).
    refine (forall (q:(forall (tn:TableName r), SQL Γ (s tn))), _).
    refine (forall (g:Tuple Γ) (t:Tuple (projSchema (SQLType r) (projectionTypes r) T)), (⟦ Γ ⊢ _ : _ ⟧ g t : Prop) -> ⟦ Γ ⊢ _ : _ ⟧ g t : Prop).
    - refine (denoteConjunctiveQuery _ _ _ _ Γ s T c q (query0 r)).
    - refine (denoteConjunctiveQuery _ _ _ _ Γ s T c q (query1 r)).
  Defined. 

  Definition denoteConjunctiveQueryRewriteEquivalence (r:ConjunctiveQueryRewrite) : Type.
    refine (forall (Γ:Schema), _).
    refine (forall (s:TableName r -> Schema), _).
    refine (forall (T:SQLType r -> type), _).
    refine (forall (c:forall (st:SQLType r) (tn:TableName r) (cn:columnName r st tn), Column (T st) (s tn)), _).
    refine (forall (q:(forall (tn:TableName r), SQL Γ (s tn))), _).
    refine (⟦ Γ ⊢ _ : _ ⟧ = ⟦ Γ ⊢ _ : _ ⟧).
    - refine (denoteConjunctiveQuery _ _ _ _ Γ s T c q (query0 r)).
    - refine (denoteConjunctiveQuery _ _ _ _ Γ s T c q (query1 r)).
  Defined. 

  Module SelfJoin.
    Inductive tables := R.
    Inductive columns := a.
    Inductive aliases0 := x | y.
    Inductive aliases1 := z.
    Inductive types := string.

    Definition selfJoin : ConjunctiveQueryRewrite.
      refine {|
        TableName := tables;
        columnName t tn := columns;
        projectionTypes := [string];
        query0 := {| TableAlias tn := aliases0; 
                     projection i := (R;(x,a));
                     selections := [(string; ((R;(x,a)), (R;(y,a))))]
                  |};
        query1 := {| TableAlias tn := aliases1; 
                     projection i := (R;(z,a));
                     selections := []
                  |}
      |}.
    Defined.

    Goal denoteConjunctiveQueryRewriteEquivalence selfJoin.
      unfold selfJoin.
      unfold denoteConjunctiveQueryRewriteEquivalence.
      simpl.
      intros.
      extensionality g.
      extensionality t.
      apply prop_ext.
      constructor;
      intros [t0 h];
      repeat match goal with
             | h:?A /\ ?B |- _ => destruct h
             end.
      - simple refine (ex_intro _ _ _). {
          unfold const.
          intros [] []; apply t0.
          + exact y.
        }
        simpl.
        repeat match goal with
        | h:denoteProj _ _ = denoteProj _ _ |- _ => rewrite h in *; clear h
        | h:_ = t |- _ => rewrite <- h; clear h
        end.
        match goal with
        | h:forall _ _, denoteSQL _ _ _ |- _ => rename h into from
        end.
        repeat match goal with
        | |- _ /\ _ => constructor
        end.
        + reflexivity.
        + intros [] [];
          match goal with
          | h:forall _ _, denoteSQL _ _ _ |- _ => apply h
          end.
        + reflexivity.
      - simple refine (ex_intro _ _ _). {
          unfold const.
          intros [] []; apply t0.
          + exact z.
          + exact z.
        }
        simpl.
        repeat match goal with
        | h:denoteProj _ _ = denoteProj _ _ |- _ => rewrite h in *; clear h
        | h:_ = t |- _ => rewrite <- h; clear h
        end.
        match goal with
        | h:forall _ _, denoteSQL _ _ _ |- _ => rename h into from
        end.
        repeat match goal with
        | |- _ /\ _ => constructor
        end.
        + reflexivity.
        + trivial.
        + intros [] [];
          match goal with
          | h:forall _ _, denoteSQL _ _ _ |- _ => apply h
          end.
        + reflexivity.
    Qed.
  End SelfJoin.

  Module TransitiveJoin.
    Inductive tables := R.
    Inductive columns := a | b | c.
    Inductive aliases := x.
    Variable string : type.

    Definition transitiveJoin : ConjunctiveQueryRewrite.
      refine {|
        TableName := tables;
        columnName t tn := columns;
        projectionTypes := [string];
        query0 := {| TableAlias tn := aliases; 
                     projection i := (R;(x,a));
                     selections := [(string; ((R;(x,a)), (R;(x,b))));
                                    (string; ((R;(x,b)), (R;(x,c))))]
                  |};
        query1 := {| TableAlias tn := aliases; 
                     projection i := (R;(x,a));
                     selections := [(string; ((R;(x,a)), (R;(x,b))));
                                    (string; ((R;(x,a)), (R;(x,c))))]
                  |}
      |}.
    Defined.

    Goal denoteConjunctiveQueryRewriteEquivalence transitiveJoin.
      unfold transitiveJoin.
      unfold denoteConjunctiveQueryRewriteEquivalence.
      simpl.
      intros.
      extensionality g.
      extensionality t.
      apply prop_ext.
      constructor;
      intros [t0 h];
      repeat match goal with
             | h:?A /\ ?B |- _ => destruct h
             end.
      - simple refine (ex_intro _ _ _). {
          unfold const.
          intros [] []; apply t0.
          + exact x.
        }
        simpl.
        repeat match goal with
        | h:denoteProj _ _ = denoteProj _ _ |- _ => rewrite h in *; clear h
        | h:_ = t |- _ => rewrite <- h; clear h
        end.
        repeat match goal with
        | |- _ /\ _ => constructor
        end.
        + reflexivity.
        + reflexivity.
        + trivial.
        + intros [] [];
          match goal with
          | h:forall _ _, denoteSQL _ _ _ |- _ => apply h
          end.
        + reflexivity.
      - simple refine (ex_intro _ _ _). {
          unfold const.
          intros [] []; apply t0.
          + exact x.
        }
        simpl.
        repeat match goal with
        | h:denoteProj _ _ = denoteProj _ _ |- _ => rewrite h in *; clear h
        | h:_ = t |- _ => rewrite <- h; clear h
        end.
        repeat match goal with
        | |- _ /\ _ => constructor
        end.
        + reflexivity.
        + reflexivity.
        + trivial.
        + intros [] [];
          match goal with
          | h:forall _ _, denoteSQL _ _ _ |- _ => apply h
          end.
        + reflexivity.
    Qed.
  End TransitiveJoin.

  Instance fullArrow {A B} `{Full A} `{Full B} : Full (A -> B).
  Admitted.

  Instance fullForall {A B} `{Full A}
                            `{forall a:A, Full (B a)} : 
                             Full (forall a : A, B a).
  Admitted.

  Arguments full [_] _ [_].

  Arguments TableAlias {_ _ _ _} _ _.
  Arguments selections {_ _ _ _} _.
  Arguments projection {_ _ _ _} _ _.

  (* `query0 r <= query1 r`
      every tuple of `query0 r` is contained in `query1 r` *)
  Section Correctness.
    Variable r:ConjunctiveQueryRewrite.
    
    Context `{Basic}.
    Context `{Full (TableName r)}.
    Context `{forall tn, Full (TableAlias (query0 r) tn)}.
    Context `{forall tn, Full (TableAlias (query1 r) tn)}.

    Definition Assignment := (forall tn:TableName r, TableAlias (query1 r) tn -> TableAlias (query0 r) tn).
    
    Instance freeAssignment : Full Assignment.
      unfold Assignment. 
      eapply fullForall. 
    Defined.


(*
    Variable TableName : Type.
    Variable columnName : type -> TableName -> Type.
    Variable projectionTypes : list type.

    Definition Access (TableAlias : TableName -> Type) (t:type) := {tn : TableName & (TableAlias tn * columnName t tn)}.

*)
(*
    Check (Access (TableName r) (columnName r) (TableAlias (query0 r))). *)
    Print Access.

(* potential related work
http://webdam.inria.fr/Alice/pdfs/Chapter-4.pdf (recommended by Shumo)
http://www.sciencedirect.com/science/article/pii/S0022000000917136

*)

    Context `{Search}.
 
    Definition containment : Result Assignment.
      refine (search _).
      refine (bind (full Assignment) (fun a => _)).

    (*     
        create a variable for every single Access,
        then say that a bunch of them are equal



        refine ()
    *)
    Admitted.

    Definition soundContainment : option (denoteConjunctiveQueryRewriteContainment r).
      refine ((match containment as c return containment = c -> _ with
      | solution a => fun ctEq => Some _
      | uninhabited => fun _ => None
      end) _); [|reflexivity].
      unfold denoteConjunctiveQueryRewriteContainment.
      simpl.
      intros Γ s T c q g t [t0 [[select from] project]].
      unfold Assignment in a.
      refine (ex_intro _ (fun tn ta => t0 tn (a tn ta)) _).
      constructor; [constructor|].
      - unfold denoteSelection.
        induction (selections (query1 r)) as [|sel sels rec].
        + simpl.
          trivial.
        + simpl.
          constructor; [|apply rec].
          clear rec sels.
          destruct sel as [st [[tn [ta cn]] [tn' [ta' cn']]]].
          simpl.
          admit.
      - intros tn ta.
        apply from.
      - rewrite <- project; clear select project.
        unfold fromSchema in *.
        simpl.
        (* induction (projectionTypes r). *)
        idtac.
    Admitted.
  End Correctness.
End ConjuctiveQueryData.
