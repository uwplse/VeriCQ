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

Module ConjuctiveQueryData (T : Types) (S : Schemas T) (R : Relations T S).
  Import T S R.
  Module SQL_TSR := SQL T S R.
  Import SQL_TSR.

  Arguments namedProduct {_ _ _} _.

  Section ConjunctiveQuery.
    Variable SQLType : Type.
    Variable TableName : Type.
    Variable columnName : SQLType -> TableName -> Type.
    Variable ProjName : Type.
    Variable projType : ProjName -> SQLType.

    Record ConjunctiveQuery := {
      (* NOTE we originally had:
      `TableAlias : Type` and `from : TableAlias -> TableName`
      instead of 
      `TableAlias : TableName -> Type`
      this was less convenient to work with, 
      because enumerating all Aliases to the same table was harder.

      we originally had a list of projection types, but then
      the projection had to depend on the types in that list,
      which was hard to induct over. The named approach is much easier now.
      *)
      TableAlias : TableName -> Type;
      Access (st:SQLType) := {tn : TableName & (TableAlias tn * columnName st tn)};
      selections : list {st:SQLType & (Access st * Access st)};
      projection (pn:ProjName) : Access (projType pn)
    }.

    Variable Γ:Schema.
    Variable s:TableName -> Schema.
    Variable t:SQLType -> type.
    Variable c:forall (st:SQLType) (tn:TableName) (cn:columnName st tn), Column (t st) (s tn).
    Variable q:forall (tn:TableName), SQL Γ (s tn).
    Variable cq:ConjunctiveQuery.

    Definition projSchema : Schema := 
      namedNode ProjName (fun pn => leaf (t (projType pn))).

    Definition fromSchema := namedNode TableName (fun tn => namedNode (TableAlias cq tn) (const (s tn))).

    Definition access {st} (a : Access cq st) : Column (t st) (Γ ++ fromSchema).
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

    Definition denoteProjection : Proj (Γ ++ fromSchema) projSchema :=
       named (fun pn => access (projection cq pn)).

    Definition denoteConjunctiveQuery : SQL Γ projSchema :=
      SELECT1 denoteProjection 
      FROM1 denoteFrom 
      WHERE denoteSelection.
  End ConjunctiveQuery.
 
  Record ConjunctiveQueryRewrite := conjunctiveQueryRewrite {
    SQLType : Type;
    TableName : Type;
    columnName : SQLType -> TableName -> Type;
    ProjName : Type;
    projType : ProjName -> SQLType;
    query0 : ConjunctiveQuery SQLType TableName columnName ProjName projType; 
    query1 : ConjunctiveQuery SQLType TableName columnName ProjName projType
  }.

  Definition denoteConjunctiveQueryRewriteContainment (r:ConjunctiveQueryRewrite) : Type.
    refine (forall (Γ:Schema), _).
    refine (forall (s:TableName r -> Schema), _).
    refine (forall (T:SQLType r -> type), _).
    refine (forall (c:forall (st:SQLType r) (tn:TableName r) (cn:columnName r st tn), Column (T st) (s tn)), _).
    refine (forall (q:(forall (tn:TableName r), SQL Γ (s tn))), _).
    refine (forall (g:Tuple Γ) (t:Tuple (projSchema _ _ (projType r) T)), (⟦ Γ ⊢ _ : _ ⟧ g t : Prop) -> ⟦ Γ ⊢ _ : _ ⟧ g t : Prop).
    - refine (denoteConjunctiveQuery _ _ _ _ _ Γ s T c q (query0 r)).
    - refine (denoteConjunctiveQuery _ _ _ _ _ Γ s T c q (query1 r)).
  Defined. 

  Definition denoteConjunctiveQueryRewriteEquivalence (r:ConjunctiveQueryRewrite) : Type.
    refine (forall (Γ:Schema), _).
    refine (forall (s:TableName r -> Schema), _).
    refine (forall (T:SQLType r -> type), _).
    refine (forall (c:forall (st:SQLType r) (tn:TableName r) (cn:columnName r st tn), Column (T st) (s tn)), _).
    refine (forall (q:(forall (tn:TableName r), SQL Γ (s tn))), _).
    refine (⟦ Γ ⊢ _ : _ ⟧ = ⟦ Γ ⊢ _ : _ ⟧).
    - refine (denoteConjunctiveQuery _ _ _ _ _ Γ s T c q (query0 r)).
    - refine (denoteConjunctiveQuery _ _ _ _ _ Γ s T c q (query1 r)).
  Defined. 

  Module SelfJoin.
    Inductive tables := R.
    Inductive columns := a.
    Inductive projs := w.
    Inductive aliases0 := x | y.
    Inductive aliases1 := z.
    Inductive types := string.

    Definition selfJoin : ConjunctiveQueryRewrite.
      refine {|
        TableName := tables;
        columnName t tn := columns;
        ProjName := projs;
        projType pn := string;
        query0 := {| TableAlias tn := aliases0; 
                     projection pn := (R;(x,a));
                     selections := [(string; ((R;(x,a)), (R;(y,a))))]
                  |};
        query1 := {| TableAlias tn := aliases1; 
                     projection pn := (R;(z,a));
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
    Inductive projs := w.
    Inductive aliases := x.
    Variable string : type.

    Definition transitiveJoin : ConjunctiveQueryRewrite.
      refine {|
        TableName := tables;
        columnName t tn := columns;
        ProjName := projs;
        projType pn := string;
        query0 := {| TableAlias tn := aliases; 
                     projection pn := (R;(x,a));
                     selections := [(string; ((R;(x,a)), (R;(x,b))));
                                    (string; ((R;(x,b)), (R;(x,c))))]
                  |};
        query1 := {| TableAlias tn := aliases; 
                     projection pn := (R;(x,a));
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

  Arguments full [_] _ [_].

  Arguments TableAlias {_ _ _ _ _} _ _.
  Arguments selections {_ _ _ _ _} _.
  Arguments projection {_ _ _ _ _} _ _.
  Arguments Access {_ _ _ _ _} _ _.

  Require Import EqDec.

  (* `query0 r <= query1 r`
      every tuple of `query0 r` is contained in `query1 r` *)
  Section Correctness.
    Variable SQLType : Type.
    Variable TableName : Type.
    Variable columnName : SQLType -> TableName -> Type.
    Variable ProjName : Type.
    Variable projType : ProjName -> SQLType.
    Variable query0 : ConjunctiveQuery SQLType TableName columnName ProjName projType.
    Variable query1 : ConjunctiveQuery SQLType TableName columnName ProjName projType.
    Definition r := conjunctiveQueryRewrite SQLType TableName columnName ProjName projType query0 query1.
  
    Require Import Native.
 
    Context {BA:Basic}.
    Context {SE:@Search BA}.

    Instance fullForall {A B} `{@Full listSpace A}
                              `{forall a:A, @Full BA (B a)} : 
                               Full (forall a : A, B a).
    Admitted.

    Context `{@Full listSpace TableName}.
    Context `{forall st tn, @Full BA (columnName st tn)}.
    Context `{@Full listSpace ProjName}.
    Context `{forall tn, @Full BA (TableAlias query0 tn)}.
    Context `{forall tn, @Full listSpace (TableAlias query1 tn)}.

    Context `{eqDec TableName}.
    Context `{eqDec ProjName}.
    Context `{forall st tn, eqDec (columnName st tn)}.
    Context `{forall tn, eqDec (TableAlias query0 tn)}.
    Context `{forall tn, eqDec (TableAlias query1 tn)}.

    Definition Assignment := (forall tn:TableName, TableAlias query1 tn -> TableAlias query0 tn).
   
    Instance fullAssignment : @Full BA Assignment.
      unfold Assignment. 
      refine (_).
    Defined.

    Definition AccessQ0 := Access query0.
    Definition AccessQ1 := Access query1.

    Instance eqDecAccessQ1 st : eqDec (AccessQ1 st).
      unfold Access.
      refine (_).
    Defined.

(* potential related work
http://webdam.inria.fr/Alice/pdfs/Chapter-4.pdf (recommended by Shumo)
http://www.sciencedirect.com/science/article/pii/S0022000000917136

*)

    Require Import Bool.

    Coercion sumBoolToBool {P Q} (pq:{P} + {Q}) : bool :=
      if pq then Datatypes.true else Datatypes.false.

    Definition assignmentAccess {st} (a:Assignment) (ac:AccessQ1 st) : AccessQ0 st.
        unfold AccessQ0, AccessQ1, Access in *.
        refine (let tn := ac.1 in _).
        refine (let ta := fst ac.2 in _).
        refine (let cn := snd ac.2 in _).
        refine (tn; (a tn ta, cn)).
    Defined.

    Definition containment : Result Assignment.
      refine (search _).
      refine (all (fun a : Assignment => _)).
      unfold Assignment in a.
      refine (if (_:bool) then single a else empty).
      refine (_ && _).
      - (* check selection variables are equal *)
        refine (forallb _  (selections query1)).
        intros ac.
        refine (assignmentAccess a (fst ac.2) =? 
                assignmentAccess a (snd ac.2)).
      - (* check projection variables are equal *)
        refine (forallb _  (full ProjName)).
        intros pn.
        refine (assignmentAccess a (projection query1 pn) =? 
                projection query0 pn).
    Defined.
    
    Require Import JamesTactics.
    Require Import CpdtTactics.
    Require EnsemblesEx.

    Definition containment' : option {a |
        (forall ac : {st : SQLType & (AccessQ1 st * AccessQ1 st)}, 
          List.In ac (selections query1) -> 
            assignmentAccess a (fst ac.2) = assignmentAccess a (snd ac.2))
        /\
        (forall (pn:ProjName), 
            assignmentAccess a (projection query1 pn) = projection query0 pn)
      }.
      destruct containment as [a|] eqn:h; [|exact None].
      refine (Some (exist _ a _)).
      unfold containment in *.
      apply searchSolution in h.
      rewrite denoteAllOk in h.
      destruct h as [a' h].
      break_match; revgoals. {
        specialize (@denoteEmptyOk BA Assignment); intros h'.
        unfold Ensemble in h'.
        rewrite h' in h; clear h'.
        destruct h.
      }
      specialize (@denoteSingleOk BA Assignment); intros h'.
      unfold Ensemble in h'.
      rewrite h' in h; clear h'.
      destruct h; rename a' into a.
      rename Heqb into h.
      rewrite andb_true_iff in h.
      constructor.
      - destruct h as [h _].
        rewrite forallb_forall in h.
        intros ac inSel.
        specialize (h ac inSel).
        unfold sumBoolToBool in h.
        break_match; intuition.
      - destruct h as [_ h].
        rewrite forallb_forall in h.
        intros pn.
        specialize (@denoteFullOk listSpace ProjName _); intros inFull.
        cbn in inFull.
        apply equal_f with (x:=pn) in inFull.
        rewrite fullIsTrue in inFull.
        specialize (h pn).
        rewrite inFull in h.
        unfold sumBoolToBool in h.
        break_match; intuition.
    Defined.

    Definition soundContainment : option (denoteConjunctiveQueryRewriteContainment r).
      destruct containment' as [[a [h h']]|]; [|exact None].
      refine (Some _).
      unfold denoteConjunctiveQueryRewriteContainment.
      simpl.
      intros Γ s T c q g t [t0 [[select from] project]].
      refine (ex_intro _ (fun tn ta => t0 tn (a tn ta)) _).
      constructor; [constructor|].
      - (* selection variables are correct *)
        clear h'.
        unfold denoteSelection.
        induction (selections query1) as [|sel sels rec].
        + simpl.
          trivial.
        + simpl.
          constructor.
          * clear rec.
            destruct sel as [st [[tn [ta cn]] [tn' [ta' cn']]]].
            simpl.
            simpl in h.
            match goal with
            | h:forall _, ?a = _ \/ _ -> _ |- _ => specialize (h a (or_introl eq_refl))
            end.
            unfold assignmentAccess in h.
            simpl in h.
            crush.
          * apply rec.
            intuition.
      - (* from clause is correct *)
        intros tn ta.
        apply from.
      - (* projection variables are correct *)
        rewrite <- project; clear select project.
        extensionality pn.
        specialize (h' pn).
        unfold assignmentAccess in h'.
        rewrite <- h'.
        simpl.
        reflexivity.
    Qed.
  End Correctness.
End ConjuctiveQueryData.
