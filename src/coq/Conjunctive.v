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
Require Import JamesTactics.
Require Import CpdtTactics.
Require EnsemblesEx.
Require Import Bool.
Require Import Native.
Require Import EqDec.
Require Import ProofIrrelevance.
Import EqNotations.

Set Implicit Arguments.
Open Scope type.

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").
  
Inductive Maybe (P : Prop) : Set :=
| unknown : Maybe P
| holds : P -> Maybe P.

Definition getHolds {P p} (m:Maybe P) (h:m = holds p) : P.
  destruct m.
  - discriminate h.
  - apply p.
Defined.
Arguments getHolds {_ _} _ _.

Coercion sumBoolToBool {P Q} (pq:{P} + {Q}) : bool :=
  if pq then Datatypes.true else Datatypes.false.

Arguments full [_] _ [_].

Lemma inFull {A} `{@Full listSpace A} (a:A) : In a (full A).
  simpl.
  specialize (@denoteFullOk listSpace A _).
  rewrite fullIsTrue.
  simpl.
  intros h.
  apply equal_f with (x:=a) in h.
  rewrite h.
  trivial.
Qed.

Section FullForall.
  Context `{S:Basic}.
  Variable A : Type.
  Variable B : A -> Type.
  Context `{eqDec A}.
  Context `{forall a:A, @Full S (B a)}.

  Global Instance fullInForall (l:list A) : @Full S (forall a, In a l -> B a).
    induction l as [|a l rec].
    - simple refine {| full := single _ |}.
      + intros _ [].
      + rewrite denoteSingleOk.
        rewrite fullIsTrue.
        apply Extensionality_Ensembles'.
        intros f.
        rewrite singletonIsEqual.
        intuition.
        simpl.
        extensionality a.
        extensionality h.
        destruct h.
    - simple refine {| full := _ |}.
      + refine (all (fun b:B a => _)).
        refine (all (fun f:(forall a, In a l -> B a) => _)).
        refine (single _).
        intros a' inl.
        simpl in inl.
        refine (match a =? a' with Specif.left e => _ | Specif.right e => _ end).
        * refine (rew e in b).
        * refine (f a' _).
          clear -inl e.
          abstract (destruct inl; congruence).
      + rewrite fullIsTrue.
        apply Extensionality_Ensembles'.
        intros f.
        intuition.
        rewrite denoteAllOk.
        simple refine (ex_intro _ _ _). {
          refine (f a _).
          left.
          reflexivity.
        }
        simpl.
        specialize @denoteAllOk; unfold Ensemble; intro h; rewrite h; clear h.
        simple refine (ex_intro _ _ _). {
          intros a' inl.
          refine (f a' _).
          simpl.
          intuition.
        }
        simpl.
        specialize @denoteSingleOk; unfold Ensemble; intro h; rewrite h; clear h.
        rewrite singletonIsEqual.
        extensionality a'.
        extensionality inl.
        break_match.
        * destruct e.
          simpl.
          f_equal.
          apply proof_irrelevance.
        * f_equal.
          apply proof_irrelevance.
  Defined.

  Context `{@Full listSpace A}.
  Global Instance fullForall : Full (forall a : A, B a).
    specialize (fullInForall (@full listSpace A _)); intros h.
    simple refine {| full := _ |}.
    - refine (all (fun f => single (fun a => _))).
      exact (f a (inFull a)).
    - rewrite fullIsTrue.
      apply Extensionality_Ensembles'.
      intros f.
      intuition.
      rewrite denoteAllOk.
      simple refine (ex_intro _ _ _). {
        intros a _.
        apply f.
      }
      simpl.
      specialize @denoteSingleOk; unfold Ensemble; intro h'; rewrite h'; clear h'.
      constructor.
  Defined.
End FullForall.

(* potential related work
http://webdam.inria.fr/Alice/pdfs/Chapter-4.pdf (recommended by Shumo)
http://www.sciencedirect.com/science/article/pii/S0022000000917136

NOTE, in the definition of ConjunctiveQuery, we originally had:
`TableAlias : Type` and `from : TableAlias -> TableName`
instead of 
`TableAlias : TableName -> Type`
this was less convenient to work with, 
because enumerating all Aliases to the same table was harder.

we originally had a list of projection types, but then
the projection had to depend on the types in that list,
which was hard to induct over. The named approach is much easier now.
*)

Section CQ.
  Variable SQLType : Type.
  Variable TableName : Type.
  Variable columnName : SQLType -> TableName -> Type.
  Variable ProjName : Type.
  Variable projType : ProjName -> SQLType.
  
  Class CQ := {
    TableAlias : TableName -> Type;
    Access (st:SQLType) := {tn : TableName & (TableAlias tn * columnName st tn)};
    selections : list {st:SQLType & (Access st * Access st)};
    projection (pn:ProjName) : Access (projType pn);

    fullTableAlias `{Basic} tn :> Full (TableAlias tn);
    eqDecTableAlias tn :> eqDec (TableAlias tn)
  }.
End CQ.

Class CQRewrite := {
  SQLType : Type;
  TableName : Type;
  columnName : SQLType -> TableName -> Type;
  ProjName : Type;
  projType : ProjName -> SQLType;
  query0 :> CQ columnName projType; 
  query1 :> CQ columnName projType;

  fullTableName `{Basic} :> Full TableName;
  fullProjName `{Basic} :> Full ProjName;
  fullColumnName `{Basic} st tn :> Full (columnName st tn);
  eqDecTableName :> eqDec TableName;
  eqDecProjName :> eqDec ProjName;
  eqDecColumnName st tn :> eqDec (columnName st tn)
}.

Section Checks.
  Context `{S:Search}.

  Section Containment.
    Context `{r:CQRewrite}.
  
    Definition Assignment := (forall tn:TableName, TableAlias (CQ:=query1) tn -> TableAlias (CQ:=query0) tn).
  
    Definition assignmentAccess {st} (a:Assignment) (ac:Access (CQ:=query1) st) : Access (CQ:=query0) st.
      unfold Access in *.
      refine (let tn := ac.1 in _).
      refine (let ta := fst ac.2 in _).
      refine (let cn := snd ac.2 in _).
      refine (tn; (a tn ta, cn)).
    Defined.
  
    Definition containmentCheck : option Assignment.
      refine (match search _ with solution a => Some a | _ => None end).
      refine (all (fun a : Assignment => _)).
      unfold Assignment in a.
      refine (if (_:bool) then single a else empty).
      refine (_ && _).
      - (* check selection variables are equal *)
        refine (forallb _  (selections (CQ:=query1))).
        intros ac.
        refine (assignmentAccess a (fst ac.2) =? 
                assignmentAccess a (snd ac.2)).
      - (* check projection variables are equal *)
        refine (forallb _ (@full listSpace ProjName _)).
        intros pn.
        refine (assignmentAccess a (projection (CQ:=query1) pn) =? 
                projection (CQ:=query0) pn).
    Defined.
  End Containment.

  Section Equivalence.
    Context `{r:CQRewrite}.

    Definition equivalenceCheck :=
      let r' : CQRewrite := {| query0 := query1; query1 := query0 |} in 
      match containmentCheck (r:=r), containmentCheck (r:=r') with
      | Some a, Some a' => Some (a, a')
      | _,_ => None
      end.
  End Equivalence.
End Checks.

(* it's really ugly that I have to use Parameters, but I don't 
   see any other way to universally quantify over modules *)
Parameter type : Type.
Parameter denoteType : type -> Type.

Module T : Types.
  Definition type := type.
  Definition denotationType := {| denote := denoteType |}.
End T.
  
Module TD := SQLDenotation T.
Import TD.
Parameter relation : Schema -> Type.
Parameter denoteRelation : forall s, relation s -> Relation s.

Module R : Relations T.
  Module TD := TD.
  Definition relation := relation.
  Definition denotationRelation s := {| denote := @denoteRelation s |}.
End R.

Module SQL := SQL T R.
Import SQL.
Export SQL.
Import T.
Export T.
Import R.
Export R.

Section DenoteCQ.
  Variable SQLType : Type.
  Variable TableName : Type.
  Variable columnName : SQLType -> TableName -> Type.
  Variable ProjName : Type.
  Variable projType : ProjName -> SQLType.

  Variable Γ:Schema.
  Variable s:TableName -> Schema.
  Variable t:SQLType -> type.
  Variable c:forall (st:SQLType) (tn:TableName) (cn:columnName st tn), Column (t st) (s tn).
  Variable q:forall (tn:TableName), SQL Γ (s tn).
  Variable cq:CQ columnName projType.

  Definition projSchema : Schema := 
    namedNode ProjName (fun pn => leaf (t (projType pn))).

  Definition fromSchema := namedNode TableName (fun tn => namedNode (TableAlias tn) (const (s tn))).

  Definition access {st} (a : Access st) : Column (t st) (Γ ++ fromSchema).
    unfold Access in a.
    refine (right ⋅ _).
    refine (name (a.1) ⋅ _).
    refine (name (fst a.2) ⋅ _).
    refine (c (snd a.2)).
  Defined.

  Definition denoteFrom : SQL Γ fromSchema.
    refine (namedProduct (fun tn : TableName => _)).
    refine (namedProduct (fun _ : TableAlias tn => _)).
    refine (q tn).
  Defined.

  Definition denoteSelection : Pred (Γ ++ fromSchema).
    refine ((fix rec (sels:list _) := _) (selections (CQ:=cq))).
    refine (match sels with
    | [] => TRUE
    | sel::sels => _ AND rec sels
    end).
    refine (equal (variable _) (variable _)).
    - exact (access (fst sel.2)).
    - exact (access (snd sel.2)).
  Defined.

  Definition denoteProjection : Proj (Γ ++ fromSchema) projSchema :=
     named (fun pn => access (projection pn)).

  Definition denoteCQ : SQL Γ projSchema :=
    SELECT1 denoteProjection FROM1 denoteFrom WHERE denoteSelection.
End DenoteCQ.

Section CQRewrite.
  Context `{r:CQRewrite}.
  
  Definition denoteCQRewriteContainment : Prop.
    refine (forall (Γ:Schema), _ : Prop).
    refine (forall (s:TableName -> Schema), _ : Prop).
    refine (forall (T:SQLType -> type), _ : Prop).
    refine (forall (c:forall (st:SQLType) (tn:TableName) (cn:columnName st tn), Column (T st) (s tn)), _ : Prop).
    refine (forall (q:(forall (tn:TableName), SQL Γ (s tn))), _ : Prop).
    refine (forall (g:Tuple Γ) (t:Tuple (projSchema projType T)), (⟦ Γ ⊢ _ : _ ⟧ g t : Prop) -> ⟦ Γ ⊢ _ : _ ⟧ g t : Prop).
    - refine (denoteCQ s T c q query0).
    - refine (denoteCQ s T c q query1).
  Defined. 
  
  Definition denoteCQRewriteEquivalence : Prop.
    refine (forall (Γ:Schema), _ : Prop).
    refine (forall (s:TableName -> Schema), _ : Prop).
    refine (forall (T:SQLType -> type), _ : Prop).
    refine (forall (c:forall (st:SQLType) (tn:TableName) (cn:columnName st tn), Column (T st) (s tn)), _ : Prop).
    refine (forall (q:(forall (tn:TableName), SQL Γ (s tn))), _ : Prop).
    refine (⟦ Γ ⊢ _ : _ ⟧ = ⟦ Γ ⊢ _ : _ ⟧).
    - refine (denoteCQ s T c q query0).
    - refine (denoteCQ s T c q query1).
  Defined. 
End CQRewrite.

Section Soundness.
  Context `{S:Search}.

  Section Containment.
    Context `{r:CQRewrite}.
  
    Lemma containmentSpec {a} (h:containmentCheck = Some a) : 
        (forall ac : {st : SQLType & (Access (CQ:=query1) st * Access (CQ:=query1) st)}, 
          List.In ac (selections (CQ:=query1)) -> 
            assignmentAccess a (fst ac.2) = assignmentAccess a (snd ac.2))
        /\
        (forall (pn:ProjName), 
            assignmentAccess a (projection (CQ:=query1) pn) = projection (CQ:=query0) pn).
      unfold containmentCheck in *.
      break_match; [|congruence]. 
      inversion h; subst; clear h; rename Heqr0 into h.
      apply searchSolution in h.
      rewrite denoteAllOk in h.
      destruct h as [a' h].
      break_match; revgoals. {
        specialize @denoteEmptyOk; unfold Ensemble; intro h'; rewrite h' in h; clear h'.
        destruct h.
      }
      specialize @denoteSingleOk; unfold Ensemble; intro h'; rewrite h' in h; clear h'.
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
        specialize (h pn (inFull pn)).
        unfold sumBoolToBool in h.
        break_match; intuition.
    Qed.
    
    Lemma containmentSound {a} (h:containmentCheck = Some a) : denoteCQRewriteContainment.
      destruct (containmentSpec h) as [h'' h']; clear h; rename h'' into h.
      unfold denoteCQRewriteContainment.
      simpl.
      intros Γ s T c q g t [t0 [[select from] project]].
      simple refine (ex_intro _ _ _). {
        intros tn ta.
        refine (t0 tn (a tn ta)).
      }
      constructor; [constructor|].
      - (* selection variables are correct *)
        clear h'.
        unfold denoteSelection.
        induction (selections (CQ:=query1)) as [|sel sels rec].
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

    Definition containmentVerifier : Maybe denoteCQRewriteContainment.
      destruct containmentCheck eqn:h; [apply holds|apply unknown].
      exact (containmentSound h).
    Defined.
  End Containment.
  
  Section Equivalence.
    Context `{r:CQRewrite}.

    Lemma equivalenceSound {a a'} (h:equivalenceCheck = Some (a,a')) : denoteCQRewriteEquivalence.
      unfold equivalenceCheck in h.
      break_match; [|congruence].
      break_match; [|congruence].
      inversion h; clear h; subst.
      rename Heqo into h; rename Heqo0 into h'.
      apply containmentSound in h.
      apply containmentSound in h'.
      unfold denoteCQRewriteContainment in h.
      unfold denoteCQRewriteContainment in h'.
      unfold denoteCQRewriteEquivalence.
      intros.
      extensionality g.
      apply Extensionality_Ensembles'; intros t.
      specialize (h Γ s T c q g t).
      specialize (h' Γ s T c q g t).
      intuition.
    Qed.
      
    Definition equivalenceVerifier : Maybe denoteCQRewriteEquivalence.
      destruct equivalenceCheck as [[a a']|] eqn:h; [apply holds|apply unknown].
      exact (equivalenceSound h).
    Defined.
  End Equivalence.
End Soundness.

Ltac fullInductive :=
  rewrite fullIsTrue;
  apply Extensionality_Ensembles';
  intros [];
  (repeat rewrite denoteUnionOk);
  (repeat rewrite unionIsOr);
  (repeat rewrite denoteSingleOk);
  intuition. 
