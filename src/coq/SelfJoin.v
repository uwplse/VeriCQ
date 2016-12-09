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
Require Import Conjunctive.

Set Implicit Arguments.
Open Scope type.

Inductive tables := R.
Inductive columns := a.
Inductive projs := w.
Inductive aliases0 := x | y.
Inductive aliases1 := z | zz.  (* Coq can't extract this inductive types with one constructor *)
Inductive types := string.

Definition selfJoin : CQRewrite.
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

Goal denoteCQRewriteEquivalence selfJoin.
  unfold selfJoin.
  unfold denoteCQRewriteEquivalence.
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

Ltac fullIndList :=
  rewrite fullIsTrue;
  apply Extensionality_Ensembles';
  intros [];
  simpl;
  intuition.

Instance fullTables : Full tables.
  refine {| full := [R] |}; fullIndList.
Defined.

Instance fullProjs : Full projs.
  refine {| full := [w] |}; fullIndList.
Defined.

Instance fullAliases0 : Full aliases0.
  refine {| full := [x;y] |}; fullIndList.
Defined.

Instance fullAliases1 : Full aliases1.
  refine {| full := [z;zz] |}; fullIndList.
Defined.

Instance eqDecTables : eqDec tables. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecAliases0 : eqDec aliases0. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecAliases1 : eqDec aliases1. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecColumns : eqDec columns. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Definition checkSelfJoinContainment :=
  match containmentCheck selfJoin with 
  | solution _ => Datatypes.true 
  | _ => Datatypes.false 
  end.
