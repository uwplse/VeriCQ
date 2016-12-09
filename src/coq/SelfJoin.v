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
Require Import Datatypes.

Set Implicit Arguments.
Open Scope type.

(* NOTE, we could define tables etc as `Inductive tables := R`, but
unfortunately Coq's extraction is broken for inductive types with just
one constructor in two ways. Some such types (specifically aliases1)
it simply cannot extract (it fails with an error message), and others
it extracts incorrectly, such that __ is sometimes called as a function. 
Another advantage of using unit is that we can automatically infer the
full and eqdec instances.

UPDATE: The fix is to have these inductive definitions in Set.
*)
Inductive tables : Set := R.
Inductive columns : Set := a.
Inductive projs : Set := w.
Inductive aliases0 : Set := x | y.
Inductive aliases1 : Set := z.
Inductive types : Set := string.

Section Full.
  Context `{S:Basic}.

  Global Instance fullTables : Full tables.
    refine {| full := single R |}; fullInductive.
  Defined.
  
  Global Instance fullProjs : Full projs.
    refine {| full := single w |}; fullInductive.
  Defined.

  Global Instance fullColumns : Full columns.
    refine {| full := single a |}; fullInductive.
  Defined.
  
  Global Instance fullAliases0 : Full aliases0.
    refine {| full := union (single x) (single y) |}; fullInductive.
  Defined.
  
  Global Instance fullAliases1 : Full aliases1.
    refine {| full := single z |}; fullInductive.
  Defined.
End Full.

Instance eqDecTables : eqDec tables. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecProjs : eqDec projs. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecColumns : eqDec columns. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecAliases0 : eqDec aliases0. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance eqDecAliases1 : eqDec aliases1. 
  refine {| eqDecide := _ |}; decide equality.
Defined.

Instance selfJoin : CQRewrite.
  refine {|
    SQLType := types;
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

Goal denoteCQRewriteEquivalence.
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
