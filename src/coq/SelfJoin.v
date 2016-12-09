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

(* NOTE, we could define tables as `Inductive tables := R`, but
unfortunately Coq's extraction is broken for inductive types with just
one constructor in two ways. Some such types (specifically aliases1)
it simply cannot extract (it fails with an error message), and others
it extracts incorrectly, such that __ is sometimes called as a function. 
Another advantage of using unit is that we can automatically infer the
full and eqdec instances.
*)
Definition tables := unit.
Definition R := tt.
Definition columns := unit.
Definition a := tt.
Definition projs := unit.
Definition w := tt.
Inductive aliases0 := x | y.
Definition aliases1 := unit.
Definition z := tt.
Definition types := unit.
Definition string := tt.

Definition selfJoin : CQRewrite.
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

Global Instance fullAliases0 : Full aliases0.
  refine {| full := [x;y] |}; fullIndList.
Defined.

Global Instance eqDecAliases0 : eqDec aliases0. 
  refine {| eqDecide := _ |}; decide equality.
Defined.
