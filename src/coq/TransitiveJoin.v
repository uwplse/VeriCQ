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

Definition tables := unit.
Definition R := tt.
Inductive columns := a | b | c.
Definition projs := unit.
Definition aliases := unit.
Definition x := tt.
Definition types := unit.
Definition string := tt.

Definition transitiveJoin : CQRewrite.
  refine {|
    SQLType := types;
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

Goal denoteCQRewriteEquivalence transitiveJoin.
  unfold transitiveJoin.
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
      + exact x.
    }
    simpl; unfold R in *.
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
    simpl; unfold R in *.
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

Global Instance fullColumns : Full columns.
  refine {| full := [a;b;c] |}; fullIndList.
Defined.

Global Instance eqDecColumns : eqDec columns.
  refine {| eqDecide := _ |}; decide equality.
Defined.
