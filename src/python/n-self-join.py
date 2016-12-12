#!/usr/bin/env python

import sys

seg0 = """Require Import Denotation.
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

Inductive tables : Set := R.
Inductive columns : Set := a.
Inductive projs : Set := w."""

seg1 = """Inductive aliases1 : Set := y.
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
  
  Global Instance fullAliases0 : Full aliases0."""

seg2 = """  Defined.
  
  Global Instance fullAliases1 : Full aliases1.
    refine {| full := single y |}; fullInductive.
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
                 projection pn := (R;(x0,a));"""

seg3 = """              |};
    query1 := {| TableAlias tn := aliases1; 
                 projection pn := (R;(y,a));
                 selections := []
              |}
  |}.
Defined."""

if __name__ == "__main__":
	
	n = sys.argv[1]

	#write the first chunk, this is always the same
	print(seg0)

	# add aliases 0 to n
	#Inductive aliases0 : Set := x0 | x1 | x2 | x3. ...

	alias_line = "Inductive aliases0 : Set :="

	for i in range(0, int(n) - 1):
		alias_line += " x" + str(i) + " |"

	alias_line += " x" + str(int(n) - 1) + ".\n"

	print(alias_line)

	#write the second chunk, this is always the same
	print(seg1)

	# union x0 to xn
    #refine {| full := union (single x0) (
    #                  union (single x1) (
    #                  union (single x2) 
    #                        (single x3))) |}; fullInductive.

	
	union_line = "    refine {| full := "

	for i in range(0, int(n) - 1):
		union_line += "union (single x" + str(i) + ") ("
		if (i < int(n) - 2):
			union_line += "\n                      "

	union_line += "single x" + str(int(n) - 1) + ")" * (int(n) - 1) + " |}; fullInductive.\n"

	print(union_line)

	#write the third chunk, this is always the same
	print(seg2)

	# all tuples pairs of x_i, x_i+1 from i = 0 to n-1
	#                 selections := [(string; ((R;(x0,a)), (R;(x1,a))));
	#                                (string; ((R;(x1,a)), (R;(x2,a))));
	#                                (string; ((R;(x2,a)), (R;(x3,a))))]
	#              |};

	select_line = "                 selections := ["

	for i in range(0, int(n) - 1):
		select_line += "(string; ((R;(x" + str(i) + ",a)), (R;(x" + str(i+1) + ",a))))"
		if (i < int(n) - 2):
			select_line += ";\n                                "
	select_line += "]\n"

	print(select_line)
	print(seg3)
