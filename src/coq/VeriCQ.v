Require Import Basic.
Require Import Rosette.Unquantified.
Require Import Precise.
Require Import Full.
Require Import JamesTactics.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import SQLSemantics.
Require Import Conjunctive.
Require Import SelfJoin.

Set Implicit Arguments.

Definition vericq :=
  match containmentCheck selfJoin with 
  | solution _ => Datatypes.true 
  | _ => Datatypes.false 
  end.

Extraction Language Scheme.
Extraction "vericq" vericq.
