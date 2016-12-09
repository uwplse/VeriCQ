Require Import Basic.
Require Import Rosette.Unquantified.
Require Import Precise.
Require Import Full.
Require Import JamesTactics.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import SQLSemantics.
Require Import Conjunctive.
Require Import SelfJoin.
Require Import TransitiveJoin.
Require Import Datatypes.

Set Implicit Arguments.

Definition vericq := (
  containmentSound (r:=selfJoin),
  containmentSound (r:=transitiveJoin)
).
    
Extraction Language Scheme.
Extraction "vericq" vericq.
