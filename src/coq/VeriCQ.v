Require Import Rosette.Unquantified.
Require Import Conjunctive.
Require Import SelfJoin.
Require Import TransitiveJoin.

Set Implicit Arguments.

Definition vericq := (
  containmentSound (S:=rosetteSearch) (r:=selfJoin),
  containmentSound (S:=rosetteSearch) (r:=transitiveJoin)
).
   
Extraction Language Scheme.
Extraction "vericq" vericq.
