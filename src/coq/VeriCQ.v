Require Import Rosette.Unquantified.
Require Import Conjunctive.
Require Import SelfJoin.
Require Import TransitiveJoin.

Set Implicit Arguments.

Definition vericq := (
  equivalenceVerifier (S:=rosetteSearch) (r:=selfJoin),
  equivalenceVerifier (S:=rosetteSearch) (r:=transitiveJoin)
).
   
Extraction Language Scheme.
Extraction "vericq" vericq.
