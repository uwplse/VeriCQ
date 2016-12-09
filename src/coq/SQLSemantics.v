Require Import Denotation.

Open Scope type.

Inductive Tree (A:Type) := 
| namedNode N (t:N -> Tree A)
| node (t0 t1 : Tree A)
| leaf (a:A)
| empty
.

Arguments namedNode {_} _ _.
Arguments node {_} _ _.
Arguments leaf {_} _.
Arguments empty {_}. 

Module Type Types.
  Parameter type : Type.
  Parameter denotationType : Denotation type Type.
End Types.

Module SQLDenotation (T : Types).
  Import T.
  (* definition of inductive types in 
     modules isn't supported by Coq in this case *)
  (* NOTE ideally schemas would have little structure, and users
          of this library would be free to implement products of
          schemas etc as they wish. All this structure is useful 
          though because it introduces more computation in our
          proofs, and thus leads to much simpler proofs. *)
  Definition Schema := Tree type.
  Definition singleton := @leaf type.
  Notation "s0 ++ s1" := (node s0 s1).

  Fixpoint Tuple (s:Schema) : Type.
    refine (match s with
    | namedNode N t => forall n:N, Tuple (t n)
    | node t0 t1 => (Tuple t0) * (Tuple t1)
    | leaf T => ⟦T⟧
    | empty => unit
    end).
  Defined.

  (* NOTE we have a set semantics, this way we don't need HoTT *)
  Definition Relation s := Tuple s -> Prop.
  Definition Query Γ s := Tuple Γ -> Relation s.
End SQLDenotation.

Module Type Relations (T : Types).
  Import T.
  Module TD := SQLDenotation T.
  Import TD.
  Export TD.

  Parameter relation : Schema -> Type.
  Parameter denotationRelation : forall s, Denotation (relation s) (Relation s).
End Relations.

(* We have SQL depend on modules instead of type class instances
   because type classes lead to bad unfolding behavior of 
   mutually inductive fixpoints. *)
Module SQL (T : Types) (R : Relations T).
  Import T R.

  Inductive SQL : Schema -> Schema -> Type :=
  | select  {Γ s} : Pred (Γ ++ s) -> SQL Γ s -> SQL Γ s
  | product {Γ s0 s1} : SQL Γ s0 -> SQL Γ s1 -> SQL Γ (s0 ++ s1)
  | namedProduct {Γ N} {s:N -> Schema} : (forall n, SQL Γ (s n)) -> SQL Γ (namedNode N s)
  | project {Γ s s'} : Proj (Γ ++ s) s' -> SQL Γ s -> SQL Γ s'
  
  with Pred : Schema -> Type :=
  | equal {Γ T} : Expr Γ T -> Expr Γ T -> Pred Γ
  | and {Γ} : Pred Γ -> Pred Γ -> Pred Γ
  | true {Γ} : Pred Γ
  | false {Γ} : Pred Γ

  with Proj : Schema -> Schema -> Type :=
  | combine  {Γ Γ0 Γ1} : Proj Γ Γ0 -> Proj Γ Γ1 -> Proj Γ (Γ0 ++ Γ1)
  | left  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ0
  | right  {Γ0 Γ1} : Proj (Γ0 ++ Γ1) Γ1
  | named {N Γ s} : (forall n, Proj Γ (s n)) -> Proj Γ (namedNode N s)
  | name {N s} n : Proj (namedNode N s) (s n)
  | compose  {Γ Γ' Γ''} : Proj Γ Γ' -> Proj Γ' Γ'' -> Proj Γ Γ''
  | erase    {Γ} : Proj Γ empty
 
  with Expr : Schema -> type -> Type :=
  | variable {T Γ} (c:Proj Γ (leaf T)) : Expr Γ T 
  .

  Fixpoint denoteSQL {Γ s} (a : SQL Γ s) : Query Γ s 
  with     denotePred {Γ} (slct : Pred Γ) : Tuple Γ -> Prop
  with     denoteProj {Γ Γ'} (cast: Proj Γ Γ') {struct cast} : Tuple Γ -> Tuple Γ'
  with     denoteExpr {Γ T} (e : Expr Γ T) : Tuple Γ -> ⟦T⟧.
    - refine (
      match a in SQL Γ s return Query Γ s with
      | select slct a => fun g t => denotePred _ slct (g, t) /\
                                 denoteSQL _ _ a g t 
      | product a0 a1 => fun g t => denoteSQL _ _ a0 g (fst t) /\
                                denoteSQL _ _ a1 g (snd t)
      | @namedProduct _ N s a => fun g t => forall n:N, denoteSQL _ _ (a n) g (t n)
      | project proj a => fun g t' => exists t, denoteSQL _ _ a g t /\
                                        (denoteProj _ _ proj (g, t) = t')
      end).
    - refine (
      match slct in Pred Γ return Tuple Γ -> Prop with
      | equal e0 e1 => fun g => (denoteExpr _ _ e0 g = denoteExpr _ _ e1 g)
      | and slct0 slct1 => fun g => (denotePred _ slct0 g) /\ (denotePred _ slct1 g)
      | true => fun _ => True
      | false => fun _ => False
      end).
    - refine (
      match cast in Proj s s' return Tuple s -> Tuple s' with
      | combine c c' => fun t => (denoteProj _ _ c t, denoteProj _ _ c' t)
      | left => fst
      | right => snd
      | named p => fun t n => denoteProj _ _ (p n) t
      | name n => fun t => t n
      | compose c c' => fun t => denoteProj _ _ c' (denoteProj _ _ c t)
      | erase => fun _ => tt
      end).
    - refine (
      match e in Expr Γ T return Tuple Γ -> ⟦T⟧ with
      | variable c => fun g => denoteProj _ _ c g
      end).
  Defined.

  Global Instance denotationProj {Γ Γ'} : Denotation (Proj Γ Γ') (Tuple Γ -> Tuple Γ') := {| 
    denote := denoteProj 
  |}.

  Global Instance denotationSQL Γ s : Denotation (SQL Γ s) _ := {| 
    denote := denoteSQL 
  |}.

  Global Instance denotationPred Γ : Denotation (Pred Γ) _ := {| 
    denote := denotePred 
  |}.
  
  Global Instance denotationExpr Γ T : Denotation (Expr Γ T) _ := {| 
    denote := denoteExpr 
  |}.

  Definition Column T Γ := Proj Γ (leaf T).

  Definition Projection Γ s s' := Proj (Γ ++ s) s'.

  Arguments Projection _ _ _ /.

  Definition projectStar {Γ s} : Projection Γ s s := right.
   
  Notation "p1 ⋅ p2" := (compose p1 p2) (at level 45).
  Notation "Γ ⊢ x : s" := (x:(SQL Γ s)) (at level 45, x at level 45).
  Notation "a 'WHERE' c" := (select c a) (at level 45, c at level 45).
  Notation "'SELECT' '*' a" := (a) (at level 45).
  Notation "'SELECT1' proj a" := (project proj a) (at level 45).
  Notation "'FROM1' a" := (a) (at level 45).
  Notation "'FROM' a , b , .. , c" := (product .. (product a b) .. c) (at level 46, c at level 44).
  Notation "s0 'AND' s1" := (and s0 s1) (at level 45).
  Notation "'TRUE'" := (true) (at level 45).
  Notation "'FALSE'" := (false) (at level 45).
End SQL.
