Require Import Coq.Lists.List.

Class ElemOf (A B: Type) := elemOf: A -> B -> Prop.
Class Blob (A B: Type) := blob: A -> B -> A.

Instance elemOf_list {A} : ElemOf A (list A) := @In A.

Inductive union (A B: Type) := union_ : A -> B -> union A B.

Notation "A ∪ B" := (union_ _ _ A B) (at level 60, right associativity).
Notation "A ∈ B" := (elemOf A B) (at level 70).
Notation "A ∘ B" := (blob A B) (at level 60).

Instance elemOf_union {A B C: Type} {_: ElemOf A B} {_: ElemOf A C}: ElemOf A (union B C) :=
  fun a u => match u with union_ _ _ b c => a ∈ b \/ a ∈ c end.
