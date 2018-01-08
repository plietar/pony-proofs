Require Import Coq.Lists.List.

Require Import Cap.
Require Import CapSets.
Require Import Notations.

Inductive cap_group := G : cap -> cap_group.

Instance elemOf_capgroup : ElemOf capset cap_group := fun λs g =>
  match g with
    G κ => In (unalias κ) λs /\ (forall λ, In λ λs -> subcap (unalias κ) λ)
  end.

Inductive bottom := BOT.
Instance elemOf_bot : ElemOf capset bottom :=
  fun λs _ => λs = nil.

Definition ISO := G iso.
Definition TRN := G trn.
Definition REF := G ref.
Definition VAL := G val.
Definition BOX := G box.
Definition TAG := G tag.

Definition STABLE := ISO ∪ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT.
Definition READABLE := ISO ∪ TRN ∪ REF ∪ VAL ∪ BOX.
Definition WRITABLE := ISO ∪ TRN ∪ REF.

Ltac destruct_READABLE H := destruct H as [|[|[|[|]]]].
Ltac destruct_STABLE H := destruct H as [|[|[|[|[|[|]]]]]].
Ltac destruct_WRITABLE H := destruct H as [|[|]].
