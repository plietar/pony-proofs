Require Import Coq.Lists.List.

Require Import Cap.
Require Import CapSets.
Require Import Notations.

Inductive cap_group := G : cap -> cap_group.
Definition unG (g: cap_group) := match g with G κ => κ end.

Definition ISO := G iso.
Definition TRN := G trn.
Definition REF := G ref.
Definition VAL := G val.
Definition BOX := G box.
Definition TAG := G tag.
Inductive bottom := BOT.

Instance elemOf_capgroup : ElemOf capset cap_group :=
  fun λs g => In (unalias (unG g)) λs /\ (forall λ, In λ λs -> subcap (unalias (unG g)) λ).

Instance elemOf_bot : ElemOf capset bottom :=
  fun λs _ => λs = nil.

Definition STABLE := ISO ∪ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT.
Definition READABLE := ISO ∪ TRN ∪ REF ∪ VAL ∪ BOX.
Definition WRITABLE := ISO ∪ TRN ∪ REF.
