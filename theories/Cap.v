Inductive cap := iso | trn | ref | box | val | tag.
Inductive ecap := C : cap -> ecap | iso_eph | trn_eph.

Inductive op := read | extract.
Definition adapt (o: op) (λ: ecap) (κ: cap) : option ecap :=
  match o, λ, κ with
  | read, iso_eph, iso => Some iso_eph
  | read, iso_eph, trn => Some iso_eph
  | read, iso_eph, ref => Some iso_eph
  | read, iso_eph, val => Some (C val)
  | read, iso_eph, box => Some (C val)
  | read, iso_eph, tag => Some (C tag)

  | read, C iso, iso => Some (C iso)
  | read, C iso, trn => Some (C iso)
  | read, C iso, ref => Some (C iso)
  | read, C iso, val => Some (C val)
  | read, C iso, box => Some (C val)
  | read, C iso, tag => Some (C tag)

  | read, trn_eph, iso => Some iso_eph
  | read, trn_eph, trn => Some trn_eph
  | read, trn_eph, ref => Some trn_eph
  | read, trn_eph, val => Some (C val)
  | read, trn_eph, box => Some (C val)
  | read, trn_eph, tag => Some (C tag)

  | read, C trn, iso => Some (C iso)
  | read, C trn, trn => Some (C trn)
  | read, C trn, ref => Some (C trn)
  | read, C trn, val => Some (C val)
  | read, C trn, box => Some (C val)
  | read, C trn, tag => Some (C tag)

  | read, C ref, iso => Some (C iso)
  | read, C ref, trn => Some (C trn)
  | read, C ref, ref => Some (C ref)
  | read, C ref, val => Some (C val)
  | read, C ref, box => Some (C box)
  | read, C ref, tag => Some (C tag)

  | read, C val, iso => Some (C val)
  | read, C val, trn => Some (C val)
  | read, C val, ref => Some (C val)
  | read, C val, val => Some (C val)
  | read, C val, box => Some (C val)
  | read, C val, tag => Some (C tag)

  | read, C box, iso => Some (C tag)
  | read, C box, trn => Some (C box)
  | read, C box, ref => Some (C box)
  | read, C box, val => Some (C val)
  | read, C box, box => Some (C box)
  | read, C box, tag => Some (C tag)

  | read, C tag, _ => None

  | extract, iso_eph, iso => Some iso_eph
  | extract, iso_eph, trn => Some iso_eph
  | extract, iso_eph, ref => Some iso_eph
  | extract, iso_eph, val => Some (C val)
  | extract, iso_eph, box => Some (C val)
  | extract, iso_eph, tag => Some (C tag)

  | extract, C iso, iso => Some iso_eph
  | extract, C iso, trn => Some (C val)
  | extract, C iso, ref => Some (C tag)
  | extract, C iso, val => Some (C val)
  | extract, C iso, box => Some (C tag)
  | extract, C iso, tag => Some (C tag)

  | extract, trn_eph, iso => Some iso_eph
  | extract, trn_eph, trn => Some trn_eph
  | extract, trn_eph, ref => Some trn_eph
  | extract, trn_eph, val => Some (C val)
  | extract, trn_eph, box => Some (C val)
  | extract, trn_eph, tag => Some (C tag)

  | extract, C trn, iso => Some iso_eph
  | extract, C trn, trn => Some (C val)
  | extract, C trn, ref => Some (C box)
  | extract, C trn, val => Some (C val)
  | extract, C trn, box => Some (C box)
  | extract, C trn, tag => Some (C tag)

  | extract, C ref, iso => Some iso_eph
  | extract, C ref, trn => Some trn_eph
  | extract, C ref, ref => Some (C ref)
  | extract, C ref, val => Some (C val)
  | extract, C ref, box => Some (C box)
  | extract, C ref, tag => Some (C tag)

  | extract, C val, _ => None
  | extract, C box, _ => None
  | extract, C tag, _ => None
  end.

Definition alias (λ: ecap) :=
  match λ with
  | iso_eph => iso
  | trn_eph => trn
  | C iso => tag
  | C trn => box
  | C ref => ref
  | C val => val
  | C box => box
  | C tag => tag
  end.

Definition unalias (κ: cap) :=
  match κ with
  | iso => iso_eph
  | trn => trn_eph
  | ref => C ref
  | val => C val
  | box => C box
  | tag => C tag
  end.

Inductive compatible : ecap -> ecap -> Prop :=
| compatible_isoe_tag : compatible iso_eph (C tag)

| compatible_trne_tag : compatible trn_eph (C tag)
| compatible_trne_box : compatible trn_eph (C box)

| compatible_iso_tag : compatible (C iso) (C tag)

| compatible_trn_tag : compatible (C trn) (C tag)
| compatible_trn_box : compatible (C trn) (C box)

| compatible_ref_tag : compatible (C ref) (C tag)
| compatible_ref_box : compatible (C ref) (C box)
| compatible_ref_ref : compatible (C ref) (C ref)

| compatible_val_tag : compatible (C val) (C tag)
| compatible_val_box : compatible (C val) (C box)
| compatible_val_val : compatible (C val) (C val)

| compatible_box_tag : compatible (C box) (C tag)
| compatible_box_box : compatible (C box) (C box)
| compatible_box_val : compatible (C box) (C val)
| compatible_box_ref : compatible (C box) (C ref)
| compatible_box_trn : compatible (C box) (C trn)
| compatible_box_trne : compatible (C box) trn_eph

| compatible_tag : forall λ, compatible (C tag) λ
.
Hint Constructors compatible.

Inductive subcap : ecap -> ecap -> Prop :=
| subcap_refl : forall λ, subcap λ λ
| subcap_isoe_iso : subcap iso_eph (C iso)
| subcap_iso_tag : subcap (C iso) (C tag)
| subcap_isoe_trne : subcap iso_eph trn_eph
| subcap_trne_trn : subcap trn_eph (C trn)
| subcap_trne_ref : subcap trn_eph (C ref)
| subcap_trne_val : subcap trn_eph (C val)
| subcap_trn_box : subcap (C trn) (C box)
| subcap_ref_box : subcap (C ref) (C box)
| subcap_val_box : subcap (C val) (C box)
| subcap_box_tag : subcap (C box) (C tag)

| subcap_isoe_trn : subcap iso_eph (C trn)
| subcap_isoe_ref : subcap iso_eph (C ref)
| subcap_isoe_val : subcap iso_eph (C val)
| subcap_isoe_box : subcap iso_eph (C box)
| subcap_isoe_tag : subcap iso_eph (C tag)

| subcap_trne_box : subcap trn_eph (C box)
| subcap_trne_tag : subcap trn_eph (C tag)

| subcap_ref_tag : subcap (C ref) (C tag)
| subcap_val_tag : subcap (C val) (C tag)
| subcap_trn_tag : subcap (C trn) (C tag)
(* | subcap_trans : forall λ λ' λ'', subcap λ λ' -> subcap λ' λ'' -> subcap λ λ'' *)
.
Hint Constructors subcap.

Inductive safe_to_write : ecap -> cap -> Prop :=
| safe_to_write_isoe : forall κ, safe_to_write iso_eph κ
| safe_to_write_trne : forall κ, safe_to_write trn_eph κ
| safe_to_write_ref  : forall κ, safe_to_write (C ref) κ

| safe_to_write_iso_iso : safe_to_write (C iso) iso
| safe_to_write_iso_val : safe_to_write (C iso) val
| safe_to_write_iso_tag : safe_to_write (C iso) tag

| safe_to_write_trn_iso : safe_to_write (C trn) iso
| safe_to_write_trn_trn : safe_to_write (C trn) trn
| safe_to_write_trn_val : safe_to_write (C trn) val
| safe_to_write_trn_tag : safe_to_write (C trn) tag
.
Hint Constructors safe_to_write.

