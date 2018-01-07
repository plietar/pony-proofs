Require Import Coq.Lists.List.

Require Import Cap.
Require Import Notations.

Definition capset := list ecap.
Definition compatible_set (λs λs': capset) : Prop :=
  forall λ λ', In λ λs ->
               In λ' λs' -> 
               compatible λ λ'.

Fixpoint combine_one (λs: capset) (κ: cap) : capset :=
  match λs with
  | λ0::tail =>
    match adapt read λ0 κ, adapt extract λ0 κ with
    | Some λr, Some λe => λr :: λe :: combine_one tail κ
    | Some λr, None => λr :: combine_one tail κ
    | None, Some λe => λe :: combine_one tail κ
    | None, None => combine_one tail κ
    end
  | nil => nil
  end.

Definition combine (λs: capset) (κs: list cap) : capset :=
  fold_left combine_one κs λs.

Instance blob_combine_one : Blob capset cap := { blob := combine_one }.
Instance blob_combine : Blob capset (list cap) := { blob := combine }.
