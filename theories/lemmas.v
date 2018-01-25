Require Import Coq.Lists.List.
Import ListNotations.

Require Import Cap.
Require Import CapSets.
Require Import CapGroups.
Require Import Notations.

Ltac unfold_classes := repeat unfold
  alias, unalias,
  blob, blob_combine, blob_combine_one,
  elemOf, elemOf_union, elemOf_list, elemOf_bot,
  READABLE, NONWRITABLE, WRITABLE, STABLE, ISO, TRN, REF, VAL, BOX, TAG in *.
Ltac finish := solve [subst; unfold_classes; tauto].
Hint Extern 4 (~(_ = _)) => discriminate.
Hint Extern 4 ((_ = _)) => symmetry.
Hint Extern 4 => unfold_classes.

Tactic Notation "destruct_ecap" constr(e) :=
  (destruct e as [[]| |]).
Tactic Notation "destruct_ecap" constr(e1) "," constr(e2) :=
  (destruct_ecap e1 ; destruct_ecap e2).
Tactic Notation "destruct_ecap" constr(e1) "," constr(e2) "," constr(e3) :=
  (destruct_ecap e1 ; destruct_ecap e2 ; destruct_ecap e3).

Tactic Notation "destruct'" constr(H) := destruct H.
Tactic Notation "destruct'" constr(H) "by" tactic(tac) :=
  (let h := fresh "H" in assert H as h by tac; destruct h).
Tactic Notation "destruct'" constr(H) "as" simple_intropattern(pat) "by" tactic(tac) :=
  (let h := fresh "H" in assert H as h by tac; destruct h as pat).

Tactic Notation "replace'" constr(e1) "with" constr(e2) "by" tactic(tac) :=
  replace e1 with e2 in * by (symmetry; tac).

Lemma lemma1 {A} : forall (x y: A), In x [y] -> x = y.
Proof. intros. destruct H; [auto | destruct H]. Qed.
Hint Resolve lemma1.

Lemma lemma2 {A} : forall (x: A) (xs: list A), In x (x::xs).
Proof. simpl. finish. Qed.
Hint Resolve lemma2.

Lemma lemma3 {A} : forall (x y: A) (xs: list A), In y xs -> In y (x::xs).
Proof. simpl. finish. Qed.
Hint Resolve lemma3.

Lemma lemma4 : forall λ λs κ,
  λ ∈ (λs ∘ κ) -> exists o λ0, λ0 ∈ λs /\ adapt o λ0 κ = Some λ.
Proof with auto.
intros.
induction λs as [|λ0].
- exfalso. auto.
- assert (λ ∈ (λs ∘ κ) -> exists (o : op) (λ1 : ecap), λ1 ∈ (λ0::λs) /\ adapt o λ1 κ = Some λ) as IHλs'.
  + intro.
    destruct IHλs as [o [λ10 [? ?]]]. auto.
    exists o, λ10. split. apply lemma3. auto. auto.

  + unfold_classes; unfold combine_one in H; fold combine_one in H.
    destruct (adapt read λ0 κ) eqn:?; destruct (adapt extract λ0 κ) eqn:?.
    1:   inversion_clear H; [subst; eexists read, λ0; eauto | rename H0 into H].
    1-3: inversion_clear H; [subst; eexists _, λ0; eauto |].
    all: apply IHλs'; auto.
Qed.

Lemma lemma5: forall o λ0 λs κ λ1,
  λ0 ∈ λs -> adapt o λ0 κ = Some λ1 -> λ1 ∈ (λs ∘ κ).
Proof with auto.
intros.
induction λs.
- inversion H.
- destruct H; unfold_classes; unfold combine_one.
  + destruct o.
    * subst. rewrite H0.
      destruct (adapt extract λ0 κ)...
    * subst. rewrite H0.
      destruct (adapt read λ0 κ)...
  + destruct (adapt extract a κ); destruct (adapt read a κ)...
Qed.

Lemma lemma6: forall λ λ',
  subcap λ λ' -> subcap λ' λ -> λ = λ'.
Proof with auto.
intros.
destruct_ecap λ, λ';
inversion H; inversion H0; auto.
Qed.

Lemma lemma7: forall λ λ' λ'',
  subcap λ λ' -> subcap λ' λ'' -> subcap λ λ''.
Proof.
intros.
inversion H; inversion H0; subst; try inversion H3; auto.
Qed.

Lemma lemma8: forall κ κ',
  unalias κ = unalias κ' -> κ = κ'.
Proof with auto.
destruct κ, κ'; unfold unalias; inversion 1...
Qed.

Lemma lemma9: forall λs κ κ',
  λs ∈ (G κ) ->
  λs ∈ (G κ') ->
  κ = κ'.
Proof with auto.
intros λs κ κ' [HκA HκB] [Hκ'A Hκ'B].
apply lemma8, lemma6...
Qed.

Lemma lemma10: forall λ κ κ',
  adapt extract (unalias κ) κ' = Some λ ->
  unalias (alias λ) = λ.
Proof.
intros.
destruct κ, κ'; inversion H; subst; auto.
Qed.

Lemma lemma11: forall λ κ κ',
  adapt extract (unalias κ) κ' = None ->
  adapt read (unalias κ) κ' = Some λ ->
  unalias (alias λ) = λ.
Proof.
intros.
destruct κ, κ'; inversion H0; inversion H; subst; auto.
Qed.

Lemma lemma12: forall o λ0 λ0' κ λ1 λ1',
  subcap λ0 λ0' ->
  adapt o λ0 κ = Some λ1 ->
  adapt o λ0' κ = Some λ1' ->
  subcap λ1 λ1'.
Proof.
intros.
inversion H.
1: subst. rewrite H0 in H1. inversion H1. subst. apply subcap_refl.
all: destruct o, κ ; subst; inversion H0; inversion H1; auto.
Qed.

Lemma lemma13: forall κ κ' λe λr,
  adapt extract (unalias κ) κ' = Some λe ->
  adapt read (unalias κ) κ' = Some λr ->
  subcap λe λr.
Proof with auto.
destruct κ, κ'; inversion 1; inversion 1; subst...
Qed.

Lemma lemma14: forall λ κ λe,
  adapt extract λ κ = Some λe ->
  exists λr, adapt read λ κ = Some λr.
Proof with auto.
intros.
destruct (adapt read λ κ) as [λr|] eqn:?.
- exists λr...
- destruct_ecap λ; destruct κ; inversion Heqo; inversion H.
Qed.

Lemma lemma15 : forall λs κ κ' λ,
  λs ∈ (G κ) ->
  adapt extract (unalias κ) κ' = Some λ ->
  (λs ∘ κ') ∈ (G (alias λ)).
Proof with eauto.
intros λs κ κ' λ [? ?] ?.
unfold elemOf, elemOf_capgroup in *.
erewrite lemma10; eauto.
split.
- eapply lemma5...
- intros λ0 ?.
  edestruct lemma4 as [[] [λ' [? Hadapt]]]; eauto.
  * edestruct lemma14 as [λ'']; eauto.
    apply lemma7 with (λ':=λ'').
    + eapply lemma13...
    + eapply lemma12; [apply H0|..] ...
  * eapply lemma12; [apply H0|..] ...
Qed.


Lemma lemma16 : forall λs κ κ' λ,
  λs ∈ (G κ) -> λ ∈ λs ->
  adapt extract (unalias κ) κ' = None ->
  adapt extract λ κ' = None.
Proof.
intros.
assert (subcap (unalias κ) λ) by (apply H; auto).
destruct_ecap λ; destruct κ, κ'; simpl in *;
inversion H1; inversion H2; auto.
Qed.

Lemma lemma17 : forall λs κ κ' λ,
  λs ∈ (G κ) ->
  adapt extract (unalias κ) κ' = None ->
  adapt read (unalias κ) κ' = Some λ ->
  (λs ∘ κ') ∈ (G (alias λ)).
Proof with eauto.
intros λs κ κ' λ [? ?] ? ?.
unfold elemOf, elemOf_capgroup in *.
erewrite lemma11; eauto.
split.
- eapply lemma5...
- intros λ0 ?.
  edestruct lemma4 as [[] [λ' [? Hadapt]]]; eauto.
  * eapply lemma12; [apply H0|..] ...
  * assert (adapt extract λ' κ' = None)
      by (eapply lemma16; unfold elemOf, elemOf_capgroup; eauto).
    rewrite H5 in Hadapt. inversion Hadapt.
Qed.

Lemma lemma18 : forall λs κ,
  (λs ∈ (G iso ∪ G trn ∪ G val)) ->
  (λs ∘ κ ∈ (G iso ∪ G trn ∪ G val) \/ κ = tag).
Proof with auto.
intros.
destruct H as [|[|]].

all: try solve [
  destruct κ eqn:?;
  eassert ((λs ∘ κ) ∈ (G _))
    by (eapply lemma15 + eapply lemma17; eauto; subst κ; finish);
  subst κ; finish].
Qed.

Lemma lemma19 : forall λs κs κ,
  λs ∘ (κs++[κ]) = λs ∘ κs ∘ κ.
Proof.
intros. unfold_classes. unfold combine. rewrite fold_left_app. auto.
Qed.

Lemma lemma20: [C ref] ∈ (G ref).
Proof with auto.
split; simpl; auto.
intros. rewrite lemma1 with (y:=C ref); auto.
Qed.
Hint Resolve lemma20.

Lemma lemma21 {A}: forall (xs: list A),
  (forall x, x ∈ xs -> False) -> xs = [].
Proof.
intros.
destruct xs; [auto | exfalso; apply H with (x:=a); apply lemma2].
Qed.

Lemma lemma22: forall (λs: capset) (κ: cap),
  λs ∈ TAG -> (λs ∘ κ) ∈ BOT.
Proof.
intros.
unfold_classes.
apply lemma21.
intros λ1 ?.
edestruct lemma4 as [o [λ0 [? Hadapt]]]; only 1: apply H0.
assert (subcap (C tag) λ0) by (apply H; auto).
assert (λ0 = C tag) by (inversion H2; auto).
subst λ0.
destruct o, κ; inversion Hadapt.
Qed.

Lemma lemma23: forall (λs: capset) (κ: cap),
  λs ∈ BOT -> (λs ∘ κ) ∈ BOT.
Proof.
intros; unfold_classes; subst λs; unfold combine_one; trivial.
Qed.

Lemma lemma24: forall (λs: capset) (κ: cap),
  λs ∈ READABLE -> exists κ', (λs ∘ κ) ∈ G(κ').
Proof.
intros.
destruct_READABLE H.
all:
  destruct κ eqn:?;
  eassert ((λs ∘ κ) ∈ (G (alias _)))
    by (eapply lemma15 + eapply lemma17; eauto; subst κ; finish);
  eexists _; subst; apply H0.
Qed.

Lemma lemma25: forall λs (κ: cap),
  λs ∈ G κ -> λs ∈ STABLE.
Proof.
intros.
destruct κ; unfold STABLE; unfold_classes; finish.
Qed.
Hint Resolve lemma25.

Lemma lemma26: forall λs (κ: cap),
  λs ∈ STABLE -> (λs ∘ κ) ∈ STABLE.
Proof with auto.
intros.
unfold STABLE in *.
destruct_STABLE H.

1-5: edestruct lemma24 with (λs:=λs);
     [ unfold_classes; unfold READABLE; auto
     | eapply lemma25; eauto].

all: assert ((λs ∘ κ) ∈ BOT) by (apply lemma22 + apply lemma23; auto);
     unfold_classes; finish.
Qed.
Hint Resolve lemma26.

Lemma lemma27: forall λs (κs: list cap),
  λs ∈ STABLE -> (λs ∘ κs) ∈ STABLE.
Proof.
induction κs using rev_ind.
- unfold blob, blob_combine, combine, fold_left; auto.
- intros. erewrite lemma19. apply lemma26. auto.
Qed.
Hint Resolve lemma27.

Lemma lemma28: forall (λs: capset),
  λs ∈ READABLE -> λs ∘ tag ∈ TAG.
Proof with auto.
intros.
destruct_READABLE H.
all:
  eassert ((λs ∘ tag) ∈ (G (alias (C tag))))
    by (eapply lemma15 + eapply lemma17; eauto)...
Qed.

Lemma lemma29 : forall λs,
  λs ∈ STABLE -> λs ∘ tag ∈ TAG \/ λs ∘ tag ∈ BOT.
Proof with finish.
intros.
destruct_STABLE H.
1-5: left; apply lemma28; unfold READABLE...
- right; apply lemma22...
- right; apply lemma23...
Qed.

Lemma lemma30 : forall κ, [unalias κ] ∈ G κ.
Proof.
split.
unfold_classes; auto.
inversion 1; [subst; auto | inversion H0].
Qed.
Hint Resolve lemma30.

Lemma lemma31 : forall κ, [unalias κ] ∈ STABLE.
Proof.
intros.
assert ([unalias κ] ∈ G κ) by apply lemma30.
destruct κ; finish.
Qed.
Hint Resolve lemma31.

Lemma lemma32 : [C ref] ∈ STABLE.
Proof.
replace (C ref) with (unalias ref) by auto. apply lemma31.
Qed.
Hint Resolve lemma32.

Lemma lemma34 : forall (λs: capset) (κs: list cap),
  (λs ∈ (ISO ∪ TRN ∪ VAL)) ->
  λs ∘ κs ∈ (ISO ∪ TRN ∪ VAL)
  \/ (λs ∘ κs ∈ TAG /\ [C ref] ∘ κs ∈ TAG)
  \/ ([C ref] ∘ κs ∈ BOT).
Proof with finish.
intros.
induction κs as [|κ] using rev_ind.
1: destruct H as [|[|]]...

destruct IHκs as [|[|]]; repeat rewrite lemma19.
- edestruct lemma18 with (λs:=combine λs κs) (κ:=κ) as [|]; auto.

  assert (λs ∘ κs ∘ tag ∈ TAG)
    by (apply lemma28; finish).

  destruct lemma29 with ([C ref] ∘ κs);
    [apply lemma27, lemma32 | ..]...

- assert ([C ref] ∘ κs ∘ κ ∈ BOT) by (apply lemma22; finish)...
- assert ([C ref] ∘ κs ∘ κ ∈ BOT) by (apply lemma23; finish)...
Qed.

Lemma lemma35 : forall λs (κs: list cap),
  λs ∈ (ISO ∪ TRN ∪ VAL) ->
  λs ∘ κs ∈ TAG ->
  [C ref] ∘ κs ∈ TAG ∪ BOT.
Proof with finish.
intros.
edestruct lemma34 as [|[|]]; eauto.
- destruct H1 as [|[|]];
  eassert (_=tag) as H2 by (eapply lemma9; [eapply H1 | eapply H0]);
  inversion H2.
- finish.
Qed.

Lemma lemma36 : forall (λs: capset) (κ: cap),
  λs ∈ G κ -> λs ∈ BOT -> False.
Proof.
intros.
inversion H0. subst.
destruct H. destruct H.
Qed.

Lemma lemma37 : forall (λs: capset) (κ: cap) (κ': cap),
  λs ∈ STABLE -> λs ∘ κ ∈ G κ' -> λs ∈ READABLE.
Proof.
intros.
destruct_STABLE H.
1-5: finish.
- exfalso; eapply lemma36; [apply H0 | apply lemma22; auto].
- exfalso; eapply lemma36; [apply H0 | apply lemma23; auto].
Qed.

Lemma lemma38 : forall (λs λs': capset) (κ1: cap) (κ κ': cap),
  λs ∈ G κ -> λs' ∈ G κ -> λs ∘ κ1 ∈ G κ' ->
  λs' ∘ κ1 ∈ G κ'.
Proof with finish.
intros.
assert (λs ∈ READABLE)
  by (eapply lemma37; [eapply lemma25|]; eauto).
destruct_READABLE H2; try (
  eassert (κ=_) by (eapply lemma9; [apply H | apply H2]); subst κ;
  destruct κ1 eqn:?; (
    eassert (κ' = alias _)
      by (eapply lemma9; [apply H1 | eapply lemma15 + eapply lemma17; [apply H2 | tauto..]]);
     subst κ'; eapply lemma15 + eapply lemma17 ; [apply H0 | solve [auto]..]
  )
).
Qed.

Lemma lemma39 (P: capset -> Prop):
  (forall λs, P λs) -> (forall λs (κ: cap), P λs -> P (λs ∘ κ)) -> forall λs κs, P (λs ∘ κs).
Proof.
intros.
induction κs as [|κ0] using rev_ind.
- apply H.
- rewrite lemma19. apply H0. apply IHκs.
Qed.

Lemma lemma40 : forall (λs: capset), λs ∈ READABLE -> exists κ, λs ∈ G κ.
Proof.
intros.
destruct_READABLE H.
1-5: eexists _; apply H.
Qed.

Lemma lemma41 : forall (κ κ': cap) (λs λs': capset) (κs: list cap),
  λs ∈ G κ ->
  λs' ∈ G κ ->
  λs ∘ κs ∈ G κ' ->
  λs' ∘ κs ∈ G κ'.
Proof with finish.
intros.
generalize dependent λs; generalize dependent λs'; generalize dependent κ; generalize dependent κ'.
induction κs as [|κ] using rev_ind.
- intros.
  assert (κ=κ') by (eapply lemma9; [apply H | apply H1]).
  subst. auto.

- intros κ2 κ0.
  intros.
  rewrite lemma19 in *.
  destruct lemma40 with (λs:=combine λs κs) as [κ1]; auto.
  eapply lemma37; [apply lemma27; eapply lemma25; apply H | apply H1].
  apply lemma38 with (λs:=combine λs κs) (κ:=κ1); auto.
  apply IHκs with (κ:=κ0) (λs:=λs); auto.
Qed.

Lemma lemma42 : forall λs (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ TAG ->
  [C ref] ∘ κs ∈ TAG ∪ BOT.
Proof.
intros.
destruct_WRITABLE H.
1-2: eapply lemma35; unfold_classes; eauto.
assert ([C ref] ∘ κs ∈ TAG)
  by (apply lemma41 with (λs:=λs) (κ:=ref); auto).
finish.
Qed.

Lemma lemma43 : forall (κ κ': cap),
  compatible (C κ) (C κ') ->
  compatible (unalias κ) (unalias κ').
Proof.
intros.
inversion H; unfold unalias; auto.
Qed.

Lemma lemma44 : forall (λ λ' λ'': ecap),
  compatible λ λ' ->
  subcap λ' λ'' ->
  compatible λ λ''.
Proof.
intros.
inversion H; subst; inversion H0; subst; auto.
Qed.

Lemma lemma45 : forall (λ1 λ2: ecap),
  compatible λ1 λ2 ->
  compatible λ2 λ1.
Proof.
intros.
inversion H; auto.
- destruct_ecap λ2; auto.
Qed.

Lemma lemma46 : forall (λ1 λ1' λ2 λ2': ecap),
  compatible λ1 λ2 ->
  subcap λ1 λ1' ->
  subcap λ2 λ2' ->
  compatible λ1' λ2'.
Proof.
intros.
apply lemma44 with λ2; [ apply lemma45 |].
apply lemma44 with λ1; [ apply lemma45 |].
all: auto.
Qed.

Lemma lemma47 : forall (κ κ': cap),
  compatible (unalias κ) (unalias κ') ->
  compatible (C κ) (C κ').
Proof.
intros.
destruct κ, κ'; inversion H; auto.
Qed.

Lemma lemma48 : forall (λs λs': capset) (κ κ': cap),
  λs ∈ G κ ->
  λs' ∈ G κ' ->
  compatible (C κ) (C κ') ->
  compatible_set λs λs'.
Proof.
intros.
intros λ λ' ? ?.
apply lemma46 with (unalias κ) (unalias κ') ;
[ apply lemma43 | apply H | apply H0 ]; auto.
Qed.

Lemma lemma49 : forall (λs λs': capset) (κ κ': cap),
  λs ∈ G κ ->
  λs' ∈ G κ' ->
  compatible_set λs λs' ->
  compatible (C κ) (C κ').
Proof.
intros.
apply lemma47.
apply H1; [ apply H | apply H0 ].
Qed.

Lemma lemma50 : forall (λs: capset),
  λs ∈ STABLE -> λs ∈ BOT \/ exists κ, λs ∈ G κ.
Proof.
intros.
destruct_STABLE H;
solve [ right; eexists _; apply H | auto ].
Qed.

Lemma lemma52 : forall (λs λs': capset),
  λs ∈ BOT -> compatible_set λs λs'.
Proof.
intros.
unfold compatible_set.
unfold_classes.
intros. subst. inversion H0.
Qed.

Lemma lemma54 : forall (λs: capset) (λ: ecap),
  λs ∈ TAG -> λ ∈ λs -> λ = C tag.
Proof.
intros.
assert (subcap (C tag) λ) by (apply H, H0).
inversion H1. auto.
Qed.

Lemma lemma55 : forall (λs λs': capset),
  λs ∈ TAG -> compatible_set λs λs'.
Proof.
intros.
unfold compatible_set.
intros.
replace λ with (C tag)
  by (symmetry; eapply lemma54; eauto).
apply compatible_tag.
Qed.

Lemma lemma56 : forall o λ λ' κ,
  adapt o λ κ = None ->
  subcap λ λ' ->
  adapt o λ' κ = None.
Proof.
intros.
inversion H0; subst; auto;
destruct o, κ; inversion H; auto.
Qed.

Lemma lemma57 : forall (λs: capset) (κ: cap),
  λs ∈ G κ ->
  unalias κ :: λs ∈ G κ.
Proof.
intros.
split; auto.
intros.
destruct H0; [subst | apply H]; auto.
Qed.

Lemma lemma58 : forall λs κ κ',
  (unalias κ :: λs) ∈ (G κ) ->
  adapt extract (unalias κ) κ' = None ->
  adapt read (unalias κ) κ' = None ->
  (unalias κ :: λs) ∘ κ' ∈ BOT.
Proof with eauto.
intros.
unfold blob, blob_combine_one.
induction λs as [|λ0]; auto.
- unfold combine_one; fold combine_one.
  rewrite H0, H1. finish.

- unfold combine_one; fold combine_one.
  replace (adapt read λ0 κ') with (None : option ecap)
    by (symmetry; apply lemma56 with (unalias κ); [| apply H]; auto).
  replace (adapt extract λ0 κ') with (None : option ecap)
    by (symmetry; apply lemma56 with (unalias κ); [| apply H]; auto).

  apply IHλs.
  split; auto.
  intros.
  apply H.
  destruct H2. subst. auto.
  auto.
Qed.

Lemma lemma59 : forall (λs: capset) (κ: cap) (λ: ecap) (λ1: ecap),
  λ1 ∈ λs ∘ κ ->
  λ1 ∈ (λ :: λs) ∘ κ.
Proof.
intros.
destruct lemma4 with λ1 λs κ as [o [λ0 [? ?]]]; auto.
apply lemma5 with o λ0; [apply lemma3|]; auto.
Qed.

Lemma lemma60 : forall (λs: capset) (κ: cap) (λ: ecap),
  (λ :: λs) ∘ κ ∈ BOT ->
  λs ∘ κ ∈ BOT.
Proof.
intros.
apply lemma21.
intros λ1 ?.
assert (λ1 ∈ (λ :: λs) ∘ κ)
  by (apply lemma59; auto).
unfold_classes.
rewrite H in H1.
destruct H1.
Qed.

Lemma lemma61 : forall (λs: capset) (κ κ': cap),
  λs ∈ (G κ) ->
  adapt extract (unalias κ) κ' = None ->
  adapt read (unalias κ) κ' = None ->
  λs ∘ κ' ∈ BOT.
Proof with eauto.
intros.
apply lemma60 with (unalias κ).
apply lemma58; auto.
apply lemma57; auto.
Qed.

Inductive group_adapt : cap -> cap -> cap -> Prop :=
| group_adapt_iso_iso : group_adapt iso iso iso
| group_adapt_iso_trn : group_adapt iso trn iso
| group_adapt_iso_ref : group_adapt iso ref iso
| group_adapt_iso_val : group_adapt iso val val
| group_adapt_iso_box : group_adapt iso box val
| group_adapt_iso_tag : group_adapt iso tag tag

| group_adapt_trn_iso : group_adapt trn iso iso
| group_adapt_trn_trn : group_adapt trn trn trn
| group_adapt_trn_ref : group_adapt trn ref trn
| group_adapt_trn_val : group_adapt trn val val
| group_adapt_trn_box : group_adapt trn box val
| group_adapt_trn_tag : group_adapt trn tag tag

| group_adapt_ref_iso : group_adapt ref iso iso
| group_adapt_ref_trn : group_adapt ref trn trn
| group_adapt_ref_ref : group_adapt ref ref ref
| group_adapt_ref_val : group_adapt ref val val
| group_adapt_ref_box : group_adapt ref box box
| group_adapt_ref_tag : group_adapt ref tag tag

| group_adapt_val_iso : group_adapt val iso val
| group_adapt_val_trn : group_adapt val trn val
| group_adapt_val_ref : group_adapt val ref val
| group_adapt_val_val : group_adapt val val val
| group_adapt_val_box : group_adapt val box val
| group_adapt_val_tag : group_adapt val tag tag

| group_adapt_box_iso : group_adapt box iso tag
| group_adapt_box_trn : group_adapt box trn box
| group_adapt_box_ref : group_adapt box ref box
| group_adapt_box_val : group_adapt box val val
| group_adapt_box_box : group_adapt box box box
| group_adapt_box_tag : group_adapt box tag tag
.
Hint Constructors group_adapt.

Lemma lemma62 : forall (λs: capset) (κ κ' κ'': cap),
  λs ∈ G κ ->
  λs ∘ κ' ∈ G κ'' <-> group_adapt κ κ' κ''.
Proof.
intros.
split.
- intro.
  destruct κ eqn:?, κ' eqn:?;
  (destruct (adapt extract (unalias κ) κ') as [λ|] eqn:Hextract;
  [| destruct (adapt read (unalias κ) κ') as [λ|] eqn:Hread];
  [
    replace κ'' with (alias λ)
      by (apply lemma9 with (λs ∘ κ'); [apply lemma15 with κ|]; subst; auto);
    (subst; inversion Hextract; auto)
  |
    replace κ'' with (alias λ)
      by (apply lemma9 with (λs ∘ κ'); [apply lemma17 with κ|]; subst; auto);
    (subst; inversion Hread; auto)
  |
    exfalso; subst;
      eapply lemma36; eauto;
      eapply lemma61; eauto
  ]).
  inversion Hextract.
  inversion Hextract.

- intro.
  assert (forall κ, G κ = G (alias (unalias κ))) as Hrewrite
    by (destruct 0; auto).
  rewrite Hrewrite.
  inversion H0; subst;
  solve [ eapply lemma15; eauto | eapply lemma17; eauto].
Qed.

Lemma lemma62a : forall (λs: capset) (κ κ' κ'': cap),
  λs ∈ G κ ->
  λs ∘ κ' ∈ G κ'' -> group_adapt κ κ' κ''.
Proof. eapply lemma62. Qed.

Ltac destruct_group_adapt κ κ' κ'' :=
  let H := fresh "H" in
  eassert (group_adapt κ κ' κ'') as H; [apply -> lemma62 | inversion H].

Lemma lemma63 : forall (κ: cap),
  [C ref] ∘ κ ∈ ISO -> κ = iso.
Proof.
intros. destruct_group_adapt ref κ iso; eauto. Qed.

Lemma lemma64 (κ: cap) : forall (λs λs': capset),
  λs ∈ STABLE ->
  λs' ∈ G κ ->
  compatible_set λs λs' ->
  match κ with
  | iso => λs ∈ TAG ∪ BOT
  | trn => λs ∈ BOX ∪ TAG ∪ BOT
  | ref => λs ∈ REF ∪ BOX ∪ TAG ∪ BOT
  | val => λs ∈ VAL ∪ BOX ∪ TAG ∪ BOT
  | box => λs ∈ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT
  | tag => λs ∈ ISO ∪ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT
  end.
Proof with finish.
intros.
destruct lemma50 with λs as [|[κ' ?]]; auto.
- destruct κ; finish.
- assert (compatible (C κ') (C κ)) as Hcompat
    by (eapply lemma49; eauto).
  destruct κ; inversion Hcompat...
Qed.

Lemma lemma66 : forall (λs: capset),
  λs ∈ WRITABLE -> λs ∈ STABLE.
Proof. finish. Qed.
Hint Resolve lemma66.

Lemma lemma67 : forall λs (κs: list cap),
  λs ∈ (ISO ∪ TRN ∪ VAL) ->
  λs ∘ κs ∈ BOT ->
  [C ref] ∘ κs ∈ BOT.
Proof with finish.
intros.
edestruct lemma34 as [|[|]]; eauto.
- exfalso; destruct H1 as [|[|]]; eapply lemma36; eauto.
- exfalso; eapply lemma36 with (λs:=λs ∘ κs); [eapply H1 | auto].
Qed.

Lemma lemma68 : forall λs (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ BOT ->
  [C ref] ∘ κs ∈ BOT.
Proof with finish.
intros.
destruct_writable λs by auto.
1-2: eapply lemma67 with λs...

edestruct lemma50 with ([C ref] ∘ κs) as [|[κ]];
[apply lemma27, lemma32|..]; auto.
exfalso.
apply lemma36 with (λs:=λs ∘ κs) (κ:=κ); auto.
apply lemma41 with (λs:=[C ref]) (κ:=ref); auto.
Qed.

Lemma lemma69 : forall λs (κs: list cap),
  λs ∈ (ISO ∪ TRN ∪ VAL) ->
  λs ∘ κs ∈ BOX ->
  [C ref] ∘ κs ∈ BOT.
Proof with finish.
intros.
edestruct lemma34 as [[|[|]]|[|]]; eauto;
eassert (_=box) as H2 by (eapply lemma9 with (λs:=λs ∘ κs); [apply H1 | apply H0]); inversion H2.
Qed.

Lemma lemma70 : forall λs (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ BOX ->
  [C ref] ∘ κs ∈ BOX ∪ BOT.
Proof with finish.
intros.
destruct_writable λs by auto.
1-2: right; eapply lemma69 with λs...
     left; apply lemma41 with ref λs; auto.
Qed.

Lemma lemma71 : forall λs (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ BOX ∪ TAG ∪ BOT ->
  [C ref] ∘ κs ∈ BOX ∪ TAG ∪ BOT.
Proof with finish.
intros.
destruct H0 as [|[|]].
- assert ([C ref] ∘ κs ∈ BOX ∪ BOT) by (eapply lemma70; eauto)...
- assert ([C ref] ∘ κs ∈ TAG ∪ BOT) by (eapply lemma42; eauto)...
- assert ([C ref] ∘ κs ∈ BOT) by (eapply lemma68; eauto)...
Qed.

Lemma lemma72 : forall λs (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ TAG ∪ BOT ->
  [C ref] ∘ κs ∈ TAG ∪ BOT.
Proof with finish.
intros.
destruct H0 as [|].
- assert ([C ref] ∘ κs ∈ TAG ∪ BOT) by (eapply lemma42; eauto)...
- assert ([C ref] ∘ κs ∈ BOT) by (eapply lemma68; eauto)...
Qed.

Lemma lemma73 : forall (λs1 λs2: capset),
  compatible_set λs1 λs2 ->
  compatible_set λs2 λs1.
Proof.
unfold compatible_set.
intros; apply lemma45; auto.
Qed.

Lemma lemma74 : forall (λs1 λs2: capset) (κ: cap),
  λs1 ∈ STABLE -> λs2 ∈ STABLE ->
  λs1 ∘ κ ∈ ISO ->
  λs2 ∘ κ ∈ TRN ∪ REF ->
  λs1 ∈ ISO /\ λs2 ∈ TRN ∪ REF.
Proof.
intros.
destruct' (exists κ1 : cap, λs1 ∈ G κ1) as [κ1]
  by (destruct lemma50 with λs1 as [|[]]; [| exfalso ; apply lemma36 with (λs1 ∘ κ) iso; [|apply lemma23]; eauto |]; eauto).

destruct H2 as [H2|H2];

 (destruct' (exists κ2 : cap, λs2 ∈ G κ2) as [κ2]
    by (destruct lemma50 with λs2 as [|[]]; [| exfalso ; eapply lemma36 with (λs2 ∘ κ) _; [|apply lemma23]; eauto |]; eauto));

  eassert (group_adapt κ1 κ iso) as Hadapt1 by (apply -> lemma62; eauto);
  eassert (group_adapt κ2 κ _) as Hadapt2 by (apply -> lemma62; eauto);

  inversion Hadapt1; subst;
  inversion Hadapt2; subst;

  finish.
Qed.

Lemma lemma75 : forall (λs1 λs2: capset) (κs: list cap),
  λs1 ∈ STABLE -> λs2 ∈ STABLE ->
  λs1 ∘ κs ∈ ISO ->
  λs2 ∘ κs ∈ TRN ∪ REF ->
  λs1 ∈ ISO /\ λs2 ∈ TRN ∪ REF.
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
- rewrite lemma19 in *.
  destruct lemma74 with (λs1 ∘ κs) (λs2 ∘ κs) κ; eauto.
Qed.

Lemma lemma76 : forall (λs: capset) (κ: cap),
  λs ∈ STABLE ->
  λs ∘ κ ∈ ISO ->
  λs ∈ ISO \/ κ = iso.
Proof.
intros.
assert (exists κ, λs ∈ G κ) as [κ0]
  by (apply lemma40; apply lemma37 with κ iso; eauto).
destruct_group_adapt κ0 κ iso; subst; eauto.
Qed.

Lemma lemma77 : forall (κ κ': cap),
  [unalias κ] ∈ G κ' -> κ = κ'.
Proof.
intros.
symmetry.
apply lemma8.
apply lemma1.
apply H.
Qed.

Lemma lemma78 : forall (λs: capset) (κ0 κ1 κ2: cap),
  λs ∈ G κ0 ->
  λs ∘ κ1 ∈ G κ2 ->
  adapt extract (unalias κ0) κ1 = Some (unalias κ2) \/
  adapt extract (unalias κ0) κ1 = None /\ adapt read (unalias κ0) κ1 = Some (unalias κ2).
Proof.
intros.
destruct_group_adapt κ0 κ1 κ2; eauto.
Qed.

Lemma lemma79: forall o λ0 λ0' κ λ1',
  subcap λ0 λ0' ->
  adapt o λ0' κ = Some λ1' ->
  exists λ1, adapt o λ0 κ = Some λ1 /\ subcap λ1 λ1'.
Proof.
intros.
inversion H.
1: subst. exists λ1'. auto.
all: destruct o, κ ; subst; inversion H0;
  (eexists _; unfold adapt; eauto).
Qed.

Lemma lemma81 : forall (κ: cap), alias (unalias κ) = κ.
Proof. destruct 0; auto. Qed.

Lemma lemma82 : forall (κ κ': cap) λ,
  adapt extract (unalias κ) κ' = Some λ ->
  exists κ'', λ = unalias κ''.
Proof.
intros.
destruct κ, κ'; inversion H;
exists (alias λ); subst; auto.
Qed.

Lemma lemma83 : forall (κ κ': cap) λ,
  adapt extract (unalias κ) κ' = None ->
  adapt read (unalias κ) κ' = Some λ ->
  exists κ'', λ = unalias κ''.
Proof.
intros.
destruct κ, κ'; inversion H0;
exists (alias λ); subst; auto.

all: inversion H.
Qed.

Lemma lemma84 : forall (λs λs': capset) (κ0 κ0' κ1' κ: cap),
  λs ∈ G κ0 ->
  λs' ∈ G κ0' ->
  λs' ∘ κ ∈ G κ1' ->
  subcap (unalias κ0) (unalias κ0') ->
  exists κ1, λs ∘ κ ∈ G κ1 /\ subcap (unalias κ1) (unalias κ1').
Proof.
intros.
destruct lemma78 with λs' κ0' κ κ1' as [|[]]; auto;
[| destruct (adapt extract (unalias κ0) κ) eqn:? ].

- edestruct lemma79 as [? []]; eauto.
  edestruct lemma82 with κ0 κ x; auto.
  exists (alias x).
  split.
  + eapply lemma15; [ apply H | auto..].
  + subst x. rewrite lemma81. auto.

- edestruct lemma79 as [? []]; eauto.
  edestruct lemma82 with κ0 κ e; auto.
  exists (alias e).
  split.
  + eapply lemma15; [ apply H | auto..].
  + subst e; try rewrite lemma81.
    eapply lemma7; [ eapply lemma13 |]; eauto.
- edestruct lemma79 as [? []]; eauto.
  destruct lemma83 with κ0 κ x; auto.
  exists (alias x).
  split.
  + eapply lemma17; [ apply H | auto..].
  + subst x. rewrite lemma81. auto.
Qed.

Lemma lemma85 : forall (λs λs': capset) (κ0 κ0' κ1': cap) (κs: list cap),
  λs ∈ G κ0 ->
  λs' ∈ G κ0' ->
  λs' ∘ κs ∈ G κ1' ->
  subcap (unalias κ0) (unalias κ0') ->
  exists κ1, λs ∘ κs ∈ G κ1 /\ subcap (unalias κ1) (unalias κ1').
Proof.
intros.
generalize dependent κ0.
generalize dependent κ0'.
generalize dependent κ1'.
induction κs as [|κ] using rev_ind; auto.
- intros.
  exists κ0.
  replace κ1' with κ0' by (eapply lemma9; eauto).
  auto.
- intros.
  rewrite lemma19 in *.

  destruct lemma40 with (λs' ∘ κs); [eapply lemma37|]; eauto.
  edestruct IHκs as [? []]; eauto.
  eapply lemma84 with (λs:=λs ∘ κs) (λs':=λs' ∘ κs); eauto.

Qed.

Lemma lemma86 : forall (λs: capset) (κs: list cap),
  λs ∈ WRITABLE ->
  [C ref] ∘ κs ∈ ISO ->
  λs ∘ κs ∈ ISO.
Proof.
intros.
(destruct_writable λs by auto); (
  edestruct lemma85 with (λs:=λs) (λs':=[C ref]) (κ0':=ref) (κs:=κs) as [κ1 [? Hsubcap]]; eauto;
  destruct κ1; inversion Hsubcap; auto
).
Qed.

Lemma lemma87 : forall (λs: capset) (κ: cap),
  λs ∈ STABLE ->
  λs ∘ κ ∈ REF ->
  λs ∈ REF /\ κ = ref.
Proof.
intros.
assert (exists κ, λs ∈ G κ) as [κ0]
  by (apply lemma40; eapply lemma37; eauto).
assert (group_adapt κ0 κ ref)
  by (eapply lemma62; eauto).
inversion H2.
subst; auto.
Qed.

Lemma lemma89 {A} : forall (xs: list A) (x y: A),
  In x (xs ++ [y]) -> In x xs \/ x =  y.
Proof. intros; edestruct in_app_or; eauto. Qed.
Hint Resolve lemma89.

Lemma lemma88 {A} : forall (xs: list A) (x y: A),
  In x xs -> In x (xs ++ [y]).
Proof. intros; apply in_or_app; auto. Qed.
Hint Resolve lemma88.

Lemma lemma90 {A} : forall (xs: list A) (x: A),
  In x (xs ++ [x]).
Proof. intros; apply in_or_app; auto. Qed.
Hint Resolve lemma90.

Lemma lemma91 : forall (λs: capset) (κs: list cap),
  λs ∈ STABLE ->
  λs ∘ κs ∈ REF ->
  λs ∈ REF /\ (forall κ, κ ∈ κs -> κ = ref).
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
rewrite lemma19 in *.
destruct lemma87 with (λs ∘ κs) κ; auto; subst.
split.
- apply IHκs; auto.
- intros.
  destruct (@lemma89 cap) with κs κ ref; auto.
  apply IHκs; auto.
Qed.

Lemma lemma92 : forall (λs: capset) (κs: list cap),
  λs ∈ REF ->
  (forall κ, κ ∈ κs -> κ = ref) -> 
  λs ∘ κs ∈ REF.
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
rewrite lemma19 in *.
eapply lemma62.
- apply IHκs; (intros; apply H0; apply lemma88; auto).
- replace κ with ref by (symmetry; apply H0; apply lemma90).
  auto.
Qed.

Lemma lemma94 : forall (λs: capset) (κs: list cap),
  λs ∈ STABLE ->
  λs ∘ κs ∈ REF ->
  λs ∈ REF /\ (forall κ, κ ∈ κs -> κ = ref).
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
rewrite lemma19 in *.
destruct lemma87 with (λs ∘ κs) κ; auto; subst.
split.
- apply IHκs; auto.
- intros.
  destruct (@lemma89 cap) with κs κ ref; auto.
  apply IHκs; auto.
Qed.

Lemma lemma99: forall λs κ κ',
  λs ∈ G κ ->
  match κ, κ' with
  | iso, iso => λs ∘ κ' ∈ ISO
  | iso, trn => λs ∘ κ' ∈ ISO
  | iso, ref => λs ∘ κ' ∈ ISO
  | iso, val => λs ∘ κ' ∈ VAL
  | iso, box => λs ∘ κ' ∈ VAL
  | iso, tag => λs ∘ κ' ∈ TAG

  | trn, iso => λs ∘ κ' ∈ ISO
  | trn, trn => λs ∘ κ' ∈ TRN
  | trn, ref => λs ∘ κ' ∈ TRN
  | trn, val => λs ∘ κ' ∈ VAL
  | trn, box => λs ∘ κ' ∈ VAL
  | trn, tag => λs ∘ κ' ∈ TAG

  | ref, iso => λs ∘ κ' ∈ ISO
  | ref, trn => λs ∘ κ' ∈ TRN
  | ref, ref => λs ∘ κ' ∈ REF
  | ref, val => λs ∘ κ' ∈ VAL
  | ref, box => λs ∘ κ' ∈ BOX
  | ref, tag => λs ∘ κ' ∈ TAG

  | val, iso => λs ∘ κ' ∈ VAL
  | val, trn => λs ∘ κ' ∈ VAL
  | val, ref => λs ∘ κ' ∈ VAL
  | val, val => λs ∘ κ' ∈ VAL
  | val, box => λs ∘ κ' ∈ VAL
  | val, tag => λs ∘ κ' ∈ TAG

  | box, iso => λs ∘ κ' ∈ TAG
  | box, trn => λs ∘ κ' ∈ BOX
  | box, ref => λs ∘ κ' ∈ BOX
  | box, val => λs ∘ κ' ∈ VAL
  | box, box => λs ∘ κ' ∈ BOX
  | box, tag => λs ∘ κ' ∈ TAG
  | tag, _ => λs ∘ κ' ∈ BOT
  end.
Proof.
intros.
destruct κ, κ';
solve [ eapply lemma62; eauto | apply lemma22; auto].
Qed.

Lemma lemma101 (A: Type): forall (P: A -> Prop) (x: A) (xs: list A),
  (forall y, In y (xs++[x]) -> P y) ->
  (forall y, In y xs -> P y).
Proof. auto. Qed.

Lemma lemma102 (A: Type): forall (P: A -> Prop) (x: A) (xs: list A),
  (forall y, In y (xs++[x]) -> P y) ->
  P x.
Proof. auto. Qed.

Lemma lemma104: forall λs, λs ∘ [] = λs.
Proof. finish. Qed.

Lemma lemma105: forall λs κ κ',
  λs ∈ G κ -> λs ∈ G κ' -> κ <> κ' -> False.
Proof. intros; apply H1; eapply lemma9; eauto. Qed.

Lemma lemma100: forall λs (κ: cap),
  λs ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  (κ = ref \/ κ = box \/ κ = tag) ->
  λs ∘ κ ∈ REF ∪ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct H as [|[|[|]]];
destruct H0 as [|[|]]; subst κ.

all: solve
  [ left; eapply lemma62; eauto
  | right; left; eapply lemma62; eauto
  | right; right; left; eapply lemma62; eauto
  | right; right; right; apply lemma22; auto
  | right; right; right; apply lemma23; auto].
Qed.

Lemma lemma103: forall λs (κs: list cap),
  λs ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  (forall κ, κ ∈ κs -> κ = ref) ->
  λs ∘ κs ∈ REF ∪ BOX ∪ TAG ∪ BOT.
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.

rewrite lemma19.
apply lemma100.
- apply IHκs; apply lemma101 with (x:=κ); auto.
- left; apply lemma102 with (x:=κ) (xs:=κs); auto.
Qed.

Lemma lemma107: forall λs (κ: cap),
  λs ∈ STABLE ->
  λs ∘ κ ∈ BOT ->
  λs ∈ BOT ∪ TAG.
Proof.
intros.
destruct lemma50 with λs as [|[κ' ?]]; auto.
- pose (lemma99 λs κ' κ) as H2.
  destruct κ eqn:?, κ' eqn:?;
  solve [ exfalso; eapply lemma36; [ apply H2; auto | auto ]
        | finish ].
Qed.

Lemma lemma109: forall λs,
  λs ∈ STABLE ->
  λs ∘ tag ∈ TAG ∪ BOT.
Proof.
intros.
(destruct_stable λs by auto);
solve [ eassert (λs ∘ tag ∈ G _) by (eapply lemma62; eauto); finish
      | assert (λs ∘ tag ∈ BOT) by (apply lemma22; auto); finish
      | assert (λs ∘ tag ∈ BOT) by (apply lemma23; auto); finish ].
Qed.

Lemma lemma114 : forall λs,
  λs ∈ STABLE ->
  compatible_set λs [C iso] ->
  λs ∈ TAG ∪ BOT.
Proof.
intros.
destruct lemma50 with λs as [|[κ' ?]]; auto.
destruct κ';
solve [ eassert (compatible _ (C _)) as Hcompat by (apply H0; [apply H1 | auto]);
          inversion Hcompat
      | finish ].
Qed.

Lemma lemma115 : forall λs,
  λs ∈ STABLE ->
  compatible_set λs [C trn] ->
  λs ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct lemma50 with λs as [|[κ' ?]]; auto.
destruct κ';
solve [ eassert (compatible _ (C _)) as Hcompat by (apply H0; [apply H1 | auto]);
          inversion Hcompat
      | finish ].
Qed.

Lemma lemma117: forall (λs: capset) (κ: cap),
  λs ∈ ISO ∪ TRN ∪ VAL ->
  (λs ∘ κ) ∈ TAG ->
  κ = tag.
Proof.
intros.
destruct H as [|[|]].
- destruct_group_adapt iso κ tag; eauto.
- destruct_group_adapt trn κ tag; eauto.
- destruct_group_adapt val κ tag; eauto.
Qed.

Lemma lemma119: forall (λs: capset) (κ: cap),
  λs ∈ ISO ∪ TRN ∪ VAL ->
  (λs ∘ κ) ∈ TAG ->
  ([C ref] ∘ κ) ∈ TAG.
Proof.
intros.
replace' κ with tag by (apply lemma117 with λs; auto).
eapply lemma62; eauto.
Qed.

Lemma lemma121: forall (λs: capset) (κ: cap),
  λs ∈ ISO ∪ TRN ∪ VAL ->
  (λs ∘ κ) ∈ ISO ∪ TRN ∪ VAL \/ κ = tag.
Proof.
intros.
destruct κ; auto;
left;
destruct H as [|[|]];
solve [ left; eapply lemma62; eauto
      | right; left; eapply lemma62; eauto
      | right; right; eapply lemma62; eauto ].
Qed.

Lemma lemma122: forall λs (κ: cap),
  λs ∈ TAG ∪ BOT ->
  λs ∘ κ ∈ BOT.
Proof.
intros.
destruct H.
- apply lemma22; auto.
- apply lemma23; auto.
Qed.

Lemma lemma123: forall (λs: capset) (κs: list cap),
  λs ∈ ISO ∪ TRN ∪ VAL ->
  (λs ∘ κs) ∈ ISO ∪ TRN ∪ VAL \/ ([C ref] ∘ κs) ∈ TAG ∪ BOT.
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
repeat rewrite lemma19 in *.
destruct IHκs.
- destruct lemma121 with (λs ∘ κs) κ; auto.
  right. subst. apply lemma109. auto.
- right. right. apply lemma122. auto.
Qed.

Lemma lemma124: forall (λs: capset) (κs: list cap),
  λs ∈ ISO ∪ TRN ∪ VAL ->
  (λs ∘ κs) ∈ TAG ∪ BOT ->
  ([C ref] ∘ κs) ∈ TAG ∪ BOT.
Proof.
intros.
destruct lemma123 with λs κs; auto.
exfalso.
destruct H0.
- destruct H1 as [|[|]];
  (eapply lemma105 with (λs:=λs ∘ κs); [ apply H0 | apply H1 | auto ]).
- destruct H1 as [|[|]];
  (eapply lemma36 with (λs:=λs ∘ κs); eauto).
Qed.

Lemma lemma125: forall (λs λs': capset) (κ: cap) (κs: list cap),
  λs ∈ G κ ->
  λs' ∈ G κ ->
  λs ∘ κs ∈ BOT ->
  λs' ∘ κs ∈ BOT.
Proof.
intros.
induction κs as [|κ'] using rev_ind; intros.
- exfalso; apply lemma36 with λs κ; auto.
- rewrite lemma19 in *.
  destruct lemma107 with (λs ∘ κs) κ'; eauto.
  + apply lemma23. apply IHκs. auto.
  + apply lemma22. apply lemma41 with (κ:=κ) (λs:=λs); auto.
Qed.

Lemma lemma130: forall (λs: capset) (κs: list cap),
  λs ∈ WRITABLE ->
  (λs ∘ κs) ∈ TAG ∪ BOT ->
  ([C ref] ∘ κs) ∈ TAG ∪ BOT.
Proof.
intros.
destruct_writable λs by auto.
- apply lemma124 with λs; finish.
- apply lemma124 with λs; finish.
- destruct H0.
  + left; apply lemma41 with ref λs; auto.
  + right; apply lemma125 with λs ref; auto.
Qed.

Lemma lemma133: forall (λs: capset) (κs: list cap),
  λs ∈ WRITABLE ->
  (λs ∘ κs) ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  ([C ref] ∘ κs) ∈ REF ∪ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct H0 as [|[|]].
1-2:
  (destruct_writable λs by auto);
  try solve [ destruct lemma123 with λs κs; [finish| |finish];
              exfalso; destruct H2 as [|[|]]; (eapply lemma105 with (λs:=λs ∘ κs); [apply H0|apply H2|auto])
            | (left + (right; left)); apply lemma41 with ref λs; auto ].

right; right; apply lemma130 with λs; auto.
Qed.

Lemma lemma134: forall (λs1 λs2: capset),
  λs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  λs2 ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  compatible_set λs1 λs2.
Proof.
intros λs1 λs2 [|[|[|]]] [|[|[|]]];

solve [ eapply lemma48; eauto
      | apply lemma52; auto
      | apply lemma73, lemma52; auto].
Qed.

Lemma lemma135 : forall (λs: capset) (λ: ecap),
  λs ∈ STABLE ->
  safe_to_write λ ref ->
  compatible_set λs ([C (alias λ)]) ->
  λs ∈ REF ∪ BOX ∪ TAG ∪ BOT.
Proof.
intros.
inversion H0; subst; unfold alias in H1.
- right; right; apply lemma114; auto.
- right; apply lemma115; auto.
- apply (lemma64 ref) with [C ref]; auto.
Qed.

Lemma lemma150 : forall (κ: cap) (κs: list cap),
  [unalias κ] ∘ κs ∈ VAL ->
  (κ = val \/ κ = box) \/ (val ∈ κs \/ box ∈ κs).
Proof.
intros.
induction κs as [|κ'] using rev_ind; auto.
- left. left. apply lemma77. auto.
- rewrite lemma19 in *.
  destruct_stable ([unalias κ] ∘ κs) by auto.
  + destruct_group_adapt iso κ' val;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt trn κ' val;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt ref κ' val;
    [ apply H | apply H0 | auto..].
  + destruct IHκs; auto.
    destruct H1; auto.
  + destruct_group_adapt box κ' val;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt tag κ' val;
    [ apply H | apply H0 | auto..].
  + exfalso.
    apply lemma36 with (([unalias κ] ∘ κs) ∘ κ') val; auto.
    apply lemma23; auto.
Qed.

Lemma lemma151 : forall (κ κ': cap),
  κ = val \/ κ = box ->
  subcap (C κ) (C κ') ->
  κ' = val \/ κ' = box \/ κ' = tag.
Proof.
intros.
inversion H; inversion H0; subst; auto.
Qed.

Lemma lemma152 : forall (λs: capset) (κ: cap),
  λs ∈ NONWRITABLE ->
  λs ∘ κ ∈ NONWRITABLE.
Proof.
intros.
destruct H as [|[|[|]]];
destruct κ;
solve [ left; eapply lemma62; eauto
      | right; left; eapply lemma62; eauto
      | right; right; left; eapply lemma62; eauto
      | right; right; right; eapply lemma22; eauto
      | right; right; right; eapply lemma23; eauto ].
Qed.

Lemma lemma153 : forall (λs: capset) (κs: list cap),
  λs ∈ NONWRITABLE ->
  λs ∘ κs ∈ NONWRITABLE.
Proof.
intros.
induction κs as [|κ0] using rev_ind; auto.
rewrite lemma19. apply lemma152. auto.
Qed.

Lemma lemma154 : forall (λs: capset) (κ: cap),
  λs ∈ STABLE ->
  κ = val \/ κ = box \/ κ = tag ->
  λs ∘ κ ∈ NONWRITABLE.
Proof.
intros.
(destruct_stable λs by auto);
destruct H0 as [|[|]]; subst;
solve [ left; eapply lemma62; eauto
      | right; left; eapply lemma62; eauto
      | right; right; left; eapply lemma62; eauto
      | right; right; right; eapply lemma22; eauto
      | right; right; right; eapply lemma23; eauto ].
Qed.

Lemma lemma155 : forall (λs: capset) (κ: cap) (κs: list cap),
  λs ∈ STABLE ->
  κ = val \/ κ = box \/ κ = tag ->
  λs ∘ κ ∘ κs ∈ NONWRITABLE.
Proof.
intros; apply lemma153; apply lemma154; auto.
Qed.

Lemma lemma156: forall (λs: capset) (κ: cap),
  λs ∈ STABLE ->
  λs ∘ κ ∈ BOT ->
  λs ∈ TAG ∪ BOT.
Proof.
intros.
destruct_stable λs by auto.
6-7: finish.

all:
exfalso;
destruct κ;
(eapply lemma36; [| apply H0]);
eapply lemma62; eauto.
Qed.

Lemma lemma160 : forall (λs: capset) (κ: cap),
  λs ∈ STABLE ->
  λs ∘ κ ∈ NONWRITABLE ->
  λs ∈ NONWRITABLE \/ (κ = val \/ κ = box \/ κ = tag).
Proof.
intros.
destruct_stable λs by auto.
4-7: finish.

- destruct H0 as [|[|[|]]].
  + destruct_group_adapt iso κ val; eauto.
  + destruct_group_adapt iso κ box; eauto.
  + destruct_group_adapt iso κ tag; eauto.
  + assert (λs ∈ TAG ∪ BOT) by (apply lemma156 with κ; auto); finish.

- destruct H0 as [|[|[|]]].
  + destruct_group_adapt trn κ val; eauto.
  + destruct_group_adapt trn κ box; eauto.
  + destruct_group_adapt trn κ tag; eauto.
  + assert (λs ∈ TAG ∪ BOT) by (apply lemma156 with κ; auto); finish.

- destruct H0 as [|[|[|]]].
  + destruct_group_adapt ref κ val; eauto.
  + destruct_group_adapt ref κ box; eauto.
  + destruct_group_adapt ref κ tag; eauto.
  + assert (λs ∈ TAG ∪ BOT) by (apply lemma156 with κ; auto); finish.
Qed.

Lemma lemma161 : forall (λs: capset),
  λs ∈ WRITABLE ->
  λs ∈ NONWRITABLE ->
  False.
Proof.
intros.
destruct H0 as [|[|[|]]];
destruct_writable λs; auto;
solve [ eapply lemma105; [apply H0 | apply H1 | auto]
      | eapply lemma36; eauto ].
Qed.

Lemma lemma162 : forall (λs: capset) (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ NONWRITABLE ->
  [C ref] ∘ κs ∈ NONWRITABLE.
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
- exfalso; apply lemma161 with λs; eauto.
- rewrite lemma19 in *.
  destruct lemma160 with (λs ∘ κs) κ; eauto.
  + apply lemma152; auto.
  + apply lemma154; auto.
Qed.

Lemma lemma163 : forall (λs1 λs2: capset),
  λs1 ∈ NONWRITABLE ->
  λs2 ∈ NONWRITABLE ->
  compatible_set λs1 λs2.
Proof.
intros λs1 λs2 [|[|[|]]] [|[|[|]]];

solve [ eapply lemma48; eauto
      | apply lemma52; auto
      | apply lemma73, lemma52; auto].
Qed.

Lemma lemma164 : forall λs (κs: list cap) (κ: cap),
  λs ∘ (κ::κs) = λs ∘ κ ∘ κs.
Proof. auto. Qed.

Lemma lemma165 : forall (λs: capset) (κs: list cap),
  λs ∈ STABLE ->
  val ∈ κs \/ box ∈ κs ->
  λs ∘ κs ∈ NONWRITABLE.
Proof.
intros.
generalize dependent λs.
induction κs; intros.
- destruct H0; destruct H0.
- rewrite lemma164.
  destruct H0;
  ( destruct H0; [ subst; apply lemma155; tauto | apply IHκs; auto ] ).
Qed.

Lemma lemma177 {A} : forall (x: A) (y: A),
  x <> y -> not (x ∈ [y]).
Proof. auto. Qed.
Hint Resolve lemma177.

Lemma lemma178 {A} : forall (x: A) (xs ys: list A),
  not (x ∈ xs) ->
  not (x ∈ ys) ->
  not (x ∈ xs ++ ys).
Proof.
intros.
intro; subst.
destruct in_app_or with A xs ys x; auto.
Qed.
Hint Resolve lemma178.

Lemma lemma179 {A} : forall (x y: A) (xs: list A),
  not (y ∈ xs) ->
  x <> y ->
  not (y ∈ xs ++ [x]).
Proof. eauto. Qed.
Hint Resolve lemma179.

Lemma lemma180 : forall (κ: cap) (κs: list cap),
  [unalias κ] ∘ κs ∈ BOX ->
  κ = box \/ box ∈ κs.
Proof.
intros.
induction κs as [|κ'] using rev_ind; auto.
- left. apply lemma77. auto.
- rewrite lemma19 in *.
  destruct_stable ([unalias κ] ∘ κs) by auto.
  + destruct_group_adapt iso κ' box;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt trn κ' box;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt ref κ' box;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt val κ' box;
    [ apply H | apply H0 | auto..].
  + destruct IHκs; auto.
  + destruct_group_adapt tag κ' box;
    [ apply H | apply H0 | auto..].
  + exfalso.
    apply lemma36 with (([unalias κ] ∘ κs) ∘ κ') box; auto.
    apply lemma23; auto.
Qed.

Lemma lemma181 : forall (κ: cap) (κs: list cap),
  [unalias κ] ∘ κs ∈ REF ∪ BOX ->
  κ <> val /\ not (val ∈ κs).
Proof.
intros.
induction κs as [|κ'] using rev_ind; auto.
- destruct H.
  + (replace' κ with ref by (apply lemma77; auto)); auto.
  + (replace' κ with box by (apply lemma77; auto)); auto.
- rewrite lemma19 in *.
  destruct H;
  destruct_stable ([unalias κ] ∘ κs) by auto.
  + destruct_group_adapt iso κ' ref;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt trn κ' ref;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt ref κ' ref;
    [ apply H | apply H0 | auto..].
    destruct IHκs; auto.
  + destruct_group_adapt val κ' ref;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt box κ' ref;
    [ apply H | apply H0 | auto..]; subst;
    destruct IHκs; auto.
  + destruct_group_adapt tag κ' ref;
    [ apply H | apply H0 | auto..].
  + exfalso.
    apply lemma36 with (([unalias κ] ∘ κs) ∘ κ') ref; auto.
    apply lemma23; auto.
  + destruct_group_adapt iso κ' box;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt trn κ' box;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt ref κ' box;
    [ apply H | apply H0 | auto..];
    destruct IHκs; auto.
  + destruct_group_adapt val κ' box;
    [ apply H | apply H0 | auto..].
  + destruct_group_adapt box κ' box;
    [ apply H | apply H0 | auto..]; subst;
    destruct IHκs; auto.
  + destruct_group_adapt tag κ' box;
    [ apply H | apply H0 | auto..].
  + exfalso.
    apply lemma36 with (([unalias κ] ∘ κs) ∘ κ') box; auto.
    apply lemma23; auto.
Qed.

Lemma lemma182 : forall (λs: capset) (κ: cap),
  λs ∈ BOX ∪ TAG ∪ BOT ->
  κ <> val ->
  λs ∘ κ ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct H as [|[|]];
destruct κ;
solve [ left; eapply lemma62; eauto
      | right; left; eapply lemma62; eauto
      | right; right; eapply lemma22; eauto
      | right; right; eapply lemma23; eauto
      | elim H0; auto ].
Qed.

Lemma lemma183 {A} : forall (x y: A) (xs: list A),
  not (y ∈ xs ++ [x]) ->
  x <> y.
Proof.
intros.
intro; subst.
apply H. auto.
Qed.
Hint Resolve lemma183.

Lemma lemma184 : forall (λs: capset) (κs: list cap),
  λs ∈ BOX ∪ TAG ∪ BOT ->
  not (val ∈ κs) ->
  λs ∘ κs ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
induction κs as [|κ0] using rev_ind; auto.
rewrite lemma19.
apply lemma182.
- apply IHκs. auto.
- eauto.
Qed.

Lemma lemma185 : forall (λs: capset) (κ: cap),
  λs ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  κ = box \/ κ = tag ->
  λs ∘ κ ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct H0; subst;
destruct H as [|].
- left; eapply lemma62; eauto.
- apply lemma182; eauto.
- right; left; eapply lemma62; eauto.
- apply lemma182; eauto.
Qed.

Lemma lemma186 : forall (λs1 λs2: capset),
  λs1 ∈ BOX ∪ TAG ∪ BOT ->
  λs2 ∈ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT ->
  compatible_set λs1 λs2.
Proof.
intros λs1 λs2 [|[|]] [|[|[|[|[|]]]]];

solve [ eapply lemma48; eauto
      | apply lemma52; auto
      | apply lemma73, lemma52; auto].
Qed.

Lemma lemma188 : forall (λs: capset) (λ: ecap),
  λs ∈ STABLE ->
  safe_to_write λ box ->
  compatible_set λs ([C (alias λ)]) ->
  λs ∈ REF ∪ BOX ∪ TAG ∪ BOT.
Proof.
intros.
inversion H0; subst; unfold alias in H1.
- right; right; apply lemma114; auto.
- right; apply lemma115; auto.
- apply (lemma64 ref) with [C ref]; auto.
Qed.

Lemma lemma189 : forall (λs: capset) (κ: cap),
  λs ∈ STABLE ->
  λs ∘ κ ∈ BOX ->
  (λs ∈ BOX /\ (κ = trn \/ κ = ref \/ κ = box)) \/
  (λs ∈ REF /\ (κ = box)).
Proof.
intros.
(destruct_stable λs by auto);
solve [ epose (lemma62a _ _ _ box H1 H0); inversion g
      | epose (lemma62a _ _ _ box H1 H0); inversion g; subst; auto
      | exfalso; apply lemma36 with (λs ∘ κ) box; [| apply lemma23]; auto ].
Qed.

Lemma lemma187 {A} : forall (P: A -> Prop),
  forall x, x ∈ [] -> P x.
Proof. intros; inversion H. Qed.

Lemma lemma191 {A} : forall (P: A -> Prop) (xs ys: list A),
  (forall x, x ∈ xs -> P x) ->
  (forall x, x ∈ ys -> P x) ->
  (forall x, x ∈ xs ++ ys -> P x).
Proof.
intros.
destruct in_app_or with A xs ys x; auto.
Qed.

Lemma lemma192 {A} : forall (P: A -> Prop) (x: A),
  P x -> (forall y, y ∈ [x] -> P y).
Proof. intros; replace y with x; auto. Qed.

Lemma lemma200 : forall (λs: capset) (κs: list cap),
  λs ∈ STABLE ->
  λs ∘ κs ∈ BOX ->
  (λs ∈ BOX /\ forall κ, κ ∈ κs -> κ = trn \/ κ = ref \/ κ = box) \/
  exists κs' κs'', (κs = κs' ++ [box] ++ κs'' /\ λs ∘ κs' ∈ REF /\ forall κ, κ ∈ κs'' -> κ = trn \/ κ = ref \/ κ = box).
Proof.
intros.
induction κs as [|κ] using rev_ind.
- left. split. auto. apply lemma187.
- rewrite lemma19 in *.
  destruct lemma189 with (λs ∘ κs) κ as [[? ?]|[? ?]]; auto.
  + destruct IHκs as [[? ?]|[κs' [κs'' [? [? ?]]]]]; auto.
    * left; split; [| apply lemma191; [| apply lemma192]]; auto.
    * right.
      eexists κs'; eexists (κs''++[κ]).
      split; [|split].
      -- subst κs; repeat rewrite <- app_assoc; auto.
      -- auto.
      -- apply lemma191; [| apply lemma192]; auto.
  + right.
    eexists κs; eexists [].
    split; [subst κ|split]; auto.
Qed.

Lemma lemma201 : forall (λs: capset) (κ: cap),
  λs ∈ BOX ∪ TAG ∪ BOT ->
  κ = trn \/ κ = ref \/ κ = box ->
  λs ∘ κ ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct H0 as [|[|]]; subst;
destruct H as [|[|]];
try solve [ left; eapply lemma62; eauto
      | right; left; eapply lemma62; eauto
      | right; right; eapply lemma22; eauto
      | right; right; eapply lemma23; eauto ].
Qed.

Lemma lemma202 : forall (λs: capset) (κs: list cap),
  λs ∈ BOX ∪ TAG ∪ BOT ->
  (forall κ, κ ∈ κs -> κ = trn \/ κ = ref \/ κ = box) ->
  λs ∘ κs ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
induction κs as [|κ] using rev_ind; auto.
rewrite lemma19.
apply lemma201; auto.
Qed.

Lemma lemma203 : forall λs κs κs',
  λs ∘ (κs++κs') = λs ∘ κs ∘ κs'.
Proof.
intros. unfold_classes. unfold combine. rewrite fold_left_app. auto.
Qed.

Lemma lemma204 : forall (λs: capset) (κs κs': list cap),
  λs ∘ κs ∈ REF ∪ BOX ∪ TAG ∪ BOT ->
  (forall κ, κ ∈ κs' -> κ = trn \/ κ = ref \/ κ = box) ->
  λs ∘ (κs ++ [box] ++ κs') ∈ BOX ∪ TAG ∪ BOT.
Proof.
intros.
rewrite lemma203; unfold app; rewrite lemma164.
apply lemma202; auto.
apply lemma185; auto.
Qed.

Lemma lemma205 : [C ref] ∈ WRITABLE.
Proof.
unfold WRITABLE.
right; right. auto.
Qed.
Hint Resolve lemma205.

Lemma lemma206 : forall (λs: capset) (κs: list cap),
  λs ∈ WRITABLE ->
  λs ∘ κs ∈ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT ->
  [C ref] ∘ κs ∈ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT.
Proof.
intros.
destruct_stable ([C ref] ∘ κs); auto.
destruct H0 as [|[|[|[|[|]]]]];
exfalso;
solve [ eapply lemma105; [ apply H0 | apply lemma86 | .. ]; auto
      | eapply lemma36; [ apply lemma86 | apply H0 | .. ]; auto ].
all: finish.
Qed.


Lemma lemmaB1 : forall (λs: capset) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  [unalias κ] ∘ κs3 ∈ ISO ->
  compatible_set ([C ref] ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof.
intros.

assert (λs ∘ κs4 ∈ TAG ∪ BOT)
  by (eapply (lemma64 iso) with ([unalias κ] ∘ κs3); eauto).

destruct' ([C ref] ∘ κs4 ∈ TAG ∪ BOT) as [|]
  by (apply lemma72 with λs; auto).

- apply lemma55; auto.
- apply lemma52; auto.
Qed.

Lemma lemmaB2 : forall (λs: capset) (λ: ecap) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  subcap (unalias κ) (C κ2) ->
  safe_to_write λ κ ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  compatible_set (λs ∘ κs1) ([C (alias λ)]) ->
  [unalias κ] ∘ κs3 ∈ TRN ->
  compatible_set ([C ref] ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof.
intros.

(* -κ ∘ κs3 ∈ TRN *)

assert (λs ∘ κs4 ∈ BOX ∪ TAG ∪ BOT)
  by (eapply (lemma64 trn); [ apply lemma27 | ..]; eauto).

assert ([C ref] ∘ κs4 ∈ BOX ∪ TAG ∪ BOT) as [|[|]]
  by (apply lemma71 with λs; auto).

(* TAG and BOT are compatible with anything else. *)
2-3: solve [ apply lemma55; auto | apply lemma52; auto ].

(* ref ∘ κs4 ∈ BOX *)

(* All cases except ISO are compatible with BOX.  *)
destruct_stable ([C ref] ∘ κs1 ∘ κ2 ∘ κs3) by eauto.
2-7: solve [ eapply lemma48; eauto | apply lemma73, lemma52; auto ].

(* ref ∘ κs1 ∘ κ2 ∘ κs3 ∈ ISO *)

assert ([C ref] ∘ κs1 ∘ κ2 ∈ ISO /\ [unalias κ] ∈ TRN ∪ REF) as []
  by (apply lemma75 with κs3; eauto; finish).

assert ([C ref] ∘ κs1 ∈ ISO \/ κ2 = iso) as [|]
  by (apply lemma76; eauto).

(* κ2 = iso is impossible as -κ < κ2 and -κ = trn or -κ = ref *)
2: solve [
  destruct H9;
  [ assert (κ=trn) by (apply lemma77; auto)
  | assert (κ=ref) by (apply lemma77; auto)];
  subst; inversion H0
].

(* ref ∘ κs1 ∈ ISO *)
assert (λs ∘ κs1 ∈ ISO) by (apply lemma86; auto).

assert (compatible (unalias iso) (C (alias λ)))
  by (apply H3; [apply H11|auto]).
destruct λ as [[]| |] eqn:?; inversion H12.
2: solve [ inversion H1 ].

(* λ = C iso *)

(* κ = iso \/ κ = val \/ κ = tag *)
inversion H1;
(destruct H9;
  [ assert (κ=trn) by (apply lemma77; auto)
  | assert (κ=ref) by (apply lemma77; auto)]);
subst; inversion H13.
Qed.

Lemma lemmaB3 : forall (λs: capset) (λ: ecap) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  subcap (unalias κ) (C κ2) ->
  safe_to_write λ κ ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  compatible_set (λs ∘ κs1) ([C (alias λ)]) ->
  [unalias κ] ∘ κs3 ∈ REF ->
  compatible_set ([C ref] ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof.
intros.

assert (λs ∘ κs4 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
  by (apply (lemma64 ref) with ([unalias κ] ∘ κs3); auto).
assert ([C ref] ∘ κs4 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
  by (apply lemma133 with λs; auto).

assert ([unalias κ] ∈ REF /\ forall κ, κ ∈ κs3 -> κ = ref) as []
  by (apply lemma91; auto).

replace' κ with ref by (apply lemma77; auto).

assert (κ2 = ref \/ κ2 = box \/ κ2 = tag)
  by (inversion H0; auto).

assert (λs ∘ κs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
  by (apply lemma135 with (λ:=λ); auto).
assert ([C ref] ∘ κs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
  by (apply lemma133 with λs; auto).
assert ([C ref] ∘ κs1 ∘ κ2 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
  by (apply lemma100; auto).
assert ([C ref] ∘ κs1 ∘ κ2 ∘ κs3 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
  by (apply lemma103; auto).

apply lemma134; auto.

Qed.

Lemma lemmaB4 : forall (λs: capset) (λ: ecap) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  subcap (unalias κ) (C κ2) ->
  safe_to_write λ κ ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  compatible_set (λs ∘ κs1) ([C (alias λ)]) ->
  [unalias κ] ∘ κs3 ∈ VAL ->
  compatible_set ([C ref] ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof.
intros.

assert (λs ∘ κs4 ∈ NONWRITABLE)
  by (apply (lemma64 val) with ([unalias κ] ∘ κs3); auto).
assert ([C ref] ∘ κs4 ∈ NONWRITABLE)
  by (apply lemma162 with λs; auto).

destruct lemma150 with κ κs3 as [|]; auto.

- (* κ = val \/ κ = box *)
  assert (κ2 = val \/ κ2 = box \/ κ2 = tag)
    by (apply lemma151 with κ; [| destruct H7; subst]; auto).
  assert ([C ref] ∘ κs1 ∘ κ2 ∘ κs3 ∈ NONWRITABLE)
    by (apply lemma155; auto).
  apply lemma163; auto.

- (* val ∈ κs3 \/ box ∈ κs3 *)
  assert ([C ref] ∘ κs1 ∘ κ2 ∘ κs3 ∈ NONWRITABLE)
    by (apply lemma165; auto; auto).
  apply lemma163; auto.
Qed.

Lemma lemmaB5 : forall (λs: capset) (λ: ecap) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  subcap (unalias κ) (C κ2) ->
  safe_to_write λ κ ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  compatible_set (λs ∘ κs1) ([C (alias λ)]) ->
  [unalias κ] ∘ κs3 ∈ BOX ->
  compatible_set ([C ref] ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof.
intros.

assert (λs ∘ κs4 ∈ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT)
  by (apply (lemma64 box) with ([unalias κ] ∘ κs3); auto).

assert ([C ref] ∘ κs4 ∈ TRN ∪ REF ∪ VAL ∪ BOX ∪ TAG ∪ BOT) by
  (apply lemma206 with λs; auto).

destruct lemma200 with [unalias κ] κs3 as [[? ?]|[κs3' [κs3'' [? [? ?]]]]]; auto.
- replace' κ with box by (apply lemma77; auto).

  assert (κ2 = box \/ κ2 = tag)
    by (inversion H0; auto).

  assert (λs ∘ κs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
   by (eapply lemma188 with (λ:=λ); auto).

  assert ([C ref] ∘ κs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
    by (apply lemma133 with λs; auto).

  assert ([C ref] ∘ κs1 ∘ κ2 ∈ BOX ∪ TAG ∪ BOT)
    by (apply lemma185; auto).

  assert ([C ref] ∘ κs1 ∘ κ2 ∘ κs3 ∈ BOX ∪ TAG ∪ BOT)
    by (apply lemma202; auto).

  apply lemma73, lemma186; auto.

- assert ([unalias κ] ∈ REF /\ forall κ, κ ∈ κs3' -> κ = ref) as []
    by (apply lemma91; auto).
  replace' κ with ref by (apply lemma77; auto).

  assert (κ2 = ref \/ κ2 = box \/ κ2 = tag)
    by (inversion H0; tauto).

  assert (λs ∘ κs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
    by (apply lemma135 with λ; auto).

  assert ([C ref] ∘ κs1 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
    by (apply lemma133 with λs; auto).

  assert ([C ref] ∘ κs1 ∘ κ2 ∈ REF ∪ BOX ∪ TAG ∪ BOT)
    by (apply lemma100; auto).

  assert ([C ref] ∘ κs1 ∘ κ2 ∘ κs3' ∈ REF ∪ BOX ∪ TAG ∪ BOT)
    by (apply lemma103; auto).

  assert ([C ref] ∘ κs1 ∘ κ2 ∘ κs3 ∈ BOX ∪ TAG ∪ BOT)
    by (subst κs3; apply lemma204; auto).

  apply lemma73, lemma186; auto.
Qed.

Lemma lemmaB : forall (λs: capset) (λ: ecap) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  subcap (unalias κ) (C κ2) ->
  safe_to_write λ κ ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  compatible_set (λs ∘ κs1) ([C (alias λ)]) ->
  compatible_set ([C ref] ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof with finish.
intros.
destruct_stable ([unalias κ] ∘ κs3) by auto.
- (* [unalias κ] ∘ κs3 ∈ ISO *) apply lemmaB1 with λs κ...
- (* [unalias κ] ∘ κs3 ∈ TRN *) apply lemmaB2 with λs λ κ...
- (* [unalias κ] ∘ κs3 ∈ REF *) apply lemmaB3 with λs λ κ...
- (* [unalias κ] ∘ κs3 ∈ VAL *) apply lemmaB4 with λs λ κ...
- (* [unalias κ] ∘ κs3 ∈ BOX *) apply lemmaB5 with λs λ κ...
- (* [unalias κ] ∘ κs3 ∈ TAG *) admit.
- (* [unalias κ] ∘ κs3 ∈ BOT *) admit.
Admitted.
