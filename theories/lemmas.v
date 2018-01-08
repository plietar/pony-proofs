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
  READABLE, WRITABLE, STABLE, ISO, TRN, REF, VAL, BOX, TAG in *.
Ltac finish := solve [subst; unfold_classes; tauto].

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
destruct λ as [[]| |], λ' as [[]| |];
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
- destruct λ as [[]| |], κ; inversion Heqo; inversion H.
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
destruct λ as [[]| |], κ, κ'; simpl in *;
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

Lemma lemma27: forall λs (κs: list cap),
  λs ∈ STABLE -> (λs ∘ κs) ∈ STABLE.
Proof.
induction κs using rev_ind.
- unfold blob, blob_combine, combine, fold_left; auto.
- intros. erewrite lemma19. apply lemma26. auto.
Qed.

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

Lemma lemma31 : forall κ, [unalias κ] ∈ STABLE.
Proof.
intros.
assert ([unalias κ] ∈ G κ) by apply lemma30.
destruct κ; finish.
Qed.

Lemma lemma32 : [C ref] ∈ STABLE.
Proof.
replace (C ref) with (unalias ref) by auto. apply lemma31.
Qed.

Lemma lemma33 : [C ref] ∈ G ref.
Proof.
replace (C ref) with (unalias ref) by auto. apply lemma30.
Qed.

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
  by (apply lemma41 with (λs:=λs) (κ:=ref); [|apply lemma33|]; auto).
finish.
Qed.

Hint Constructors compatible.

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
- destruct λ2 as [[]| |]; auto.
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

Lemma lemmaB1 : forall (λs: capset)(κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ STABLE ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  [unalias κ] ∘ κs3 ∈ ISO ->
  compatible_set (λs ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof.
intros.
destruct lemma50 with (λs ∘ κs4) as [|[κ1 ?]]; [ apply lemma27; auto | ..].
- apply lemma52; auto.
- replace κ1 with tag in *.
  apply lemma55; auto.

  assert (compatible (C κ1) (C iso)) as Hcompat_κ1_iso by (eapply lemma49; eauto).
  inversion Hcompat_κ1_iso; subst; auto.
Qed.

Lemma lemmaB : forall (λs: capset) (λ: ecap) (κs1 κs3 κs4: list cap) (κ κ2: cap),
  λs ∈ WRITABLE ->
  (* λ writable -> *)
  subcap (unalias κ) (C κ2) ->
  safe_to_write λ κ ->
  compatible_set (λs ∘ κs4) ([unalias κ] ∘ κs3) ->
  compatible_set (λs ∘ κs4) ([C ref] ∘ κs1 ∘ κ2 ∘ κs3).
Proof with finish.
intros.
assert ([unalias κ] ∘ κs3 ∈ STABLE) as Hstable_κs3
  by (apply lemma27, lemma31).
destruct_STABLE Hstable_κs3.

- (* [unalias κ] ∘ κs3 ∈ ISO *) eapply lemmaB1 with κ...
- (* [unalias κ] ∘ κs3 ∈ TRN *) admit.
- (* [unalias κ] ∘ κs3 ∈ REF *) admit.
- (* [unalias κ] ∘ κs3 ∈ VAL *) admit.
- (* [unalias κ] ∘ κs3 ∈ BOX *) admit.
- (* [unalias κ] ∘ κs3 ∈ TAG *) admit.
- (* [unalias κ] ∘ κs3 ∈ BOT *) admit.

Admitted.
