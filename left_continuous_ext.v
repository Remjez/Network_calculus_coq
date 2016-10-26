Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Bool.
Require Import network_calculus_def.

Local Open Scope R_scope.

Definition seq_growing (seq : nat -> Rbar):=
  forall n : nat, Rbar_le (seq n) (seq (S n)).

Lemma seq_growing_prop u n m :
  seq_growing u -> (n <= m)%nat -> Rbar_le (u n) (u m).
Proof.
intros Hu; induction m.
{ case n; [now intro Hn; apply Rbar_le_refl|].
  intros n' Hn'; elim (Nat.nle_succ_0 _ Hn'). }
intro Hn; case (le_le_S_dec n m); intro Hm.
{ apply (Rbar_le_trans _ _ _ (IHm Hm)), Hu. }
rewrite (Nat.le_antisymm _ _ Hn Hm); apply Rbar_le_refl.
Qed.

Definition Rbar_is_lim_seq (u : nat -> Rbar) (l : Rbar) :=
  filterlim u eventually (Rbar_locally_Rbar l).

Lemma Rbar_lub_spec (E : Rbar -> Prop) : Rbar_is_lub E (Rbar_lub E).
Proof.
now destruct (Rbar_ex_lub E) as [l Hl]; rewrite (Rbar_is_lub_unique _ _ Hl).
Qed.

Lemma seq_growing_cv (s : nat -> Rbar) : seq_growing s ->
  Rbar_is_lim_seq s (Rbar_lub (fun y => exists n, y = s n)).
Proof.
intro Gs; set (E := fun _ => _); set (l := Rbar_lub E).
assert (Rbar_lt_or_not : forall x y, Rbar_lt x y \/ ~ Rbar_lt x y).
{ now intros x y; case (Rbar_lt_dec x y); [left|right]. }
case_eq l; [intro rl| |]; intro Hl.
{ intros P [eps Heps].
  elim (LPO _ (fun n => Rbar_lt_or_not (rl - eps) (s n))).
  { intros [n Hn1]; exists n; intros n' Hn'.
    assert (Hn2 : Rbar_le (s n) rl).
    { now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n. }
    assert (Fsn : is_finite (s n)); [now revert Hn1 Hn2; case (s n)|].
    assert (Hsn'1 := seq_growing_prop _ _ _ Gs Hn').
    assert (Hsn'2 : Rbar_le (s n') rl).
    { now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n'. }
    assert (Fsn' : is_finite (s n')).
    { now revert Hsn'1 Hsn'2; rewrite <-Fsn; case (s n'). }
    rewrite <-Fsn'; apply Heps, (proj2 (Rabs_lt_between' _ _ _)); split.
    { cut(Rbar_lt (rl - eps) (s n')); [now rewrite <-Fsn'|].
      now apply (Rbar_lt_le_trans _ _ _ Hn1). }
    apply (Rle_lt_trans _ rl); [now revert Hsn'2; rewrite <-Fsn'|].
    assert (H := cond_pos eps); revert H; lra. }
  intro Hn.
  assert (Hl' : Rbar_le l (rl - eps)).
  { apply (proj2 (Rbar_lub_spec _)); intros x [n' Hn']; rewrite Hn'.
    apply Rbar_not_lt_le, Hn. }
  elim (Rbar_le_not_lt _ _ Hl'); rewrite Hl; simpl.
  assert (H := cond_pos eps); revert H; lra. }
{ intros P [M HM].
  elim (LPO _ (fun n => Rbar_lt_or_not M (s n))).
  { intros [n Hn1]; exists n; intros n' Hn'.
    now apply HM, (Rbar_lt_le_trans _ _ _ Hn1), seq_growing_prop. }
  intro Hn.
  assert (Hl' : Rbar_le l M).
  { apply (proj2 (Rbar_lub_spec _)); intros x [n' Hn']; rewrite Hn'.
    apply Rbar_not_lt_le, Hn. }
  now revert Hl'; rewrite Hl. }
intros P [M HM]; exists O; intros n' _; apply HM.
apply (Rbar_le_lt_trans _ m_infty); [|now simpl].
now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n'.
Qed.

Definition seq_at_left (x : Rbar) (n : nat) :=
  match x with
  | Finite a => a - (1 / 2)^n
  | p_infty => INR n
  | m_infty => m_infty
  end.

Lemma seq_at_left_growing x : seq_growing (seq_at_left x).
Proof.
intro n; case x; [intro rx; simpl|now rewrite S_INR; simpl; lra|now right].
assert (H' : 0 < (1 / 2)^n); [apply pow_lt|]; lra.
Qed.

Lemma ex_seq_at_left_gt (y x : Rbar) :
  Rbar_lt y x -> exists n, Rbar_lt y (seq_at_left x n).
Proof.
case x; [intro rx| |now case y];
  (case y; [|now simpl|now exists O]); simpl; intros ry Hy.
{ assert (Hhalf : Rabs (1 / 2) < 1); [now rewrite Rabs_pos_eq; lra|].
  apply Rminus_lt_0 in Hy.
  destruct (pow_lt_1_zero _ Hhalf _ Hy) as [N HN].
  specialize (HN _ (le_refl _)).
  exists N.
  apply (Rplus_lt_reg_r ((1 / 2)^N - ry)).
  ring_simplify; rewrite (Rplus_comm _ rx); fold (Rminus rx ry).
  now rewrite <-(Rabs_pos_eq _); [|apply pow_le; lra]. }
pose (z := up (Rmax 0 ry)); assert (Hz : 0 < IZR z).
{ apply (Rle_lt_trans _ _ _ (Rmax_l 0 ry)), Rgt_lt, (proj1 (archimed _)). }
revert Hz; case_eq z; [now simpl; lra| |]; intros p Hp.
{ exists (Pos.to_nat p); change (INR _) with (IZR (Z.pos p)); rewrite <-Hp.
  apply (Rle_lt_trans _ _ _ (Rmax_r 0 ry)), Rgt_lt, (proj1 (archimed _)). }
simpl; assert (H := INR_pos p); lra.
Qed.

Lemma ex_lim_left_ndf (f : ndf_Rbar_Rbar) (x : Rbar) :
  is_lim_left f x (Rbar_lub (fun y => exists n, y = f (seq_at_left x n))).
Proof.
set (s := fun n => f (seq_at_left x n)); set (l := Rbar_lub _).
assert (Gs : seq_growing s); [now intro n; apply (ndf_Rbar_Rbar_prop f), seq_at_left_growing|].
assert (Hs := seq_growing_cv _ Gs).
intros P; case_eq l; [intro r| |]; intro Hl.
{ simpl; intros [eps Heps].
  pose (b := fun x : Rbar => Rbar_lt (r - eps) x /\ Rbar_lt x (r + eps)).
  assert (Hb : Rbar_locally_Rbar l b).
  { rewrite Hl; exists eps; intro y; apply Rabs_lt_between'. }
  elim (Hs _ Hb); intros n Hn; specialize (Hn _ (le_refl _)).
  assert (Ffxn : is_finite (s n)).
  { now revert Hn; unfold b; case (s n). }
  case_eq x; [intro rx| |]; intro Hx.
  { assert (Heps' : 0 < x - seq_at_left x n).
    { unfold seq_at_left; rewrite Hx; simpl; ring_simplify; apply pow_lt; lra. }
    exists (mkposreal _ Heps'); intros x' Hx'1 Hx'2.
    apply (proj1 (Rabs_lt_between' _ _ _)), proj1 in Hx'1.
    simpl in Hx'1; rewrite Hx in Hx'1; simpl in Hx'1; ring_simplify in Hx'1.
    change (_ < _) with (Rbar_lt (seq_at_left rx n) x') in Hx'1.
    rewrite <-Hx in Hx'1, Hx'2.
    assert (Hfx'1 := ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hx'1)); fold (s n) in Hfx'1.
    destruct (ex_seq_at_left_gt _ _ Hx'2) as [n' Hn'].
    assert (Hfx'2 : Rbar_le (f x') r).
    { apply (Rbar_le_trans _ _ _ (ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hn'))).
      now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n'. }
    assert (Ffx' : is_finite (f x')).
    { now revert Hfx'1 Hfx'2; rewrite <-Ffxn; case (f x'). }
    rewrite <-Ffx'; apply Heps, (proj2 (Rabs_lt_between' _ _ _)); split.
    { revert Hfx'1; rewrite <-Ffxn, <-Ffx'; apply Rlt_le_trans.
      now revert Hn; unfold b; rewrite <-Ffxn. }
    rewrite <-Ffx' in Hfx'2; apply (Rle_lt_trans _ _ _ Hfx'2).
    assert (H := cond_pos eps); lra. }
  { exists (seq_at_left x n); intros x' Hx'1 Hx'2.
    assert (Hfx'1 := ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hx'1)); fold (s n) in Hfx'1.
    destruct (ex_seq_at_left_gt _ _ Hx'2) as [n' Hn']; rewrite <-Hx in Hn'.
    assert (Hfx'2 : Rbar_le (f x') r).
    { apply (Rbar_le_trans _ _ _ (ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hn'))).
      now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n'. }
    assert (Ffx' : is_finite (f x')).
    { now revert Hfx'1 Hfx'2; rewrite <-Ffxn; case (f x'). }
    rewrite <-Ffx'; apply Heps, (proj2 (Rabs_lt_between' _ _ _)); split.
    { revert Hfx'1; rewrite <-Ffxn, <-Ffx'; apply Rlt_le_trans.
      now revert Hn; unfold b; rewrite <-Ffxn. }
    rewrite <-Ffx' in Hfx'2; apply (Rle_lt_trans _ _ _ Hfx'2).
    assert (H := cond_pos eps); lra. }
  now exists 0; intro x'; case x'. }
{ intros [M HM].
  pose (b := fun x : Rbar => Rbar_lt M x).
  assert (Hb : Rbar_locally_Rbar l b); [now rewrite Hl; exists M|].
  elim (Hs _ Hb); intros n Hn; specialize (Hn _ (le_refl _)).
  case_eq x; [intro rx| |]; intro Hx.
  { assert (Heps' : 0 < x - seq_at_left x n).
    { unfold seq_at_left; rewrite Hx; simpl; ring_simplify; apply pow_lt; lra. }
    exists (mkposreal _ Heps'); intros x' Hx'1 Hx'2.
    apply (proj1 (Rabs_lt_between' _ _ _)), proj1 in Hx'1.
    simpl in Hx'1; rewrite Hx in Hx'1; simpl in Hx'1; ring_simplify in Hx'1.
    change (_ < _) with (Rbar_lt (seq_at_left rx n) x') in Hx'1.
    rewrite <-Hx in Hx'1, Hx'2.
    assert (Hfx'1 := ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hx'1)).
    destruct (ex_seq_at_left_gt _ _ Hx'2) as [n' Hn'].
    now apply HM, (Rbar_lt_le_trans _ _ _ Hn). }
  { exists (seq_at_left x n); intros x' Hx'1 Hx'2.
    assert (Hfx'1 := ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hx'1)).
    destruct (ex_seq_at_left_gt _ _ Hx'2) as [n' Hn']; rewrite <-Hx in Hn'.
    now apply HM, (Rbar_lt_le_trans _ _ _ Hn). }
  now exists 0; intro x'; case x'. }
intros [M HM].
pose (b := fun x : Rbar => Rbar_lt x M).
assert (Hb : Rbar_locally_Rbar l b); [now rewrite Hl; exists M|].
elim (Hs _ Hb); intros n Hn; specialize (Hn _ (le_refl _)).
case_eq x; [intro rx| |]; intro Hx.
{ assert (Heps' : 0 < x - seq_at_left x n).
  { unfold seq_at_left; rewrite Hx; simpl; ring_simplify; apply pow_lt; lra. }
  exists (mkposreal _ Heps'); rewrite <-Hx; intros x' _ Hx'2.
  destruct (ex_seq_at_left_gt _ _ Hx'2) as [n' Hn'].
  assert (Hfx'2 : Rbar_le (f x') m_infty).
  { apply (Rbar_le_trans _ _ _ (ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hn'))).
    now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n'. }
  now apply HM; revert Hfx'2; case (f x'). }
{ exists (seq_at_left x n); intros x' _ Hx'2.
  destruct (ex_seq_at_left_gt _ _ Hx'2) as [n' Hn']; rewrite <-Hx in Hn'.
  assert (Hfx'2 : Rbar_le (f x') m_infty).
  { apply (Rbar_le_trans _ _ _ (ndf_Rbar_Rbar_prop f _ _ (Rbar_lt_le _ _ Hn'))).
    now rewrite <-Hl; apply (proj1 (Rbar_lub_spec _)); exists n'. }
  now apply HM; revert Hfx'2; case (f x'). }
now exists 0; intro x'; case x'.
Qed.
