Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Bool.
Require Import network_calculus_def.

Local Open Scope R_scope.
Local Open Scope Rbar_scope.

Definition pseudo_inv_inf (f : ndf_Rbar_Rbar) (y : Rbar) :=
  Rbar_glb (fun x => y <= (f x)).

Definition pseudo_inv_sup (f : ndf_Rbar_Rbar) (y : Rbar) :=
  Rbar_lub (fun x => (f x) <= y).

Theorem pseudo_inv_inf_non_decreasing (f : ndf_Rbar_Rbar) (x y : Rbar) :
  x <= y -> pseudo_inv_inf f x <= pseudo_inv_inf f y.
Proof.
intros H_xy.
assert (H_fxy' := ndf_Rbar_Rbar_prop f _ _ H_xy).
unfold pseudo_inv_inf; set (Ex := fun _ => Rbar_le x _); set (Ey := fun _ => _).
assert (Hx := proj2_sig (Rbar_ex_glb Ex)).
assert (Hy := proj2_sig (Rbar_ex_glb Ey)).
now apply (Rbar_is_glb_subset Ex Ey); [intro x'; apply Rbar_le_trans| |].
Qed.

Lemma Non_decr_recipr (f : ndf_Rbar_Rbar) (x y : Rbar) :
  (f x) < (f y) -> x < y.
Proof.
intro H_fx_fy; apply Rbar_not_le_lt; intro H_xy.
now apply (Rbar_lt_not_le _ _ H_fx_fy), (ndf_Rbar_Rbar_prop f).
Qed.


Lemma ex_el_between x y :
  Rbar_lt x y -> {z : Rbar | Rbar_lt x z /\ Rbar_lt z y}.
Proof.
case x; [intro rx|now exists p_infty|];
  (case y; [intro ry| |now exists m_infty]); intro H_xy.
{ exists ((rx + ry) / 2); revert H_xy; simpl; lra. }
{ exists (rx + 1); simpl; lra. }
{ exists (ry - 1); simpl; lra. }
now exists 0.
Qed.

Lemma alt_def_pseudo_inv_inf (f : ndf_Rbar_Rbar) (y : Rbar) :
  pseudo_inv_inf f y = Rbar_lub (fun x => (f x) < y).
Proof.
apply Rbar_is_glb_unique.
set (Ele := fun x => _ y _); set (Elt := fun x => _).
destruct (Rbar_ex_lub Elt) as [l Hl]; rewrite (Rbar_is_lub_unique _ _ Hl).
split.
{ intros x H_x; apply (proj2 Hl); intros z Hz.
  now apply Rbar_lt_le, (Non_decr_recipr f), (Rbar_lt_le_trans _ _ _ Hz). }
intros b Hb; apply Rbar_not_lt_le; intro H_lb.
destruct (ex_el_between _ _ H_lb) as [m [H_ml H_mb]].
case (Rbar_le_lt_dec y (f m)); intro H_m.
{ now apply (Rbar_lt_not_le _ _ H_mb), Hb. }
now apply (Rbar_lt_not_le _ _ H_ml), (proj1 Hl).
Qed.

Lemma alt_def_pseudo_inv_sup (f : ndf_Rbar_Rbar) (y : Rbar) :
  pseudo_inv_sup f y = Rbar_glb (fun x => y < (f x)).
Proof.
apply Rbar_is_lub_unique.
set (Ele := fun x => _ y _); set (Elt := fun x => _).
destruct (Rbar_ex_glb Ele) as [l Hl]; rewrite (Rbar_is_glb_unique _ _ Hl).
split.
{ intros x H_x; apply (proj2 Hl); intros z Hz.
  now apply Rbar_lt_le, (Non_decr_recipr f), (Rbar_le_lt_trans _ _ _ H_x). }
intros b Hb; apply Rbar_not_lt_le; intro H_lb.
destruct (ex_el_between _ _ H_lb) as [m [H_mb H_ml]].
case (Rbar_le_lt_dec (f m) y); intro H_m.
{ now apply (Rbar_lt_not_le _ _ H_mb), Hb. }
now apply (Rbar_lt_not_le _ _ H_ml), (proj1 Hl).
Qed.

Lemma P4 (f : ndf_Rbar_Rbar) (y : Rbar) :
  (pseudo_inv_inf f y) <= (pseudo_inv_sup f y).
Proof.
  rewrite alt_def_pseudo_inv_inf.
  apply Rbar_lub_subset.
  intros x H_x.
  now apply Rbar_lt_le.
Qed.

Lemma P5 (f : ndf_Rbar_Rbar) (y y' : Rbar) :
  y < y' -> (pseudo_inv_sup f y) <= (pseudo_inv_inf f y').
Proof.
  intros H_yy'.
  rewrite alt_def_pseudo_inv_inf.
  apply Rbar_lub_subset.
  intros x H_x.
  now apply (Rbar_le_lt_trans (f x) y y').
Qed.

Lemma P6 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  (f x) <= y -> x <= (pseudo_inv_sup f y).
Proof.
  intros H.
  destruct (proj2_sig (Rbar_ex_lub (fun x => Rbar_le (f x) y)))as [H_ub _].
  now apply H_ub.
Qed.

Lemma P7 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  y <= (f x) -> (pseudo_inv_inf f y) <= x.
Proof.
  intros H.
  destruct (proj2_sig (Rbar_ex_glb (fun x => Rbar_le y (f x))))as [H_ub _].
  now apply H_ub.
Qed.

Lemma P8 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  (f x) < y -> x <= (pseudo_inv_inf f y).
Proof.
  intros H.
  rewrite alt_def_pseudo_inv_inf.
  destruct (proj2_sig (Rbar_ex_lub (fun x => Rbar_lt (f x) y)))as [H_ub _].
  now apply H_ub.
Qed.

Lemma P9 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  y < (f x) -> (pseudo_inv_sup f y) <= x.
Proof.
  intros H.
  rewrite alt_def_pseudo_inv_sup.
  destruct (proj2_sig (Rbar_ex_glb (fun x => Rbar_lt y (f x))))as [H_lb _].
  now apply H_lb.
Qed.

Lemma P10 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  (pseudo_inv_inf f y) < x -> y <= (f x).
Proof.
  rewrite alt_def_pseudo_inv_inf.
  set (Elt := fun _ => _).
  intro H.
  apply Rbar_not_lt_le.
  intro H0.
  destruct (proj2_sig (Rbar_ex_lub Elt)) as [H_ub _].
  exact ((Rbar_lt_not_le _ _ H) (H_ub _ H0)).
Qed.

Lemma P11 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  x < (pseudo_inv_sup f y) -> (f x) <= y.
Proof.
  rewrite alt_def_pseudo_inv_sup.
  set (Elt := fun _ => _).
  intro H.
  apply Rbar_not_lt_le.
  intro H0.
  destruct (proj2_sig (Rbar_ex_glb Elt)) as [H_lb _].
  exact ((Rbar_lt_not_le _ _ H) (H_lb _ H0)).
Qed.

Lemma P12 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  (pseudo_inv_sup f y) < x -> y < (f x).
Proof.
  unfold pseudo_inv_sup; set (Ele := fun _ => _).
  intro H.
  apply Rbar_not_le_lt.
  intro H0.
  destruct (proj2_sig (Rbar_ex_lub Ele)) as [H_ub _].
  exact ((Rbar_lt_not_le _ _ H) (H_ub _ H0)).
Qed.

Lemma P14 (f : ndf_Rbar_Rbar) (x y : Rbar) :
  x < (pseudo_inv_inf f y) -> (f x) < y.
Proof.
  unfold pseudo_inv_inf; set (Ele := fun _ => _).
  intro H.
  apply Rbar_not_le_lt.
  intro H0.
  destruct (proj2_sig (Rbar_ex_glb Ele)) as [H_lb _].
  exact ((Rbar_lt_not_le _ _ H) (H_lb _ H0)).
Qed.