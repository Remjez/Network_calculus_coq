From mathcomp Require Import eqtype.
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Bool.
Require Import network_calculus_def.

Definition is_upper_interval_bound (f : nnR -> nnR) (phi : nnR -> nnRbar) :=
  forall (t d : nnR), (f (nnR_plus t d)) - (f t) <= (phi d).

Definition is_lower_interval_bound (f : nnR -> nnR) (phi : nnR -> nnRbar) :=
  forall (t d : nnR), (phi d) <= (f (nnR_plus t d)) - (f t).

Lemma UIB_alt_def (f : nnR -> nnR) (phi : nnR -> nnRbar) :
  is_upper_interval_bound f phi
  <-> (forall t : nnR, (f t) <= (min_conv f phi t)).
Proof.
split.
{ intros H t; apply (proj2 (proj2_sig (Rbar_ex_glb _))).
  intros x [u [v [Ht Hx]]]; rewrite Hx.
  unfold is_upper_interval_bound in H.
  apply (Rbar_le_trans _ (Rbar_plus (f u)
                                    (Rbar_minus (f (nnR_plus u v)) (f u)))).
  { assert (Ht' : nnR_plus u v = t); [now apply nnR_inj; simpl in Ht; inversion Ht|].
    rewrite Ht'; simpl; right; ring. }
  now apply Rbar_plus_le_compat; [apply Rbar_le_refl|apply H]. }
intros H t d.
specialize (H (nnR_plus t d)).
unfold min_conv, min_conv_val in H; simpl nnRbar_val in H.
set (E := fun _ => _) in H.
assert (H0 : Rbar_le (Rbar_glb E) (Rbar_plus (f t) (phi d))).
{ now apply (proj1 (proj2_sig (Rbar_ex_glb _))); exists t, d. }
assert (H1 := Rbar_le_trans _ _ _ H H0); revert H1.
now case (phi d : Rbar); simpl; first intro r; lra.
Qed.

Lemma conv_preserves_arrival_curve (f : nnR -> nnR) (phi psi : nnR -> nnRbar) :
  is_upper_interval_bound f phi ->
  is_upper_interval_bound f psi ->
  is_upper_interval_bound f (min_conv phi psi).
Proof.
intros Hphi Hpsi.
  unfold is_upper_interval_bound, min_conv, min_conv_val.
  intros t d.
  simpl (_ d).
  set (E := fun _ => _) at 1.
  destruct (proj2_sig (Rbar_ex_glb E)) as [_ Hglb].
  apply Hglb.
  intros x Hx.
  destruct Hx as [u [v [Huv Hx]]].
  rewrite Hx.
  assert ((Rbar_minus (f (nnR_plus t d)) (f t)) = Rbar_plus (Rbar_minus (f (nnR_plus t d)) (f (nnR_plus t u))) (Rbar_minus (f (nnR_plus t u)) (f t))).
  case (f (nnR_plus t u)); simpl; intros; f_equal; ring.
  rewrite H.
  rewrite Rbar_plus_comm.
  apply Rbar_plus_le_compat.
  apply (Hphi t u).
  assert (nnR_plus t d = nnR_plus (nnR_plus t u) v).
  apply nnR_inj.
  simpl.
  inversion Huv as [Huv_inj].
  ring.
  rewrite H0; apply (Hpsi (nnR_plus t u) v).
Qed.

Lemma conv_closure_preserves_arrival_curve (f : nnR -> nnR) (phi : nnR -> nnRbar) :
  is_upper_interval_bound f phi ->
  is_upper_interval_bound f (min_conv_closure phi).
Proof.
  intros H.
  intros t d.
  unfold min_conv_closure, min_conv_closure_val.
  simpl (_ d).
  set (E := fun _ => _).
  destruct (proj2_sig (Rbar_ex_glb E)) as [_ Hglb].
  apply Hglb.
  intros x [n Hx].
  rewrite Hx.
  clear Hx E Hglb.
  assert (is_upper_interval_bound f (min_conv_iter n phi)).
  induction n.
  { 
    unfold is_upper_interval_bound.
    intros t0 d0.
    simpl; case (Rbar_eq_dec d0 0); simpl.
    intros Hd0.
    assert (nnR_plus t0 d0 = t0 :> R).
    revert Hd0.
    case d0; simpl; intros. injection Hd0. intro Hdd0. rewrite Hdd0. f_equal; ring.
    rewrite (nnR_inj _ _ H0).
    unfold contract_eps_val.
    case eqP; simpl.
    now lra.
    now trivial.
    unfold contract_eps_val.
    case eqP; simpl.
    now intros H' H''; exfalso; apply H''; rewrite H'.
    now trivial.
  }
  {
    unfold is_upper_interval_bound.
    intros t0 d0.
    simpl (min_conv_iter (S n) phi d0).
    now apply conv_preserves_arrival_curve.
  }
  exact (H0 t d).
Qed.

Theorem UIB_equiv_conv_closure (f : nnR -> nnR) (phi : nnR -> nnRbar) :
  is_upper_interval_bound f phi
  <-> is_upper_interval_bound f (min_conv_closure phi).
Proof.
  split.
  apply conv_closure_preserves_arrival_curve.
  intro H.
  apply UIB_alt_def.
  destruct (UIB_alt_def f (min_conv_closure phi)) as [H0 _].
  specialize (H0 H).
  intro t.
  apply (Rbar_le_trans _ (min_conv f (min_conv_closure phi) t) _).
  exact (H0 t).
  clear H0.
  unfold min_conv, min_conv_val.
  simpl.
  pose (E := fun y : Rbar => exists (u v : nnR), u + v = t /\ y = Rbar_plus (f u) (min_conv_closure phi v)).
  pose (E' := fun y : Rbar => exists (u v : nnR), u + v = t /\ y = Rbar_plus (f u) (phi v)).
  destruct (proj2_sig (Rbar_ex_glb E')) as [_ HE'glb].
  apply HE'glb.
  unfold Rbar_is_lower_bound.
  intros x Hx.
  unfold E' in Hx.
  destruct Hx as [u [v [Ht Hx]]].
  apply (Rbar_le_trans _ (Rbar_plus (f u) (min_conv_closure phi v))).
  { destruct (proj2_sig (Rbar_ex_glb E)) as [HElb _].
    apply HElb.
    exists u, v; split; now trivial. }
  rewrite Hx.
  apply Rbar_plus_le_compat; try (simpl; lra).
  unfold min_conv_closure, min_conv_closure_val; simpl.
  set (E'' := fun _ => _).
  destruct (proj2_sig (Rbar_ex_glb E'')) as [HE''lb _].
  apply HE''lb.
  exists (1%nat).
  apply Rbar_le_antisym.
  {
    simpl; unfold min_conv, min_conv_val.
    set (Eters := fun _ => _).
    destruct (proj2_sig (Rbar_ex_glb Eters)) as [_ HEters_glb].
    apply HEters_glb.
    intros x0 Hx0.
    destruct Hx0 as [u0 [v0 [Hv Hx0]]].
    rewrite Hx0.
    case (Rbar_eq_dec v0 0).
    intro Hv0; injection Hv0; intro Hiv0; simpl.
    assert (nnR_plus u0 v0 = v).
    now apply nnR_inj; inversion Hv.
    rewrite <- H0.
    assert (nnR_plus u0 v0 = u0 :> R).
    simpl; rewrite Hiv0; ring.
    rewrite (nnR_inj _ _ H1).
    unfold contract_eps_val.
    change R0 with (nnR0 : R) in Hiv0.
    now rewrite (nnR_inj _ _ Hiv0), eqxx, Rbar_plus_0_r; apply Rbar_le_refl.
    unfold contract_eps, contract_eps_val; simpl.
    case (Rbar_eq_dec v0 0).
    now intros; exfalso.
    case eqP; intros Hv0.
    { now rewrite Hv0; intro H'; exfalso; apply H'. }
    assert (Hu0 := nnRbar_pos (phi u0)).
    assert (Hv' := nnRbar_pos (phi v)).
    now revert Hu0 Hv'; case (phi v : Rbar), (phi u0 : Rbar).
  }
  {
    simpl; unfold min_conv_val. 
    apply (proj1 (proj2_sig (Rbar_ex_glb _))).
    exists v, nnR0; simpl; unfold contract_eps_val; case eqP.
    now simpl; intro H1; split; [rewrite Rplus_0_r|rewrite Rbar_plus_0_r].
    now intro H'; exfalso; apply H'.
  }
Qed.
