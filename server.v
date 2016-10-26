From mathcomp Require Import ssreflect ssrfun ssrbool eqtype bigop fintype finfun ssralg ssrnat.
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Bool.
Require Import network_calculus_def.
Require Import interval_bounding.
Require Import Rstruct.

Open Scope ring_scope.
Local Open Scope R_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Definition start' (A D : dflow) (t : nnR) :=
  Lub_Rbar (fun u => exists u' : nnR, u = u' /\ u <= t /\ A u' = D u' :> R).

Lemma start_proof (A D : dflow) (t : nnR) : 0 <= start' A D t.
Proof.
  unfold start'.
  set (E := fun _ => _).
  assert (Rbar_le 0 (Lub_Rbar E)).
  destruct (proj2_sig (ex_lub_Rbar E)) as [Hub _].
  apply Hub.
  unfold E.
  exists nnR0.
  split. now trivial. 
  split. pose (Ht := nnR_pos t); now lra.
  rewrite (dflow_cond_start A).
  now rewrite (dflow_cond_start D).
  revert H. unfold Rbar_le.
  case (Lub_Rbar E); simpl; intros; first [now lra | now trivial].
Qed.

Definition start (A D : dflow) (t : nnR) :=
  mk_nnR (start' A D t) (start_proof A D t).

Lemma start'_is_finite A D t : is_finite (start' A D t).
Proof.
  unfold start'.
  set (E := fun _ => _).
  assert (Rbar_le (Lub_Rbar E) t).
  { apply (proj2 (proj2_sig (ex_lub_Rbar _))).
    now intros x Hx; destruct Hx. }
  assert (H0 : Rbar_le 0 (start' A D t)).
  { unfold start'.
    assert (Rbar_le 0 (Lub_Rbar E)).
    { apply (proj1 (proj2_sig (ex_lub_Rbar E))).
      unfold E.
      exists nnR0.
      split; [now simpl|]; split.
      { pose (Ht := nnR_pos t); lra. }
      now rewrite !dflow_cond_start. }
    revert H; unfold Rbar_le.
    now case (Lub_Rbar E); simpl; intros; [|lra|].
  }
  revert H H0.
  unfold start'.
  fold E.
  now case (Lub_Rbar E).
Qed.

Lemma ndf_start' (A D : dflow) (x y : nnR) :
  x <= y -> start' A D x <= start' A D y.
Proof.
  intro H.
  cut (Rbar_le (start' A D x) (start' A D y)).
  - now unfold Rbar_le; rewrite <- start'_is_finite; rewrite <- start'_is_finite at 1; intros.
  unfold start'.
  set (E1 := fun _ => _).
  set (E2 := fun _ => _).
  apply (is_lub_Rbar_subset E2 E1).
  - intros z [u [Hz [Hz_re Hu]]].
    exists u.
    split; [trivial | split; [lra | trivial]].
  - apply Lub_Rbar_correct.
  - apply Lub_Rbar_correct.
Qed.

Lemma start'_le_t A D t : start' A D t <= t.
Proof.
  unfold start'.
  set (E := fun _ => _).
  destruct (proj2_sig (ex_lub_Rbar E)) as [_ Hlub].
  assert (Rbar_le (Lub_Rbar E) t).
  { apply Hlub.
    intros x [u' [_ [Hx_le _]]].
    now simpl. }
  assert (HR := start'_is_finite).
  specialize (HR A D t).
  unfold start' in HR; fold E in HR.
  rewrite <- HR in H; simpl in H.
  now trivial.
Qed.

Definition nnR_minus x y (P : y <= x) :=
  mk_nnR (x - y) (Rge_le _ _ (Rge_minus _ _ (Rle_ge _ _ P))).

Lemma start_eq (A D : dflow) (t : nnR) : A (start A D t) = D (start A D t).
Proof.
  unfold start, start'.
  set (E := fun _ => _).
  assert (HA : Lub_Rbar (fun y => exists x, y = A x /\ E x) = A (start A D t) :> R).
  { 
    assert (HA : Lub_Rbar (fun y => exists x, y = A x /\ E x) = A (start A D t) :> Rbar).
    apply (dflow_cond_cont_left A).
    rewrite (start'_is_finite A D t).
    exact (proj2_sig (ex_lub_Rbar E)).
    now rewrite HA. }
  assert (HD : Lub_Rbar (fun y => exists x, y = D x /\ E x) = D (start A D t) :> R).
  { 
    assert (HD : Lub_Rbar (fun y => exists x, y = D x /\ E x) = D (start A D t) :> Rbar).
    apply (dflow_cond_cont_left D).
    rewrite (start'_is_finite A D t).
    exact (proj2_sig (ex_lub_Rbar E)).
    now rewrite HD. }
  apply nnR_inj.
  unfold E.
  fold (start' A D t); fold (start A D t).
  rewrite <- HA; rewrite <- HD.
  f_equal.
  apply Lub_Rbar_eqset.
  intro x.
  split;
  intro H; destruct H as [x0 [Hx0D Hx0E]]; exists x0;
  split; auto;
  destruct Hx0E as [x0' [H1 [H2 H3]]];
  assert (H1' := nnR_inj _ _ H1);
  rewrite <- H1' in H3.
  now rewrite <- H3.
  now rewrite H3.
Qed.

Ltac simpl_re := rewrite /GRing.add /GRing.zero /=.

Lemma big_sum_pred_pos_pos n (P : pred 'I_n) F :
  (forall i, P i -> 0 <= F i) -> 0 <= \sum_(i | P i) F i.
Proof.
move=> HF.
apply big_rec; [by right|]; move=> i x HP Hx.
by apply Rplus_le_le_0_compat; [apply HF|].
Qed.

Lemma big_sum_pos_eq_0 n (F : 'I_n -> R) :
  (forall i, 0 <= F i) -> \sum_i F i = 0 -> forall i, F i = 0.
Proof.
move=> H Hi i.
have [R|//] := Rle_lt_or_eq_dec _ _ (H i).
suff HH: (0 < \big[+%R/0]_j F j)%Re by move: Hi HH; simpl_re; lra.
rewrite (bigD1 i) //=.
set X := \big[_/_]_(_|_) _.
suff: (0 <= X)%Ri by simpl_re; lra.
by apply big_sum_pred_pos_pos.
Qed.

Lemma sum_eq_imp_el_eq n (S : n_server n.+1) (A D : dflow^n.+1) (x : nnR) :
  S A D -> sum_dflow A x = sum_dflow D x -> forall i, (A i) x = (D i) x.
Proof.
  intros HAD Heq i.
  simpl in Heq; unfold ndf_sum_dflow_val in Heq.
  inversion Heq as [Heq'].
  unfold ndf_sum_dflow_val_val in Heq'; simpl in Heq'.
  assert (\sum_i (A i x - D i x)%Re = 0).
  { rewrite GRing.sumrB.
    rewrite Heq'.
    unfold GRing.add, GRing.opp; simpl.
    ring. }
  cut (A i x - D i x = 0).
  - now intros; apply nnR_inj; rewrite <- Rplus_0_l; rewrite <- H0; ring.
  revert H i; apply big_sum_pos_eq_0; intro i.
  apply Rge_le, Rge_minus, Rle_ge, (n_server_cond_dflow _ _ _ _ HAD).
Qed.

Lemma after_start_is_backlog_period (S : server) (A D : dflow) (t : nnR) :
  S A D -> forall (s : nnR), start A D t < s <= t -> D s < A s.
Proof.
  intros HAD s (Hs_lt, Hs_le).
  apply Rnot_le_lt.
  intro H.
  case H.
  { intro H0.
    exact (Rlt_not_le _ _ H0 (server_cond_dflow S A D HAD s)). }
  { intro H0.
    unfold start, start' in Hs_lt. simpl in Hs_lt.
    set (E := fun _ => _) in Hs_lt.
    destruct (Lub_Rbar_correct E) as [Hub Hlub].
    refine (Rbar_le_not_lt _ _ (Hub s _) _).
    now exists s.
    assert (H1 := start'_is_finite A D t).
    revert H1.
    unfold start'. fold E.
    now revert Hs_lt; case (Lub_Rbar E).
   }
Qed.

Lemma strict_imp_simpl (S : server) (A D : dflow) (beta : nnR -> nnRbar) :
  S A D -> is_strict_min_service_curve S beta -> is_min_service_curve S beta.
Proof.
  intros HAD Hbeta.
  unfold is_min_service_curve.
  unfold is_strict_min_service_curve in Hbeta.
  intros A0 D0 HA0D0 t.
  specialize(Hbeta A0 D0 HA0D0).
  unfold min_conv, min_conv_val; simpl.
  apply Rbar_le_trans with (y := (Rbar_plus (A0 (start A0 D0 t)) (beta (nnR_minus t (start A0 D0 t) (start'_le_t A0 D0 t))))).
  {
    unfold nnR_plus, nnR_minus.
    simpl.
    set (E := fun _ => _).
    destruct (proj2_sig (Rbar_ex_glb E)) as [Hlb _].
    unfold is_lb_Rbar in Hlb.
    unfold is_ub_Rbar in Hlb.
    apply Hlb.
    exists (start A0 D0 t), (nnR_minus t (start A0 D0 t) (start'_le_t A0 D0 t));
    split; first[ now simpl; f_equal; ring | now trivial].
  }
  rewrite start_eq.
  specialize (Hbeta (start A0 D0 t) (nnR_minus t (start A0 D0 t) (start'_le_t A0 D0 t))).
  simpl in Hbeta.
  replace (_ + (_ - _)) with (nnR_val t) in Hbeta by ring.
  specialize (Hbeta (after_start_is_backlog_period S A0 D0 t HA0D0)).
  replace (nnR_plus _ _) with t in Hbeta.
  { revert Hbeta.
    now case (D0 t), (D0 (start A0 D0 t)), nnRbar_val; simpl; [lra| |]. }
  apply nnR_inj; simpl; ring.
Qed.

Lemma sum_equiv_Rbar_sum_on_R I r (P : pred I) (E1 : I -> R) :
  \sum_(i <- r | P i) E1 i
  = \big[Rbar_plus/Finite 0]_(i <- r | P i) E1 i :> Rbar.
Proof. now apply big_morph. Qed.

Theorem blind_multiplexing n (S : n_server n.+1)
        (alpha : (nnR -> nnRbar)^n.+1) (beta : nnR -> nnRbar)
        i :
  (forall A D, S A D -> forall j, is_upper_interval_bound (A j) (alpha j)) ->
  is_strict_min_service_curve (aggregate_server S) beta ->
  is_min_service_curve
    (residual_server S i)
    (non_decreasing_closure 
       (fun x =>
         Rbar_to_nnRbar
           (Rbar_minus
              (beta x)
              (\big[Rbar_plus/Finite 0]_(j | j != i) (alpha j x))))).
Proof.
  intros HA Hbeta Ai Di HAiDi t.
  destruct HAiDi as [A [D [HAD [HAi HDi]]]].
  specialize (HA A D HAD).
  unfold min_conv, min_conv_val.
  set (E := fun _ => _).
  destruct (proj2_sig (Rbar_ex_glb E)) as [Hlb _].
  unfold Rbar_is_lower_bound in Hlb.
  simpl.
  pose (start_sum := start (sum_dflow A) (sum_dflow D) t).
  pose (v := (nnR_minus t start_sum (start'_le_t (sum_dflow A) (sum_dflow D) t))).
  pose (El := Rbar_plus
                (Ai start_sum)
                (non_decreasing_closure 
                   (fun v => (Rbar_to_nnRbar
                   (Rbar_minus
                      (beta v)
                      (\big[Rbar_plus/Finite 0]_(j | j != i) alpha j v)))) v)).
  assert (HEl : E El).
  { now exists start_sum, v; split; [simpl; f_equal; ring|]. }
  apply (Rbar_le_trans _ _ _ (Hlb El HEl)).
  unfold El.
  rewrite <- (HAi start_sum).
  rewrite (sum_eq_imp_el_eq _ _ _ _ _ HAD (start_eq _ _ _)).
  rewrite <- (HDi t). 
  cut (Rbar_le (non_decreasing_closure 
                 (fun v => Rbar_to_nnRbar
                 (Rbar_minus (beta v)
                 (\big[Rbar_plus/Finite 0]_(j | j != i) alpha j v))) v) 
               (Rbar_minus (D i t) (D i start_sum))).
  { case non_decreasing_closure; fold start_sum; simpl; intro nv.
    case nv; intro nnRbar_val; case nnRbar_val; unfold Rbar_le, Rbar_plus; simpl; intros; simpl; lra. }
  simpl. unfold non_decreasing_closure_val_val; simpl.
  set (E' := fun _ => _).
  destruct (proj2_sig (Rbar_ex_lub E')) as [_ Hlub].
  apply Hlub.
  unfold Rbar_is_upper_bound.
  intros W [w [Hw HW]].
  rewrite HW; clear W HW.
  pose (u := nnR_plus w start_sum).
  assert (Hu_le : start_sum <= u).
  - now unfold u; assert(Hw_pos := Rle_bool_Rle _ _ (nnR_prop w)); simpl; lra.
  assert (Hwu : w = nnR_minus u start_sum Hu_le).
  - now apply nnR_inj; unfold u; simpl; ring.
  rewrite Hwu.
  apply Rbar_le_trans with (y := (D i u - D i start_sum)); 
  [| apply Rplus_le_compat; [apply (ndf_nnR_nnR_prop (D i)); unfold u; simpl; lra | now lra]].
  (* PR : ça vaudrait peut être le coup de sortir ce assert dans un lemme *)
  assert (Hnd : forall x y, Rbar_le x y -> Rbar_le (Rbar_to_nnRbar x) (Rbar_to_nnRbar y)).
  { intros x y Hxy; simpl; unfold nn_part.
    case Rbar_le_dec, Rbar_le_dec; simpl; [now simpl| |now simpl|lra].
    now exfalso; apply n0, (Rbar_le_trans _ _ _ r).
  } 
  apply Rbar_le_trans
  with (y := (Rbar_to_nnRbar (Rbar_minus (beta (nnR_minus u start_sum Hu_le))
                                         (\big[Rbar_plus/Finite 0]_(j | j != i)
                                           ((A j u) - (A j start_sum))%Re)))).
  { apply Hnd.
    (* PR : un lemme Rbar_plus_le_compat_l ? *)
    apply Rbar_plus_le_compat; [now apply Rbar_le_refl|]; apply Rbar_opp_le.
    apply Rbar_leq_sum.
    intros i0 Hi0.
    specialize (HA i0 start_sum w).
    rewrite <- Hwu.
    assert (H : nnR_plus start_sum w = u).
    { now apply nnR_inj; unfold u; simpl; ring. }
    rewrite <- H.
    now apply HA.
  }
  apply Rbar_le_trans
  with (y := (Rbar_to_nnRbar (Rbar_minus (beta w)
                                         (\big[Rbar_plus/Finite 0]_(j | j != i)
                                           ((D j u) - (A j start_sum))%Re)))).
  { apply Hnd.
    rewrite <- Hwu.
    apply Rbar_plus_le_compat; [now apply Rbar_le_refl|]; apply Rbar_opp_le.
    apply Rbar_leq_sum.
    intros i0 Hi0.
    apply Rplus_le_compat; [|now right].
    apply (n_server_cond_dflow _ _ _ _ HAD).
  }
  assert (H : (Rbar_minus (D i u) (D i start_sum) =
               (Rbar_minus (\big[Rbar_plus/Finite 0]_j
                             ((D j u) - (D j start_sum)))
                           (\big[Rbar_plus/Finite 0]_(j | j != i)
                             ((D j u) - (D j start_sum)))))).
  {
    rewrite <- !sum_equiv_Rbar_sum_on_R; simpl.
    rewrite (bigD1 i); [|now simpl].
    repeat (unfold GRing.add; simpl); f_equal.
    change ((Finite.eqType (ordinal_finType n))) with ((ordinal_eqType n)).
    ring.
  }
  (* PR : éviter de laisser Coq choisir les noms des hypothèses (H, H0,...),
   * ça rend les preuves beaucoup moins robustes *)
  assert (H0 : (Rbar_minus (D i u) (D i start_sum))
               = Rbar_to_nnRbar (Rbar_minus (D i u) (D i start_sum))).
  {
    assert (H0 : Rbar_le 0 (Rbar_minus (D i u) (D i start_sum))).
    { rewrite <- (Rbar_minus_eq_0 (D i u)).
      apply Rbar_plus_le_compat; [now apply (ndf_nnR_nnR_prop (D i)); simpl; lra|].
      simpl; apply Ropp_ge_le_contravar; apply Rle_ge.
      apply (ndf_nnR_nnR_prop (D i)), Hu_le. }
    now symmetry; apply ifT; case Rbar_le_dec.
  }
  simpl in H0; rewrite H0.
  apply Hnd.
  assert (H1 : (\big[Rbar_plus/Finite 0]_(j | j != i) (D j u - A j start_sum))
               = (\big[Rbar_plus/Finite 0]_(j | j != i) (D j u - D j start_sum))).
  { apply eq_bigr; intros j Hj; do 3 f_equal.
    now rewrite (sum_eq_imp_el_eq _ _ _ _ _ HAD (start_eq _ _ t)). }
  rewrite H1.
  simpl in H; rewrite H.
  apply Rbar_plus_le_compat; [|now apply Rbar_le_refl].
  assert (HAsDs : (aggregate_server S) (sum_dflow A) (sum_dflow D)).
  { now simpl; unfold aggregate_server_val; exists A, D. }
  unfold u.
  assert (Hbacklog := after_start_is_backlog_period
                        (aggregate_server S) (sum_dflow A) (sum_dflow D)
                        (nnR_plus w start_sum) HAsDs).
  rewrite <- sum_equiv_Rbar_sum_on_R.
  rewrite GRing.sumrB.
  unfold GRing.add, GRing.opp; simpl.
  assert (Hcomm : nnR_plus w start_sum = nnR_plus start_sum w).
  - now apply nnR_inj; simpl; ring.
  rewrite Hcomm.
  apply (Hbeta _ _ HAsDs _ _).
  intros s [Hs_lt Hs_le].
  assert (Hs_weak : start (sum_dflow A) (sum_dflow D) (nnR_plus w start_sum) < s
                 <= nnR_plus w start_sum).
  split.
  - apply Rle_lt_trans with (r2 := start_sum).
    * apply ndf_start'; simpl; lra.
    * now trivial.
  - now simpl; simpl in Hs_le; lra.
  now apply (Hbacklog s Hs_weak).
Qed.