From mathcomp Require Import ssreflect ssrfun ssrbool eqtype bigop fintype finfun ssralg ssrnat tuple.
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Bool.
Require Import Rstruct.

Open Scope ring_scope.
Local Open Scope R_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

(** ** Definition of non negative real numbers. *)

(** R is an eqType (its equality is decidable). *)
Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof. by rewrite /eqr => r1 r2; case: Req_EM_T=> H; apply: (iffP idP). Qed.

Definition real_eqMixin := EqMixin eqrP.
Canonical real_eqType := Eval hnf in EqType R real_eqMixin.

(** Since order on R is decidable, we can get a boolean predicate for <=. *)
Definition Rle_bool x y := if Rle_dec x y then true else false.

Lemma Rle_bool_Rle x y : Rle_bool x y = true -> x <= y.
Proof. now unfold Rle_bool; case (Rle_dec x y). Qed.
  
Lemma Rle_Rle_bool x y : x <= y -> Rle_bool x y = true.
Proof. now unfold Rle_bool; case (Rle_dec x y). Qed.
  
(** nnR is the subset of non negative values of R. *)
Record nnR := { nnR_val :> R; nnR_prop : Rle_bool 0 nnR_val = true }.

(** It then inherits the eqType structure of R. *)
Canonical nnR_subType := [subType for nnR_val].
Definition nnR_eqMixin := Eval hnf in [eqMixin of nnR by <:].
Canonical nnR_eqType := Eval hnf in EqType nnR nnR_eqMixin.

(** In particular, the coercion to R is injective. *)
Lemma nnR_inj : injective nnR_val. Proof. exact: val_inj. Qed.

Lemma nnR_pos (n : nnR) : 0 <= n. Proof. apply Rle_bool_Rle, valP. Qed.

Definition mk_nnR (x : R) (Px : 0 <= x) := Build_nnR x (Rle_Rle_bool 0 x Px).

(** ** nnRbar is defined similarly. *)

Definition eqrbar (r1 r2 : Rbar) : bool :=
  if Rbar_eq_dec r1 r2 then true else false.

Lemma eqrbarP : Equality.axiom eqrbar.
Proof.
by rewrite /eqrbar => r1 r2; case: Rbar_eq_dec=> H; apply: (iffP idP).
Qed.

Definition Rbar_eqMixin := EqMixin eqrbarP.
Canonical Rbar_eqType := Eval hnf in EqType Rbar Rbar_eqMixin.

Definition Rbar_le_bool x y := if Rbar_le_dec x y then true else false.

Lemma Rbar_le_bool_Rbar_le x y : Rbar_le_bool x y = true -> Rbar_le x y.
Proof. now unfold Rbar_le_bool; case (Rbar_le_dec x y). Qed.
  
Lemma Rbar_le_Rbar_le_bool x y : Rbar_le x y -> Rbar_le_bool x y = true.
Proof. now unfold Rbar_le_bool; case (Rbar_le_dec x y). Qed.
  
Record nnRbar := {
  nnRbar_val :> Rbar;
  nnRbar_prop : Rbar_le_bool 0 nnRbar_val = true
}.

Canonical nnRbar_subType := [subType for nnRbar_val].
Definition nnRbar_eqMixin := Eval hnf in [eqMixin of nnRbar by <:].
Canonical nnRbar_eqType := Eval hnf in EqType nnRbar nnRbar_eqMixin.

Lemma nnRbar_inj : injective nnRbar_val. Proof. exact: val_inj. Qed.

Lemma nnRbar_pos (n : nnRbar) : Rbar_le 0 n.
Proof. apply Rbar_le_bool_Rbar_le, valP. Qed.

Definition mk_nnRbar (x : Rbar) (Px : Rbar_le 0 x) :=
  Build_nnRbar x (Rbar_le_Rbar_le_bool 0 x Px).

Lemma nnR_to_nnRbar_proof (x : nnR) : Rbar_le 0 (Finite x).
Proof. by move: (nnR_pos x). Qed.

(** Coercion from nnR to nnRbar. *)
Coercion nnR_to_nnRbar (x : nnR) := mk_nnRbar _ (nnR_to_nnRbar_proof x).

Definition nn_part (x : Rbar) := if Rbar_le_dec 0 x then x else 0.

Lemma Rbar_to_nnRbar_proof (x : Rbar) : Rbar_le 0 (nn_part x).
Proof. now unfold nn_part; case Rbar_le_dec; [|intro; simpl; lra]. Qed.

Definition Rbar_to_nnRbar (x : Rbar) := mk_nnRbar _ (Rbar_to_nnRbar_proof x).

(** Constants *)

Definition nnR0 := mk_nnR _ (Rle_refl 0).

Definition nnRbar0 := mk_nnRbar _ (Rbar_le_refl 0).

Definition nnRbar_infty := mk_nnRbar p_infty I.

(** Notations *)

Delimit Scope Rbar_scope with Rbar.
Open Scope Rbar_scope.

Infix "<=" := Rbar_le : Rbar_scope.
Infix "<"  := Rbar_lt : Rbar_scope.
Notation "f1 <=1 f2" := ((fun f g => forall t : Rbar, f t <= g t) f1 f2)
  (at level 70, no associativity) : Rbar_scope.
Notation "f1 <=1 f2 :> A" := (f1 <=1 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : Rbar_scope.
Notation "f1 <1 f2" := ((fun f g => forall t : Rbar, f t <= g t) f1 f2)
  (at level 70, no associativity) : Rbar_scope.
Notation "f1 <1 f2 :> A" := (f1 <1 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : Rbar_scope.

Notation "f1 <=1 f2" := ((fun f g t => (f t <= g t)%Re) f1 f2)
  (at level 70, no associativity) : R_scope.
Notation "f1 <=1 f2 :> A" := (f1 <=1 (f2 : A))%Re
  (at level 70, f2 at next level, A at level 90) : R_scope.
Notation "f1 <1 f2" := ((fun f g t => (f t <= g t)%Re) f1 f2)
  (at level 70, no associativity) : R_scope.
Notation "f1 <1 f2 :> A" := (f1 <1 (f2 : A))%Re
  (at level 70, f2 at next level, A at level 90) : R_scope.

Infix "+" := Rbar_plus : Rbar_scope.
Infix "-"  := Rbar_minus : Rbar_scope.

(** ** Non decreasing functions. *)

Record ndf_nnR_nnR := {
  ndf_nnR_nnR_val :> nnR -> nnR;
  ndf_nnR_nnR_prop :
    forall (x y: nnR), x <= y -> ndf_nnR_nnR_val x <= ndf_nnR_nnR_val y
}.

Record ndf_nnR_nnRbar := {
  ndf_nnR_nnRbar_val :> nnR -> nnRbar;
  ndf_nnR_nnRbar_prop :
    forall (x y: nnR),
      x <= y -> Rbar_le (ndf_nnR_nnRbar_val x) (ndf_nnR_nnRbar_val y)
}.

Record ndf_Rbar_Rbar := {
  ndf_Rbar_Rbar_val :> Rbar -> Rbar;
  ndf_Rbar_Rbar_prop :
    forall (x y: Rbar),
      Rbar_le x y -> Rbar_le (ndf_Rbar_Rbar_val x) (ndf_Rbar_Rbar_val y)
}.

Definition non_decreasing_closure_val_val (phi : nnR -> nnRbar) (x : nnR) :=
  Rbar_lub (fun y => exists t : nnR, t <= x /\ y = phi t).

Lemma non_decreasing_closure_val_proof (phi : nnR -> nnRbar) (x : nnR) :
  Rbar_le_bool 0 (non_decreasing_closure_val_val phi x).
Proof.
  apply Rbar_le_Rbar_le_bool.
  unfold non_decreasing_closure_val_val.
  set (E := fun _ => _).
  destruct (proj2_sig (Rbar_ex_lub E)) as [Hub _].
  apply Rbar_le_trans with (y := phi x).
  - now apply nnRbar_pos.
   - apply Hub.
     exists x.
     split.
     * now simpl; lra.
     * now trivial.
Qed.

Definition non_decreasing_closure_val (phi : nnR -> nnRbar) (x : nnR) :=
  Build_nnRbar (non_decreasing_closure_val_val phi x) (non_decreasing_closure_val_proof phi x).

Lemma non_decreasing_closure_proof (phi : nnR -> nnRbar) (x y : nnR) :
  x <= y -> Rbar_le (non_decreasing_closure_val phi x) (non_decreasing_closure_val phi y).
Proof.
  intro Hxy.
  unfold non_decreasing_closure_val, non_decreasing_closure_val_val; simpl.
  set (Ex := fun _ => _).
  set (Ey := fun _ => _).
  apply Rbar_lub_subset.
  intros z Hz.
  destruct Hz as [t [Hz_le Hz_phi]].
  exists t; split.
  - now apply (Rle_trans _ _ _ Hz_le Hxy).
  - now trivial.
Qed.

Definition non_decreasing_closure (phi : nnR -> nnRbar) :=
  Build_ndf_nnR_nnRbar (non_decreasing_closure_val phi) (non_decreasing_closure_proof phi).

(** ** Definitions for continuity. *)

Definition Rbar_locally_Rbar (a : Rbar) (P : Rbar -> Prop) :=
  match a with
  | Finite a => locally a P
  | p_infty => exists M : R, forall x : Rbar, Rbar_lt M x -> P x
  | m_infty => exists M : R, forall x : Rbar, Rbar_lt x M -> P x
  end.

Definition at_left_Rbar (x : Rbar) :=
  within (fun u : Rbar => Rbar_lt u x) (Rbar_locally_Rbar x).

Definition at_right_Rbar (x : Rbar) :=
  within (fun u : Rbar => Rbar_lt x u) (Rbar_locally_Rbar x).

Definition is_lim (f : Rbar -> Rbar) (x l : Rbar) :=
  filterlim f (Rbar_locally' x) (Rbar_locally_Rbar l).

Definition is_lim_left (f : Rbar -> Rbar) (x l : Rbar) :=
  filterlim f (at_left_Rbar x) (Rbar_locally_Rbar l).

Definition is_lim_right (f : Rbar -> Rbar) (x l : Rbar) :=
  filterlim f (at_right_Rbar x) (Rbar_locally_Rbar l).

Definition cont_left (f : Rbar -> Rbar) :=
  forall (x : Rbar), is_lim_left f x (f x).

Definition cont_right (f : Rbar -> Rbar) :=
  forall (x : Rbar), is_lim_right f x (f x).

(*
Definition nnR_locally (x : nnR) (P : nnR -> Prop) := locally (nnR_val x) (fun x => P x).

Definition at_left_nnR (x : nnR) :=
  within (fun u : nnR => u < x) (nnR_locally x).
*)
(** ** Min convolution. *)

Definition Rbar_plus_nc (x y : Rbar) : Rbar :=
  match Rbar_plus' x y with
  | Some z => z 
  | None => p_infty
  end.

Lemma nnRbar_plus_nc_proof :
  forall (x y : nnRbar), 0 <= (Rbar_plus_nc x y).
Proof.
intros x y; destruct x as [x Hx]; destruct y as [y Hy]; simpl.
apply Rbar_le_bool_Rbar_le in Hx; apply Rbar_le_bool_Rbar_le in Hy.
revert Hx Hy; unfold Rbar_plus_nc, Rbar_plus'; simpl; case x, y; try lra.
Qed.

Definition nnRbar_plus_nc (x y : nnRbar) : nnRbar :=
  mk_nnRbar _ (nnRbar_plus_nc_proof x y).

Lemma Rbar_plus_nc_le_compat (a b c d : Rbar) :
  a <= b -> c <= d -> (Rbar_plus_nc a c) <= (Rbar_plus_nc b d).
Proof.
unfold Rbar_le, Rbar_plus_nc, Rbar_plus'; intros Hab Hcd.
now case a, b, c, d; first lra.
Qed.

Definition Rbar_minus_nc (x y : Rbar) : Rbar := Rbar_plus_nc x (Rbar_opp y).

Lemma nnR_plus_proof (x y : nnR) : (0 <= (x + y))%Re.
Proof. assert (Hx := nnR_pos x); assert (Hy := nnR_pos y); lra. Qed.

Definition nnR_plus (x y : nnR) := mk_nnR _ (nnR_plus_proof x y).

Definition min_conv_val (f g : nnR -> nnRbar) (t : nnR) :=
  Rbar_glb (fun y => exists (u v : nnR),
                       u + v = t /\ y = (f u) + (g v)).

Lemma min_conv_proof f g t : 0 <= (min_conv_val f g t).
Proof.
apply (proj2 (proj2_sig (Rbar_ex_glb _))); intros x [u [v [Ht Hx]]]; rewrite Hx.
replace (Finite 0) with (Rbar_plus 0 0); [|now simpl; rewrite Rplus_0_r].
apply Rbar_plus_le_compat; apply nnRbar_pos.
Qed.

(** min convolution *)
Definition min_conv (f g : nnR -> nnRbar) (t : nnR) :=
  mk_nnRbar _ (min_conv_proof f g t).

Definition contract_eps_val (x : nnR) :=
  if x == nnR0 then nnRbar0 else nnRbar_infty.

Lemma contract_eps_proof x : Rbar_le 0 (contract_eps_val x).
Proof. now unfold contract_eps_val; case eqP; simpl; [intro H; right|]. Qed.

Definition contract_eps (x : nnR) :=
  mk_nnRbar _ (contract_eps_proof x).

Definition min_conv_iter (n : nat) (f : nnR -> nnRbar) :=
  Nat.iter n (min_conv f) contract_eps.

(** min convolution closure *)
Definition min_conv_closure_val (f : nnR -> nnRbar) (t : nnR) :=
  Rbar_glb (fun y => exists n, y = min_conv_iter n f t).

Lemma min_conv_closure_proof f t : Rbar_le 0 (min_conv_closure_val f t).
Proof.
apply (proj2 (proj2_sig (Rbar_ex_glb _))); intros x [n Hx]; rewrite Hx.
now case n; [apply nnRbar_pos|intro n'; apply min_conv_proof].
Qed.


Definition min_conv_closure (f : nnR -> nnRbar) (t : nnR) :=
  mk_nnRbar _ (min_conv_closure_proof f t).

(** ** Data flow: a non decreasing function R+ -> R+ whose value in 0 is 0. *)

Definition cont_left_lub_crit (f : ndf_nnR_nnR) :=
  forall (E : R -> Prop) (l : nnR),
  is_lub_Rbar E l ->
  Lub_Rbar (fun y => exists x, y = f x /\ E x) = f l.

Lemma filtermap_ndf :
  forall {T U : Type } (f : T -> U) (F G : (T -> Prop) -> Prop),
  filter_le F G -> filter_le (filtermap f F) (filtermap f G).
Proof.
  intros T U f F G H P.
  unfold filtermap.
  exact (H (fun x : T => P (f x))).
Qed.
(*
Lemma alt_def_cont_left :
  forall (f : ndf_nnR_nnR), (forall x, filterlim f (fun P => (at_left x (fun y : R => y < 0 \/ P y))) (locally (f x))) <-> cont_left_lub_crit f.
*)

Record dflow := { dflow_f :> ndf_nnR_nnR;
                  dflow_cond_start : (dflow_f nnR0) = nnR0;
                  dflow_cond_cont_left : cont_left_lub_crit dflow_f}.

(** ** Server: a relation between dflow which is left total and verifies D <= A *)

Record server := 
  {server_f :> dflow -> dflow -> Prop;
   server_cond_left_total : forall A, exists D, server_f A D;
   server_cond_dflow : forall A D, server_f A D -> forall t, D t <= A t }.
(* PR : Ça serait pratique d'avoir une notation du genre f <=1 g pour dire
 * forall t : nnR, f t <= g t *)

Record n_server (n : nat) :=
  {n_server_f :> dflow^n -> dflow^n -> Prop;
   n_server_cond_left_total : forall A, exists D, n_server_f A D;
   n_server_cond_dflow :
     forall A D, n_server_f A D -> forall i t, (D i) t <= (A i) t}.

Definition aggregate_server_val {n : nat} (S : n_server n) (As Ds : dflow) :=
  exists A D, S A D /\ forall t, \sum_i ((A i) t : R) = As t
                              /\ \sum_i ((D i) t : R) = Ds t.

Definition f0_nnR_nnR (_ : nnR) : nnR := nnR0.

Lemma ndf_f0_nnR_nnR_proof :
  forall (x y: nnR),
      x <= y -> Rbar_le (f0_nnR_nnR x) (f0_nnR_nnR y).
Proof. now intros; unfold f0_nnR_nnR; simpl; lra. Qed.

Definition ndf_f0_nnR_nnR := Build_ndf_nnR_nnR f0_nnR_nnR ndf_f0_nnR_nnR_proof.

Lemma f0_cond_cont_left : cont_left_lub_crit ndf_f0_nnR_nnR.
Proof. 
  unfold cont_left_lub_crit; intros; simpl.
Admitted.

Definition dflow0 := Build_dflow ndf_f0_nnR_nnR erefl f0_cond_cont_left. 

Definition ndf_sum_dflow_val_val {n : nat} (A : dflow^n) :=
  fun t => \sum_i ((A i) t : R).
(* PR : on pourrait peut être utiliser cette définition dans celle de
 * aggregate_server_val *)

Lemma leq_sum I r (P : pred I) (E1 E2 : I -> R) :
  ((forall i, P i -> E1 i <= E2 i) ->
  \sum_(i <- r | P i) E1 i <= \sum_(i <- r | P i) E2 i)%Re.
Proof. by move=> leE12; (elim/big_ind2: _ ; try lra) => // m1 m2 n1 n2;
          unfold GRing.add; simpl; intros; lra. Qed.

Lemma Rbar_leq_sum I r (P : pred I) (E1 E2 : I -> Rbar) :
  (forall i, P i -> Rbar_le (E1 i) (E2 i)) ->
  Rbar_le (\big[Rbar_plus/Finite 0]_(i <- r | P i) E1 i)
          (\big[Rbar_plus/Finite 0]_(i <- r | P i) E2 i).
Proof. by move=> leE12; (elim/big_ind2: _ ; try (simpl; lra)) => // m1 m2 n1 n2;
          apply Rbar_plus_le_compat. Qed.

Lemma ndf_sum_dflow_val_prop n (A : dflow^n) (t : nnR) :
  0 <= ndf_sum_dflow_val_val A t.
Proof.
  unfold ndf_sum_dflow_val_val.
  assert (H : \sum_(i < n) 0 = 0).
  apply big_rec; try (now trivial).
  now intros; rewrite GRing.add0r.
  rewrite <- H.
  apply leq_sum.
  intros; apply nnR_pos.
Qed.

Definition ndf_sum_dflow_val {n : nat} (A : dflow^n) (t : nnR) :=
  mk_nnR (ndf_sum_dflow_val_val A t) (ndf_sum_dflow_val_prop n A t).

Lemma ndf_sum_dflow n (A : dflow^n) (x y : nnR) :
  x <= y -> Rbar_le (ndf_sum_dflow_val A x) (ndf_sum_dflow_val A y).
Proof.
  intro H.
  unfold ndf_sum_dflow_val; simpl; apply leq_sum.
  now intros; apply ndf_nnR_nnR_prop.
Qed.

Definition sum_dflow_val {n} (A : dflow^n) :=
  Build_ndf_nnR_nnR (ndf_sum_dflow_val A) (ndf_sum_dflow n A).

Lemma sum_dflow_start n (A : dflow^n) : sum_dflow_val A nnR0 = nnR0.
Proof.
  simpl; unfold ndf_sum_dflow_val.
  apply nnR_inj. simpl.
  unfold ndf_sum_dflow_val_val.
  apply big_rec; try (now trivial).
  intros; unfold GRing.add; simpl; rewrite H0; rewrite Rplus_0_r; trivial.
  now rewrite (dflow_cond_start (A i)).
Qed.

Lemma sum_dflow_cont_left n (A : dflow^n) :
  cont_left_lub_crit (sum_dflow_val A).
Proof.
Admitted.

Definition sum_dflow {n} (A : dflow^n) :=
  Build_dflow (sum_dflow_val A) (sum_dflow_start n A) (sum_dflow_cont_left n A).

Lemma aggregate_server_is_left_total n (S : n_server n.+1) (A : dflow) :
  exists D, aggregate_server_val S A D.
Proof.
  destruct (n_server_cond_left_total
              n.+1 S [ffun i : 'I_n.+1 => if i == ord0 then A else dflow0])
    as [Dn H].
  exists (sum_dflow Dn).
  unfold aggregate_server_val.
  exists [ffun i : 'I_n.+1 => if i == ord0 then A else dflow0].
  exists Dn.
  split. trivial.
  intro t.
  split.
  {
    rewrite big_ord_recl ffunE.
    unfold lift, bump; simpl.
    unfold GRing.add; simpl.
    rewrite <- Rplus_0_r.
    apply Rplus_eq_compat_l.
    apply big_rec; try (now trivial).
    intros i x _ Hx.
    now rewrite ffunE Hx Rplus_0_r.
  }
  now simpl.
Qed.

Lemma aggregate_server_cond_dflow_proof n (S : n_server n.+1) (A D : dflow) :
  aggregate_server_val S A D -> forall t, D t <= A t.
Proof.
  intros [A0 [D0 [HA0D0 H]]] t.
  specialize (H t).
  destruct H as [HA HD].
  rewrite <- HA; rewrite <- HD.
  apply leq_sum.
  intros i _.
  assert (HS := n_server_cond_dflow n.+1 S).
  exact (HS A0 D0 HA0D0 i t).
Qed.

Definition aggregate_server {n} (S : n_server n.+1) :=
  Build_server
    (aggregate_server_val S)
    (aggregate_server_is_left_total n S)
    (aggregate_server_cond_dflow_proof n S).

Definition residual_server_val {n} (S : n_server n.+1) i (Ai Di : dflow) :=
  exists A D, S A D /\ A i =1 Ai /\ D i =1 Di.

Lemma residual_server_is_left_total n (S : n_server n.+1) i Ai :
  exists Di : dflow, residual_server_val S i Ai Di.
Proof.
  destruct (n_server_cond_left_total
              _ S [ffun j => if j == i then Ai else dflow0]) as [D HD].
  exists (D i).
  exists [ffun j => if j == i then Ai else dflow0], D.
  now rewrite ffunE eqxx.
Qed.

Lemma residual_server_cond_dflow n (S : n_server n.+1) i Ai Di :
  residual_server_val S i Ai Di -> forall t, Di t <= Ai t.
Proof.
  intros H t.
  destruct H as [A [D [HAD [HA HD]]]].
  specialize (HA t); specialize (HD t).
  rewrite <- HA; rewrite <- HD.
  apply (n_server_cond_dflow _ S A D HAD i).
Qed.

Definition residual_server {n} (S : n_server n.+1) i :=
  Build_server
    (residual_server_val S i)
    (residual_server_is_left_total n S i)
    (residual_server_cond_dflow n S i).

Definition is_min_service_curve (S : server) (beta : nnR -> nnRbar) :=
  forall A D, S A D -> forall t, (min_conv [eta A] beta t) <= (D t).

Definition is_strict_min_service_curve (S : server) (beta : nnR -> nnRbar) :=
  forall A D, S A D ->
  forall u v : nnR, (forall x : nnR, u < x <= u + v -> D x < A x) ->
  Rbar_le (beta v) (D (nnR_plus u v) - D u).