(* ============================================================== *)
(*  CRTSigns.v                                                      *)
(*                                                                  *)
(*  Machine-verify that the sign vectors (signs_at_x0, signs_at_inf *)
(*  from Witness.v) agree with signs computed from the shipped       *)
(*  Sturm chain data in WitnessChain.v.                              *)
(*                                                                  *)
(*  Strategy: evaluate directly in BigZ arithmetic (native word-     *)
(*  arrays, fast under vm_compute), then bridge to the stdlib Z      *)
(*  formulation via BigZ spec lemmas.                                *)
(*                                                                  *)
(*  Total vm_compute time: ~1 second for all 43 chain entries.       *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
From Bignums Require Import BigZ.
Import ListNotations.
From PrimeGapS1 Require Import IntPoly SignChain Witness WitnessChain Recompose.

Open Scope Z_scope.

(* ============================================================== *)
(*  Section 1: BigZ sign and polynomial helpers                     *)
(* ============================================================== *)

(* Sign of a BigZ value. Uses BigZ.compare which operates directly
   on the word-array representation -- no conversion to stdlib Z. *)
Definition sign_bigZ (x : BigZ.t_) : Z :=
  match BigZ.compare x 0%bigZ with
  | Lt => (-1)%Z
  | Eq => 0%Z
  | Gt => 1%Z
  end.

(* Leading coefficient of a BigZ polynomial (low-to-high order). *)
Fixpoint plead_bigZ_aux (p : list BigZ.t_) (acc : BigZ.t_) : BigZ.t_ :=
  match p with
  | [] => acc
  | x :: xs =>
      if BigZ.eqb x 0%bigZ then plead_bigZ_aux xs acc
      else plead_bigZ_aux xs x
  end.

Definition plead_bigZ (p : list BigZ.t_) : BigZ.t_ :=
  plead_bigZ_aux p 0%bigZ.

(* Horner evaluation of a low-to-high BigZ polynomial at num/den.
   Returns (den^(length p) * p(num/den), den^(length p)).
   Mirrors IntPoly.peval_at_rat_aux but in BigZ arithmetic. *)
Fixpoint peval_bigZ_aux (p : list BigZ.t_) (num den : BigZ.t_)
  : (BigZ.t_ * BigZ.t_) :=
  match p with
  | [] => (0%bigZ, 1%bigZ)
  | a :: rest =>
      let '(rest_val, rest_den_pow) := peval_bigZ_aux rest num den in
      let dp := BigZ.mul den rest_den_pow in
      (BigZ.add (BigZ.mul a dp) (BigZ.mul num rest_val), dp)
  end.

Definition peval_bigZ (p : list BigZ.t_) (num den : BigZ.t_) : BigZ.t_ :=
  fst (peval_bigZ_aux p num den).

(* ============================================================== *)
(*  Section 2: BigZ computation — the fast vm_compute checks        *)
(* ============================================================== *)

Lemma signs_at_inf_bigZ :
  List.map (fun p => sign_bigZ (plead_bigZ p)) sturm_chain_bigZ
  = signs_at_inf.
Proof. vm_compute. reflexivity. Qed.

Lemma signs_at_x0_bigZ :
  List.map (fun p => sign_bigZ (peval_bigZ p 4%bigZ 105%bigZ))
           sturm_chain_bigZ
  = signs_at_x0.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  Section 3: Bridge — BigZ operations agree with Z operations     *)
(* ============================================================== *)

(* plead on BigZ agrees with plead on Z after lift. *)
Lemma plead_bigZ_aux_spec :
  forall p acc,
    BigZ.to_Z (plead_bigZ_aux p acc) = plead_aux (List.map BigZ.to_Z p) (BigZ.to_Z acc).
Proof.
  induction p as [| x xs IH]; intros acc; simpl.
  - reflexivity.
  - rewrite BigZ.spec_eqb. change (BigZ.to_Z 0%bigZ) with 0%Z.
    destruct (BigZ.to_Z x =? 0)%Z eqn:E; apply IH.
Qed.

Lemma plead_bigZ_spec :
  forall p,
    BigZ.to_Z (plead_bigZ p) = plead (List.map BigZ.to_Z p).
Proof.
  intro p. unfold plead_bigZ, plead.
  rewrite plead_bigZ_aux_spec. change (BigZ.to_Z 0%bigZ) with 0%Z.
  reflexivity.
Qed.

(* sign_bigZ agrees with sgn_Z after to_Z. *)
Lemma sign_bigZ_spec :
  forall x, sign_bigZ x = sgn_Z (BigZ.to_Z x).
Proof.
  intro x. unfold sign_bigZ, sgn_Z.
  rewrite BigZ.spec_compare. change (BigZ.to_Z 0%bigZ) with 0%Z.
  destruct (BigZ.to_Z x) eqn:E; simpl; reflexivity.
Qed.

(* peval_bigZ_aux agrees with peval_at_rat_aux after to_Z. *)
Lemma peval_bigZ_aux_spec :
  forall p num den,
    let '(v, d) := peval_bigZ_aux p (BigZ.of_Z num) (BigZ.of_Z den) in
    let '(v', d') := peval_at_rat_aux (List.map BigZ.to_Z p) num den in
    BigZ.to_Z v = v' /\ BigZ.to_Z d = d'.
Proof.
  induction p as [| a rest IH]; intros num den; simpl.
  - split; vm_compute; reflexivity.
  - specialize (IH num den).
    destruct (peval_bigZ_aux rest (BigZ.of_Z num) (BigZ.of_Z den))
      as [rv rd] eqn:Ebigz.
    destruct (peval_at_rat_aux (List.map BigZ.to_Z rest) num den)
      as [rv' rd'] eqn:Ez.
    destruct IH as [Hv Hd].
    split.
    + rewrite BigZ.spec_add. rewrite !BigZ.spec_mul.
      rewrite Hv. rewrite Hd. rewrite !BigZ.spec_of_Z. ring.
    + rewrite BigZ.spec_mul. rewrite Hd.
      rewrite BigZ.spec_of_Z. reflexivity.
Qed.

(* ============================================================== *)
(*  Section 4: Derive the Z-level statements                        *)
(*                                                                  *)
(*  These match the signatures expected by downstream consumers.    *)
(* ============================================================== *)

Lemma signs_at_inf_shipped :
  signs_at_inf
  = List.map sign_at_pinf WitnessChain.sturm_chain.
Proof.
  rewrite <- signs_at_inf_bigZ.
  unfold WitnessChain.sturm_chain, sign_at_pinf, lift_bigZ2.
  rewrite List.map_map.
  apply List.map_ext. intro p.
  rewrite sign_bigZ_spec. f_equal. apply plead_bigZ_spec.
Qed.

Lemma signs_at_x0_shipped :
  signs_at_x0
  = List.map (fun p => sign_at_rat p 4 105) WitnessChain.sturm_chain.
Proof.
  rewrite <- signs_at_x0_bigZ.
  unfold WitnessChain.sturm_chain, sign_at_rat, lift_bigZ2.
  rewrite List.map_map.
  apply List.map_ext. intro p.
  rewrite sign_bigZ_spec. f_equal.
  unfold peval_at_rat, peval_bigZ, lift_bigZ.
  change 4%bigZ with (BigZ.of_Z 4). change 105%bigZ with (BigZ.of_Z 105).
  pose proof (peval_bigZ_aux_spec p 4 105) as H.
  destruct (peval_bigZ_aux p (BigZ.of_Z 4) (BigZ.of_Z 105)) as [v d] eqn:Ep.
  destruct (peval_at_rat_aux (List.map BigZ.to_Z p) 4 105) as [v' d'] eqn:Ez.
  simpl. destruct H as [Hv _]. exact Hv.
Qed.
