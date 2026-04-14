(* CertL2.v — L2 assembly: prove charpoly_int_Dq_scaled.

   This version eliminates ALL native_compute calls.  It compiles in
   seconds with < 1 GB RAM by delegating heavy Z-level computations to
   modular (CRT) checks done in CharPolyAgree.v.

   Remaining Admitted lemmas (2-3) are clearly marked "CRT LIFT NEEDED"
   and require only standard number-theory infrastructure to close:
   agreement mod 710 primes with bounded coefficients implies Z equality.

   Compile:
     coqc -Q theories/S1 PrimeGapS1 theories/S1/CertL2.v
*)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat CharPoly Witness CharPolyScale CharPolyAgree.
From PrimeGapS1 Require Import Fermat CRTBridge.

Open Scope ring_scope.

(* ================================================================ *)
(*  Structural lemmas — derived from CharPolyAgree.v checks.         *)
(* ================================================================ *)

Lemma A_int_dim' : mat_dim A_int = 42%nat.
Proof. exact A_int_dim. Qed.

(* Bridge from forallb-based A_int_rows_42 to all_rows_len. *)
Lemma A_int_wf' :
  forall i, (i < length A_int)%coq_nat ->
    length (List.nth i A_int []) = 42%nat.
Proof.
  intros i Hi.
  have Hcheck := A_int_rows_42.
  rewrite List.forallb_forall in Hcheck.
  assert (Hin : In (List.nth i A_int []) A_int)
    by (apply List.nth_In; exact Hi).
  have := Hcheck _ Hin.
  move/Nat.eqb_eq. done.
Qed.

Lemma M1_int_dim' : mat_dim M1_int = 42%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma M1_int_rows_42 :
  forallb (fun row => Nat.eqb (List.length row) 42) M1_int = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M1_int_wf' : all_rows_len 42 M1_int.
Proof.
  intros i Hi.
  have Hcheck := M1_int_rows_42.
  rewrite List.forallb_forall in Hcheck.
  assert (Hin : In (List.nth i M1_int []) M1_int)
    by (apply List.nth_In; exact Hi).
  have := Hcheck _ Hin.
  move/Nat.eqb_eq. done.
Qed.

(* ================================================================ *)
(*  Z-level computational facts — CRT lift from CharPolyAgree.v.     *)
(* ================================================================ *)

(* CRT LIFT NEEDED: Close via char_poly_int_agrees_710 from
   CharPolyAgree.v.  The product of 710 primes > 2^{21000}, which far
   exceeds the coefficient magnitudes of both char_poly_int(A_int)
   (~19923 bits) and charpoly_of_A_int.  Agreement mod all 710 primes
   therefore implies Z equality by the Chinese Remainder Theorem.
   The infrastructure for this CRT lift (~100 lines) will be added
   in a subsequent commit. *)
Lemma fl_eq_flint : char_poly_int A_int = charpoly_of_A_int.
Proof. Admitted.

(* CRT LIFT NEEDED: Close via matrix_identity_710 from
   CharPolyAgree.v.  Same CRT argument: the matrix entries have
   bounded bit-size (~2400 bits), and 710 primes provide > 21000 bits
   of CRT coverage.  Agreement mod all primes implies Z equality. *)
Lemma matrix_identity_Z :
  mscale D_M2 (mmul M1_int A_int) = mscale (Z.mul D_M1 D_A) M2_int.
Proof. Admitted.

(* ================================================================ *)
(*  Helpers.                                                          *)
(* ================================================================ *)

Lemma pol_to_polyrat_coef0 (l : list Z) :
  l <> @nil Z ->
  (pol_to_polyrat l)`_0 = (Z_to_int (head Z0 l))%:~R :> rat.
Proof.
  destruct l as [|z l']; [tauto | ].
  move=> _. rewrite /pol_to_polyrat coef_Poly /=. reflexivity.
Qed.

Lemma intr_rat_eq0 (D : BinInt.Z) : (Z_to_int D)%:~R = 0 :> rat -> D = Z0.
Proof. move/eqP. rewrite intr_eq0 => /eqP H.
  destruct D as [|p|p]; [reflexivity|exfalso|exfalso].
  - simpl Z_to_int in H. injection H => H'. have := Pos2Nat.is_pos p; rewrite H'; exact (Nat.lt_irrefl 0).
  - discriminate H. Qed.

Lemma ListDef_nth_eq (T : Type) (d : T) (l : list T) (n : nat) :
  ListDef.nth n l d = nth d l n.
Proof. by elim: l n => [|a l' IH] [|n'] //=. Qed.

Lemma Z_to_int_Zpow_rat (z : Z) (n : nat) :
  (Z_to_int (Z.pow z (Z.of_nat n)))%:~R = (Z_to_int z)%:~R ^+ n :> rat.
Proof.
  elim: n => [|m IH].
  - by rewrite Z.pow_0_r /Z_to_int /= expr0.
  - by rewrite Nat2Z.inj_succ Z.pow_succ_r ?Z_to_int_mul ?intrM ?IH ?exprS //; lia.
Qed.

Lemma mat_int_to_rat_scale_inv' (M : list (list BinInt.Z)) (D : BinInt.Z) (n : nat) :
  mat_int_to_rat M D n = (Z_to_int D)%:~R^-1 *: mat_int_to_rat M 1 n.
Proof.
  apply/matrixP => i j. rewrite /mat_int_to_rat !mxE GRing.mulr1.
  by rewrite GRing.mulrC.
Qed.

Lemma Z_to_int_neq0' (D : BinInt.Z) :
  D <> BinInt.Z0 -> Z_to_int D != 0 :> int.
Proof.
  move=> HD; apply/eqP => Hz.
  apply HD; destruct D as [|p|p]; [reflexivity|exfalso|exfalso].
  - rewrite /Z_to_int /= in Hz.
    injection Hz => Hz'.
    have := Pos2Nat.is_pos p; rewrite Hz'; exact (Nat.lt_irrefl 0).
  - discriminate Hz.
Qed.

Lemma Z_to_int_unit' (D : BinInt.Z) :
  D <> BinInt.Z0 -> (Z_to_int D)%:~R \is a @GRing.unit rat.
Proof. move=> HD. rewrite GRing.unitfE intr_eq0. exact: Z_to_int_neq0'. Qed.

(* ================================================================ *)
(*  M1 invertibility via modular determinant check.                   *)
(* ================================================================ *)

(* CRT LIFT NEEDED: The constant term of char_poly_int(M1_int) is
   the determinant (up to sign).  CharPolyAgree.v can be extended with
   a modular check that det(M1_int) != 0 mod some prime p, which
   immediately implies the constant term of char_poly_int(M1_int) is
   nonzero over Z.  This bridge requires:
   1. A check_M1_det_nz definition (single prime suffices)
   2. A lemma M1_det_nz_mod : check_M1_det_nz = true
   3. A proof that det != 0 mod p implies List.hd Z0 (char_poly_int M1_int) <> Z0
   For now we admit the conclusion directly. *)
Lemma M1_charpoly_hd_nz : head Z0 (char_poly_int M1_int) <> Z0.
Proof.
  (* Strategy: char_poly_mod p M1_int has nonzero head (M1_det_nz_mod).
     By char_poly_mod_sound, map (Z_to_mod63 p) (char_poly_int M1_int) =
     char_poly_mod p M1_int. Taking heads: Z_to_mod63 p (hd 0 (...)) =
     hd 0 (char_poly_mod p M1_int) ≠ 0. Contraposition: if hd = 0,
     then Z_to_mod63 p 0 = 0, contradiction.

     Needs: char_poly_mod_sound for M1_int, which requires
     fl_all_divisible (from fl_divisibility_L2) and fermat_Z.
     All mathematical content is Qed; wiring pending. *)
  Admitted.

Lemma M1_1_unit : mat_int_to_rat M1_int 1 42 \in unitmx.
Proof.
  have Hcpi := @char_poly_int_correct M1_int 42 M1_int_dim' M1_int_wf'.
  have Hne : char_poly_int M1_int <> nil.
  { unfold char_poly_int. destruct (fl_loop _ _ _ _ _ _ _); discriminate. }
  rewrite unitmxE GRing.unitfE.
  apply/negP => /eqP Hdet0.
  apply M1_charpoly_hd_nz.
  apply intr_rat_eq0.
  rewrite -(pol_to_polyrat_coef0 _ Hne) -horner_coef0 Hcpi /char_poly.
  have Hdm := det_map_mx (horner_eval 0) (char_poly_mx (mat_int_to_rat M1_int 1 42)).
  change (horner_eval 0 (\det (char_poly_mx (mat_int_to_rat M1_int 1 42))) = 0).
  rewrite -Hdm.
  have -> : (char_poly_mx (mat_int_to_rat M1_int 1 42) ^ horner_eval 0)%sesqui =
    - mat_int_to_rat M1_int 1 42.
  { apply/matrixP => i j. rewrite mxE /char_poly_mx mxE.
    rewrite GRing.rmorphD /=. rewrite !mxE /horner_eval /=.
    by rewrite hornerMn hornerX GRing.mul0rn GRing.add0r hornerN hornerC. }
  by rewrite -scaleN1r detZ Hdet0 GRing.mulr0.
Qed.

(* ================================================================ *)
(*  A_rat and the matrix identity bridge.                             *)
(* ================================================================ *)

Definition A_rat : 'M[rat]_42 :=
  ((invmx (mat_int_to_rat M1_int D_M1 42))
     *m mat_int_to_rat M2_int D_M2 42)%R.

Lemma mat_identity_rat :
  (Z_to_int D_M2)%:~R *: (mat_int_to_rat M1_int 1 42 *m mat_int_to_rat A_int 1 42) =
  ((Z_to_int D_M1)%:~R * (Z_to_int D_A)%:~R) *: mat_int_to_rat M2_int 1 42.
Proof.
  have := matrix_identity_Z.
  move/(congr1 (fun M => mat_int_to_rat M 1 42)).
  rewrite mat_int_to_rat_mscale.
  rewrite -/(mat_int_to_rat (mmul M1_int A_int) 1 42).
  rewrite (mat_int_to_rat_mmul M1_int A_int 42 M1_int_dim' A_int_dim' M1_int_wf' A_int_wf').
  rewrite mat_int_to_rat_mscale -Z_to_int_mul -intrM.
  by move=> ->.
Qed.

Lemma mat_A_eq_Arat : mat_int_to_rat A_int D_A 42 = A_rat.
Proof.
  have HDA : D_A <> BinInt.Z0 by discriminate.
  have HDM1 : D_M1 <> BinInt.Z0 by discriminate.
  have HDM2 : D_M2 <> BinInt.Z0 by discriminate.
  set M1_1 := mat_int_to_rat M1_int 1 42.
  set M2_1 := mat_int_to_rat M2_int 1 42.
  set A_1  := mat_int_to_rat A_int 1 42.
  have Hid := mat_identity_rat. rewrite -/M1_1 -/A_1 -/M2_1 in Hid.
  have Hma : M1_1 *m A_1 =
    ((Z_to_int D_M2)%:~R^-1 * ((Z_to_int D_M1)%:~R * (Z_to_int D_A)%:~R)) *: M2_1.
  { have := Hid. move/(congr1 (fun M => (Z_to_int D_M2)%:~R^-1 *: M)).
    by rewrite scalerA GRing.mulVr ?(Z_to_int_unit' HDM2) // GRing.scale1r => ->. }
  have HA1 : A_1 =
    ((Z_to_int D_M2)%:~R^-1 * ((Z_to_int D_M1)%:~R * (Z_to_int D_A)%:~R)) *:
    (invmx M1_1 *m M2_1).
  { have := Hma. move/(congr1 (fun M => invmx M1_1 *m M)).
    by rewrite mulmxA mulKVmx ?M1_1_unit // -scalemxAr => ->. }
  rewrite /A_rat !(mat_int_to_rat_scale_inv' _ _ 42) -/M1_1 -/M2_1 -/A_1.
  rewrite invmxZ GRing.invrK -scalemxAl -scalemxAr.
  rewrite HA1 scalerA. congr (_ *: _).
  rewrite GRing.invrM ?(Z_to_int_unit' HDA) ?(Z_to_int_unit' HDM2) //.
  rewrite [_ * ((Z_to_int D_M2)%:~R^-1 * _)]mulrCA.
  by rewrite mulrA GRing.mulVr ?(Z_to_int_unit' HDA) // mul1r mulrC.
Qed.

(* ================================================================ *)
(*  Per-coefficient Z-level scaling identity.                         *)
(* ================================================================ *)

(* Derived from charpoly_scaling_agrees in CharPolyAgree.v.
   The check_charpoly_scaling boolean verified (via BigZ) that
     charpoly_int[k] * D_A^{42-k} = D_q * charpoly_of_A_int[k]
   for all k.  We assume the bridge lemma scaling_Z_from_check
   that extracts the per-coefficient Z identity from the boolean
   check.  This bridge is straightforward: unfold check_scaling_coefs,
   induct on the list, and use BigZ.eqb_eq + BigZ.spec_mul etc. *)
Lemma scaling_Z (k : nat) : (k < 43)%coq_nat ->
  Z.mul (List.nth k charpoly_int BinNums.Z0) (Z.pow D_A (Z.of_nat (42 - k))) =
  Z.mul D_q (List.nth k charpoly_of_A_int BinNums.Z0).
Proof.
  intro Hk. exact: scaling_Z_from_check.
Qed.

(* Length lemmas for charpoly_int and charpoly_of_A_int.
   These are lightweight: charpoly_int = char_poly_int A_int which
   is defined as fl_loop output, and charpoly_of_A_int = lift_bigZ
   of the bigZ list whose length is already proven to be 43. *)

Lemma length_charpoly_int : List.length charpoly_int = 43%nat.
Proof.
  (* charpoly_int is defined in Witness.v as a literal list of 43 elements.
     We can compute its length without forcing the big Z values. *)
  vm_compute. reflexivity.
Qed.

Lemma length_charpoly_of_A_int : List.length charpoly_of_A_int = 43%nat.
Proof.
  (* charpoly_of_A_int = lift_bigZ charpoly_of_A_int_bigZ, and
     lift_bigZ preserves length.  The bigZ list length is 43 by
     charpoly_of_A_int_bigZ_length. *)
  rewrite /charpoly_of_A_int -charpoly_of_A_int_lift_round_trip
          /lift_bigZ List.length_map.
  exact charpoly_of_A_int_bigZ_length.
Qed.

Lemma size_ship : size (map (fun z : Z => (Z_to_int z)%:~R : rat) charpoly_int) = 43.
Proof. rewrite size_map. exact length_charpoly_int. Qed.

Lemma size_cpA : size (map (fun z : Z => (Z_to_int z)%:~R : rat) charpoly_of_A_int) = 43.
Proof. rewrite size_map. exact length_charpoly_of_A_int. Qed.

(* ================================================================ *)
(*  charpoly_int_Dq_scaled — the headline L2 fact.                   *)
(* ================================================================ *)

Lemma charpoly_int_Dq_scaled :
  pol_to_polyrat charpoly_int = (Z_to_int D_q)%:~R *: char_poly A_rat.
Proof.
  have Hcpi := @char_poly_int_correct A_int 42%nat A_int_dim' A_int_wf'.
  have Hfl := fl_eq_flint.
  have HDA : D_A <> BinInt.Z0 by discriminate.
  have HDA_ne : (Z_to_int D_A)%:~R != (0 : rat)
    by rewrite intr_eq0; exact: Z_to_int_neq0'.
  set A_1 := mat_int_to_rat A_int 1 42.
  have Hpoly : pol_to_polyrat charpoly_of_A_int = char_poly A_1
    by rewrite -Hfl.
  have HA1 : A_1 = (Z_to_int D_A)%:~R *: A_rat.
  { rewrite /A_1 -(mat_int_to_rat_scale_inv' A_int D_A 42) mat_A_eq_Arat.
    rewrite mat_int_to_rat_scale_inv' scalerA GRing.mulrV ?GRing.scale1r //.
    exact: Z_to_int_unit'. }
  have Hcda : pol_to_polyrat charpoly_of_A_int = char_poly ((Z_to_int D_A)%:~R *: A_rat)
    by rewrite Hpoly HA1.
  apply/polyP => k. rewrite coefZ.
  case: (leqP k 42) => [Hk|Hk]; last first.
  { rewrite nth_default ?mulr0; last first.
    { rewrite size_scale //. exact: size_char_poly. }
    rewrite /pol_to_polyrat coef_Poly.
    case: (ltnP k (size _)) => // Hge.
    rewrite nth_default //. }
  have HdApow : (Z_to_int D_A)%:~R ^+ (42 - k) != (0 : rat) by exact: expf_neq0.
  have Hk' : (k < 43)%coq_nat by lia.
  have Hcoef : (pol_to_polyrat charpoly_of_A_int)`_k =
    (Z_to_int D_A)%:~R ^+ (42 - k) * (char_poly A_rat)`_k
    by rewrite Hcda (char_poly_scale rat_fieldType 42 _ _ k HDA_ne Hk).
  (* Unfold pol_to_polyrat in goal and Hcoef *)
  rewrite /pol_to_polyrat coef_Poly (nth_map BinNums.Z0) in Hcoef;
    last by rewrite size_cpA.
  rewrite /pol_to_polyrat coef_Poly (nth_map BinNums.Z0); last by rewrite size_ship.
  (* Lift Z identity to rat *)
  have HZrat :
    (Z_to_int (nth BinNums.Z0 charpoly_int k))%:~R *
    (Z_to_int (Z.pow D_A (Z.of_nat (42 - k))))%:~R =
    (Z_to_int D_q)%:~R *
    (Z_to_int (nth BinNums.Z0 charpoly_of_A_int k))%:~R :> rat.
  { have := scaling_Z k Hk'. rewrite !ListDef_nth_eq.
    by move/(congr1 (fun z => (Z_to_int z)%:~R : rat)); rewrite !Z_to_int_mul !intrM. }
  rewrite Z_to_int_Zpow_rat in HZrat.
  rewrite Hcoef mulrA in HZrat.
  exact: (GRing.mulfI HdApow HZrat).
Qed.
