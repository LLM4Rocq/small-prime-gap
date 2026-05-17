(* ==================================================================
   AbstractPencilHelper.v

   Per-cell rational identity used by `CertPencil.pencil_rat_scaled_eq`
   to lift the integer cross-multiplication
       D_M1 * D_M2 * pencil_int_clean[i,j]
         = D_pencil_clean * (4*D_M2*M1[i,j] - 105*D_M1*M2[i,j])
   (shipped via `PencilCleanGrid.pencil_clean_match_Z`) into the
   rat-matrix identity
       K *: (lambda_q *: M1_rat - M2_rat) = mat_int_to_rat pencil_int_clean 1 42.

   Isolated into its own file so that `CertPencil.v` doesn't have to
   load `mathcomp.algebra_tactics` (which `field` requires) — using
   `field` in the heavy 'M[rat]_42 context of CertPencil adds several
   GB of RSS to the compile.  Here we prove the cell-level identity
   over abstract `Z` integers, so `field` is invoked exactly once.
   ================================================================== *)

From Stdlib Require Import ZArith.
From mathcomp Require Import all_boot all_algebra.
From mathcomp.algebra_tactics Require Import ring.
From PrimeGapS1 Require Import IntMat CharPoly.   (* Z_to_int + mat_get + mat_int_to_rat *)

Import GRing.Theory.
Local Open Scope ring_scope.

(* Z-level subtraction unfolded into add+opp at the rat level. *)
Lemma Z_to_int_sub_intrR (a b : Z) :
  ((Z_to_int (BinInt.Z.sub a b))%:~R : rat)
  = (Z_to_int a)%:~R - (Z_to_int b)%:~R.
Proof. by rewrite -BinInt.Z.add_opp_r Z_to_int_add Z_to_int_opp intrD intrN. Qed.

(* The per-cell identity, purely scalar (no matrix cells in scope). *)
Lemma pencil_cell_eq
  (Mij Nij Pij d1 d2 Dpc : Z)
  (Hd1 : (Z_to_int d1)%:~R != 0 :> rat)
  (Hd2 : (Z_to_int d2)%:~R != 0 :> rat)
  (Hxm : BinInt.Z.mul (BinInt.Z.mul d1 d2) Pij =
         BinInt.Z.mul Dpc (BinInt.Z.sub (BinInt.Z.mul (BinInt.Z.mul 4 d2) Mij)
                                        (BinInt.Z.mul (BinInt.Z.mul 105 d1) Nij))) :
  let M := (Z_to_int Mij)%:~R : rat in
  let N := (Z_to_int Nij)%:~R : rat in
  let P := (Z_to_int Pij)%:~R : rat in
  let D1 := (Z_to_int d1)%:~R : rat in
  let D2 := (Z_to_int d2)%:~R : rat in
  let DP := (Z_to_int Dpc)%:~R : rat in
  let K  := ((Z_to_int (BinInt.Z.mul Dpc 105))%:~R : rat) in
  let lq : rat := 4%:Q / 105%:Q in
  K * (lq * (M / D1) - N / D2) = P / 1.
Proof.
move=> M N P D1 D2 DP K lq.
have HK : K = DP * 105%:Q.
{ rewrite /K /DP Z_to_int_mul intrM /=. by congr (_ * _). }
have Hxm_rat :
  D1 * D2 * P = DP * (4%:Q * D2 * M - 105%:Q * D1 * N).
{ have HZ := f_equal (fun z => (Z_to_int z)%:~R : rat) Hxm.
  cbv beta in HZ.
  rewrite !Z_to_int_mul !intrM in HZ.
  rewrite Z_to_int_sub_intrR !Z_to_int_mul !intrM /= in HZ.
  by exact HZ. }
rewrite HK.
have H105 : (105%:Q : rat) != 0 by rewrite intr_eq0.
rewrite divr1.
have HD1D2 : D1 * D2 != 0 by rewrite mulf_neq0.
apply: (mulfI HD1D2).
rewrite mulrA Hxm_rat.
rewrite /lq.
field.
by rewrite Hd1 Hd2.
Qed.

(* ==================================================================
   Generic matrix-level bridge: given the per-entry cross-check
   `D1 * D2 * P[i,j] = Dpc * (4*D2*M[i,j] - 105*D1*N[i,j])`
   for every (i, j), the rat-matrix identity
   `K *: (lq *: (mat_int_to_rat M D1 n) - mat_int_to_rat N D2 n) =
    mat_int_to_rat P 1 n`
   holds, where K = (Dpc * 105)%:~R and lq = 4/105.

   We prove the bridge over abstract `'M[rat]_n` Variables so the
   mathcomp matrix elaboration cost stays here (where there's no
   concrete 'M[rat]_42 in scope) rather than in CertPencil.v.
   ================================================================== *)

Section MatrixBridge.

Variable n : nat.
Variables (Mmat Nmat Pmat : mat).
Variables (d1 d2 Dpc : Z).
Hypothesis Hd1 : (Z_to_int d1)%:~R != 0 :> rat.
Hypothesis Hd2 : (Z_to_int d2)%:~R != 0 :> rat.

Hypothesis Hcross :
  forall (i j : 'I_n),
    BinInt.Z.mul (BinInt.Z.mul d1 d2)
      (mat_get Pmat (nat_of_ord i) (nat_of_ord j)) =
    BinInt.Z.mul Dpc
      (BinInt.Z.sub
        (BinInt.Z.mul (BinInt.Z.mul 4 d2)
          (mat_get Mmat (nat_of_ord i) (nat_of_ord j)))
        (BinInt.Z.mul (BinInt.Z.mul 105 d1)
          (mat_get Nmat (nat_of_ord i) (nat_of_ord j)))).

Lemma pencil_matrix_bridge :
  ((Z_to_int (BinInt.Z.mul Dpc 105))%:~R : rat) *:
    ((4%:Q / 105%:Q : rat) *: mat_int_to_rat Mmat d1 n
       - mat_int_to_rat Nmat d2 n) =
  mat_int_to_rat Pmat 1 n.
Proof.
apply/matrixP => i j.
rewrite ![in LHS]mxE.
rewrite [in RHS]mxE.
exact: (pencil_cell_eq _ _ _ _ _ _ Hd1 Hd2 (Hcross i j)).
Qed.

End MatrixBridge.
