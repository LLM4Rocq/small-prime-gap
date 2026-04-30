(* ============================================================== *)
(*  MaynardSpecBridge.v                                             *)
(*                                                                  *)
(*  Bridge between PART A (rat-level) and PART B (Z-level) of       *)
(*  MaynardSpec.v.  Each operation in PART A has a directly         *)
(*  corresponding operation in PART B, so each bridge is a small    *)
(*  structural induction.                                           *)
(*                                                                  *)
(*  Headlines:                                                      *)
(*    M1_spec_rat_eq i j  :  M1_spec_ij i j = qfrac (m1_num_den_at i j)*)
(*    M2_spec_rat_eq i j  :  M2_spec_ij i j = qfrac (m2_num_den_at i j)*)
(*                                                                  *)
(*  This file is a leaf in the dependency DAG (Cert.v does not      *)
(*  import it) and is independent of MaynardVerify.v's load-bearing *)
(*  Z-level cross-check.  Its purpose is to certify in the kernel   *)
(*  that the rat-level paper-form spec and the Z-level computational*)
(*  spec encode the same closed forms.                              *)
(* ============================================================== *)

From Stdlib Require Import ZArith List Lia Znumtheory.
Import ListNotations.

From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import
  MaynardFactQ MaynardBasis MaynardSpec CharPoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ============================================================== *)
(*  Layer 0: factorial bridge.                                      *)
(* ============================================================== *)

(* `factZ n = Z.of_nat n!`.  Pure structural induction. *)
Lemma factZ_eq_Z_of_nat (n : nat) :
  factZ n = BinInt.Z.of_nat n`!.
Proof.
  elim: n => [//|n IH] /=.
  rewrite IH factS.
  by rewrite -multE Nat2Z.inj_mul.
Qed.

(* `Z_to_int (factZ n) = Posz n!`. *)
Lemma Z_to_int_factZ (n : nat) :
  Z_to_int (factZ n) = Posz n`!.
Proof. by rewrite factZ_eq_Z_of_nat Z_to_int_of_nat. Qed.

(* `factZ n` lifted to `rat` equals `factQ n`. *)
Lemma factZ_to_rat (n : nat) :
  ((Z_to_int (factZ n))%:~R : rat) = factQ n.
Proof. by rewrite Z_to_int_factZ /factQ. Qed.

(* nat-level: m! divides n! when m <= n.  Standard induction. *)
Lemma fact_dvd_fact (m n : nat) :
  (m <= n)%nat -> (m`! %| n`!)%nat.
Proof.
  elim: n => [|n IH] H.
  - by rewrite leqn0 in H; rewrite (eqP H).
  - rewrite factS.
    case: (leqP m n) => Hmn.
    + apply: dvdn_mull; exact: (IH Hmn).
    + have -> : m = n.+1 by apply/eqP; rewrite eqn_leq H Hmn.
      exact: dvdnn.
Qed.

(* Z.of_nat preserves divisibility from nat to Z. *)
Lemma Z_of_nat_dvd (a b : nat) :
  (a %| b)%nat -> (Z.of_nat a | Z.of_nat b)%Z.
Proof.
  move=> /dvdnP[k Hk]. exists (Z.of_nat k).
  by rewrite Hk -multE Nat2Z.inj_mul Z.mul_comm.
Qed.

(* Z-level: factZ x divides factZ (2*x) for any nat x. *)
Lemma factZ_dvd_double (x : nat) :
  (factZ x | factZ (2 * x)%nat)%Z.
Proof.
  rewrite !factZ_eq_Z_of_nat.
  apply: Z_of_nat_dvd; apply: fact_dvd_fact.
  by rewrite leq_pmull.
Qed.

(* `factZ n` is strictly positive. *)
Lemma factZ_pos (n : nat) : Z.lt 0 (factZ n).
Proof.
  rewrite factZ_eq_Z_of_nat.
  have /ltP H := fact_gt0 n.
  lia.
Qed.

(* `Z_to_int` of a strictly-positive Z is nonzero in int. *)
Lemma Z_to_int_pos_nz (z : Z) : Z.lt 0 z -> Z_to_int z != 0.
Proof.
  case: z => [|p _|p H] //.
  rewrite Z_to_int_pos_pos eqz_nat -lt0n.
  apply/ltP; exact: Pos2Nat.is_pos.
Qed.

(* Lifted to rat: ((Z_to_int z)%:~R : rat) is nonzero when z > 0. *)
Lemma Z_to_int_pos_rat_nz (z : Z) :
  Z.lt 0 z -> ((Z_to_int z)%:~R : rat) != 0.
Proof.
  by move=> /Z_to_int_pos_nz; rewrite intr_eq0.
Qed.

(* Generic integer-division-is-exact bridge: when `b | a` and `b > 0`,
   the integer division `a / b` lifts to the rat division
   `(a : rat) / (b : rat)`. *)
Lemma Z_to_int_div_exact (a b : Z) :
  Z.lt 0 b -> (b | a)%Z ->
  ((Z_to_int (a / b))%:~R : rat)
  = (Z_to_int a)%:~R / (Z_to_int b)%:~R.
Proof.
  move=> Hbpos Hdvd.
  have Hnz : ((Z_to_int b)%:~R : rat) != 0 by exact: Z_to_int_pos_rat_nz.
  apply: (canRL (mulfK Hnz)).
  rewrite -intrM -Z_to_int_mul Z.mul_comm.
  by rewrite -Zdivide_Zdiv_eq.
Qed.

(* ============================================================== *)
(*  Layer 1: dblratZ, prod_dblratZ, cffZ                            *)
(* ============================================================== *)

Lemma dblratZ_to_rat (x : nat) :
  ((Z_to_int (dblratZ x))%:~R : rat)
  = factQ (2 * x) / factQ x.
Proof.
  rewrite /dblratZ Z_to_int_div_exact ?factZ_to_rat //.
  - exact: factZ_pos.
  - exact: factZ_dvd_double.
Qed.

Lemma prod_dblratZ_to_rat (a : list nat) :
  ((Z_to_int (prod_dblratZ a))%:~R : rat)
  = \prod_(x <- a) (factQ (2 * x) / factQ x).
Proof.
  elim: a => [|x a IH] /=.
  - by rewrite Z_to_int_1_rat big_nil.
  - rewrite Z_to_int_mul intrM dblratZ_to_rat IH.
    by rewrite big_cons.
Qed.

(* `cffZ a = prod_dblratZ a` definitionally; bridge is direct. *)
Lemma cffZ_to_rat (a : list nat) :
  ((Z_to_int (cffZ a))%:~R : rat) = cff a.
Proof.
  by rewrite /cffZ /cff prod_dblratZ_to_rat.
Qed.

(* ============================================================== *)
(*  Layer 2: binZ                                                   *)
(* ============================================================== *)

(* nat-level: k! * (n-k)! divides n! when k <= n.  Standard via
   bin_fact: 'C(n,k) * (k! * (n-k)!) = n!. *)
Lemma bin_dvd_fact (n k : nat) :
  (k <= n)%nat -> (k`! * (n - k)`! %| n`!)%nat.
Proof.
  move=> Hkn. apply/dvdnP. exists 'C(n,k).
  by rewrite -(bin_fact Hkn).
Qed.

(* Z-level lift: factZ k * factZ (n-k) divides factZ n. *)
Lemma factZ_factZ_dvd (n k : nat) :
  (k <= n)%nat ->
  (factZ k * factZ (n - k)%nat | factZ n)%Z.
Proof.
  move=> Hkn.
  rewrite !factZ_eq_Z_of_nat -Nat2Z.inj_mul.
  apply: Z_of_nat_dvd. exact: bin_dvd_fact.
Qed.

Lemma factZ_factZ_pos (n k : nat) :
  Z.lt 0 (factZ k * factZ (n - k)%nat).
Proof.
  apply: Z.mul_pos_pos; exact: factZ_pos.
Qed.

(* binQ n k = factQ n / (factQ k * factQ (n-k)) when k <= n. *)
Lemma binQ_factQ (n k : nat) :
  (k <= n)%nat ->
  binQ n k = factQ n / (factQ k * factQ (n - k)%nat).
Proof.
  move=> Hkn.
  have Hnz : factQ k * factQ (n - k)%nat != 0
    by rewrite mulf_neq0 ?factQ_nz.
  apply: (canRL (mulfK Hnz)).
  rewrite /binQ /factQ -natrM -natrM.
  apply/eqP. rewrite Num.Theory.eqr_nat. apply/eqP.
  exact: bin_fact.
Qed.

Lemma binZ_to_rat (n k : nat) :
  (k <= n)%nat ->
  ((Z_to_int (binZ n k))%:~R : rat) = binQ n k.
Proof.
  move=> Hkn.
  rewrite /binZ.
  have -> : Nat.leb k n = true by apply/Nat.leb_le; apply/leP.
  rewrite Z_to_int_div_exact;
    [|exact: factZ_factZ_pos|exact: factZ_factZ_dvd].
  rewrite Z_to_int_mul intrM !factZ_to_rat.
  by rewrite -binQ_factQ.
Qed.
