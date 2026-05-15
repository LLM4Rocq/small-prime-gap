(* ==================================================================
   CRTPencilChecksProof.v

   The two heavy vm_compute discharges of the 710-prime per-prime
   modular agreement check between:

     List.nth 0 (char_poly_mod p M1_int)          and  det_M1_int_value mod p
     List.nth 0 (char_poly_mod p pencil_mat_int)  and  D_pencil_int_value mod p

   for each p in `crt_primes_all`.  Each is a Uint63 native-arithmetic
   compute over 710 primes x 42x42 mod-p char_poly, plus 710 mod-p
   reductions of the shipped Z literals.

   Compile time: ~12 min (dominated by the pencil-side char_poly_mod
   over 800-bit-entry matrix).
   ================================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.

From Stdlib Require Import Uint63.

From PrimeGapS1 Require Import IntMat Witness CharPoly.
From PrimeGapS1 Require Import ModularArith CRTBridge.
From PrimeGapS1.CharPolyAgree Require Import Def.   (* crt_primes_all *)
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import CertPencil.          (* pencil_mat_int *)

Open Scope Z_scope.

(* Per-prime check definitions. *)

Definition check_M1_det_at (p : Uint63.int) : bool :=
  Uint63.eqb (List.nth 0 (char_poly_mod p M1_int) 0%uint63)
             (Z_to_mod63 p det_M1_int_value).

Definition check_pencil_det_at (p : Uint63.int) : bool :=
  Uint63.eqb (List.nth 0 (char_poly_mod p pencil_mat_int) 0%uint63)
             (Z_to_mod63 p D_pencil_int_value).

Definition check_M1_det_710 : bool :=
  List.forallb check_M1_det_at crt_primes_all.

Definition check_pencil_det_710 : bool :=
  List.forallb check_pencil_det_at crt_primes_all.

(* The two heavy vm_compute lemmas. *)

Lemma check_M1_det_710_true : check_M1_det_710 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma check_pencil_det_710_true : check_pencil_det_710 = true.
Proof. vm_compute. reflexivity. Qed.
