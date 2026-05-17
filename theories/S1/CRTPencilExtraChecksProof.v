(* ==================================================================
   CRTPencilExtraChecksProof.v

   Per-prime modular agreement check for `pencil_mat_int` over the
   500 extra primes added in `CRTPencilExtraPrimes.v`.  ~9 min
   vm_compute (cached thereafter).

   The combined check `check_pencil_det_pencil_true` (over the full
   1210-prime list crt_primes_pencil) is assembled in
   `CRTPencilExtraChecksProofAsm.v` so this heavy proof can be
   cached independently.
   ================================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.

From Stdlib Require Import Uint63.

From PrimeGapS1 Require Import IntMat Witness CharPoly ModularArith CRTBridge.
From PrimeGapS1.CharPolyAgree Require Import Def.
From PrimeGapS1 Require Import Witness_PencilDet CertPencilDef.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.
From PrimeGapS1 Require Import CRTPencilChecksProof.   (* check_pencil_det_at *)

Open Scope Z_scope.

Definition check_pencil_det_extra : bool :=
  List.forallb check_pencil_det_at crt_primes_pencil_extra.

Lemma check_pencil_det_extra_true : check_pencil_det_extra = true.
Proof. vm_compute. reflexivity. Qed.

(* Sealed forall-form so downstream Qed kernel verification doesn't
   chase the 500-cons list when applying. *)
Opaque crt_primes_pencil_extra.

Lemma check_pencil_det_extra_at (p : Uint63.int) (Hin : In p crt_primes_pencil_extra) :
  check_pencil_det_at p = true.
Proof. exact (proj1 (List.forallb_forall _ _) check_pencil_det_extra_true p Hin). Qed.
