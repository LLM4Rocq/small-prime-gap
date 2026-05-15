(* ==================================================================
   CRTPencilCheck.v

   Lift the 1-coefficient CRT per-prime agreement (proved in
   `CRTPencilChecksProof.v` by ~12 min of vm_compute) to Z equality
   between `det_M1_int` / `D_pencil_int` (computed via fl_loop on
   M1_int and pencil_mat_int respectively) and the precomputed Z
   literals shipped in `Witness_PencilDet.v`.

   Pipeline at each prime p in crt_primes_all:

     (1) From check_{M1,pencil}_det_710_true (proved in
         CRTPencilChecksProof.v), get per-prime agreement at p:

           List.nth 0 (char_poly_mod p M) 0%uint63
                                  = Z_to_mod63 p shipped_value.

     (2) Apply char_poly_mod_sound (CRTBridge.v) to convert to:

           Z_to_mod63 p (List.nth 0 (char_poly_int M) 0%Z)
                                  = Z_to_mod63 p shipped_value.

     (3) Take Uint63.to_Z (via Z_to_mod63_spec): obtain

           List.nth 0 (char_poly_int M) 0%Z mod (to_Z p)
                                  = shipped_value mod (to_Z p).

         Hence p | (det_M_int - shipped_value).

     (4) Aggregate across crt_primes_all via all_primes_divide_product:

           crt_product_710 | (det_M_int - shipped_value).

     (5) Apply small_multiple_zero with the Hadamard bound

           2 * |det_M_int - shipped_value| < crt_product_710

         to conclude `det_M_int - shipped_value = 0`, hence equality.

     (6) vm_compute the sign of the literal.

   `CertPencil.{D_pencil_int_neg, det_M1_int_pos}` close by chaining
   the equality with the literal-sign lemma.

   STATUS: pipeline laid out below.  The four nontrivial steps (per-
   prime divisibility from char_poly_mod_sound, all_primes_divide_-
   product application with the right discharges, Hadamard bound for
   the determinants, small_multiple_zero) are all available as
   lemmas in CRTBridge.v / CRTCheck.v / CRTLift.v / PrimeCheck.v —
   this is plumbing.  Estimated remaining work: ~80-150 LOC.
   ================================================================== *)

From Stdlib Require Import ZArith List Lia.

From PrimeGapS1 Require Import IntMat Witness CharPoly.
From PrimeGapS1 Require Import ModularArith CRTBridge.
From PrimeGapS1 Require Import Witness_PencilDet.
From PrimeGapS1 Require Import CertL2 CertPencil.
From PrimeGapS1 Require Import CRTPencilChecksProof.

Open Scope Z_scope.

(* The signs of the shipped Z literals: trivial vm_compute. *)

Lemma det_M1_int_value_pos : (0 < det_M1_int_value)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma D_pencil_int_value_neg : (D_pencil_int_value < 0)%Z.
Proof. vm_compute. reflexivity. Qed.

(* The two Z equalities — see the file header for the pipeline. *)

Theorem det_M1_int_eq : det_M1_int = det_M1_int_value.
Proof. (* TODO: assemble (1)-(5) from the file header. *)
Admitted.

Theorem D_pencil_int_eq : D_pencil_int = D_pencil_int_value.
Proof. (* TODO: same shape as det_M1_int_eq. *)
Admitted.
