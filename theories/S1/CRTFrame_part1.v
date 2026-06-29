(* ===================================================================
   CRTFrame_part1.v -- chunk 1 (table primes 25..49) of the
   per-prime fast (O(n^3) Hessenberg) char-poly check.

   Sharded out of CRTFrame so make -j8 runs the eight heavy [vm_compute]
   passes concurrently.  The boolean forallb over this 25-prime slice
   reduces to [true] under the VM; [vm_cast_no_check (eq_refl true)] runs
   it once and casts.  No Uint63 / PrimInt63 / native_compute / Axiom.
   =================================================================== *)

From Stdlib Require Import List.
From PrimeGapS1 Require Import CRTFrameDefs.

Lemma per_prime_hess_chunk1 :
  List.forallb per_prime_hess_chk (crt_chunk 1) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
