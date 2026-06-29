(* ===================================================================
   CRTFrameDefs.v -- shared base for the sharded per-prime Hessenberg
   char-poly check (CRTFrame_part0..7 / CRTFrame).

   This file factors out, with NO heavy computation of its own:

     list_Z_eqb           : element-wise boolean equality on list Z
     per_prime_hess_chk   : the per-prime fast (O(n^3) Hessenberg)
                              char-poly check used by CRTFrame
     crt_chunk            : the 8 firstn/skipn slices of crt_primes_M1
                              (25 primes each) discharged in parallel by
                              the CRTFrame_part* files.

   The expensive [vm_compute] forallb over the 200 table primes lives
   in the eight CRTFrame_part*.v files (one chunk each), so make -j8
   runs them concurrently.  CRTFrame then reassembles them into
   per_prime_hess_all without re-running the VM.

   No Uint63 / PrimInt63 / native_compute / Axiom / Parameter appears.
   =================================================================== *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
From PrimeGapS1 Require Import IntMat CharPoly Witness.
From PrimeGapS1 Require Import WitnessM1CharPoly ModularHess.

Open Scope Z_scope.

(* Element-wise boolean equality on lists of Z. *)
Fixpoint list_Z_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with
  | nil, nil => true
  | x :: l1', y :: l2' => Z.eqb x y && list_Z_eqb l1' l2'
  | _, _ => false
  end.

(* The per-prime fast char-poly check: the O(n^3) Hessenberg char-poly of
   M1_int agrees with cp_M1_value mod p. *)
Definition per_prime_hess_chk (p : Z) : bool :=
  list_Z_eqb (char_poly_hess p M1_int)
             (map (fun c => c mod p) cp_M1_value).

(* The 8 contiguous 25-prime slices of the 200-prime crt_primes_M1 table.
   chunk k = primes [25*k .. 25*k+24].  Their concatenation is
   crt_primes_M1 (proved in CRTFrame as crt_primes_M1_chunks). *)
Definition crt_chunk (k : nat) : list Z :=
  firstn 25 (skipn (25 * k) crt_primes_M1).
