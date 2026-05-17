(* Trial-division primality check for the 500 EXTRA primes.
   ~6 min vm_compute. *)

From Stdlib Require Import ZArith List.
From Stdlib Require Import Uint63.

From PrimeGapS1 Require Import PrimeCheck.
From PrimeGapS1 Require Import CRTPencilExtraPrimes.

Open Scope Z_scope.

Definition check_extra_primes : bool :=
  List.forallb (fun p => check_prime_Z (Uint63.to_Z p)) crt_primes_pencil_extra.

Lemma check_extra_primes_true : check_extra_primes = true.
Proof. vm_compute. reflexivity. Qed.

(* Re-seal the prime list locally so the kernel doesn't walk it during
   Qed verification of the wrapper below.  (Opaque hint in
   CRTPencilExtraPrimes.v may not survive the inter-file boundary.) *)
Opaque crt_primes_pencil_extra.

Lemma extra_prime_at (p : Uint63.int) (Hin : In p crt_primes_pencil_extra) :
  check_prime_Z (Uint63.to_Z p) = true.
Proof. exact (proj1 (List.forallb_forall _ _) check_extra_primes_true p Hin). Qed.
