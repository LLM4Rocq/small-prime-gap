(* CharPolyAgreeChunk_0.v -- 710-prime CRT, primes 0..118 of crt_primes_all.

   One of 6 parallel chunks; assembly in CharPolyAgree.v. *)

From PrimeGapS1 Require Import CharPolyAgreeDef.

Lemma char_poly_chunk_0 :
  List.forallb check_charpoly_one_prime_710 crt_chunk_0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma matrix_identity_chunk_0 :
  List.forallb check_mat_identity_one_prime crt_chunk_0 = true.
Proof. vm_compute. reflexivity. Qed.
