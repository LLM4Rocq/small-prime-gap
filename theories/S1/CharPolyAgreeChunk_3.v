(* CharPolyAgreeChunk_3.v -- 710-prime CRT, primes 357..475. *)

From PrimeGapS1 Require Import CharPolyAgreeDef.

Lemma char_poly_chunk_3 :
  List.forallb check_charpoly_one_prime_710 crt_chunk_3 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma matrix_identity_chunk_3 :
  List.forallb check_mat_identity_one_prime crt_chunk_3 = true.
Proof. vm_compute. reflexivity. Qed.
