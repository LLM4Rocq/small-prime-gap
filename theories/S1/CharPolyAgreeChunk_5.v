(* CharPolyAgreeChunk_5.v -- 710-prime CRT, primes 595..709. *)

From PrimeGapS1 Require Import CharPolyAgreeDef.

Lemma char_poly_chunk_5 :
  List.forallb check_charpoly_one_prime_710 crt_chunk_5 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma matrix_identity_chunk_5 :
  List.forallb check_mat_identity_one_prime crt_chunk_5 = true.
Proof. vm_compute. reflexivity. Qed.
