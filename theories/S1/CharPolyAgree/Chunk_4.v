(* CharPolyAgree/Chunk_4.v -- 710-prime CRT, primes 476..594. *)

From PrimeGapS1.CharPolyAgree Require Import Def.

Lemma char_poly_chunk_4 :
  List.forallb check_charpoly_one_prime_710 crt_chunk_4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma matrix_identity_chunk_4 :
  List.forallb check_mat_identity_one_prime crt_chunk_4 = true.
Proof. vm_compute. reflexivity. Qed.
