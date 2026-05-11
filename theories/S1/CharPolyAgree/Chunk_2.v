(* CharPolyAgree/Chunk_2.v -- 710-prime CRT, primes 238..356. *)

From PrimeGapS1.CharPolyAgree Require Import Def.

Lemma char_poly_chunk_2 :
  List.forallb check_charpoly_one_prime_710 crt_chunk_2 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma matrix_identity_chunk_2 :
  List.forallb check_mat_identity_one_prime crt_chunk_2 = true.
Proof. vm_compute. reflexivity. Qed.
