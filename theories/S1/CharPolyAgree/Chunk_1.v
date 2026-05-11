(* CharPolyAgree/Chunk_1.v -- 710-prime CRT, primes 119..237. *)

From PrimeGapS1.CharPolyAgree Require Import Def.

Lemma char_poly_chunk_1 :
  List.forallb check_charpoly_one_prime_710 crt_chunk_1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma matrix_identity_chunk_1 :
  List.forallb check_mat_identity_one_prime crt_chunk_1 = true.
Proof. vm_compute. reflexivity. Qed.
