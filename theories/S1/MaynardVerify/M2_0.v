(* MaynardVerify/M2_0.v -- M2 closed-form check, rows 0..6.

   One of 6 parallel chunks; assembly in MaynardVerify.v. *)

From PrimeGapS1.MaynardVerify Require Import Def.

Lemma M2_check_rows_0_6 :
  M2_check_rows (List.seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.
