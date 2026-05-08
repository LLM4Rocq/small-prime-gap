(* MaynardVerifyM2_1.v -- M2 closed-form check, rows 7..13. *)

From PrimeGapS1 Require Import MaynardVerifyDef.

Lemma M2_check_rows_7_13 :
  M2_check_rows (List.seq 7 7) = true.
Proof. vm_compute. reflexivity. Qed.
