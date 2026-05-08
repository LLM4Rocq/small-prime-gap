(* MaynardVerifyM2_3.v -- M2 closed-form check, rows 21..27. *)

From PrimeGapS1 Require Import MaynardVerifyDef.

Lemma M2_check_rows_21_27 :
  M2_check_rows (List.seq 21 7) = true.
Proof. vm_compute. reflexivity. Qed.
