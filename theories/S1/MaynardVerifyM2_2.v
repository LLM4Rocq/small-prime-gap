(* MaynardVerifyM2_2.v -- M2 closed-form check, rows 14..20. *)

From PrimeGapS1 Require Import MaynardVerifyDef.

Lemma M2_check_rows_14_20 :
  M2_check_rows (List.seq 14 7) = true.
Proof. vm_compute. reflexivity. Qed.
