(* MaynardVerify/M2_5.v -- M2 closed-form check, rows 35..41. *)

From PrimeGapS1.MaynardVerify Require Import Def.

Lemma M2_check_rows_35_41 :
  M2_check_rows (List.seq 35 7) = true.
Proof. vm_compute. reflexivity. Qed.
