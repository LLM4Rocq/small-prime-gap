(* ==================================================================
   AllRowsLenHelper.v

   Tiny extraction of `forallb_all_rows_len` from `CharPolyAgree.v`,
   so the pencil (quad) route can use it without importing the heavy
   six CRT chunk verifications (~30 min vm_compute) that the original
   `CharPolyAgree.v` aggregates.
   ================================================================== *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

From PrimeGapS1 Require Import CharPoly.

Lemma forallb_all_rows_len n (M : list (list BinNums.Z)) :
  forallb (fun row => Nat.eqb (length row) n) M = true ->
  all_rows_len n M.
Proof.
  intros Hfb.
  unfold all_rows_len. intros i Hi.
  rewrite forallb_forall in Hfb.
  assert (Hin : In (nth i M nil) M).
  { apply nth_In. exact Hi. }
  specialize (Hfb _ Hin).
  rewrite Nat.eqb_eq in Hfb.
  exact Hfb.
Qed.
