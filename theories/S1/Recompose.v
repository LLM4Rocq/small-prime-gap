(* ============================================================== *)
(*  Recompose.v                                                     *)
(*                                                                  *)
(*  Stdlib Coq's Z literal parser elaborates each Z constant in     *)
(*  super-linear time and stack-overflows on values above ~10 000   *)
(*  bits. The shipped `charpoly_of_A_int` (43 coefficients) has    *)
(*  individual integers up to ~20 000 bits.                         *)
(*                                                                  *)
(*  Workaround: ship those integers as `bigZ` (rocq-bignums) which  *)
(*  has a number notation 1000× faster on huge literals — a single  *)
(*  20 kbit `bigZ` constant elaborates in well under a second.      *)
(*  Convert to stdlib Z lazily via `BigZ.to_Z` only where needed    *)
(*  by downstream proofs (the sole user is                          *)
(*  `Witness.charpoly_of_A_int`).                                   *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
From Bignums Require Import BigZ.
Import ListNotations.
Open Scope Z_scope.

(* Lift a `list bigZ` to a `list Z`.  Reduces under vm_compute. *)
Definition lift_bigZ (xs : list BigZ.t_) : list Z :=
  List.map BigZ.to_Z xs.
