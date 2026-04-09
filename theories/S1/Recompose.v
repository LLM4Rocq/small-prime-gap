(* ============================================================== *)
(*  Recompose.v                                                     *)
(*                                                                  *)
(*  Stdlib Coq's Z literal parser elaborates each Z constant in     *)
(*  super-linear time and stack-overflows on values above ~10 000   *)
(*  bits. The Brown-Traub Sturm chain we ship has individual        *)
(*  integers up to ~200 000 bits.                                   *)
(*                                                                  *)
(*  Workaround: ship those integers as `bigZ` (rocq-bignums) which  *)
(*  has a number notation 1000× faster on huge literals — a single  *)
(*  100 kbit `bigZ` constant elaborates in ~0.4 s, and an 11 MB     *)
(*  certificate file in ~30 s. Convert to stdlib Z lazily via       *)
(*  `BigZ.to_Z` only where needed by downstream proofs.             *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
From Bignums Require Import BigZ.
Import ListNotations.
Open Scope Z_scope.

(* Lift a `list bigZ` to a `list Z`.  Reduces under vm_compute. *)
Definition lift_bigZ (xs : list BigZ.t_) : list Z :=
  List.map BigZ.to_Z xs.

Definition lift_bigZ2 (xss : list (list BigZ.t_)) : list (list Z) :=
  List.map lift_bigZ xss.

(* Sanity tests. *)
Example lift_nil : lift_bigZ [] = [].
Proof. reflexivity. Qed.

Example lift_one : lift_bigZ [42%bigZ] = [42%Z].
Proof. vm_compute. reflexivity. Qed.

Example lift_two : lift_bigZ [(-3)%bigZ; 7%bigZ] = [(-3)%Z; 7%Z].
Proof. vm_compute. reflexivity. Qed.
