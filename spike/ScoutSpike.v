(* Computational spike for mathcomp-real-closed paths. *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf qe_rcf_th.

Set Implicit Arguments.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* === 3x3 symmetric rat matrix, char_poly.[0] === *)
Definition M3 : 'M[rat]_3 :=
  \matrix_(i, j) (if (i == j :> nat) then 2%:Q
                  else if (i + j == 1)%N then 1%:Q else 0%:Q).

Definition cp3 : {poly rat} := char_poly M3.

(* Does vm_compute reduce this to a concrete value?
   char_poly at 0 should equal (-1)^3 * det(M3). *)
Time Eval vm_compute in (size cp3).
