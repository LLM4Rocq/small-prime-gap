(* ============================================================== *)
(*  SignChain.v                                                     *)
(*                                                                  *)
(*  After the cleanup branch retired the Sturm-count layer, this    *)
(*  file exposes only the per-polynomial sign primitives the IVT    *)
(*  proof in CertL1.v actually consumes:                            *)
(*                                                                  *)
(*    sgn_Z : Z -> Z                                                *)
(*    sign_at_rat : pol -> Z -> Z -> Z                              *)
(*    sign_at_pinf : pol -> Z                                       *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
From PrimeGapS1 Require Import IntPoly.

(* ---------- Sign of an integer ---------- *)

Definition sgn_Z (z : Z) : Z :=
  match z with
  | Z0     => 0
  | Zpos _ => 1
  | Zneg _ => -1
  end.

(* ---------- Sign of a polynomial at a rational point ---------- *)

(* Precondition: den > 0.  Under this assumption, peval_at_rat p num den
   = den^(length p) * p(num/den) is sign-equivalent to p(num/den), so
   taking its sign gives the correct answer. *)
Definition sign_at_rat (p : pol) (num den : Z) : Z :=
  sgn_Z (peval_at_rat p num den).

(* At +infinity, the sign of p equals the sign of its leading coefficient. *)
Definition sign_at_pinf (p : pol) : Z := sgn_Z (plead p).
