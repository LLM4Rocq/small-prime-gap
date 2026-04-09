(* ============================================================== *)
(*  SignChain.v                                                     *)
(*                                                                  *)
(*  Sign-variation counting on chains of `pol = list Z`             *)
(*  polynomials.  This is the computational core of our Rocq        *)
(*  implementation of Sturm's theorem: given a Sturm chain built    *)
(*  by Brown--Traub (see BrownTraub.v), the number of real roots    *)
(*  of the base polynomial in an interval (a, b] is                 *)
(*     V(a) - V(b)                                                  *)
(*  where V(x) counts sign changes along the chain evaluated at x. *)
(*                                                                  *)
(*  Rationals are represented as pairs (num, den) with den > 0;     *)
(*  this invariant is assumed throughout but not verified, because  *)
(*  downstream code always constructs positive denominators.        *)
(* ============================================================== *)

From Stdlib Require Import ZArith List PeanoNat.
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
   taking its sign gives the correct answer.  If den is allowed to be
   negative, a correction by (-1)^(length p) would be needed; we avoid
   that complication by requiring positive denominators. *)
Definition sign_at_rat (p : pol) (num den : Z) : Z :=
  sgn_Z (peval_at_rat p num den).

(* ---------- Signs at +/- infinity ---------- *)

(* At +infinity, the sign of p equals the sign of its leading coefficient. *)
Definition sign_at_pinf (p : pol) : Z := sgn_Z (plead p).

(* At -infinity, the sign is lc(p) * (-1)^(deg p). *)
Definition sign_at_minf (p : pol) : Z :=
  if Nat.even (pdeg p) then sgn_Z (plead p) else - sgn_Z (plead p).

(* ---------- Sign-variation count of a list of integers ---------- *)

(* We count the number of consecutive non-zero sign disagreements,
   skipping zeros entirely.  This matches MathComp's qe_rcf_th.changes
   on integer inputs.

   Implementation: walk the list carrying the last non-zero sign seen
   (as an option Z).  When we meet a new non-zero element, compare it
   to the last sign and bump the counter on disagreement. *)

Fixpoint variation_aux (last : option Z) (s : list Z) : nat :=
  match s with
  | [] => 0%nat
  | x :: xs =>
      if Z.eqb x 0 then
        variation_aux last xs
      else
        match last with
        | None => variation_aux (Some x) xs
        | Some y =>
            if Z.eqb (x * y) 0 then
              (* shouldn't occur since x <> 0 and y is the last nonzero *)
              variation_aux (Some x) xs
            else if Z.ltb (x * y) 0 then
              S (variation_aux (Some x) xs)
            else
              variation_aux (Some x) xs
        end
  end.

Definition variation (s : list Z) : nat := variation_aux None s.

(* ---------- Variation count of a chain of polynomials ---------- *)

Definition variation_at_rat (c : list pol) (num den : Z) : nat :=
  variation (map (fun p => sign_at_rat p num den) c).

Definition variation_at_pinf (c : list pol) : nat :=
  variation (map sign_at_pinf c).

Definition variation_at_minf (c : list pol) : nat :=
  variation (map sign_at_minf c).

(* ---------- Sturm counts ---------- *)

(* Number of distinct real roots of p in (a, b], where a = anum/aden and
   b = bnum/bden, computed as V(a) - V(b).  Nat subtraction truncates
   at zero; the caller is expected to choose a, b so that V(a) >= V(b). *)
Definition sturm_count_in
  (c : list pol) (anum aden bnum bden : Z) : nat :=
  Nat.sub (variation_at_rat c anum aden) (variation_at_rat c bnum bden).

(* Number of real roots strictly above a = anum/aden, using +infinity
   as the upper endpoint. *)
Definition sturm_count_above (c : list pol) (anum aden : Z) : nat :=
  Nat.sub (variation_at_rat c anum aden) (variation_at_pinf c).

(* ============================================================== *)
(*  Sanity tests (must reduce under vm_compute)                     *)
(* ============================================================== *)

Example sgn_Z_zero  : sgn_Z 0      = 0.  Proof. vm_compute. reflexivity. Qed.
Example sgn_Z_pos   : sgn_Z 7      = 1.  Proof. vm_compute. reflexivity. Qed.
Example sgn_Z_neg   : sgn_Z (-3)   = -1. Proof. vm_compute. reflexivity. Qed.

Example variation_flat : variation [1; 1; 1] = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Example variation_alt : variation [1; -1; 1] = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example variation_skip_zero : variation [1; 0; -1] = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example variation_skip_zeros : variation [-1; 0; 0; 1] = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example variation_empty : variation [] = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(* p(X) = X^2 - 2.  p(0) = -2, p(2) = 2, p(1) = -1. *)
Example sign_at_rat_zero : sign_at_rat [-2; 0; 1] 0 1 = -1.
Proof. vm_compute. reflexivity. Qed.

Example sign_at_rat_two : sign_at_rat [-2; 0; 1] 2 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Example sign_at_rat_one : sign_at_rat [-2; 0; 1] 1 1 = -1.
Proof. vm_compute. reflexivity. Qed.

Example sign_at_pinf_pos : sign_at_pinf [-2; 0; 1] = 1.
Proof. vm_compute. reflexivity. Qed.

Example sign_at_pinf_neg : sign_at_pinf [-2; 0; -1] = -1.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  End-to-end smoke test                                           *)
(*                                                                  *)
(*  Chain for p(X) = X^2 - 2:                                       *)
(*    p0 = X^2 - 2    = [-2; 0; 1]                                  *)
(*    p1 = 2X         = [0; 2]   (derivative of p0)                 *)
(*    p2 = 2          = [2]      (pseudo-remainder-style const)     *)
(*                                                                  *)
(*  At x = 0:  signs = [-1; 0; 1], variation = 1                    *)
(*  At +inf:    signs = [1; 1; 1],  variation = 0                   *)
(*  => one real root of X^2 - 2 in (0, +inf), namely +sqrt 2.       *)
(* ============================================================== *)

Definition smoke_chain : list pol :=
  [[-2; 0; 1]; [0; 2]; [2]].

Example smoke_variation_at_zero :
  variation_at_rat smoke_chain 0 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.

Example smoke_variation_at_pinf :
  variation_at_pinf smoke_chain = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Example smoke_sturm_count_above :
  sturm_count_above smoke_chain 0 1 = 1%nat.
Proof. vm_compute. reflexivity. Qed.
