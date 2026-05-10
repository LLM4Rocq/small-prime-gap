(* ============================================================== *)
(*  IntPoly.v                                                       *)
(*                                                                  *)
(*  A plain `list Z` polynomial library for the computational       *)
(*  layer of the Maynard S1 proof.                                  *)
(*                                                                  *)
(*  MathComp's `{poly R}` does not reduce under `vm_compute` at     *)
(*  the sizes we need (42-degree polys, 200-bit coefs). Stdlib      *)
(*  `ZArith` + plain `list Z` does, so the whole computational      *)
(*  workload lives here.                                            *)
(*                                                                  *)
(*  Convention: a polynomial is the LOW-TO-HIGH coefficient list.   *)
(*    - `pol[0]` is the constant term.                              *)
(*    - The last element (if any) is the leading coefficient.       *)
(*    - The empty list represents the zero polynomial.              *)
(*    - No invariant is assumed: trailing zeros are allowed.        *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ---------- Core type ---------- *)

Definition pol : Type := list Z.

(* ---------- Leading coefficient ---------- *)

Fixpoint plead_aux (p : pol) (acc : Z) : Z :=
  match p with
  | [] => acc
  | x :: xs => if Z.eqb x 0 then plead_aux xs acc else plead_aux xs x
  end.

Definition plead (p : pol) : Z := plead_aux p 0.

(* ---------- Evaluation at a rational ---------- *)

(* Given p = a0 + a1 X + ... + ad X^d, returns
   den^d * p(num/den) = a0*den^d + a1*num*den^(d-1) + ... + ad*num^d.
   This integer has the same sign as p(num/den) when den > 0. *)
Fixpoint peval_at_rat_aux (p : pol) (num den : Z) : Z * Z :=
  (* Returns (value, den_power) where den_power is den^length(p) used
     to scale higher-order terms. We walk low-to-high, keeping an
     accumulator of the current num^i and the complementary den^(d-i). *)
  match p with
  | [] => (0, 1)
  | a :: rest =>
      let '(rest_val, rest_den_pow) := peval_at_rat_aux rest num den in
      (* rest represents p' = a1 + a2 X + ... + ad X^(d-1) of length d,
         scaled as den^(d-1) * p'(num/den) (the ghost d-1 here).
         Then a + (num/den) * p'(num/den) scaled by den^d becomes
         a * den^d + num * (den^(d-1) * p'(num/den)). *)
      (a * (den * rest_den_pow) + num * rest_val, den * rest_den_pow)
  end.

Definition peval_at_rat (p : pol) (num den : Z) : Z :=
  fst (peval_at_rat_aux p num den).

(* ============================================================== *)
(*  Sanity tests for the load-bearing primitives.                   *)
(* ============================================================== *)

Example plead_test1 : plead [1; 2; 3] = 3.
Proof. vm_compute. reflexivity. Qed.

Example plead_test2 : plead [1; 2; 0; 0] = 2.
Proof. vm_compute. reflexivity. Qed.

Example plead_test3 : plead [] = 0.
Proof. vm_compute. reflexivity. Qed.

(* (1 + 2 X + 3 X^2) at X = 1/2: den^2 * p = 4 + 2*2 + 3*1 = 4+4+3 = 11.
   Length here is 3, so peval_at_rat scales by den^3 = 8 giving 22. *)
Example peval_at_rat_test : peval_at_rat [1; 2; 3] 1 2 = 22.
Proof. vm_compute. reflexivity. Qed.
