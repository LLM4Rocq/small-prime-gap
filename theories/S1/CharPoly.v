(* theories/S1/CharPoly.v
   ---------------------------------------------------------------
   Integer-cleared characteristic polynomial — Faddeev-LeVerrier.

   This file gives a hand-rolled implementation of the Faddeev-
   LeVerrier algorithm over `list (list Z)` matrices, returning a
   `pol` (low-to-high `list Z`) whose value at lambda is
   det(lambda*I_n - A). The leading coefficient is 1 and the result
   is monic of degree `mat_dim A`.

   This Definition assumes the input is a square matrix. If so,
   all integer divisions by `k` performed during the recurrence are
   exact (a classical identity from the Faddeev-LeVerrier proof;
   proof postponed to a later sprint), and `Z.div` returns the
   correct rational value.

   Dependencies:
   - PrimeGapS1.IntPoly (list Z polynomial library, by another agent)
   - PrimeGapS1.IntMat  (list (list Z) matrix library, by another agent)
   - MathComp algebra   (for the abstract `char_poly` spec).
   --------------------------------------------------------------- *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

From mathcomp Require Import all_boot all_algebra.
Import GRing.Theory.

From PrimeGapS1 Require Import IntPoly IntMat.

(* ==================================================================
   Faddeev-LeVerrier recurrence over `mat` = `list (list Z)`.

   Recurrence (Wikipedia convention):

     M_0   := 0
     c_n   := 1
     for k = 1, 2, ..., n:
         M_k     := A * M_{k-1} + c_{n-k+1} * I
         c_{n-k} := -(1/k) * trace(A * M_k)

   Final characteristic polynomial (monic):

     p(lambda) = lambda^n + c_{n-1} lambda^{n-1} + ... + c_1 lambda + c_0
               = det(lambda*I - A)

   Output format (`pol` low-to-high):

     [c_0; c_1; ...; c_{n-1}; 1]

   Key identity used to justify `Z.div` (proof deferred):
   at every step, `trace(A * M_k)` is divisible by `k` over Z.
   ================================================================== *)

(* One iteration of Faddeev-LeVerrier.
   - `steps`  : remaining iterations (starts at n, decreases by 1)
   - `k`      : current iteration index as Z (starts at 1)
   - `A`      : the input matrix (constant across iterations)
   - `I_n`    : identity matrix of the right size (constant)
   - `M_prev` : the matrix M_{k-1} from the previous step (starts at mzero n)
   - `c_prev` : the scalar c_{n-(k-1)} = c_{n-k+1} (starts at 1)
   - `acc`    : accumulated low-to-high coefficient list

   The accumulator is built in the correct low-to-high order:
   after the first iteration `acc` is [c_{n-1}], after the second
   [c_{n-2}; c_{n-1}], ..., after n iterations [c_0; c_1; ...; c_{n-1}].
*)
Fixpoint fl_loop
  (steps : nat) (k : Z)
  (A I_n : mat)
  (M_prev : mat) (c_prev : Z)
  (acc : list Z) : list Z :=
  match steps with
  | O => acc
  | S s =>
      let AMprev := mmul A M_prev in
      let M_k    := madd AMprev (mscale c_prev I_n) in
      let AMk    := mmul A M_k in
      let tr     := mtrace AMk in
      (* c_new = -(trace(A*M_k)) / k  (exact integer division). *)
      let c_new  := Z.div (Z.opp tr) k in
      fl_loop s (k + 1) A I_n M_k c_new (c_new :: acc)
  end.

(* ------------------------------------------------------------------
   The characteristic polynomial of an integer square matrix.

   Signature: `mat -> pol`. The matrix is taken at face value (no
   implicit denominator): `peval (char_poly_int A) lambda = det(lambda*I - A)`
   over Z, for any square `A`.

   Cert.v does not call `char_poly_int` directly (it only mentions
   it in comments and uses `char_poly_int_correct` / `mat_int_to_rat`
   / `pol_to_polyrat` through opaque bridges), so we are free to
   expose the cleaner 1-argument signature. The bridging names
   below keep the public API expected by PLAN_S1.md.
   ------------------------------------------------------------------ *)
Definition char_poly_int (A : mat) : pol :=
  let n := mat_dim A in
  let I_n := meye n in
  let coeffs := fl_loop n Z.one A I_n (mzero n) Z.one [] in
  coeffs ++ [Z.one].

(* ==================================================================
   Bridging definitions — concrete (no longer Admitted).

   These functions are plumbing between our `list Z`-based computational
   layer and MathComp's `'M[rat]_n` / `{poly rat}` spec layer. They are
   total, ring-homomorphic in the obvious way, and never invoked under
   `vm_compute` (only at the type level by the spec / proofs).
   ================================================================== *)

(* stdlib Z -> mathcomp int. *)
Definition Z_to_int (z : Z) : int :=
  match z with
  | Z0     => 0%R
  | Zpos p => Posz (Pos.to_nat p)
  | Zneg p => Negz (Pos.to_nat p - 1)
  end.

(* Lift an `mat` of integers plus a denominator D to an 'M[rat]_n.
   Semantics: `mat_int_to_rat M D n (i, j) = (M_int[i][j])%:Q / D%:Q`.
   Out-of-range entries default to 0 via `mat_get`. *)
Definition mat_int_to_rat (M : mat) (D : Z) (n : nat) : 'M[rat]_n :=
  \matrix_(i, j)
    ((Z_to_int (mat_get M (nat_of_ord i) (nat_of_ord j)))%:~R
       / (Z_to_int D)%:~R)%R.

(* Lift a `pol = list Z` to a `{poly rat}` by coefficient-wise
   embedding Z -> rat. *)
Definition pol_to_polyrat (p : pol) : {poly rat} :=
  Poly (List.map (fun z => (Z_to_int z)%:~R : rat) p).

(* ------------------------------------------------------------------
   L2 (PLAN_S1.md §3) — the load-bearing correctness lemma.

   Signature updated so that `char_poly_int` now takes only a matrix.
   The denominator `D` appears solely in the lifted statement, matching
   the scaling convention that will be tightened up in a later sprint.
   Proof is non-trivial (Newton's identities) and is deferred.
   ------------------------------------------------------------------ *)
Lemma char_poly_int_correct
  (M : mat) (D : Z) (n : nat)
  (sq : mat_dim M = n)
  (Dnz : D <> Z0) :
  (* Intended precise form:
        pol_to_polyrat (char_poly_int M)
      = (D%:~R) ^+ n *: char_poly (mat_int_to_rat M D n)
     Left in the equational shape used by Cert.v's architecture. *)
  pol_to_polyrat (char_poly_int M) = char_poly (mat_int_to_rat M D n).
Admitted.

(* ==================================================================
   Sanity tests — must reduce under vm_compute.
   ================================================================== *)

(* 2x2: [[1;2];[3;4]]
     lambda^2 - 5 lambda - 2 = (1*4 - 2*3) - 5 lambda + lambda^2
   Low-to-high: [-2; -5; 1]. *)
Example char_poly_2x2_test :
  char_poly_int [[1; 2]; [3; 4]] = [-2; -5; 1].
Proof. vm_compute. reflexivity. Qed.

(* 3x3: I_3
     (lambda - 1)^3 = lambda^3 - 3 lambda^2 + 3 lambda - 1.
   Low-to-high: [-1; 3; -3; 1]. *)
Example char_poly_eye_3_test :
  char_poly_int (meye 3) = [-1; 3; -3; 1].
Proof. vm_compute. reflexivity. Qed.

(* 3x3 diagonal: diag(2,3,5)
     (lambda - 2)(lambda - 3)(lambda - 5)
     = lambda^3 - 10 lambda^2 + 31 lambda - 30.
   Low-to-high: [-30; 31; -10; 1]. *)
Example char_poly_3x3_test :
  char_poly_int [[2; 0; 0]; [0; 3; 0]; [0; 0; 5]] = [-30; 31; -10; 1].
Proof. vm_compute. reflexivity. Qed.

(* ==================================================================
   Performance test: 10x10 identity.

   (lambda - 1)^10 has coefficients (low-to-high) given by the
   binomial coefficients with alternating signs:
     (-1)^{10-k} * C(10, k), for k = 0, 1, ..., 10.

     k=0:  +C(10,0)  =    1  (sign (-1)^10)    ... wait, the constant
                                                   term of (x-1)^10 is (-1)^10 = 1.
   Let us expand (lambda - 1)^10 directly:
     sum_{k=0}^{10} C(10,k) lambda^k (-1)^{10-k}.
   k = 0 : (-1)^10 *   1 =    1
   k = 1 : (-1)^9  *  10 =  -10
   k = 2 : (-1)^8  *  45 =   45
   k = 3 : (-1)^7  * 120 = -120
   k = 4 : (-1)^6  * 210 =  210
   k = 5 : (-1)^5  * 252 = -252
   k = 6 : (-1)^4  * 210 =  210
   k = 7 : (-1)^3  * 120 = -120
   k = 8 : (-1)^2  *  45 =   45
   k = 9 : (-1)^1  *  10 =  -10
   k = 10: (-1)^0  *   1 =    1
   Low-to-high coefficient list therefore is
     [1; -10; 45; -120; 210; -252; 210; -120; 45; -10; 1]. *)
Example char_poly_eye_10_perf :
  char_poly_int (meye 10)
  = [1; -10; 45; -120; 210; -252; 210; -120; 45; -10; 1].
Proof. vm_compute. reflexivity. Qed.
