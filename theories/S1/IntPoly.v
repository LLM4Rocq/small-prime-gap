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
(*      Use `pnorm` to strip them.                                  *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ---------- Core type ---------- *)

Definition pol : Type := list Z.

Definition pzero : pol := [].
Definition pone  : pol := [1].
Definition pX    : pol := [0; 1].

(* ---------- Normalization ---------- *)

(* Strip trailing zeros. We reverse, drop leading zeros, reverse back.
   This reduces fine under vm_compute. *)
Fixpoint drop_leading_zeros (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => if Z.eqb x 0 then drop_leading_zeros xs else x :: xs
  end.

Definition pnorm (p : pol) : pol :=
  List.rev (drop_leading_zeros (List.rev p)).

(* ---------- Size / degree / leading coefficient ---------- *)

Definition psize (p : pol) : nat := List.length (pnorm p).

Definition pdeg (p : pol) : nat :=
  match psize p with
  | O => O
  | S k => k
  end.

Fixpoint plead_aux (p : pol) (acc : Z) : Z :=
  match p with
  | [] => acc
  | x :: xs => if Z.eqb x 0 then plead_aux xs acc else plead_aux xs x
  end.

Definition plead (p : pol) : Z := plead_aux p 0.

(* ---------- Addition / subtraction / negation / scaling ---------- *)

Fixpoint padd (p q : pol) : pol :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | x :: xs, y :: ys => (x + y) :: padd xs ys
  end.

Definition pneg (p : pol) : pol := List.map Z.opp p.

Fixpoint psub (p q : pol) : pol :=
  match p, q with
  | [], _ => pneg q
  | _, [] => p
  | x :: xs, y :: ys => (x - y) :: psub xs ys
  end.

Definition pscale (c : Z) (p : pol) : pol := List.map (fun x => c * x) p.

(* ---------- Multiplication (convolution) ---------- *)

Fixpoint pmul (p q : pol) : pol :=
  match p with
  | [] => []
  | x :: xs => padd (pscale x q) (0 :: pmul xs q)
  end.

(* ---------- Derivative ---------- *)

(* Derivative of a_0 + a_1 X + a_2 X^2 + ... is a_1 + 2*a_2 X + ...
   We pass the index starting at 1 and multiply each a_k by k. *)
Fixpoint pderiv_aux (p : pol) (k : Z) : pol :=
  match p with
  | [] => []
  | x :: xs => (k * x) :: pderiv_aux xs (k + 1)
  end.

Definition pderiv (p : pol) : pol :=
  match p with
  | [] => []
  | _ :: xs => pderiv_aux xs 1
  end.

(* ---------- Evaluation (Horner, low-to-high) ---------- *)

(* For low-to-high, fold from the right:
   eval [a0; a1; a2] at x = a0 + x * (a1 + x * (a2 + x * 0)). *)
Fixpoint peval (p : pol) (x : Z) : Z :=
  match p with
  | [] => 0
  | a :: rest => a + x * peval rest x
  end.

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

(* ---------- Integer pseudo-remainder (Knuth) ---------- *)

(* Helpers on normalized polys: leading coefficient and degree with
   explicit fuel so reduction stays linear. *)

(* Length-based degree of a *normalized* polynomial. *)
Definition len_deg (p : pol) : nat :=
  match List.length p with O => O | S k => k end.

(* Shift by multiplying by X^k (prepend k zeros). *)
Fixpoint pshift (k : nat) (p : pol) : pol :=
  match k with
  | O => p
  | S k' => 0 :: pshift k' p
  end.

(* One pseudo-division step. Given A, B (both normalized, nonzero, with
   deg A >= deg B), compute
     A' = lc(B) * A - lc(A) * X^(deg A - deg B) * B
   which has strictly smaller degree than A. *)
Definition prem_step (A B : pol) : pol :=
  let lcA := plead A in
  let lcB := plead B in
  let dA  := len_deg A in
  let dB  := len_deg B in
  let k   := Nat.sub dA dB in
  pnorm (psub (pscale lcB A) (pscale lcA (pshift k B))).

(* The main loop: iterate pseudo-division with fuel.
   Invariant: A is normalized. Stops when deg A < deg B. *)
Fixpoint prem_loop (A B : pol) (steps : nat) : pol :=
  match steps with
  | O => A
  | S s =>
      if Nat.ltb (len_deg A) (len_deg B) then A
      else
        match A with
        | [] => A
        | _ =>
            let A' := prem_step A B in
            prem_loop A' B s
        end
  end.

Definition prem (A B : pol) : pol :=
  let A' := pnorm A in
  let B' := pnorm B in
  match B' with
  | [] => pzero (* B = 0: undefined; return 0 by convention. *)
  | _ =>
      if Nat.ltb (len_deg A') (len_deg B') then A'
      else prem_loop A' B' (S (List.length A'))
  end.

(* ============================================================== *)
(*  Sanity tests: every primitive must reduce under vm_compute.     *)
(* ============================================================== *)

Example pzero_test : pzero = [].
Proof. reflexivity. Qed.

Example pone_test : pone = [1].
Proof. reflexivity. Qed.

Example pX_test : pX = [0; 1].
Proof. reflexivity. Qed.

Example pnorm_test1 : pnorm [1; 2; 0; 0] = [1; 2].
Proof. vm_compute. reflexivity. Qed.

Example pnorm_test2 : pnorm [0; 0; 0] = [].
Proof. vm_compute. reflexivity. Qed.

Example pnorm_test3 : pnorm [1; 0; 3; 0] = [1; 0; 3].
Proof. vm_compute. reflexivity. Qed.

Example psize_test : psize [1; 2; 0; 0] = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example pdeg_test : pdeg [1; 2; 3; 0; 0] = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example plead_test1 : plead [1; 2; 3] = 3.
Proof. vm_compute. reflexivity. Qed.

Example plead_test2 : plead [1; 2; 0; 0] = 2.
Proof. vm_compute. reflexivity. Qed.

Example plead_test3 : plead [] = 0.
Proof. vm_compute. reflexivity. Qed.

Example padd_test : padd [1; 2; 3] [4; 5; 6; 7] = [5; 7; 9; 7].
Proof. vm_compute. reflexivity. Qed.

Example psub_test : psub [1; 2; 3] [4; 5; 6; 7] = [-3; -3; -3; -7].
Proof. vm_compute. reflexivity. Qed.

Example pneg_test : pneg [1; -2; 3] = [-1; 2; -3].
Proof. vm_compute. reflexivity. Qed.

Example pscale_test : pscale 3 [1; 2; 3] = [3; 6; 9].
Proof. vm_compute. reflexivity. Qed.

(* (1 + 2 X) * (3 + 4 X) = 3 + 10 X + 8 X^2 *)
Example pmul_test1 : pmul [1; 2] [3; 4] = [3; 10; 8].
Proof. vm_compute. reflexivity. Qed.

(* (X - 1)(X + 1) = X^2 - 1, i.e. [-1; 0; 1] *)
Example pmul_test2 : pmul [-1; 1] [1; 1] = [-1; 0; 1].
Proof. vm_compute. reflexivity. Qed.

(* d/dx(5 + 3 X + 2 X^2 + X^3) = 3 + 4 X + 3 X^2 *)
Example pderiv_test : pderiv [5; 3; 2; 1] = [3; 4; 3].
Proof. vm_compute. reflexivity. Qed.

(* (1 + 2 X + 3 X^2) at X=10 = 1 + 20 + 300 = 321 *)
Example peval_test : peval [1; 2; 3] 10 = 321.
Proof. vm_compute. reflexivity. Qed.

(* (1 + 2 X + 3 X^2) at X = 1/2: den^2 * p = 4 + 2*2 + 3*1 = 4+4+3 = 11.
   Length here is 3, so peval_at_rat scales by den^3 = 8 giving 22. *)
Example peval_at_rat_test : peval_at_rat [1; 2; 3] 1 2 = 22.
Proof. vm_compute. reflexivity. Qed.

(* prem sanity:
   A = X^3 - 2 X + 1, B = X^2 - 1.
   Classical remainder is -X + 1 (lcB = 1 so no scaling blowup). *)
Example prem_test1 :
  prem [1; -2; 0; 1] [-1; 0; 1] = [1; -1].
Proof. vm_compute. reflexivity. Qed.

(* Short case: deg A < deg B, so prem A B = pnorm A. *)
Example prem_test2 :
  prem [1; 2] [1; 0; 1] = [1; 2].
Proof. vm_compute. reflexivity. Qed.

