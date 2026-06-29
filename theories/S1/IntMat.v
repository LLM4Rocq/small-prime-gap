(* (c) Copyright 2024-2026, prime_gap contributors. License: CeCILL-B.        *)

(**md**************************************************************************)
(* # IntMat                                                                   *)
(*                                                                            *)
(* A minimal, purely-stdlib integer-matrix library built on the concrete      *)
(* representation `list (list Z)`.  This representation is required           *)
(* because MathComp's `'M[rat]_n` does not reduce under `vm_compute` at       *)
(* the sizes (42x42, ~200-bit entries) the Maynard S1 certificate             *)
(* demands; the hand-rolled nested-list version runs the 42x42 workload       *)
(* in ~0.14 s.                                                                *)
(*                                                                            *)
(* This file exposes only the operations and a handful of                     *)
(* `vm_compute`-based sanity examples.  Mathematical theorems (symmetry,      *)
(* multiplicativity, trace invariance, etc.) are deferred to CharPoly.v       *)
(* / Cert.v.                                                                  *)
(******************************************************************************)

From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------- Core type ----------------------------------------------------- *)

(** A matrix is its row-major nested list representation.  No
    well-formedness invariant is enforced; the correctness lemmas
    (proved elsewhere) will assume squareness. *)
Definition mat : Type := list (list Z).

Definition mat_dim (m : mat) : nat := length m.

(** `nth_Z xs i` returns the i-th element of a `list Z`, or 0 if
    the index is out of range. *)
Definition nth_Z (xs : list Z) (i : nat) : Z := nth i xs 0%Z.

Definition mat_get (m : mat) (i j : nat) : Z :=
  nth_Z (nth i m nil) j.

(* ---------- Constant constructors ----------------------------------------- *)

(** `zrow n` is a list of n zeros. *)
Fixpoint zrow (n : nat) : list Z :=
  match n with
  | O => nil
  | S k => 0%Z :: zrow k
  end.

Fixpoint mzero_aux (rows : nat) (cols : nat) : mat :=
  match rows with
  | O => nil
  | S k => zrow cols :: mzero_aux k cols
  end.

(** `mzero n` is the n x n zero matrix. *)
Definition mzero (n : nat) : mat := mzero_aux n n.

(** `eye_row n i` is the i-th row of the n x n identity matrix:
    a length-n list with 1 in position i and 0 elsewhere. *)
Fixpoint eye_row (n : nat) (i : nat) : list Z :=
  match n with
  | O => nil
  | S k =>
      match i with
      | O => 1%Z :: zrow k
      | S i' => 0%Z :: eye_row k i'
      end
  end.

Fixpoint meye_aux (n : nat) (i : nat) : mat :=
  match i with
  | O => nil
  | S k => meye_aux n k ++ [eye_row n k]
  end.

Definition meye (n : nat) : mat := meye_aux n n.

(* ---------- Element-wise arithmetic --------------------------------------- *)

(** `vadd xs ys` adds two vectors element-wise, keeping the tail of the
    longer vector once the shorter one is exhausted. *)
Fixpoint vadd (xs ys : list Z) : list Z :=
  match xs, ys with
  | nil, _ => ys
  | _, nil => xs
  | x :: xs', y :: ys' => (x + y) :: vadd xs' ys'
  end.

(** `vscale c xs` multiplies every entry of `xs` by the scalar `c`. *)
Definition vscale (c : Z) (xs : list Z) : list Z := map (fun x => c * x) xs.

(** `madd A B` adds two matrices row-by-row via `vadd`. *)
Fixpoint madd (A B : mat) : mat :=
  match A, B with
  | nil, _ => B
  | _, nil => A
  | r1 :: A', r2 :: B' => vadd r1 r2 :: madd A' B'
  end.

(** `mscale c A` multiplies every entry of `A` by the scalar `c`. *)
Definition mscale (c : Z) (A : mat) : mat := map (vscale c) A.

(* ---------- Transpose ----------------------------------------------------- *)

(** `heads m` is the list of first elements of each row of m
    (empty rows contribute 0). *)
Fixpoint heads (m : mat) : list Z :=
  match m with
  | nil => nil
  | row :: rest =>
      match row with
      | nil => 0%Z :: heads rest
      | x :: _ => x :: heads rest
      end
  end.

(** `tails m` drops the first element of every row. *)
Fixpoint tails (m : mat) : list (list Z) :=
  match m with
  | nil => nil
  | row :: rest =>
      match row with
      | nil => nil :: tails rest
      | _ :: r => r :: tails rest
      end
  end.

(** Are all rows empty? *)
Fixpoint all_empty (m : mat) : bool :=
  match m with
  | nil => true
  | nil :: rest => all_empty rest
  | _ :: _ => false
  end.

(** Transpose by column count: we must recur on a well-founded metric.
    Use the (summed) length of the first row as a fuel; on well-formed
    matrices this equals the number of columns. *)
Fixpoint mtrans_fuel (fuel : nat) (m : mat) : mat :=
  match fuel with
  | O => nil
  | S k =>
      if all_empty m then nil
      else heads m :: mtrans_fuel k (tails m)
  end.

Definition mtrans (m : mat) : mat :=
  match m with
  | nil => nil
  | row :: _ => mtrans_fuel (length row) m
  end.

(* ---------- Dot product and matrix product -------------------------------- *)

(** `dot_int xs ys` is the dot product of two vectors (any excess
    entries are ignored). *)
Fixpoint dot_int (xs ys : list Z) : Z :=
  match xs, ys with
  | nil, _ => 0%Z
  | _, nil => 0%Z
  | x :: xs', y :: ys' => x * y + dot_int xs' ys'
  end.

(** Matrix product via the transpose-trick formulation: this gives
    a clean expression that `vm_compute` reduces efficiently. *)
Definition mmul (A B : mat) : mat :=
  let Bt := mtrans B in
  map (fun row => map (fun col => dot_int row col) Bt) A.

(* ---------- Trace --------------------------------------------------------- *)

(** `mtrace_aux i m` sums the diagonal of `m` from column `i` onward. *)
Fixpoint mtrace_aux (i : nat) (m : mat) : Z :=
  match m with
  | nil => 0%Z
  | row :: rest => nth_Z row i + mtrace_aux (S i) rest
  end.

(** `mtrace m` is the trace (sum of the diagonal) of `m`. *)
Definition mtrace (m : mat) : Z := mtrace_aux 0 m.

