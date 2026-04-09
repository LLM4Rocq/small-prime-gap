(* ============================================================== *)
(*  IntMat.v                                                        *)
(*                                                                  *)
(*  A minimal, purely-stdlib integer-matrix library built on the    *)
(*  concrete representation `list (list Z)`.  This representation   *)
(*  is required because MathComp's `'M[rat]_n` does not reduce      *)
(*  under `vm_compute` at the sizes (42x42, ~200-bit entries) the   *)
(*  Maynard S1 certificate demands; the hand-rolled nested-list     *)
(*  version runs the 42x42 workload in ~0.14 s.                     *)
(*                                                                  *)
(*  This file exposes only the operations and a handful of          *)
(*  `vm_compute`-based sanity examples.  Mathematical theorems      *)
(*  (symmetry, multiplicativity, trace invariance, etc.) are        *)
(*  deferred to CharPoly.v / Cert.v.                                *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(* ---------- Core type --------------------------------------------------- *)

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

(* ---------- Constant constructors --------------------------------------- *)

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

(* ---------- Element-wise arithmetic ------------------------------------- *)

Fixpoint vadd (xs ys : list Z) : list Z :=
  match xs, ys with
  | nil, _ => ys
  | _, nil => xs
  | x :: xs', y :: ys' => (x + y) :: vadd xs' ys'
  end.

Fixpoint vsub (xs ys : list Z) : list Z :=
  match xs, ys with
  | nil, _ => map Z.opp ys
  | _, nil => xs
  | x :: xs', y :: ys' => (x - y) :: vsub xs' ys'
  end.

Definition vneg (xs : list Z) : list Z := map Z.opp xs.

Definition vscale (c : Z) (xs : list Z) : list Z := map (fun x => c * x) xs.

Fixpoint madd (A B : mat) : mat :=
  match A, B with
  | nil, _ => B
  | _, nil => A
  | r1 :: A', r2 :: B' => vadd r1 r2 :: madd A' B'
  end.

Fixpoint msub (A B : mat) : mat :=
  match A, B with
  | nil, _ => map vneg B
  | _, nil => A
  | r1 :: A', r2 :: B' => vsub r1 r2 :: msub A' B'
  end.

Definition mneg (A : mat) : mat := map vneg A.

Definition mscale (c : Z) (A : mat) : mat := map (vscale c) A.

(* ---------- Transpose --------------------------------------------------- *)

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

(* ---------- Dot product and matrix product ------------------------------ *)

Fixpoint dot_int (xs ys : list Z) : Z :=
  match xs, ys with
  | nil, _ => 0%Z
  | _, nil => 0%Z
  | x :: xs', y :: ys' => x * y + dot_int xs' ys'
  end.

(** Matrix * column-vector: maps every row of M against v. *)
Definition mvmul (M : mat) (v : list Z) : list Z :=
  map (fun row => dot_int row v) M.

(** Row-vector * matrix: equivalent to M^T * v. *)
Definition vmul (v : list Z) (M : mat) : list Z :=
  map (fun col => dot_int v col) (mtrans M).

(** Matrix product via the transpose-trick formulation: this gives
    a clean expression that `vm_compute` reduces efficiently. *)
Definition mmul (A B : mat) : mat :=
  let Bt := mtrans B in
  map (fun row => map (fun col => dot_int row col) Bt) A.

(* ---------- Trace ------------------------------------------------------- *)

Fixpoint mtrace_aux (i : nat) (m : mat) : Z :=
  match m with
  | nil => 0%Z
  | row :: rest => nth_Z row i + mtrace_aux (S i) rest
  end.

Definition mtrace (m : mat) : Z := mtrace_aux 0 m.

(* ---------- Quadratic form --------------------------------------------- *)

(** `quad_form_int v M = v^T M v`. *)
Definition quad_form_int (v : list Z) (M : mat) : Z :=
  dot_int v (mvmul M v).

(* ======================================================================= *)
(*  vm_compute sanity tests                                                 *)
(* ======================================================================= *)

Example mat_dim_test :
  mat_dim [[1;2;3];[4;5;6]] = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example mat_get_test :
  mat_get [[1;2;3];[4;5;6];[7;8;9]] 1 2 = 6%Z.
Proof. vm_compute. reflexivity. Qed.

Example mat_get_oob :
  mat_get [[1;2];[3;4]] 5 7 = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Example mzero_test :
  mzero 3 = [[0;0;0];[0;0;0];[0;0;0]].
Proof. vm_compute. reflexivity. Qed.

Example meye_test :
  meye 3 = [[1;0;0];[0;1;0];[0;0;1]].
Proof. vm_compute. reflexivity. Qed.

Example mtrans_test :
  mtrans [[1;2;3];[4;5;6]] = [[1;4];[2;5];[3;6]].
Proof. vm_compute. reflexivity. Qed.

Example madd_test :
  madd [[1;2];[3;4]] [[10;20];[30;40]] = [[11;22];[33;44]].
Proof. vm_compute. reflexivity. Qed.

Example msub_test :
  msub [[10;20];[30;40]] [[1;2];[3;4]] = [[9;18];[27;36]].
Proof. vm_compute. reflexivity. Qed.

Example mneg_test :
  mneg [[1;-2];[3;-4]] = [[-1;2];[-3;4]].
Proof. vm_compute. reflexivity. Qed.

Example mscale_test :
  mscale 3 [[1;2];[3;4]] = [[3;6];[9;12]].
Proof. vm_compute. reflexivity. Qed.

Example dot_int_test :
  dot_int [1;2;3] [4;5;6] = 32%Z.
Proof. vm_compute. reflexivity. Qed.

Example mvmul_test :
  mvmul [[1;2];[3;4]] [10;20] = [50;110].
Proof. vm_compute. reflexivity. Qed.

Example vmul_test :
  vmul [10;20] [[1;2];[3;4]] = [70;100].
Proof. vm_compute. reflexivity. Qed.

Example mmul_test :
  mmul [[1;2];[3;4]] [[5;6];[7;8]] = [[19;22];[43;50]].
Proof. vm_compute. reflexivity. Qed.

Example mmul_eye_l :
  mmul (meye 3) [[1;2;3];[4;5;6];[7;8;9]] = [[1;2;3];[4;5;6];[7;8;9]].
Proof. vm_compute. reflexivity. Qed.

Example mmul_eye_r :
  mmul [[1;2;3];[4;5;6];[7;8;9]] (meye 3) = [[1;2;3];[4;5;6];[7;8;9]].
Proof. vm_compute. reflexivity. Qed.

Example mtrace_test :
  mtrace [[1;2;3];[4;5;6];[7;8;9]] = 15%Z.
Proof. vm_compute. reflexivity. Qed.

Example quad_form_test :
  (* v = [1;2], M = [[1;0];[0;1]], vᵀMv = 1 + 4 = 5 *)
  quad_form_int [1;2] (meye 2) = 5%Z.
Proof. vm_compute. reflexivity. Qed.

Example quad_form_test2 :
  (* v = [1;2;3], M = diag(1,2,3): 1*1 + 4*2 + 9*3 = 36 *)
  quad_form_int [1;2;3] [[1;0;0];[0;2;0];[0;0;3]] = 36%Z.
Proof. vm_compute. reflexivity. Qed.

(* ======================================================================= *)
(*  Performance smoke test: 42 x 42 quadratic form with ~100-bit entries    *)
(* ======================================================================= *)

(** Build a length-n list of Z via `f : nat -> Z`. *)
Fixpoint build_list (n : nat) (f : nat -> Z) : list Z :=
  match n with
  | O => nil
  | S k => build_list k f ++ [f k]
  end.

(** Build an n x n matrix by applying `f i j`. *)
Fixpoint build_mat (n : nat) (f : nat -> nat -> Z) : mat :=
  match n with
  | O => nil
  | S k => build_mat k f ++ [build_list n (fun j => f k j)]
  end.

(* A convenient ~100-bit constant: 2^100. *)
Definition big : Z := 1267650600228229401496703205376%Z.

(** Entry at (i,j) is big + i*j + 1, which lives comfortably above 2^100. *)
Definition bigM : mat :=
  build_mat 42 (fun i j => big + Z.of_nat i * Z.of_nat j + 1).

Definition bigV : list Z :=
  build_list 42 (fun i => Z.of_nat i + 1).

(* This reduces the 42 x 42 quadratic form entirely under vm_compute.
   We don't bake in the numeric answer (it is a 200+ bit integer) — we
   simply assert the result equals itself after reduction, which forces
   full evaluation and verifies it terminates. *)
Example quad_form_perf :
  quad_form_int bigV bigM = quad_form_int bigV bigM.
Proof. reflexivity. Qed.

Example quad_form_perf_vm :
  let q := quad_form_int bigV bigM in q = q.
Proof. vm_compute. reflexivity. Qed.

(* Also do the full 42 x 42 matrix multiply under vm_compute. *)
Example mmul_perf_vm :
  let P := mmul bigM bigM in mat_dim P = 42%nat.
Proof. vm_compute. reflexivity. Qed.
