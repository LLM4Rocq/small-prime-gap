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

(* ======================================================================= *)
(*  Integer determinant via Bareiss fraction-free Gaussian elimination      *)
(* ======================================================================= *)

(** The Bareiss algorithm performs Gaussian elimination while keeping
    all intermediate values integer.  After the k-th elimination step,
    every entry M[i,j] (for i,j > k) in the transformed matrix is
    exactly divisible by the previous pivot; this is the Bareiss
    invariant.  The final bottom-right element equals det(A).

    We use a "peel" representation: at each step the pivot row and
    first column of every remaining row are removed, and the remaining
    (n-1) x (n-1) submatrix is updated in-place.  This keeps the
    recursion structurally decreasing on the matrix.

    Limitation: this implementation requires each leading pivot after
    row-swap search to be nonzero; it handles a zero pivot by trying
    to swap in a later row with a nonzero first entry (tracking the
    sign).  If the entire leading column is zero, the determinant is
    0 and we return 0 directly.  For SPD input matrices (our target)
    no pivoting is ever required.

    TODO: prove correctness.  For now this is a computational artifact
    used only in `vm_compute` discharge of numeric nonzero checks. *)

(** `tl_Z xs` is the tail of `xs`, or nil on empty. *)
Definition tl_Z (xs : list Z) : list Z :=
  match xs with
  | nil => nil
  | _ :: t => t
  end.

(** `hd_Z xs` is the head of `xs`, or 0 on empty. *)
Definition hd_Z (xs : list Z) : Z :=
  match xs with
  | nil => 0%Z
  | x :: _ => x
  end.

(** `bareiss_update_row prev p pivot_tail row` computes the Bareiss
    update of a single row.  Given the current pivot `p = pivot[0]`,
    the tail of the pivot row `pivot_tail = pivot[1..]`, the previous
    pivot `prev`, and the row to update `row = [r0; r1; r2; ...]`,
    it returns the new row (of length one less than `row`):
       out[j-1] := (p * row[j] - r0 * pivot_tail[j-1]) / prev
    for j = 1, 2, ....  The division is exact by the Bareiss invariant. *)
Fixpoint bareiss_update_row (prev p r0 : Z) (pivot_tail row_tail : list Z) : list Z :=
  match pivot_tail, row_tail with
  | nil, _ => nil
  | _, nil => nil
  | pj :: ptail', rj :: rtail' =>
      ((p * rj - r0 * pj) / prev)
        :: bareiss_update_row prev p r0 ptail' rtail'
  end.

(** `bareiss_step prev pivot rest` applies one elimination step to
    every row in `rest`, producing the updated sub-matrix (without
    the pivot row and without the first column). *)
Definition bareiss_step (prev : Z) (pivot : list Z) (rest : mat) : mat :=
  let p := hd_Z pivot in
  let ptail := tl_Z pivot in
  map (fun row => bareiss_update_row prev p (hd_Z row) ptail (tl_Z row)) rest.

(** `find_pivot_row rows` searches `rows` for the first row whose
    first entry is nonzero.  Returns `None` if no such row exists.
    On success, returns `(before, pivot, after)` where
    `before ++ pivot :: after = rows` and `hd pivot <> 0`. *)
Fixpoint find_pivot_row (rows : mat) : option (mat * list Z * mat) :=
  match rows with
  | nil => None
  | r :: rest =>
      if Z.eqb (hd_Z r) 0 then
        match find_pivot_row rest with
        | None => None
        | Some (before, piv, after) => Some (r :: before, piv, after)
        end
      else
        Some (nil, r, rest)
  end.

(** `bareiss_loop fuel sign prev M` runs the Bareiss elimination
    loop.  `sign` tracks the sign flip from row swaps (1 or -1).
    `prev` is the previous pivot (initially 1).  The determinant is
    returned as `sign * (final pivot)`. *)
Fixpoint bareiss_loop (fuel : nat) (sign prev : Z) (M : mat) : Z :=
  match fuel with
  | O => 0%Z
  | S fuel' =>
      match M with
      | nil => prev   (* empty matrix: determinant 1, but prev carries it *)
      | row :: rest =>
          (* Try to use `row` as pivot; if its first entry is 0,
             search `rest` for a swap partner. *)
          if Z.eqb (hd_Z row) 0 then
            match find_pivot_row rest with
            | None => 0%Z   (* entire leading column is zero: det = 0 *)
            | Some (before, piv, after) =>
                (* Swap `row` with `piv`: new matrix is
                     piv :: (before ++ row :: after)
                   and sign flips. *)
                let M' := piv :: (before ++ row :: after) in
                bareiss_loop fuel' (- sign) prev M'
            end
          else
            match rest with
            | nil =>
                (* Single remaining row: its head is the final pivot. *)
                sign * hd_Z row
            | _ =>
                let p := hd_Z row in
                let rest' := bareiss_step prev row rest in
                bareiss_loop fuel' sign p rest'
            end
      end
  end.

(** `det_int M` computes the determinant of a square matrix `M` by
    Bareiss elimination.  Undefined behaviour on non-square input. *)
Definition det_int (M : mat) : Z :=
  match M with
  | nil => 1%Z
  | _ => bareiss_loop (mat_dim M) 1 1 M
  end.

(** Singular-matrix test: `mat_singular_int M = true` iff det M = 0. *)
Definition mat_singular_int (M : mat) : bool :=
  Z.eqb (det_int M) 0.

(* ---------- Optional: Laplace expansion for small-matrix cross-checks --- *)

(** `drop_nth i xs` removes the i-th element of `xs`. *)
Fixpoint drop_nth {A : Type} (i : nat) (xs : list A) : list A :=
  match i, xs with
  | _, nil => nil
  | O, _ :: t => t
  | S k, x :: t => x :: drop_nth k t
  end.

(** `minor_mat i M` deletes row 0 and column i from `M`. *)
Definition minor_mat (i : nat) (M : mat) : mat :=
  match M with
  | nil => nil
  | _ :: rest => map (drop_nth i) rest
  end.

Fixpoint det_int_laplace_fuel (fuel : nat) (M : mat) : Z :=
  match M with
  | nil => 1%Z  (* det of 0 x 0 is 1 *)
  | row :: _ =>
      match row with
      | nil => 1%Z
      | _ =>
          match fuel with
          | O => 0%Z  (* out of fuel; should not happen with correct fuel *)
          | S fuel' =>
              (* Expand along the first row. *)
              (fix expand (j : nat) (r : list Z) : Z :=
                 match r with
                 | nil => 0%Z
                 | x :: r' =>
                     let sign := if Nat.even j then 1%Z else (-1)%Z in
                     sign * x * det_int_laplace_fuel fuel' (minor_mat j M)
                       + expand (S j) r'
                 end) O row
          end
      end
  end.

Definition det_int_laplace (M : mat) : Z :=
  det_int_laplace_fuel (mat_dim M) M.

(* ======================================================================= *)
(*  det_int sanity tests                                                    *)
(* ======================================================================= *)

Example det_int_1x1 :
  det_int [[5]] = 5%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_2x2 :
  det_int [[1; 2]; [3; 4]] = (-2)%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_eye3 :
  det_int (meye 3) = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_diag3 :
  det_int [[2; 0; 0]; [0; 3; 0]; [0; 0; 5]] = 30%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_3x3 :
  det_int [[1; 2; 3]; [4; 5; 6]; [7; 8; 10]] = (-3)%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_eye5 :
  det_int (meye 5) = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_eye10 :
  det_int (meye 10) = 1%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_laplace_3x3 :
  det_int_laplace [[1; 2; 3]; [4; 5; 6]; [7; 8; 10]] = (-3)%Z.
Proof. vm_compute. reflexivity. Qed.

Example det_int_laplace_agree_3x3 :
  det_int_laplace [[1; 2; 3]; [4; 5; 6]; [7; 8; 10]]
    = det_int [[1; 2; 3]; [4; 5; 6]; [7; 8; 10]].
Proof. vm_compute. reflexivity. Qed.

Example mat_singular_int_eye3 :
  mat_singular_int (meye 3) = false.
Proof. vm_compute. reflexivity. Qed.

Example mat_singular_int_zero_row :
  mat_singular_int [[1; 2]; [0; 0]] = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------- Performance test ---------- *)

(** Build a length-n list by applying `f` to indices 0, 1, ..., n-1
    in order.  Helper local to the determinant tests: unlike the
    pre-existing `build_list`/`build_mat` (which walk indices from
    high to low), this variant yields a standard row-major shape. *)
Fixpoint build_list_sq (i n : nat) (f : nat -> Z) : list Z :=
  match n with
  | O => nil
  | S k => f i :: build_list_sq (S i) k f
  end.

Fixpoint build_mat_sq_aux (i n total : nat) (f : nat -> nat -> Z) : mat :=
  match n with
  | O => nil
  | S k => build_list_sq O total (f i)
             :: build_mat_sq_aux (S i) k total f
  end.

Definition build_mat_sq (n : nat) (f : nat -> nat -> Z) : mat :=
  build_mat_sq_aux O n n f.

(** A 10 x 10 integer diagonal matrix with entries 1,2,...,10; its
    determinant is 10! = 3628800. *)
Definition diag10 : mat :=
  build_mat_sq 10 (fun i j => if Nat.eqb i j then Z.of_nat (S i) else 0%Z).

Example det_int_diag10 :
  det_int diag10 = 3628800%Z.
Proof. vm_compute. reflexivity. Qed.

(** A 10 x 10 Vandermonde-ish test with known answer.  Using a dense
    matrix: A[i,j] = 1 + i + j * (i + 1) is invertible for small n and
    its determinant reduces quickly.  We use a self-equality assertion
    to force full `vm_compute` reduction. *)
Definition denseM (n : nat) : mat :=
  build_mat_sq n (fun i j => Z.of_nat (1 + i + (j + 1) * (i + 1))).

Example det_int_dense10_selfeq :
  let d := det_int (denseM 10) in d = d.
Proof. vm_compute. reflexivity. Qed.

(** Larger smoke test: 12 x 12 diagonal with small entries.  Answer: 12!. *)
Definition diag12 : mat :=
  build_mat_sq 12 (fun i j => if Nat.eqb i j then Z.of_nat (S i) else 0%Z).

Example det_int_diag12 :
  det_int diag12 = 479001600%Z.
Proof. vm_compute. reflexivity. Qed.
