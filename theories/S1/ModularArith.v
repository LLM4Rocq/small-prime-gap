(* ===================================================================
   ModularArith.v: shared Uint63 modular arithmetic and matrix helpers.

   Both CRTBridge.v and CharPolyAgree.v previously duplicated all of
   these definitions, which caused the kernel's conversion checker to
   explode when comparing terms involving char_poly_mod from different
   files (two different constants, identical bodies). Extracting them
   here ensures a single canonical definition.
   =================================================================== *)

From Stdlib Require Import ZArith List Uint63.
From PrimeGapS1 Require Import IntMat CharPoly.
From Bignums Require Import BigZ.

Import ListNotations.
Open Scope Z_scope.
Open Scope uint63_scope.

Definition addmod63 (p a b : int) : int := (a + b) mod p.
Definition mulmod63 (p a b : int) : int := (a * b) mod p.
Definition negmod63 (p a : int) : int := (p - a mod p) mod p.

Fixpoint powmod_fast (p base : int) (exp : N) (fuel : nat) : int :=
  match fuel with
  | O => 1 mod p
  | S f =>
    match exp with
    | N0 => 1 mod p
    | Npos xH => base mod p
    | Npos (xO e) =>
        let half := powmod_fast p base (Npos e) f in
        mulmod63 p half half
    | Npos (xI e) =>
        let half := powmod_fast p base (Npos e) f in
        mulmod63 p base (mulmod63 p half half)
    end
  end.

Definition inv_mod63 (p a : int) : int :=
  let exp := N.sub (Z.to_N (Uint63.to_Z p)) 2%N in
  powmod_fast p a exp 63.

Definition divmod63 (p a b : int) : int :=
  mulmod63 p a (inv_mod63 p b).

Definition mmat := list (list int).

Definition Z_to_mod63 (p : int) (z : Z) : int :=
  let p_bigZ := BigZ.of_Z (Uint63.to_Z p) in
  Uint63.of_Z (BigZ.to_Z (BigZ.modulo (BigZ.of_Z z) p_bigZ)).

Definition reduce_mat_Z (p : int) (M : list (list Z)) : mmat :=
  List.map (List.map (Z_to_mod63 p)) M.

Fixpoint mmat_vadd (p : int) (xs ys : list int) : list int :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' => addmod63 p x y :: mmat_vadd p xs' ys'
  end.

Fixpoint mmat_add (p : int) (A B : mmat) : mmat :=
  match A, B with
  | [], _ => B
  | _, [] => A
  | r1 :: A', r2 :: B' => mmat_vadd p r1 r2 :: mmat_add p A' B'
  end.

Definition mmat_vscale (p c : int) (xs : list int) : list int :=
  List.map (mulmod63 p c) xs.

Definition mmat_scale (p c : int) (A : mmat) : mmat :=
  List.map (mmat_vscale p c) A.

Fixpoint dot_mod (p : int) (xs ys : list int) : int :=
  match xs, ys with
  | [], _ => 0
  | _, [] => 0
  | x :: xs', y :: ys' => addmod63 p (mulmod63 p x y) (dot_mod p xs' ys')
  end.

Fixpoint mmat_heads (m : mmat) : list int :=
  match m with
  | [] => []
  | row :: rest =>
      match row with
      | [] => 0 :: mmat_heads rest
      | x :: _ => x :: mmat_heads rest
      end
  end.

Fixpoint mmat_tails (m : mmat) : mmat :=
  match m with
  | [] => []
  | row :: rest =>
      match row with
      | [] => [] :: mmat_tails rest
      | _ :: r => r :: mmat_tails rest
      end
  end.

Fixpoint mmat_all_empty (m : mmat) : bool :=
  match m with
  | [] => true
  | [] :: rest => mmat_all_empty rest
  | _ :: _ => false
  end.

Fixpoint mmat_trans_fuel (fuel : nat) (m : mmat) : mmat :=
  match fuel with
  | O => []
  | S k =>
      if mmat_all_empty m then []
      else mmat_heads m :: mmat_trans_fuel k (mmat_tails m)
  end.

Definition mmat_trans (m : mmat) : mmat :=
  match m with
  | [] => []
  | row :: _ => mmat_trans_fuel (List.length row) m
  end.

Definition mmat_mul (p : int) (A B : mmat) : mmat :=
  let Bt := mmat_trans B in
  List.map (fun row => List.map (fun col => dot_mod p row col) Bt) A.

Fixpoint mmat_trace_aux (p : int) (i : nat) (m : mmat) : int :=
  match m with
  | [] => 0
  | row :: rest =>
      addmod63 p (nth i row 0) (mmat_trace_aux p (S i) rest)
  end.

Definition mmat_trace (p : int) (m : mmat) : int :=
  mmat_trace_aux p 0 m.

Fixpoint mmat_eye_row (p : int) (n i : nat) : list int :=
  match n with
  | O => []
  | S k =>
      match i with
      | O => (1 mod p) :: List.repeat 0 k
      | S i' => 0 :: mmat_eye_row p k i'
      end
  end.

Fixpoint mmat_eye_aux (p : int) (n i : nat) : mmat :=
  match i with
  | O => []
  | S k => mmat_eye_aux p n k ++ [mmat_eye_row p n k]
  end.

Definition mmat_eye (p : int) (n : nat) : mmat :=
  mmat_eye_aux p n n.

Definition mmat_zero (n : nat) : mmat :=
  List.repeat (List.repeat 0 n) n.

Fixpoint fl_mod_loop (p : int) (A I_n : mmat) (M_prev : mmat)
    (c_prev : int) (k : int) (acc : list int) (steps : nat) : list int :=
  match steps with
  | O => acc
  | S s =>
      let AM_prev := mmat_mul p A M_prev in
      let M_k := mmat_add p AM_prev (mmat_scale p c_prev I_n) in
      let AM_k := mmat_mul p A M_k in
      let tr := mmat_trace p AM_k in
      let neg_tr := negmod63 p tr in
      let c_new := divmod63 p neg_tr k in
      fl_mod_loop p A I_n M_k c_new (k + 1) (c_new :: acc) s
  end.

Definition char_poly_mod (p : int) (M : list (list Z)) : list int :=
  let n := List.length M in
  let Mr := reduce_mat_Z p M in
  let I_n := mmat_eye p n in
  let M0 := mmat_zero n in
  let one := 1 mod p in
  let coeffs := fl_mod_loop p Mr I_n M0 one 1 [] n in
  coeffs ++ [one].

Close Scope uint63_scope.
