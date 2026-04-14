(* Spike Z: integer-only (cleared denominator) mat-vec over Z. *)
Require Import ZArith.
Require Import List.
Import ListNotations.

Fixpoint zseq_from (start : nat) (len : nat) : list nat :=
  match len with
  | O => nil
  | S k => cons start (zseq_from (S start) k)
  end.
Definition seq_n (n : nat) := zseq_from O n.

Definition bigD (k : nat) : Z := Z.pow 10 (Z.of_nat k).
Definition zentry (k i j : nat) : Z := (bigD k + Z.of_nat (i*j) + 1)%Z.
Definition mk_Mi (n k : nat) : list (list Z) :=
  map (fun i => map (fun j => zentry k i j) (seq_n n)) (seq_n n).
Definition mk_vi (n : nat) : list Z :=
  map (fun i => Z.of_nat (i+1)) (seq_n n).

Fixpoint zdot (xs ys : list Z) : Z :=
  match xs, ys with
  | x::xs', y::ys' => (x * y + zdot xs' ys')%Z
  | _, _ => 0%Z
  end.
Definition zmat_vec (M : list (list Z)) (v : list Z) : list Z :=
  map (fun row => zdot row v) M.
Definition zqform (n k : nat) : Z :=
  let v := mk_vi n in
  zdot v (zmat_vec (mk_Mi n k) v).
Definition zqform_pos (n k : nat) : bool :=
  match Z.compare 0 (zqform n k) with Lt => true | _ => false end.

Time Eval vm_compute in (zqform_pos 42 30).
Time Eval vm_compute in (zqform_pos 42 100).
Time Eval vm_compute in (zqform_pos 42 300).
Time Eval vm_compute in (zqform_pos 100 300).
Time Eval native_compute in (zqform_pos 42 300).
Time Eval native_compute in (zqform_pos 100 300).
