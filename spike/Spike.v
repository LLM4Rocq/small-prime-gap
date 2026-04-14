(* Spike v2: use stdlib QArith.Q — Z-backed rationals — for the heavy
   computation. MathComp rat uses unary nat internally and is unusable. *)
Require Import ZArith QArith Lia.
Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------------ *)
(* Simple dense representation: matrix = list of list of Q, vector = list Q. *)
Fixpoint zseq_from (start : nat) (len : nat) : list nat :=
  match len with
  | O => nil
  | S k => cons start (zseq_from (S start) k)
  end.

Definition seq_n (n : nat) := zseq_from O n.

Open Scope Q_scope.

(* entry(k,i,j) := 1 / (10^k + i*j + 1) *)
Definition bigD (k : nat) : Z := Z.pow 10 (Z.of_nat k).

Definition qentry (k : nat) (i j : nat) : Q :=
  let d := (bigD k + Z.of_nat (i*j) + 1)%Z in
  (1 # (Z.to_pos d)).

Definition mk_row (n k i : nat) : list Q :=
  map (fun j => qentry k i j) (seq_n n).

Definition mk_M (n k : nat) : list (list Q) :=
  map (fun i => mk_row n k i) (seq_n n).

Definition mk_v (n k : nat) : list Q :=
  map (fun i => qentry (Nat.div k 2) (i + 2) (i + 3)) (seq_n n).

(* dot product *)
Fixpoint qdot (xs ys : list Q) : Q :=
  match xs, ys with
  | x::xs', y::ys' => x * y + qdot xs' ys'
  | _, _ => 0
  end.

(* mat-vec: M * v  as list Q *)
Definition mat_vec (M : list (list Q)) (v : list Q) : list Q :=
  map (fun row => qdot row v) M.

(* quadratic form v^T M v *)
Definition qform (M : list (list Q)) (v : list Q) : Q :=
  qdot v (mat_vec M v).

Definition rayleigh (n k : nat) : Q :=
  qform (mk_M n k) (mk_v n k).

Definition rayleigh_pos (n k : nat) : bool :=
  match Qcompare 0 (rayleigh n k) with Lt => true | _ => false end.

(* ================== TIMINGS ================== *)

(* 8x8, 10-digit *)
Time Eval vm_compute in (rayleigh_pos 8 10).
(* 8x8, 30-digit *)
Time Eval vm_compute in (rayleigh_pos 8 30).
(* 8x8, 100-digit *)
Time Eval vm_compute in (rayleigh_pos 8 100).

(* 16x16 *)
Time Eval vm_compute in (rayleigh_pos 16 10).
Time Eval vm_compute in (rayleigh_pos 16 30).
Time Eval vm_compute in (rayleigh_pos 16 100).

(* 42x42 *)
Time Eval vm_compute in (rayleigh_pos 42 10).
Time Eval vm_compute in (rayleigh_pos 42 30).
Time Eval vm_compute in (rayleigh_pos 42 100).

(* native_compute comparison *)
Time Eval native_compute in (rayleigh_pos 42 100).

(* Integer (cleared-denom) variant: M' = (10^k)*M is a list (list Z).
   We need v^T M' v > 0 as Z — fully in Z world. *)
Definition zentry (k i j : nat) : Z := (bigD k + Z.of_nat (i*j) + 1)%Z.
(* But to mimic rational weighting we'd clear with common denom; for the
   spike we just test raw integer bilinear form M' with integer vector. *)
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
Time Eval native_compute in (zqform_pos 42 300).
