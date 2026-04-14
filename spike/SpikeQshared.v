(* Spike Q-shared: Q mat-vec where all entries have a SHARED big denominator.
   Mimics M1,M2 where the entries are P(105) / (105+b+2c)!. *)
Require Import ZArith QArith.
Require Import List.
Import ListNotations.

Fixpoint zseq_from (s len : nat) : list nat :=
  match len with O => nil | S k => cons s (zseq_from (S s) k) end.
Definition seq_n (n : nat) := zseq_from O n.

Open Scope Q_scope.

(* Shared denominator: single factorial-style value D = 117! ~ 2*10^193 bits. *)
Fixpoint zfact (n : nat) : Z :=
  match n with O => 1%Z | S k => (Z.of_nat (S k) * zfact k)%Z end.
Definition D : Z := zfact 117.

(* Entries: (i*j + 17) / D  --- numerators are small integers, all sharing D. *)
Definition qentry (i j : nat) : Q :=
  (Z.of_nat (i*j + 17) # Z.to_pos D).

Definition mk_row (n i : nat) : list Q :=
  map (fun j => qentry i j) (seq_n n).
Definition mk_M (n : nat) : list (list Q) :=
  map (fun i => mk_row n i) (seq_n n).
Definition mk_v (n : nat) : list Q :=
  map (fun i => qentry (i+2) (i+3)) (seq_n n).

Fixpoint qdot (xs ys : list Q) : Q :=
  match xs, ys with
  | cons x xs', cons y ys' => Qplus (Qmult x y) (qdot xs' ys')
  | _, _ => 0
  end.
Definition mat_vec (M : list (list Q)) (v : list Q) : list Q :=
  map (fun r => qdot r v) M.
Definition qform (M : list (list Q)) (v : list Q) : Q := qdot v (mat_vec M v).

Definition rayleigh (n : nat) : Q := qform (mk_M n) (mk_v n).
Definition rayleigh_pos (n : nat) : bool :=
  match Qcompare 0 (rayleigh n) with Lt => true | _ => false end.

Time Eval vm_compute in (rayleigh_pos 8).
Time Eval vm_compute in (rayleigh_pos 16).
Time Eval vm_compute in (rayleigh_pos 24).
Time Eval vm_compute in (rayleigh_pos 42).
