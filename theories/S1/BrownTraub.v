(* ============================================================== *)
(*  BrownTraub.v                                                    *)
(*                                                                  *)
(*  A plain `list Z` implementation of the modified Sturm chain     *)
(*  (Brown-Traub style), mirroring `mathcomp.real_closed.qe_rcf_th  *)
(*  .mods` but operating on the stdlib `pol = list Z` from          *)
(*  IntPoly, so the whole chain reduces under `vm_compute`.         *)
(*                                                                  *)
(*  The "next_mod" step transcribes, up to a sign equivalence,      *)
(*                                                                  *)
(*    next_mod p q := - (lc(q) ^ rscalp(p, q)) *: rmodp p q         *)
(*                                                                  *)
(*  Here we use the integer pseudo-remainder `prem` from IntPoly,   *)
(*  which already includes the lc(q)^(deg p - deg q + 1) scaling,   *)
(*  then negate.                                                    *)
(* ============================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
From PrimeGapS1 Require Import IntPoly.

(* ---------- The "next mod" step ---------- *)

(* Sign-flipped pseudo-remainder: equivalent, up to a positive
   integer scale, to `-(lc(q)^rscalp(p,q)) *: rmodp p q`. *)
Definition next_mod (p q : pol) : pol := pneg (prem p q).

(* ---------- The modified Sturm chain ---------- *)

(* Termination helper: a polynomial is "terminal" when it has degree 0,
   i.e. when its normalized size is at most 1. We do not recurse past a
   terminal polynomial. *)
Definition pterminal (p : pol) : bool := Nat.leb (psize p) 1.

(* Fuel-based loop. Invariant: `p` has already been emitted; we decide
   whether to emit `q` and recurse. The fuel `steps` is a structural
   argument and is always an over-approximation of the number of
   remaining steps. *)
Fixpoint mods_int_loop (steps : nat) (p q : pol) : list pol :=
  match steps with
  | O => []
  | S s =>
      match pnorm q with
      | [] =>
          (* q = 0: chain terminates, nothing more to emit. *)
          []
      | qn =>
          (* q is nonzero: emit it. Then, if q has degree >= 1,
             recurse on (q, next_mod p q). Otherwise stop. *)
          if pterminal qn then
            [qn]
          else
            qn :: mods_int_loop s qn (next_mod p qn)
      end
  end.

(* Top-level chain. The initial polynomial `p` is always emitted, then
   we delegate to the loop for `q` and its successors. Fuel is generous:
   `S (S (psize p))` bounds the length of the remaining tail since the
   degree strictly decreases at each step. *)
Definition mods_int (p q : pol) : list pol :=
  let pn := pnorm p in
  match pn with
  | [] =>
      (* p = 0: return the normalized q chain alone (empty if q also 0). *)
      mods_int_loop (S (S (psize q))) pzero q
  | _ =>
      pn :: mods_int_loop (S (S (psize p))) pn q
  end.

(* The Sturm chain of a single polynomial `p` is `mods_int p p'`. *)
Definition sturm_chain (p : pol) : list pol :=
  mods_int p (pderiv p).

(* ============================================================== *)
(*  Sanity tests                                                    *)
(* ============================================================== *)

(* Constant 1: the derivative is 0, so the chain stops immediately. *)
Example sturm_one : sturm_chain pone = [pone].
Proof. vm_compute. reflexivity. Qed.

(* X: derivative is 1 (degree 0), so the chain is [X; 1]. *)
Example sturm_X : sturm_chain pX = [[0; 1]; [1]].
Proof. vm_compute. reflexivity. Qed.

(* X^2 - 2: chain is [X^2 - 2; 2X; 4] (length 3). *)
Example sturm_X2_minus_2 :
  sturm_chain [-2; 0; 1] = [[-2; 0; 1]; [0; 2]; [4]].
Proof. vm_compute. reflexivity. Qed.

Example sturm_X2_minus_2_length :
  List.length (sturm_chain [-2; 0; 1]) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* X^2 + 1: chain length is 3 as well, but the terminal sign reveals
   that there are no real roots. *)
Example sturm_X2_plus_1 :
  sturm_chain [1; 0; 1] = [[1; 0; 1]; [0; 2]; [-2]].
Proof. vm_compute. reflexivity. Qed.

Example sturm_X2_plus_1_length :
  List.length (sturm_chain [1; 0; 1]) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

(* (X-1)(X-2)(X-3) = X^3 - 6 X^2 + 11 X - 6: chain length 4. *)
Example sturm_roots_123 :
  sturm_chain [-6; 11; -6; 1] =
  [[-6; 11; -6; 1]; [11; -12; 3]; [-12; 6]; [36]].
Proof. vm_compute. reflexivity. Qed.

Example sturm_roots_123_length :
  List.length (sturm_chain [-6; 11; -6; 1]) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(* Edge cases. *)
Example sturm_zero : sturm_chain pzero = [].
Proof. vm_compute. reflexivity. Qed.

Example mods_int_zero_q : mods_int [1; 2; 3] pzero = [[1; 2; 3]].
Proof. vm_compute. reflexivity. Qed.

Example mods_int_zero_p : mods_int pzero [1; 2; 3] = [[1; 2; 3]].
Proof. vm_compute. reflexivity. Qed.

Example mods_int_both_zero : mods_int pzero pzero = [].
Proof. vm_compute. reflexivity. Qed.

(* ============================================================== *)
(*  Shape lemma                                                     *)
(* ============================================================== *)

Lemma sturm_chain_nonempty : forall p, pnorm p <> [] -> sturm_chain p <> [].
Proof.
  intros p Hp.
  unfold sturm_chain, mods_int.
  destruct (pnorm p) as [| x xs] eqn:E.
  - exfalso; apply Hp; reflexivity.
  - simpl. discriminate.
Qed.

(* A fully unconditional version: for any *normalized-nonzero* polynomial,
   the chain is nonempty. We also state the trivial direction. *)
Lemma sturm_chain_zero : sturm_chain pzero = [].
Proof. reflexivity. Qed.

(* ============================================================== *)
(*  Performance test                                                *)
(* ============================================================== *)

(* Degree-3 polynomial: the chain has length 4 and computes quickly. *)
Example perf_sturm_degree_3 :
  List.length (sturm_chain [1; -2; 3; -4]) = 4%nat.
Proof. vm_compute. reflexivity. Qed.
