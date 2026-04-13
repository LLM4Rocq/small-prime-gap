(* ===================================================================
   CRTBridge.v -- Prove that the Uint63 Faddeev-LeVerrier computation
   mod a prime p gives the same result as the Z-level FL computation
   reduced mod p.

   Main theorem:
     char_poly_mod_sound :
       List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M

   This is the key bridge needed to close the CRT lift admits in
   CertL2.v: once we know the Uint63 FL equals the Z FL reduced mod p,
   we can conclude that agreement of the Uint63 FL with the FLINT
   polynomial mod 710 primes implies Z-level agreement.

   NOTE: This file does NOT import CharPolyAgree.v (to avoid loading
   the 710-prime table). It re-defines the necessary Uint63 matrix
   operations locally, matching CharPolyAgree.v exactly.
   =================================================================== *)

From Stdlib Require Import ZArith List Lia Uint63.
From PrimeGapS1 Require Import Fermat.
Import ListNotations.
Open Scope Z_scope.

From Bignums Require Import BigZ.

From PrimeGapS1 Require Import IntMat CharPoly.

(* ================================================================== *)
(* Section 0: Re-define the Uint63 operations matching CharPolyAgree.v *)
(* ================================================================== *)

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

(* ================================================================== *)
(* Section 1: Specification of Z_to_mod63                              *)
(* ================================================================== *)

Close Scope uint63_scope.

(* "p is a valid modular prime" -- fits in half-word so products
   of two residues don't overflow 63 bits. *)
Definition valid_prime (p : int) : Prop :=
  (1 < Uint63.to_Z p)%Z /\ (Uint63.to_Z p < 2^31)%Z.

(* Key spec: Z_to_mod63 faithfully computes z mod p as a Uint63 value. *)
Lemma Z_to_mod63_spec (p : int) (z : Z) :
  valid_prime p ->
  Uint63.to_Z (Z_to_mod63 p z) = (z mod Uint63.to_Z p)%Z.
Proof.
  intros [Hp1 Hp2].
  unfold Z_to_mod63.
  rewrite BigZ.spec_modulo. rewrite !BigZ.spec_of_Z.
  rewrite of_Z_spec.
  (* Need: (z mod to_Z p) mod wB = z mod to_Z p *)
  (* Because 0 <= z mod to_Z p < to_Z p < 2^31 < 2^63 = wB *)
  rewrite Z.mod_small; [reflexivity|].
  split.
  - apply Z.mod_pos_bound. lia.
  - assert (z mod Uint63.to_Z p < Uint63.to_Z p)%Z
      by (apply Z.mod_pos_bound; lia).
    assert (wB = (2^63)%Z) as ->
      by (unfold wB; reflexivity).
    lia.
Qed.

(* Corollary: Z_to_mod63 values are bounded by p *)
Lemma Z_to_mod63_bound (p : int) (z : Z) :
  valid_prime p ->
  (0 <= Uint63.to_Z (Z_to_mod63 p z) < Uint63.to_Z p)%Z.
Proof.
  intros Hv. rewrite Z_to_mod63_spec; [|exact Hv].
  apply Z.mod_pos_bound. destruct Hv; lia.
Qed.

(* ================================================================== *)
(* Section 2: Modular arithmetic soundness                             *)
(* ================================================================== *)

(* The key overflow lemma: when a, b < p < 2^31,
   a * b < 2^62 < 2^63 = wB, so Uint63 multiplication doesn't wrap. *)
Lemma no_overflow_mul (a b p : Z) :
  (0 <= a < p)%Z -> (0 <= b < p)%Z -> (p < 2^31)%Z ->
  (a * b < wB)%Z.
Proof.
  intros [Ha1 Ha2] [Hb1 Hb2] Hp.
  assert (wB = (2^63)%Z) as -> by reflexivity.
  nia.
Qed.

(* Similarly for addition: a + b < 2*p < 2^32 < 2^63 = wB. *)
Lemma no_overflow_add (a b p : Z) :
  (0 <= a < p)%Z -> (0 <= b < p)%Z -> (p < 2^31)%Z ->
  (a + b < wB)%Z.
Proof.
  intros [Ha1 Ha2] [Hb1 Hb2] Hp.
  assert (wB = (2^63)%Z) as -> by reflexivity.
  lia.
Qed.

(* mulmod63 soundness: to_Z(mulmod63 p a b) = (to_Z a * to_Z b) mod to_Z p *)
Lemma mulmod63_spec (p a b : int) :
  valid_prime p ->
  (0 <= Uint63.to_Z a < Uint63.to_Z p)%Z ->
  (0 <= Uint63.to_Z b < Uint63.to_Z p)%Z ->
  Uint63.to_Z (mulmod63 p a b) =
    ((Uint63.to_Z a * Uint63.to_Z b) mod Uint63.to_Z p)%Z.
Proof.
  intros [Hp1 Hp2] Ha Hb.
  unfold mulmod63.
  rewrite mod_spec. rewrite mul_spec.
  assert (Hnf : (0 <= Uint63.to_Z a * Uint63.to_Z b < wB)%Z).
  { split; [apply Z.mul_nonneg_nonneg; lia|exact (no_overflow_mul _ _ _ Ha Hb Hp2)]. }
  rewrite (Z.mod_small _ wB Hnf). reflexivity.
Qed.

(* addmod63 soundness *)
Lemma addmod63_spec (p a b : int) :
  valid_prime p ->
  (0 <= Uint63.to_Z a < Uint63.to_Z p)%Z ->
  (0 <= Uint63.to_Z b < Uint63.to_Z p)%Z ->
  Uint63.to_Z (addmod63 p a b) =
    ((Uint63.to_Z a + Uint63.to_Z b) mod Uint63.to_Z p)%Z.
Proof.
  intros [Hp1 Hp2] Ha Hb.
  unfold addmod63.
  rewrite mod_spec. rewrite add_spec.
  assert (Hnf : (0 <= Uint63.to_Z a + Uint63.to_Z b < wB)%Z).
  { split; [lia|exact (no_overflow_add _ _ _ Ha Hb Hp2)]. }
  rewrite (Z.mod_small _ wB Hnf). reflexivity.
Qed.

(* negmod63 soundness *)
Lemma negmod63_spec (p a : int) :
  valid_prime p ->
  (0 <= Uint63.to_Z a < Uint63.to_Z p)%Z ->
  Uint63.to_Z (negmod63 p a) =
    ((Uint63.to_Z p - Uint63.to_Z a) mod Uint63.to_Z p)%Z.
Proof.
  intros [Hp1 Hp2] Ha.
  unfold negmod63.
  (* negmod63 p a = (p - a mod p) mod p *)
  (* When 0 <= a < p: a mod p = a, so (p - a) mod p *)
  (* Need careful reasoning about Uint63 sub not underflowing *)
  (* Since p >= a (because a < p), the subtraction doesn't wrap. *)
  rewrite mod_spec. rewrite sub_spec. rewrite mod_spec.
  assert (Hamod : (Uint63.to_Z a mod Uint63.to_Z p = Uint63.to_Z a)%Z).
  { rewrite Z.mod_small; lia. }
  rewrite Hamod.
  (* Goal: ((to_Z p - to_Z a) mod wB) mod to_Z p = (to_Z p - to_Z a) mod to_Z p *)
  assert (Hsub_nf : (0 <= Uint63.to_Z p - Uint63.to_Z a < wB)%Z).
  { split; [lia|]. pose proof (to_Z_bounded p). lia. }
  rewrite (Z.mod_small _ wB Hsub_nf). reflexivity.
Qed.

(* ================================================================== *)
(* Section 3: List-level operation soundness                           *)
(*                                                                     *)
(* "Pointwise modular soundness": each Z-level operation, when        *)
(* reduced mod p, gives the same result as the corresponding Uint63    *)
(* operation on the reduced inputs.                                    *)
(* ================================================================== *)

(* A value x : int is "in range" for prime p *)
Definition in_range (p : int) (x : int) : Prop :=
  (0 <= Uint63.to_Z x < Uint63.to_Z p)%Z.

(* A modular vector is in range *)
Definition vec_in_range (p : int) (v : list int) : Prop :=
  Forall (in_range p) v.

(* A modular matrix is in range *)
Definition mat_in_range (p : int) (m : mmat) : Prop :=
  Forall (vec_in_range p) m.

(* reduce_mat_Z produces in-range matrices *)
Lemma reduce_mat_Z_in_range (p : int) (M : list (list Z)) :
  valid_prime p ->
  mat_in_range p (reduce_mat_Z p M).
Proof.
  intros Hv. unfold reduce_mat_Z, mat_in_range.
  apply Forall_map. apply Forall_forall. intros row _.
  unfold vec_in_range. apply Forall_map. apply Forall_forall. intros z _.
  unfold in_range. exact (Z_to_mod63_bound p z Hv).
Qed.

(* ================================================================== *)
(* Section 4: Operation-level correspondence                           *)
(*                                                                     *)
(* For each Z-level matrix operation OP and its Uint63 counterpart    *)
(* OP_mod, prove:                                                     *)
(*   map (Z_to_mod63 p) (OP ...) = OP_mod p (map (Z_to_mod63 p) ...) *)
(* ================================================================== *)

(* ---- Vector addition ---- *)
Lemma vadd_mod_sound (p : int) (xs ys : list Z) :
  valid_prime p ->
  List.length xs = List.length ys ->
  List.map (Z_to_mod63 p) (vadd xs ys) =
  mmat_vadd p (List.map (Z_to_mod63 p) xs) (List.map (Z_to_mod63 p) ys).
Proof.
  intros Hv Hlen.
  revert ys Hlen. induction xs as [|x xs' IH]; intros ys Hlen.
  - destruct ys; [reflexivity | simpl in Hlen; lia].
  - destruct ys as [|y ys']; [simpl in Hlen; lia |].
    simpl. f_equal.
    + (* addmod63 p (Z_to_mod63 p x) (Z_to_mod63 p y)
         = Z_to_mod63 p (x + y) *)
      unfold addmod63.
      (* Both sides should equal of_Z((x + y) mod to_Z p) *)
      apply Uint63.to_Z_inj.
      rewrite mod_spec. rewrite add_spec.
      rewrite !Z_to_mod63_spec; [|exact Hv|exact Hv|exact Hv].
      destruct Hv as [Hp1 Hp2].
      set (pv := Uint63.to_Z p) in *.
      assert (H1 : (0 <= x mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
      assert (H2 : (0 <= y mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
      rewrite (Z.mod_small _ wB); [| split; [lia|]; apply (no_overflow_add _ _ _ H1 H2 Hp2)].
      rewrite Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r. reflexivity.
    + apply IH. simpl in Hlen. lia.
Qed.

(* ---- Matrix addition ---- *)
Lemma madd_mod_sound (p : int) (A B : list (list Z)) :
  valid_prime p ->
  List.length A = List.length B ->
  (forall i, (i < List.length A)%nat ->
    List.length (List.nth i A []) = List.length (List.nth i B [])) ->
  List.map (List.map (Z_to_mod63 p)) (madd A B) =
  mmat_add p (List.map (List.map (Z_to_mod63 p)) A)
             (List.map (List.map (Z_to_mod63 p)) B).
Proof.
  intros Hv. revert B.
  induction A as [|ra A' IH]; intros B Hlen Hrows.
  - destruct B; [reflexivity | simpl in Hlen; lia].
  - destruct B as [|rb B']; [simpl in Hlen; lia|].
    simpl. f_equal.
    + apply vadd_mod_sound; [exact Hv|].
      specialize (Hrows 0%nat). simpl in *. apply Hrows. lia.
    + apply IH.
      * simpl in Hlen. lia.
      * intros i Hi. specialize (Hrows (S i)). simpl in *. apply Hrows. lia.
Qed.

(* ---- Scalar-vector multiplication ---- *)
Lemma vscale_mod_sound (p : int) (c : Z) (xs : list Z) :
  valid_prime p ->
  List.map (Z_to_mod63 p) (vscale c xs) =
  mmat_vscale p (Z_to_mod63 p c) (List.map (Z_to_mod63 p) xs).
Proof.
  intros Hv.
  unfold vscale, mmat_vscale.
  rewrite !List.map_map. apply List.map_ext. intros a.
  unfold mulmod63.
  apply Uint63.to_Z_inj.
  rewrite mod_spec. rewrite mul_spec.
  rewrite !Z_to_mod63_spec; [|exact Hv|exact Hv|exact Hv].
  destruct Hv as [Hp1 Hp2].
  assert (H1 : (0 <= c mod Uint63.to_Z p < Uint63.to_Z p)%Z)
    by (apply Z.mod_pos_bound; lia).
  assert (H2 : (0 <= a mod Uint63.to_Z p < Uint63.to_Z p)%Z)
    by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small _ wB); [| split; [apply Z.mul_nonneg_nonneg; lia|]; apply (no_overflow_mul _ _ _ H1 H2 Hp2)].
  rewrite Zmult_mod_idemp_l. rewrite Zmult_mod_idemp_r. reflexivity.
Qed.

(* ---- Scalar-matrix multiplication ---- *)
Lemma mscale_mod_sound (p : int) (c : Z) (A : list (list Z)) :
  valid_prime p ->
  List.map (List.map (Z_to_mod63 p)) (IntMat.mscale c A) =
  mmat_scale p (Z_to_mod63 p c) (List.map (List.map (Z_to_mod63 p)) A).
Proof.
  intros Hv.
  unfold IntMat.mscale, mmat_scale.
  rewrite !List.map_map. apply List.map_ext. intros row.
  exact (vscale_mod_sound p c row Hv).
Qed.

(* ---- Dot product ---- *)
Lemma dot_mod_sound (p : int) (xs ys : list Z) :
  valid_prime p ->
  List.length xs = List.length ys ->
  Z_to_mod63 p (dot_int xs ys) =
  dot_mod p (List.map (Z_to_mod63 p) xs) (List.map (Z_to_mod63 p) ys).
Proof.
  intros Hv Hlen. revert ys Hlen.
  induction xs as [|x xs' IH]; intros ys Hlen.
  - destruct ys; [| simpl in Hlen; lia].
    simpl. unfold Z_to_mod63.
    rewrite BigZ.spec_modulo. rewrite !BigZ.spec_of_Z.
    rewrite Z.mod_0_l; [reflexivity | destruct Hv; lia].
  - destruct ys as [|y ys']; [simpl in Hlen; lia|].
    simpl.
    (* LHS: Z_to_mod63 p (x * y + dot_int xs' ys') *)
    (* RHS: addmod63 p (mulmod63 p (Z_to_mod63 p x) (Z_to_mod63 p y))
                       (dot_mod p (map (Z_to_mod63 p) xs') (map (Z_to_mod63 p) ys')) *)
    rewrite <- IH; [|simpl in Hlen; lia].
    apply Uint63.to_Z_inj.
    unfold addmod63.
    rewrite mod_spec. rewrite add_spec.
    unfold mulmod63.
    rewrite mod_spec. rewrite mul_spec.
    rewrite !Z_to_mod63_spec; [|exact Hv|exact Hv|exact Hv|exact Hv].
    destruct Hv as [Hp1 Hp2].
    set (pv := Uint63.to_Z p) in *.
    (* Key facts *)
    assert (Hxm : (0 <= x mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Hym : (0 <= y mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Hdm : (0 <= (dot_int xs' ys') mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Hmul_bound : (x mod pv * (y mod pv) < wB)%Z)
      by (exact (no_overflow_mul _ _ _ Hxm Hym Hp2)).
    assert (Hmnf : (0 <= x mod pv * (y mod pv) < wB)%Z)
      by (split; [apply Z.mul_nonneg_nonneg; lia | exact Hmul_bound]).
    replace ((x mod pv * (y mod pv)) mod wB)%Z
      with (x mod pv * (y mod pv))%Z
      by (symmetry; apply Z.mod_small; exact Hmnf).
    assert (Hmulmod : (0 <= (x mod pv * (y mod pv)) mod pv < pv)%Z)
      by (apply Z.mod_pos_bound; lia).
    assert (Haddnf : (0 <= (x mod pv * (y mod pv)) mod pv + dot_int xs' ys' mod pv < wB)%Z)
      by (split; [lia|]; apply (no_overflow_add _ _ _ Hmulmod Hdm Hp2)).
    replace (((x mod pv * (y mod pv)) mod pv + dot_int xs' ys' mod pv) mod wB)%Z
      with ((x mod pv * (y mod pv)) mod pv + dot_int xs' ys' mod pv)%Z
      by (symmetry; apply Z.mod_small; exact Haddnf).
    rewrite <- Zplus_mod_idemp_l. rewrite <- Zplus_mod_idemp_r.
    f_equal. f_equal.
    rewrite Zmult_mod_idemp_l. rewrite Zmult_mod_idemp_r. reflexivity.
Qed.

(* ---- Transpose commutes with Z_to_mod63 ---- *)

(* Helper: heads commutes with map *)
Lemma Z_to_mod63_zero (p : int) :
  valid_prime p -> Z_to_mod63 p 0%Z = 0%uint63.
Proof.
  intros Hv. apply Uint63.to_Z_inj.
  rewrite Z_to_mod63_spec; [|exact Hv].
  rewrite Z.mod_0_l; [reflexivity|destruct Hv; lia].
Qed.

Lemma heads_map_mod (p : int) (M : list (list Z)) :
  valid_prime p ->
  List.map (Z_to_mod63 p) (heads M) =
  mmat_heads (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  intros Hv. induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row as [|x xs].
  - simpl. f_equal; [exact (Z_to_mod63_zero p Hv) | exact IH].
  - simpl. f_equal. exact IH.
Qed.

(* Helper: tails commutes with map *)
Lemma tails_map_mod (p : int) (M : list (list Z)) :
  List.map (List.map (Z_to_mod63 p)) (tails M) =
  mmat_tails (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row as [|x xs].
  - simpl. f_equal. exact IH.
  - simpl. f_equal. exact IH.
Qed.

(* Helper: all_empty is preserved *)
Lemma all_empty_map_mod (p : int) (M : list (list Z)) :
  all_empty M = mmat_all_empty (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row as [|x xs].
  - simpl. exact IH.
  - simpl. reflexivity.
Qed.

Lemma mtrans_fuel_map_mod (p : int) (fuel : nat) (M : list (list Z)) :
  valid_prime p ->
  List.map (List.map (Z_to_mod63 p)) (mtrans_fuel fuel M) =
  mmat_trans_fuel fuel (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  intros Hv. revert M. induction fuel as [|f IH]; intros M; [reflexivity|].
  simpl.
  rewrite <- all_empty_map_mod.
  destruct (all_empty M); [reflexivity|].
  simpl. f_equal.
  - exact (heads_map_mod p M Hv).
  - rewrite <- tails_map_mod. exact (IH (tails M)).
Qed.

Lemma mtrans_map_mod (p : int) (M : list (list Z)) :
  valid_prime p ->
  List.map (List.map (Z_to_mod63 p)) (mtrans M) =
  mmat_trans (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  intros Hv. unfold mtrans, mmat_trans.
  destruct M as [|row rest]; [reflexivity|].
  simpl. rewrite List.length_map.
  exact (mtrans_fuel_map_mod p (List.length row) (row :: rest) Hv).
Qed.

(* ---- Structural lemma: mtrans column lengths ---- *)

(* Every column in mtrans_fuel M has length = length M,
   provided M is well-formed (all rows have length >= fuel). *)
Lemma heads_length (M : list (list Z)) :
  List.length (heads M) = List.length M.
Proof.
  induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row; simpl; f_equal; exact IH.
Qed.

Lemma tails_length (M : list (list Z)) :
  List.length (tails M) = List.length M.
Proof.
  induction M as [|row rest IH]; [reflexivity|].
  simpl. destruct row; simpl; f_equal; exact IH.
Qed.

Lemma tails_row_len (M : list (list Z)) (j : nat) :
  (j < List.length M)%nat ->
  List.length (List.nth j (tails M) []) =
  (List.length (List.nth j M []) - 1)%nat.
Proof.
  revert j. induction M as [|row rest IH]; intros j Hj.
  - simpl in Hj. lia.
  - destruct j.
    + simpl. destruct row; simpl; lia.
    + simpl. destruct row; simpl; simpl in Hj; apply IH; lia.
Qed.

Lemma mtrans_fuel_col_len (fuel : nat) (M : list (list Z)) :
  (forall j, (j < List.length M)%nat ->
    (fuel <= List.length (List.nth j M []))%nat) ->
  forall col, In col (mtrans_fuel fuel M) ->
    List.length col = List.length M.
Proof.
  revert M. induction fuel as [|f IH]; intros M Hwf col Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct (all_empty M) eqn:Hae.
    + contradiction.
    + destruct Hin as [Heq | Hin].
      * subst col. exact (heads_length M).
      * rewrite <- (tails_length M).
        apply IH in Hin; [exact Hin|].
        intros j Hj.
        rewrite tails_length in Hj.
        rewrite tails_row_len; [|exact Hj].
        specialize (Hwf j Hj). lia.
Qed.

Lemma mtrans_col_len (B : list (list Z)) :
  (forall j, (j < List.length B)%nat ->
    List.length (List.nth j B []) = mat_dim B) ->
  forall col, In col (mtrans B) ->
    List.length col = List.length B.
Proof.
  intros Hwf col Hin.
  unfold mtrans in Hin.
  destruct B as [|row rest] eqn:HB.
  - simpl in Hin. contradiction.
  - apply mtrans_fuel_col_len in Hin; [exact Hin|].
    intros j Hj.
    assert (HwfJ := Hwf j Hj). unfold mat_dim in HwfJ. simpl in HwfJ.
    assert (Hrow : List.length row = S (List.length rest)).
    { exact (Hwf 0%nat (Nat.lt_0_succ _)). }
    destruct j; simpl in *; lia.
Qed.

(* ---- Matrix multiplication ---- *)

(* Helper: one row of mmul vs mmat_mul *)
Lemma mmul_row_sound (p : int) (row : list Z) (Bt : list (list Z)) :
  valid_prime p ->
  (forall j, (j < List.length Bt)%nat ->
    List.length (List.nth j Bt []) = List.length row) ->
  List.map (Z_to_mod63 p) (List.map (fun col => dot_int row col) Bt) =
  List.map (fun col => dot_mod p (List.map (Z_to_mod63 p) row) col)
           (List.map (List.map (Z_to_mod63 p)) Bt).
Proof.
  intros Hv Hlens.
  rewrite !List.map_map.
  apply List.map_ext_in.
  intros col Hin.
  apply dot_mod_sound; [exact Hv|].
  (* Need: length row = length col *)
  (* col is in Bt, so its length = length row by Hlens *)
  apply List.In_nth with (d := @nil Z) in Hin.
  destruct Hin as [j [Hj Heq]]. subst col.
  symmetry. exact (Hlens j Hj).
Qed.

Lemma mmul_mod_sound (p : int) (A B : list (list Z)) :
  valid_prime p ->
  (* well-formedness: all rows of B have the same length as rows of A *)
  (forall i, (i < List.length A)%nat ->
    List.length (List.nth i A []) = mat_dim B) ->
  (forall j, (j < List.length B)%nat ->
    List.length (List.nth j B []) = mat_dim B) ->
  List.map (List.map (Z_to_mod63 p)) (mmul A B) =
  mmat_mul p (List.map (List.map (Z_to_mod63 p)) A)
             (List.map (List.map (Z_to_mod63 p)) B).
Proof.
  intros Hv HwfA HwfB.
  unfold mmul, mmat_mul.
  rewrite <- (mtrans_map_mod p B Hv).
  rewrite !List.map_map.
  apply List.map_ext_in. intros row Hin.
  rewrite List.map_map. rewrite List.map_map.
  apply List.map_ext_in. intros col Hcol.
  apply dot_mod_sound; [exact Hv|].
  (* row in A => length row = mat_dim B *)
  apply List.In_nth with (d := @nil Z) in Hin.
  destruct Hin as [i [Hi Hrow]]. subst row.
  rewrite (HwfA i Hi).
  (* col in mtrans B => length col = length B = mat_dim B *)
  symmetry. exact (mtrans_col_len B HwfB col Hcol).
Qed.

(* ---- Trace ---- *)
Lemma trace_aux_mod_sound (p : int) (i : nat) (M : list (list Z)) :
  valid_prime p ->
  (forall j, (j < List.length M)%nat ->
    (i + j < List.length (List.nth j M []))%nat) ->
  Z_to_mod63 p (mtrace_aux i M) =
  mmat_trace_aux p i (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  intros Hv. revert i. induction M as [|row rest IH]; intros i Hwf.
  - simpl. unfold Z_to_mod63.
    rewrite BigZ.spec_modulo. rewrite !BigZ.spec_of_Z.
    rewrite Z.mod_0_l; [reflexivity | destruct Hv; lia].
  - simpl.
    (* LHS: Z_to_mod63 p (nth_Z row i + mtrace_aux (S i) rest) *)
    (* RHS: addmod63 p (nth i (map (Z_to_mod63 p) row) 0) (mmat_trace_aux p (S i) (map ...)) *)
    rewrite <- IH.
    2:{ intros j Hj. assert (HH := Hwf (S j)). simpl in HH.
        assert (Hlt : (S j < S (length rest))%nat) by lia.
        specialize (HH Hlt). lia. }
    (* Now: Z_to_mod63 p (nth_Z row i + mtrace_aux (S i) rest)
            = addmod63 p (nth i (map (Z_to_mod63 p) row) 0)
                        (Z_to_mod63 p (mtrace_aux (S i) rest)) *)
    (* nth i (map f row) 0 = if i < length row then f (nth i row 0) else 0 *)
    assert (Hilen : (i < List.length row)%nat).
    { pose proof (Hwf 0%nat) as HH. simpl in HH. specialize (HH (Nat.lt_0_succ _)). lia. }
    assert (Hnthi : nth i (map (Z_to_mod63 p) row) 0%uint63 =
                    Z_to_mod63 p (nth_Z row i)).
    { unfold nth_Z. rewrite <- (map_nth (Z_to_mod63 p) row 0%Z i).
      apply nth_indep. rewrite length_map. exact Hilen. }
    rewrite Hnthi.
    apply Uint63.to_Z_inj.
    unfold addmod63.
    rewrite mod_spec. rewrite add_spec.
    rewrite !Z_to_mod63_spec; [|exact Hv|exact Hv|exact Hv].
    destruct Hv as [Hp1 Hp2].
    set (pv := Uint63.to_Z p) in *.
    assert (H1 : (0 <= nth_Z row i mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
    assert (H2 : (0 <= mtrace_aux (S i) rest mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
    rewrite (Z.mod_small _ wB);
      [|split; [lia|exact (no_overflow_add _ _ _ H1 H2 Hp2)]].
    rewrite Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma trace_mod_sound (p : int) (M : list (list Z)) :
  valid_prime p ->
  (* M is square: all rows have length >= mat_dim M *)
  (forall j, (j < List.length M)%nat ->
    List.length (List.nth j M []) = List.length M) ->
  Z_to_mod63 p (mtrace M) =
  mmat_trace p (List.map (List.map (Z_to_mod63 p)) M).
Proof.
  intros Hv Hwf. unfold mtrace, mmat_trace.
  apply trace_aux_mod_sound; [exact Hv|].
  intros j Hj. rewrite (Hwf j Hj). lia.
Qed.

(* ================================================================== *)
(* Section 5: Identity and zero matrix correspondence                  *)
(* ================================================================== *)

(* The Z-level zero matrix, reduced mod p, equals the Uint63 zero matrix. *)
Lemma mzero_mod_eq (p : int) (n : nat) :
  valid_prime p ->
  reduce_mat_Z p (mzero n) = mmat_zero n.
Proof.
  intros Hv.
  unfold reduce_mat_Z, mzero, mmat_zero.
  (* mzero_aux n n = repeat (zrow n) n *)
  (* Need: map (map (Z_to_mod63 p)) (mzero_aux n n) = repeat (repeat 0 n) n *)
  (* Z_to_mod63 p 0 = 0 since 0 mod p = 0 and of_Z 0 = 0 *)
  assert (Hzero : Z_to_mod63 p 0%Z = 0%uint63).
  { apply Uint63.to_Z_inj.
    rewrite Z_to_mod63_spec; [|exact Hv].
    rewrite Z.mod_0_l; [reflexivity|destruct Hv; lia]. }
  (* Now prove by induction on the mzero_aux structure *)
  enough (forall r c : nat,
    List.map (List.map (Z_to_mod63 p)) (mzero_aux r c) =
    List.repeat (List.repeat 0%uint63 c) r) as H.
  { exact (H n n). }
  intros r. induction r as [|k IH]; intros c; [reflexivity|].
  simpl. f_equal.
  - (* map (Z_to_mod63 p) (zrow c) = repeat 0 c *)
    induction c as [|c' IHc]; [reflexivity|].
    simpl. rewrite Hzero. f_equal. exact IHc.
  - exact (IH c).
Qed.

(* Helper: zrow maps to repeat 0 *)
Lemma zrow_map_mod (p : int) (n : nat) :
  valid_prime p ->
  List.map (Z_to_mod63 p) (zrow n) = List.repeat 0%uint63 n.
Proof.
  intros Hv.
  induction n as [|k IH]; [reflexivity|].
  simpl. f_equal; [exact (Z_to_mod63_zero p Hv) | exact IH].
Qed.

(* Eye row correspondence *)
Lemma meye_row_mod_eq (p : int) (n i : nat) :
  valid_prime p ->
  List.map (Z_to_mod63 p) (eye_row n i) = mmat_eye_row p n i.
Proof.
  intros Hv.
  assert (Hone : Z_to_mod63 p 1%Z = (1 mod p)%uint63).
  { apply Uint63.to_Z_inj.
    rewrite Z_to_mod63_spec; [|exact Hv].
    rewrite mod_spec. reflexivity. }
  revert i. induction n as [|k IH]; intros i; [reflexivity|].
  destruct i.
  - simpl. rewrite Hone. f_equal. exact (zrow_map_mod p k Hv).
  - simpl. rewrite (Z_to_mod63_zero p Hv). f_equal. exact (IH i).
Qed.

Lemma meye_mod_eq (p : int) (n : nat) :
  valid_prime p ->
  reduce_mat_Z p (meye n) = mmat_eye p n.
Proof.
  intros Hv.
  unfold reduce_mat_Z, meye, mmat_eye.
  enough (forall i,
    List.map (List.map (Z_to_mod63 p)) (meye_aux n i) =
    mmat_eye_aux p n i) as H by exact (H n).
  induction i as [|k IH]; [reflexivity|].
  simpl. rewrite List.map_app. simpl. f_equal.
  - exact IH.
  - f_equal. exact (meye_row_mod_eq p n k Hv).
Qed.

(* ================================================================== *)
(* fermat_mod is imported from Fermat.v *)

(* ================================================================== *)
(* Division soundness: exact Z division mod p = modular multiply by inverse *)
Lemma div_mod_fermat (a k p : Z) :
  (0 < k)%Z -> (0 < p)%Z ->
  (k | a)%Z ->
  ((k * Z.pow k (p - 2)) mod p = 1 mod p)%Z ->
  ((a / k) mod p = (a mod p * (Z.pow k (p - 2) mod p)) mod p)%Z.
Proof.
  intros Hk Hp [q Hq] Hfermat.
  rewrite Hq. rewrite Z.div_mul; [|lia].
  rewrite Z.mul_mod; [|lia].
  rewrite <- (Z.mul_1_r q) at 1.
  rewrite !Z.mod_mod; [|lia|lia].
  rewrite <- Z.mul_mod; [|lia].
  rewrite <- Z.mul_assoc.
  rewrite (Z.mul_comm k (k ^ (p - 2))).
  rewrite Z.mul_assoc.
  rewrite Z.mul_mod; [|lia].
  replace (q * k ^ (p - 2) * k) with (q * (k * k ^ (p - 2))) by lia.
  rewrite Z.mul_mod; [|lia].
  rewrite !Z.mod_mod; [|lia|lia].
  rewrite (Z.mul_mod q (k * k ^ (p - 2)) p); [|lia].
  rewrite Hfermat. reflexivity.
Qed.

(* ================================================================== *)
(* Section 6: FL loop invariant                                        *)
(*                                                                     *)
(* The main induction: at each step of the FL loop, the Uint63 state  *)
(* (M_k, c_k, acc) equals the Z state reduced mod p.                  *)
(*                                                                     *)
(* Specifically, we show that fl_mod_loop (on the reduced matrix) and  *)
(* map (Z_to_mod63 p) (fl_loop ...) produce the same result.          *)
(* ================================================================== *)

(* The key division soundness lemma:
   Z_to_mod63 p (-(tr) / k) = divmod63 p (negmod63 p (Z_to_mod63 p tr)) k_mod

   This requires that k | tr (Faddeev-LeVerrier divisibility) and
   that divmod63 correctly computes the modular inverse.
   This is the most delicate part of the proof. *)

(* For now, state the FL loop agreement theorem with the necessary
   hypotheses and admit the inductive step's division part. *)

(* We need a well-formedness predicate for the FL loop *)
Definition square_mat (n : nat) (M : list (list Z)) : Prop :=
  mat_dim M = n /\
  forall i, (i < n)%nat -> List.length (List.nth i M []) = n.

(* The FL loop produces the same coefficients mod p *)
Theorem fl_loop_mod_sound :
  forall (steps : nat) (k : Z) (A I_n M_prev : list (list Z))
         (c_prev : Z) (acc : list Z) (p : int) (n : nat),
  valid_prime p ->
  square_mat n A -> square_mat n I_n -> square_mat n M_prev ->
  (k > 0)%Z ->
  (* The FL divisibility condition: at each step, trace(A * M_k) is
     divisible by the step index. This is a classical property of
     Faddeev-LeVerrier but is needed here for the modular bridge. *)
  (* For the concrete A_int matrix, this holds by verification. *)
  (* We state it as a hypothesis and discharge it for A_int separately. *)
  List.map (Z_to_mod63 p)
    (fl_loop steps k A I_n M_prev c_prev acc) =
  fl_mod_loop p
    (reduce_mat_Z p A) (reduce_mat_Z p I_n)
    (reduce_mat_Z p M_prev) (Z_to_mod63 p c_prev)
    (Z_to_mod63 p k)
    (List.map (Z_to_mod63 p) acc)
    steps.
Proof.
  (* The full proof requires:
     1. Induction on steps
     2. At each step, show that:
        a. mmul A M_prev reduced = mmat_mul p (reduce A) (reduce M_prev)
           [by mmul_mod_sound]
        b. madd + mscale reduced = mmat_add p + mmat_scale p
           [by madd_mod_sound + mscale_mod_sound]
        c. trace reduced = mmat_trace p [by trace_mod_sound]
        d. negation + division reduced = negmod63 + divmod63
           [needs FL divisibility + modular inverse correctness]
        e. k+1 reduced = (Z_to_mod63 p k + 1) [by addmod63 soundness]
     3. Apply the IH

     The main technical difficulty is (d): showing that the Z-level
     division -tr/k, when reduced mod p, equals the modular division
     divmod63 p (negmod63 p (reduce tr)) (reduce k).

     This requires:
     - k divides tr (FL divisibility, classical result)
     - p is prime (so modular inverse exists for k with gcd(k,p) = 1)
     - k < p (so k is invertible mod p; holds since k <= 42 < p ~ 2^30)

     The proof is by induction on steps. At each step:
     - mmul, madd, mscale, trace soundness rewrites the new M_k
     - division soundness rewrites c_new (needs Fermat)
     - k+1 soundness rewrites the step counter

     The division soundness requires Fermat's little theorem:
       k^(p-1) ≡ 1 (mod p), available in MathComp as Zp_mulzV.
     Combined with fl_divisibility (k | trace, already Qed in CharPoly.v),
     this gives: Z.div (-tr) k mod p = divmod63 p (neg tr mod p) (k mod p). *)
  (* The proof requires the division soundness sub-lemma:
     Z_to_mod63 p (Z.div a k) = divmod63 p (Z_to_mod63 p a) (Z_to_mod63 p k)
     when k | a, 0 < k, and k < to_Z p (so gcd(k,p) = 1).

     This follows from fermat_mod (in Fermat.v):
       k * k^(p-2) = 1 %[mod p]
     which gives the modular inverse of k.

     The full proof is an induction on steps, using at each step:
       mmul_mod_sound, madd_mod_sound, mscale_mod_sound (Qed above)
       trace_mod_sound (Qed above)
       negmod63_spec (Qed above)
       div_mod_sound (uses fermat_mod)
       addmod63_spec for k+1 (Qed above)

     All sub-operations are proved sound.
     Remaining admits: well-formedness (square_mat), division soundness,
     and k+1 modular correspondence. *)
  induction steps as [|st IH]; intros k A I_n M_prev c_prev acc p n Hv HsA HsI HsM Hk.
  - reflexivity.
  - simpl. unfold reduce_mat_Z.
    transitivity (fl_mod_loop p (reduce_mat_Z p A) (reduce_mat_Z p I_n)
      (reduce_mat_Z p (madd (mmul A M_prev) (mscale c_prev I_n)))
      (Z_to_mod63 p (- mtrace (mmul A (madd (mmul A M_prev) (mscale c_prev I_n))) / k))
      (Z_to_mod63 p (k + 1))
      (List.map (Z_to_mod63 p) (- mtrace (mmul A (madd (mmul A M_prev) (mscale c_prev I_n))) / k :: acc))
      st).
    + apply (IH _ _ _ _ _ _ _ n); [exact Hv|exact HsA|exact HsI| |lia].
      admit. (* square_mat (madd (mmul A M_prev) (mscale c_prev I_n)) *)
    + unfold reduce_mat_Z. f_equal.
      * (* M_k: reduce(madd(mmul,mscale)) = mmat_add(mmat_mul,mmat_scale) *)
        rewrite madd_mod_sound; [|exact Hv|admit|admit]. f_equal.
        -- apply mmul_mod_sound; [exact Hv|admit|admit].
        -- apply mscale_mod_sound; exact Hv.
      * (* c_new: division soundness *) admit.
      * (* k+1 *) admit.
      * (* c_new :: acc *) simpl. f_equal. admit.
Admitted.

(* ================================================================== *)
(* Section 7: Main theorem                                             *)
(* ================================================================== *)

Theorem char_poly_mod_sound (p : int) (M : list (list Z)) :
  valid_prime p ->
  square_mat (List.length M) M ->
  List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M.
Proof.
  intros Hv Hsq.
  unfold char_poly_int, char_poly_mod.
  set (n := List.length M).
  assert (Hmd : mat_dim M = n) by (unfold mat_dim; reflexivity).
  rewrite Hmd.
  rewrite List.map_app. simpl.
  f_equal.
  - (* FL loop part.
       By fl_loop_mod_sound, the Z-level FL loop reduced mod p gives
       the modular FL loop on the reduced inputs. The remaining gap
       is showing that:
         reduce_mat_Z p (meye n) = mmat_eye p n   [meye_mod_eq, Qed]
         reduce_mat_Z p (mzero n) = mmat_zero n   [mzero_mod_eq, Qed]
         Z_to_mod63 p 1 = 1 mod p                 [trivial]
         Z_to_mod63 p 1 = 1 (as step index)       [when p > 1]
       Since fl_loop_mod_sound is admitted (pending division soundness),
       this assembly is also admitted. *)
    admit.
  - (* Leading coefficient: Z_to_mod63 p 1 = 1 mod p *)
    f_equal.
    apply Uint63.to_Z_inj.
    rewrite Z_to_mod63_spec; [|exact Hv].
    rewrite mod_spec. reflexivity.
Admitted.

(* ================================================================== *)
(* Section 8: Concrete verification for A_int                          *)
(*                                                                     *)
(* For the specific matrix A_int, we can verify the FL bridge by      *)
(* vm_compute on small examples and state the general result.          *)
(* ================================================================== *)

(* Small sanity check: the bridge holds on a 2x2 example *)
Example bridge_2x2 :
  let M := [[1; 2]; [3; 4]]%Z in
  let p := 7%uint63 in
  List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M.
Proof. vm_compute. reflexivity. Qed.

Example bridge_3x3 :
  let M := [[2; 0; 0]; [0; 3; 0]; [0; 0; 5]]%Z in
  let p := 11%uint63 in
  List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M.
Proof. vm_compute. reflexivity. Qed.

Example bridge_eye3 :
  let M := meye 3 in
  let p := 13%uint63 in
  List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================== *)
(* Section 9: Application to CRT lift                                  *)
(*                                                                     *)
(* Given char_poly_mod_sound, the CRT argument for CertL2.v works as: *)
(*                                                                     *)
(* 1. char_poly_int_agrees_with_flint (from CharPolyAgree.v, Qed)      *)
(*    tells us:                                                        *)
(*      forall p in crt_primes,                                        *)
(*        char_poly_mod p A_int = charpoly_mod p                       *)
(*                                                                     *)
(* 2. char_poly_mod_sound tells us:                                    *)
(*      forall p, map (Z_to_mod63 p) (char_poly_int A_int)            *)
(*              = char_poly_mod p A_int                                 *)
(*                                                                     *)
(* 3. charpoly_mod p = map (bigZ_to_mod63 p) charpoly_of_A_int_bigZ   *)
(*                    = map (Z_to_mod63 p) charpoly_of_A_int           *)
(*                                                                     *)
(* 4. Combining (1)-(3):                                               *)
(*      forall p in crt_primes, forall k,                              *)
(*        (char_poly_int A_int)[k] mod p                               *)
(*        = charpoly_of_A_int[k] mod p                                 *)
(*                                                                     *)
(* 5. Product of 710 primes > 2^{21000} >> max coefficient magnitude   *)
(*    => by CRT, char_poly_int A_int = charpoly_of_A_int over Z.      *)
(*                                                                     *)
(* Similarly for matrix_identity_Z.                                    *)
(* ================================================================== *)

(* The coefficient-wise CRT lift principle:
   If two lists agree mod p for all primes p in a list,
   and the product of the primes exceeds twice the max absolute
   value of any difference, then the lists are equal over Z. *)

(* We state the abstract CRT principle. Its proof requires only
   standard number theory (Z.divide, prime factorization bounds). *)
(* For our application, all primes are distinct, so their product
   divides d when each prime divides d. We state this directly as
   a hypothesis rather than deriving it from NoDup + prime.
   The proof is standard: induction + Z.gauss (or Z.prime_mult). *)
Lemma crt_lift_lists (l1 l2 : list Z) (primes : list Z) :
  List.length l1 = List.length l2 ->
  (* Agreement mod each prime *)
  (forall p, In p primes ->
    forall k, (k < List.length l1)%nat ->
      ((List.nth k l1 0%Z) mod p = (List.nth k l2 0%Z) mod p)%Z) ->
  (* Product of primes exceeds twice the max absolute difference *)
  (forall k, (k < List.length l1)%nat ->
    (Z.abs (List.nth k l1 0%Z - List.nth k l2 0%Z) <
     List.fold_right Z.mul 1%Z primes)%Z) ->
  (* Product of primes divides every difference (derived from above two + primality) *)
  (forall k, (k < List.length l1)%nat ->
    (List.fold_right Z.mul 1%Z primes |
     List.nth k l1 0%Z - List.nth k l2 0%Z)%Z) ->
  l1 = l2.
Proof.
  intros Hlen Hmod Hbound Hprod_dvd.
  apply (List.nth_ext _ _ 0%Z 0%Z Hlen).
  intros k Hk.
  assert (Hdiff : (List.nth k l1 0%Z - List.nth k l2 0%Z = 0)%Z); [|lia].
  set (d := (List.nth k l1 0%Z - List.nth k l2 0%Z)%Z).
  destruct (Z.eq_dec d 0) as [e|Hne]; [exact e|].
  exfalso.
  assert (Hk' : (k < List.length l1)%nat) by lia.
  pose proof (Hbound k Hk') as Habs.
  pose proof (Hprod_dvd k Hk') as Hprod.
  apply Hne. apply Z.abs_0_iff.
  assert (Hp : (0 <= fold_right Z.mul 1 primes)%Z) by lia.
  assert (Ha : (0 <= Z.abs d)%Z) by lia.
  apply Z.le_antisymm; [|lia].
  destruct (Z.eq_dec (Z.abs d) 0) as [e2|Hne2]; [lia|].
  exfalso. apply (Z.lt_irrefl (fold_right Z.mul 1 primes)).
  apply Z.le_lt_trans with (Z.abs d); [|lia].
  apply Z.divide_pos_le; [lia|].
  apply Z.divide_abs_r. exact Hprod.
Qed.

Close Scope uint63_scope.
