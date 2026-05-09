(* ===================================================================
   CRTBridge.v -- Prove that the Uint63 Faddeev-LeVerrier computation
   mod a prime p gives the same result as the Z-level FL computation
   reduced mod p.

   Main theorem:
     char_poly_mod_sound :
       List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M

   This is the key bridge used by CertL2.v's CRT lift (now Qed):
   once we know the Uint63 FL equals the Z FL reduced mod p,
   agreement of the Uint63 FL with the FLINT polynomial mod 710
   primes implies Z-level agreement.

   NOTE: This file does NOT import CharPolyAgree.v (to avoid loading
   the 710-prime table). It re-defines the necessary Uint63 matrix
   operations locally, matching CharPolyAgree.v exactly.
   =================================================================== *)

From Stdlib Require Import ZArith List Lia Uint63.
From PrimeGapS1 Require Import Fermat.
Import ListNotations.
Open Scope Z_scope.

From Bignums Require Import BigZ.

From PrimeGapS1 Require Import IntMat CharPoly ModularArith.

(* Section 0: Uint63 operations now live in ModularArith.v
   (imported above). Previously duplicated with CharPolyAgree.v; the
   duplication caused the kernel's conversion checker to explode in
   CRTLift.v when comparing terms containing char_poly_mod. *)

Open Scope uint63_scope.


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
(* Section 5b: Structural lemmas and relaxed soundness                 *)
(* ================================================================== *)

(* Power identity helpers for Z.pow *)
Lemma Z_pow_xI_eq (b : Z) (pos : positive) :
  b * (b ^ Z.pos pos * b ^ Z.pos pos) = b ^ Z.pos pos~1.
Proof.
  change (Z.pos pos~1) with (2 * Z.pos pos + 1)%Z.
  replace (2 * Z.pos pos + 1)%Z with (1 + Z.pos pos + Z.pos pos)%Z by lia.
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_1_r. ring.
Qed.

Lemma Z_pow_xO_eq (b : Z) (pos : positive) :
  b ^ Z.pos pos * b ^ Z.pos pos = b ^ Z.pos pos~0.
Proof.
  change (Z.pos pos~0) with (2 * Z.pos pos)%Z.
  replace (2 * Z.pos pos)%Z with (Z.pos pos + Z.pos pos)%Z by lia.
  rewrite Z.pow_add_r; [|lia|lia]. reflexivity.
Qed.

(* madd soundness without length conditions *)
Lemma madd_mod_sound_gen (p : int) (A B : list (list Z)) :
  valid_prime p ->
  List.map (List.map (Z_to_mod63 p)) (madd A B) =
  mmat_add p (List.map (List.map (Z_to_mod63 p)) A)
             (List.map (List.map (Z_to_mod63 p)) B).
Proof.
  intros Hv. revert B.
  induction A as [|ra A' IH]; intros [|rb B']; try reflexivity.
  simpl. f_equal; [|apply IH].
  revert rb. induction ra as [|x xs IHx]; intros [|y ys]; try reflexivity.
  simpl. f_equal; [|apply IHx].
  apply Uint63.to_Z_inj. unfold addmod63.
  rewrite mod_spec. rewrite add_spec.
  rewrite !Z_to_mod63_spec; [|exact Hv|exact Hv|exact Hv].
  destruct Hv as [Hp1 Hp2]. set (pv := Uint63.to_Z p) in *.
  assert (H1 : (0 <= x mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
  assert (H2 : (0 <= y mod pv < pv)%Z) by (apply Z.mod_pos_bound; lia).
  rewrite (Z.mod_small _ wB); [|split; [lia|]; apply (no_overflow_add _ _ _ H1 H2 Hp2)].
  rewrite Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* Structural length lemmas *)
Lemma vscale_length (c : Z) (xs : list Z) :
  List.length (vscale c xs) = List.length xs.
Proof. unfold vscale. apply List.length_map. Qed.

Lemma vadd_length (xs ys : list Z) :
  List.length xs = List.length ys ->
  List.length (vadd xs ys) = List.length xs.
Proof.
  revert ys. induction xs as [|x xs' IH]; intros [|y ys'] Hlen; simpl in *; try lia.
  f_equal. apply IH. lia.
Qed.

Lemma mmul_length (A B : list (list Z)) :
  List.length (mmul A B) = List.length A.
Proof. unfold mmul. rewrite List.length_map. reflexivity. Qed.

Lemma mscale_length (c : Z) (A : list (list Z)) :
  List.length (IntMat.mscale c A) = List.length A.
Proof. unfold IntMat.mscale. rewrite List.length_map. reflexivity. Qed.

Lemma madd_length (A B : list (list Z)) :
  List.length A = List.length B ->
  List.length (madd A B) = List.length A.
Proof.
  revert B. induction A as [|ra A' IH]; intros [|rb B'] Hlen; simpl in *; try lia.
  f_equal. apply IH. lia.
Qed.

Lemma mtrans_fuel_length (fuel : nat) (M : list (list Z)) :
  M <> nil ->
  (forall j, (j < List.length M)%nat -> (fuel <= List.length (List.nth j M []))%nat) ->
  List.length (mtrans_fuel fuel M) = fuel.
Proof.
  revert M. induction fuel as [|f IH]; intros M Hne Hwf.
  - reflexivity.
  - simpl. destruct M as [|row rest]; [contradiction|].
    assert (Hrow : (S f <= List.length row)%nat)
      by (specialize (Hwf 0%nat); simpl in Hwf; apply Hwf; simpl; lia).
    destruct row as [|x xs]; [simpl in Hrow; lia|].
    simpl. f_equal. apply IH.
    + simpl. discriminate.
    + intros j Hj. simpl in Hj. rewrite tails_length in Hj.
      destruct j; simpl; [simpl in Hrow; lia|].
      rewrite tails_row_len; [|lia].
      specialize (Hwf (S j) Hj). simpl in Hwf. lia.
Qed.

Lemma mtrans_length_sq (M : list (list Z)) (n : nat) :
  (0 < n)%nat -> mat_dim M = n ->
  (forall j, (j < n)%nat -> List.length (List.nth j M []) = n) ->
  List.length (mtrans M) = n.
Proof.
  intros Hn Hdim Hwf. unfold mtrans.
  destruct M as [|row rest]; [simpl in Hdim; lia|].
  simpl. assert (Hrow : List.length row = n).
  { apply (Hwf 0%nat). unfold mat_dim in Hdim. simpl in Hdim. lia. }
  rewrite <- Hrow. apply mtrans_fuel_length.
  - discriminate.
  - intros j Hj. unfold mat_dim in Hdim. simpl in Hdim.
    destruct j; simpl; [lia|].
    simpl in Hj. specialize (Hwf (S j)). simpl in Hwf.
    rewrite Hwf; [lia | lia].
Qed.

(* ================================================================== *)
(* Section 5c: square_mat preservation                                 *)
(* ================================================================== *)

Definition square_mat (n : nat) (M : list (list Z)) : Prop :=
  mat_dim M = n /\
  forall i, (i < n)%nat -> List.length (List.nth i M []) = n.

Lemma mmul_nth_length (A B : list (list Z)) (n : nat) (i : nat) :
  (0 < n)%nat -> square_mat n A -> square_mat n B ->
  (i < n)%nat ->
  List.length (List.nth i (mmul A B) []) = n.
Proof.
  intros Hn [HdA HwA] [HdB HwB] Hi. unfold mmul.
  set (f := fun row => map (fun col => dot_int row col) (mtrans B)).
  assert (Heq : nth i (map f A) [] = f (nth i A [])).
  { transitivity (nth i (map f A) (f [])).
    - apply List.nth_indep. rewrite List.length_map. unfold mat_dim in HdA. lia.
    - apply List.map_nth. }
  rewrite Heq. unfold f. rewrite List.length_map.
  apply mtrans_length_sq; [exact Hn | exact HdB | exact HwB].
Qed.

Lemma mscale_nth_length (c : Z) (A : list (list Z)) (n : nat) (i : nat) :
  square_mat n A -> (i < n)%nat ->
  List.length (List.nth i (IntMat.mscale c A) []) = n.
Proof.
  intros [Hd Hw] Hi. unfold IntMat.mscale.
  change (@nil Z) with (vscale c (@nil Z)).
  rewrite List.map_nth. rewrite vscale_length. apply Hw. exact Hi.
Qed.

Lemma madd_nth_length (A B : list (list Z)) (n : nat) (i : nat) :
  List.length A = List.length B ->
  (forall j, (j < List.length A)%nat -> List.length (List.nth j A []) = n) ->
  (forall j, (j < List.length B)%nat -> List.length (List.nth j B []) = n) ->
  (i < List.length A)%nat ->
  List.length (List.nth i (madd A B) []) = n.
Proof.
  revert B i. induction A as [|ra A' IH]; intros [|rb B'] i Hlen HwA HwB Hi;
    simpl in *; try lia.
  destruct i; simpl.
  - rewrite vadd_length; [apply (HwA 0%nat); lia|].
    rewrite (HwA 0%nat); [|lia]. rewrite (HwB 0%nat); [|lia]. reflexivity.
  - apply IH with (B := B'); try lia.
    + intros j Hj. apply (HwA (S j)). lia.
    + intros j Hj. apply (HwB (S j)). lia.
Qed.

Lemma square_mat_mmul (n : nat) (A B : list (list Z)) :
  (0 < n)%nat -> square_mat n A -> square_mat n B ->
  square_mat n (mmul A B).
Proof.
  intros Hn HsA HsB. split.
  - unfold mat_dim. rewrite mmul_length. destruct HsA; exact H.
  - intros i Hi. exact (mmul_nth_length A B n i Hn HsA HsB Hi).
Qed.

Lemma square_mat_mscale (n : nat) (c : Z) (A : list (list Z)) :
  square_mat n A -> square_mat n (IntMat.mscale c A).
Proof.
  intros Hs. split.
  - unfold mat_dim. rewrite mscale_length. destruct Hs; exact H.
  - intros i Hi. exact (mscale_nth_length c A n i Hs Hi).
Qed.

Lemma square_mat_madd (n : nat) (A B : list (list Z)) :
  square_mat n A -> square_mat n B ->
  square_mat n (madd A B).
Proof.
  intros [HdA HwA] [HdB HwB]. split.
  - unfold mat_dim. rewrite madd_length; [exact HdA | unfold mat_dim in *; lia].
  - intros i Hi.
    apply madd_nth_length; [unfold mat_dim in *; lia| | |unfold mat_dim in HdA; lia].
    + intros j Hj. apply HwA. unfold mat_dim in HdA; lia.
    + intros j Hj. apply HwB. unfold mat_dim in HdB; lia.
Qed.

(* ================================================================== *)
(* Section 5d: powmod_fast and divmod63 soundness                      *)
(* ================================================================== *)

Lemma mulmod63_in_range (p a b : int) :
  valid_prime p -> in_range p (mulmod63 p a b).
Proof.
  intros [Hp1 Hp2]. unfold in_range, mulmod63.
  rewrite mod_spec. pose proof (to_Z_bounded (a * b)%uint63) as [Ha1 Ha2].
  split; apply Z.mod_pos_bound; lia.
Qed.

Lemma powmod_fast_in_range (p base : int) (exp : N) (fuel : nat) :
  valid_prime p -> in_range p (powmod_fast p base exp fuel).
Proof.
  intros Hv. revert exp.
  induction fuel as [|f IH]; intros exp; simpl.
  - unfold in_range. rewrite mod_spec.
    destruct Hv as [Hp1 Hp2]. pose proof (to_Z_bounded 1).
    split; apply Z.mod_pos_bound; lia.
  - destruct exp as [|[pos|pos|]].
    + unfold in_range. rewrite mod_spec. destruct Hv as [Hp1 Hp2].
      pose proof (to_Z_bounded 1). split; apply Z.mod_pos_bound; lia.
    + exact (mulmod63_in_range p base _ Hv).
    + exact (mulmod63_in_range p _ _ Hv).
    + unfold in_range. rewrite mod_spec. destruct Hv as [Hp1 Hp2].
      pose proof (to_Z_bounded base). split; apply Z.mod_pos_bound; lia.
Qed.

Lemma powmod_fast_spec (p base : int) (exp : N) (fuel : nat) :
  valid_prime p ->
  in_range p base ->
  (N.size_nat exp <= fuel)%nat ->
  Uint63.to_Z (powmod_fast p base exp fuel) =
  (Z.pow (Uint63.to_Z base) (Z.of_N exp) mod Uint63.to_Z p)%Z.
Proof.
  intros Hv Hb. revert exp.
  induction fuel as [|f IH]; intros exp Hfuel.
  - destruct exp as [|p0]; [|exfalso; destruct p0; simpl in Hfuel; lia].
    simpl. rewrite mod_spec. reflexivity.
  - destruct exp as [|pos].
    + simpl. rewrite mod_spec. reflexivity.
    + destruct pos.
      * (* xI pos: base^(2*pos+1) = base * (base^pos)^2 *)
        simpl powmod_fast.
        assert (Hf : (Pos.size_nat pos <= f)%nat) by (cbn in Hfuel; lia).
        set (half := powmod_fast p base (Npos pos) f).
        assert (Hhalf_spec : Uint63.to_Z half =
          (Uint63.to_Z base ^ Z.of_N (Npos pos) mod Uint63.to_Z p)%Z)
          by (exact (IH (Npos pos) Hf)).
        assert (Hhalf_range : in_range p half).
        { unfold in_range. rewrite Hhalf_spec.
          split; apply Z.mod_pos_bound; destruct Hv; lia. }
        assert (Hpv_pos : (0 < Uint63.to_Z p)%Z) by (destruct Hv; lia).
        rewrite (mulmod63_spec p base (mulmod63 p half half) Hv Hb
                   (mulmod63_in_range p half half Hv)).
        rewrite (mulmod63_spec p half half Hv Hhalf_range Hhalf_range).
        rewrite Hhalf_spec.
        set (pv := Uint63.to_Z p) in *. set (bv := Uint63.to_Z base) in *.
        transitivity ((bv * (bv ^ Z.of_N (Npos pos) * bv ^ Z.of_N (Npos pos))) mod pv).
        2: { f_equal. change (Z.of_N (Npos pos)) with (Z.pos pos).
             change (Z.of_N (N.pos pos~1)) with (Z.pos pos~1).
             exact (Z_pow_xI_eq bv pos). }
        rewrite Z.mul_mod; [|lia].
        rewrite (Z.mul_mod (bv ^ Z.of_N (Npos pos) mod pv)
                  (bv ^ Z.of_N (Npos pos) mod pv) pv); [|lia].
        rewrite !Z.mod_mod; try lia.
        rewrite <- (Z.mul_mod (bv ^ Z.of_N (Npos pos))
                     (bv ^ Z.of_N (Npos pos)) pv); [|lia].
        rewrite <- (Z.mul_mod bv _ pv); [|lia].
        reflexivity.
      * (* xO pos: base^(2*pos) = (base^pos)^2 *)
        simpl powmod_fast.
        assert (Hf : (Pos.size_nat pos <= f)%nat) by (cbn in Hfuel; lia).
        set (half := powmod_fast p base (Npos pos) f).
        assert (Hhalf_spec : Uint63.to_Z half =
          (Uint63.to_Z base ^ Z.of_N (Npos pos) mod Uint63.to_Z p)%Z)
          by (exact (IH (Npos pos) Hf)).
        assert (Hhalf_range : in_range p half).
        { unfold in_range. rewrite Hhalf_spec.
          split; apply Z.mod_pos_bound; destruct Hv; lia. }
        rewrite (mulmod63_spec p half half Hv Hhalf_range Hhalf_range).
        rewrite Hhalf_spec.
        rewrite Zmult_mod_idemp_l. rewrite Zmult_mod_idemp_r.
        f_equal. change (Z.of_N (Npos pos)) with (Z.pos pos).
        exact (Z_pow_xO_eq (Uint63.to_Z base) pos).
      * (* xH: base^1 = base *)
        simpl. rewrite mod_spec.
        change (Z.pow_pos (Uint63.to_Z base) 1) with (Uint63.to_Z base * 1)%Z.
        rewrite Z.mul_1_r.
        destruct Hb as [Hb1 Hb2]. rewrite Z.mod_small; lia.
Qed.

(* inv_mod63 soundness — standard binary exponentiation correctness.
   The exponent spec follows from powmod_fast_spec; the fuel bound
   (63 >= N.size_nat(p-2)) holds because p < 2^31 so the exponent
   has at most 31 binary digits. *)
Lemma inv_mod63_spec (p k : int) :
  valid_prime p ->
  in_range p k ->
  Uint63.to_Z (inv_mod63 p k) =
  (Z.pow (Uint63.to_Z k) (Uint63.to_Z p - 2) mod Uint63.to_Z p)%Z.
Proof.
  intros Hv Hk. unfold inv_mod63.
  rewrite powmod_fast_spec; [|exact Hv|exact Hk|].
  - f_equal. f_equal.
    rewrite N2Z.inj_sub; [rewrite Z2N.id; [reflexivity|destruct Hv; lia]|].
    change 2%N with (Z.to_N 2). apply Z2N.inj_le; destruct Hv; lia.
  - (* fuel bound: 63 >= N.size_nat (to_N(to_Z p) - 2) *)
    destruct Hv as [Hp1 Hp2].
    set (e := (Z.to_N (Uint63.to_Z p) - 2)%N).
    assert (He : (e < 2147483648)%N).
    { subst e.
      assert (He_Z : (Z.of_N (Z.to_N (Uint63.to_Z p) - 2) < 2147483648)%Z).
      { rewrite N2Z.inj_sub; [rewrite Z2N.id; lia|].
        change 2%N with (Z.to_N 2). apply Z2N.inj_le; lia. }
      lia. }
    destruct e as [|pos]; [simpl; lia|].
    simpl N.size_nat.
    assert (HeZ : (Z.of_N (N.pos pos) < 2 ^ 31)%Z) by lia.
    clear -HeZ.
    enough (H : forall (p : positive) (k : nat),
      (Z.pos p < 2 ^ Z.of_nat k)%Z -> (Pos.size_nat p <= k)%nat).
    { specialize (H pos 31%nat HeZ). lia. }
    clear. intros p. induction p; intros k Hlt.
    + destruct k; [simpl in Hlt; lia|].
      simpl. apply le_n_S. apply IHp.
      rewrite Nat2Z.inj_succ in Hlt. rewrite Z.pow_succ_r in Hlt; [|lia]. lia.
    + destruct k; [simpl in Hlt; lia|].
      simpl. apply le_n_S. apply IHp.
      rewrite Nat2Z.inj_succ in Hlt. rewrite Z.pow_succ_r in Hlt; [|lia]. lia.
    + simpl. destruct k; [simpl in Hlt; lia|lia].
Qed.

(* divmod63 soundness: when k divides a and p is prime,
   divmod63 computes (a/k) mod p via Fermat's little theorem.
   Proof uses: mulmod63_spec, inv_mod63_spec, div_mod_fermat,
   and fermat_mod (from Fermat.v) to show k * k^(p-2) ≡ 1 (mod p).
   The Z↔nat bridge for fermat_mod is the only remaining step. *)
Lemma divmod63_spec (p : int) (a k : Z) :
  valid_prime p ->
  (0 < k)%Z -> (k < Uint63.to_Z p)%Z ->
  (k | a)%Z ->
  (* Fermat condition: k * k^(p-2) ≡ 1 (mod p).
     This holds when p is prime and 0 < k < p, by Fermat's little theorem.
     Stated as a Z-level hypothesis to avoid MathComp int ambiguity.
     Discharged at call site via fermat_mod from Fermat.v. *)
  ((k * k ^ (Uint63.to_Z p - 2)) mod Uint63.to_Z p = 1 mod Uint63.to_Z p)%Z ->
  Uint63.to_Z (divmod63 p (Z_to_mod63 p a) (Z_to_mod63 p k)) =
  ((a / k) mod Uint63.to_Z p)%Z.
Proof.
  intros Hv Hk Hkp Hdiv Hfermat. unfold divmod63.
  set (pv := Uint63.to_Z p).
  assert (Hpv : (0 < pv)%Z) by (destruct Hv; lia).
  assert (Ha_range : in_range p (Z_to_mod63 p a))
    by (unfold in_range; rewrite Z_to_mod63_spec; [|exact Hv]; split; apply Z.mod_pos_bound; lia).
  assert (Hk_range : in_range p (Z_to_mod63 p k))
    by (unfold in_range; rewrite Z_to_mod63_spec; [|exact Hv]; split; apply Z.mod_pos_bound; lia).
  assert (Hinv_range : in_range p (inv_mod63 p (Z_to_mod63 p k)))
    by exact (powmod_fast_in_range p (Z_to_mod63 p k) _ 63 Hv).
  rewrite (mulmod63_spec p _ _ Hv Ha_range Hinv_range).
  rewrite Z_to_mod63_spec; [|exact Hv].
  rewrite inv_mod63_spec; [|exact Hv|exact Hk_range].
  rewrite Z_to_mod63_spec; [|exact Hv].
  rewrite Zmult_mod_idemp_r. fold pv.
  transitivity ((a mod pv * (k ^ (pv - 2) mod pv)) mod pv).
  { rewrite (Z.mul_mod (a mod pv) ((k mod pv) ^ (pv - 2)) pv); [|lia].
    rewrite (Z.mul_mod (a mod pv) (k ^ (pv - 2) mod pv) pv); [|lia].
    rewrite Z.mod_pow_l. rewrite !Z.mod_mod; try lia. }
  symmetry. apply div_mod_fermat; [lia|lia|exact Hdiv|].
  exact Hfermat.
Qed.

(* ================================================================== *)
(* Section 6: FL loop invariant                                        *)
(* ================================================================== *)

(* negmod63 of Z_to_mod63 = Z_to_mod63 of negation *)
Lemma negmod63_Z_to_mod63 (p : int) (z : Z) :
  valid_prime p ->
  negmod63 p (Z_to_mod63 p z) = Z_to_mod63 p (-z).
Proof.
  intros Hv. apply Uint63.to_Z_inj.
  assert (Hrange : in_range p (Z_to_mod63 p z))
    by (unfold in_range; rewrite Z_to_mod63_spec; [|exact Hv];
        split; apply Z.mod_pos_bound; destruct Hv; lia).
  rewrite negmod63_spec; [|exact Hv|exact Hrange].
  rewrite !Z_to_mod63_spec; [|exact Hv|exact Hv].
  destruct Hv as [Hp1 Hp2]. set (pv := Uint63.to_Z p).
  rewrite Zminus_mod_idemp_r.
  replace (pv - z)%Z with (- z + pv)%Z by lia.
  replace (- z + pv)%Z with (pv + - z)%Z by lia.
  rewrite <- Zplus_mod_idemp_l. rewrite Z_mod_same_full. simpl. reflexivity.
Qed.

(* FL divisibility at every step *)
Fixpoint fl_all_divisible (steps : nat) (k : Z) (A I_n M_prev : list (list Z))
    (c_prev : Z) : Prop :=
  match steps with
  | O => True
  | S s =>
    let M_k := madd (mmul A M_prev) (IntMat.mscale c_prev I_n) in
    let tr := mtrace (mmul A M_k) in
    (k | tr)%Z /\
    fl_all_divisible s (k + 1) A I_n M_k (Z.div (Z.opp tr) k)
  end.

Theorem fl_loop_mod_sound :
  forall (steps : nat) (k : Z) (A I_n M_prev : list (list Z))
         (c_prev : Z) (acc : list Z) (p : int) (n : nat),
  valid_prime p ->
  (0 < n)%nat ->
  square_mat n A -> square_mat n I_n -> square_mat n M_prev ->
  (k > 0)%Z ->
  (k + Z.of_nat steps < Uint63.to_Z p)%Z ->
  fl_all_divisible steps k A I_n M_prev c_prev ->
  (* Fermat condition for all step indices *)
  (forall j : Z, (0 < j < Uint63.to_Z p)%Z ->
    (j * j ^ (Uint63.to_Z p - 2)) mod Uint63.to_Z p = 1 mod Uint63.to_Z p)%Z ->
  List.map (Z_to_mod63 p)
    (fl_loop steps k A I_n M_prev c_prev acc) =
  fl_mod_loop p
    (reduce_mat_Z p A) (reduce_mat_Z p I_n)
    (reduce_mat_Z p M_prev) (Z_to_mod63 p c_prev)
    (Z_to_mod63 p k)
    (List.map (Z_to_mod63 p) acc)
    steps.
Proof.
  induction steps as [|st IH]; intros k A I_n M_prev c_prev acc p n
    Hv Hn HsA HsI HsM Hk Hkb Hdiv Hfermat.
  - reflexivity.
  - simpl. unfold reduce_mat_Z.
    set (M_k := madd (mmul A M_prev) (IntMat.mscale c_prev I_n)).
    set (tr := mtrace (mmul A M_k)).
    set (c_new := (- tr / k)%Z).
    destruct Hdiv as [Hkdiv Hdiv_rest].
    transitivity (fl_mod_loop p (reduce_mat_Z p A) (reduce_mat_Z p I_n)
      (reduce_mat_Z p M_k)
      (Z_to_mod63 p c_new)
      (Z_to_mod63 p (k + 1))
      (List.map (Z_to_mod63 p) (c_new :: acc))
      st).
    + apply (IH _ _ _ _ _ _ _ n); [exact Hv|exact Hn|exact HsA|exact HsI| |lia|lia|exact Hdiv_rest|exact Hfermat].
      apply square_mat_madd; [|exact (square_mat_mscale n c_prev I_n HsI)].
      exact (square_mat_mmul n A M_prev Hn HsA HsM).
    + unfold reduce_mat_Z. f_equal.
      * (* M_k correspondence *)
        unfold M_k. rewrite madd_mod_sound_gen; [|exact Hv]. f_equal.
        -- apply mmul_mod_sound; [exact Hv| |].
           ++ intros i Hi. destruct HsA as [HdA HwA]. destruct HsM as [HdM _].
              rewrite HwA; [symmetry; exact HdM|unfold mat_dim in HdA; lia].
           ++ intros j Hj. destruct HsM as [HdM HwM].
              rewrite HwM; [symmetry; exact HdM | unfold mat_dim in HdM; lia].
        -- apply mscale_mod_sound; exact Hv.
      * (* c_new: division soundness *)
        assert (HsMk : square_mat n M_k)
          by (apply square_mat_madd; [exact (square_mat_mmul n A M_prev Hn HsA HsM)|
                                       exact (square_mat_mscale n c_prev I_n HsI)]).
        assert (HsAMk : square_mat n (mmul A M_k))
          by (exact (square_mat_mmul n A M_k Hn HsA HsMk)).
        assert (Htrace_eq :
          mmat_trace p (mmat_mul p (map (map (Z_to_mod63 p)) A)
            (mmat_add p (mmat_mul p (map (map (Z_to_mod63 p)) A)
              (map (map (Z_to_mod63 p)) M_prev))
              (mmat_scale p (Z_to_mod63 p c_prev) (map (map (Z_to_mod63 p)) I_n))))
          = Z_to_mod63 p tr).
        { unfold tr. symmetry.
          rewrite (trace_mod_sound p (mmul A M_k) Hv).
          2:{ destruct HsAMk as [Hd Hw]. intros j Hj.
              rewrite Hw; [unfold mat_dim in Hd; lia|unfold mat_dim in Hd; lia]. }
          f_equal. unfold M_k.
          rewrite (mmul_mod_sound p A
            (madd (mmul A M_prev) (IntMat.mscale c_prev I_n)) Hv).
          2:{ destruct HsA as [HdA HwA]. destruct HsMk as [HdMk _]. intros i Hi.
              rewrite HwA; [symmetry; exact HdMk|unfold mat_dim in HdA; lia]. }
          2:{ destruct HsMk as [HdMk HwMk]. intros j Hj.
              fold M_k. fold M_k in Hj.
              rewrite HwMk; [symmetry; exact HdMk|unfold mat_dim in HdMk; lia]. }
          f_equal. rewrite (madd_mod_sound_gen p _ _ Hv). f_equal.
          - apply mmul_mod_sound; [exact Hv| |].
            + destruct HsA as [HdA HwA]. destruct HsM as [HdM _]. intros i Hi.
              rewrite HwA; [symmetry; exact HdM|unfold mat_dim in HdA; lia].
            + destruct HsM as [HdM HwM]. intros j Hj.
              rewrite HwM; [symmetry; exact HdM|unfold mat_dim in HdM; lia].
          - apply mscale_mod_sound; exact Hv. }
        rewrite Htrace_eq. unfold c_new.
        rewrite negmod63_Z_to_mod63; [|exact Hv].
        apply Uint63.to_Z_inj.
        rewrite Z_to_mod63_spec; [|exact Hv].
        set (pv := Uint63.to_Z p).
        rewrite (divmod63_spec p (-tr) k Hv); [reflexivity|lia|lia| |].
        -- apply Z.divide_opp_r. exact Hkdiv.
        -- apply Hfermat; lia.
      * (* k+1 *)
        apply Uint63.to_Z_inj.
        rewrite Z_to_mod63_spec; [|exact Hv].
        rewrite add_spec. rewrite Z_to_mod63_spec; [|exact Hv].
        rewrite to_Z_1.
        destruct Hv as [Hp1 Hp2].
        set (pv := Uint63.to_Z p) in *.
        assert (Hkmod : (k mod pv = k)%Z) by (rewrite Z.mod_small; lia).
        rewrite Hkmod.
        assert (Hsum_nf : (0 <= k + 1 < wB)%Z).
        { split; [lia|]. assert (wB = (2^63)%Z) as -> by reflexivity. lia. }
        rewrite (Z.mod_small _ wB Hsum_nf).
        rewrite Z.mod_small; lia.
      * (* c_new :: acc — same as c_new above *)
        simpl. f_equal.
        -- (* Same as c_new goal *)
           assert (HsMk : square_mat n M_k)
             by (apply square_mat_madd; [exact (square_mat_mmul n A M_prev Hn HsA HsM)|
                                          exact (square_mat_mscale n c_prev I_n HsI)]).
           assert (HsAMk : square_mat n (mmul A M_k))
             by (exact (square_mat_mmul n A M_k Hn HsA HsMk)).
           assert (Htrace_eq :
             mmat_trace p (mmat_mul p (map (map (Z_to_mod63 p)) A)
               (mmat_add p (mmat_mul p (map (map (Z_to_mod63 p)) A)
                 (map (map (Z_to_mod63 p)) M_prev))
                 (mmat_scale p (Z_to_mod63 p c_prev) (map (map (Z_to_mod63 p)) I_n))))
             = Z_to_mod63 p tr).
           { unfold tr. symmetry.
             rewrite (trace_mod_sound p (mmul A M_k) Hv).
             2:{ destruct HsAMk as [Hd Hw]. intros j Hj.
                 rewrite Hw; [unfold mat_dim in Hd; lia|unfold mat_dim in Hd; lia]. }
             f_equal. unfold M_k.
             rewrite (mmul_mod_sound p A
               (madd (mmul A M_prev) (IntMat.mscale c_prev I_n)) Hv).
             2:{ destruct HsA as [HdA HwA]. destruct HsMk as [HdMk _]. intros i Hi.
                 rewrite HwA; [symmetry; exact HdMk|unfold mat_dim in HdA; lia]. }
             2:{ destruct HsMk as [HdMk HwMk]. intros j Hj.
                 fold M_k. fold M_k in Hj.
                 rewrite HwMk; [symmetry; exact HdMk|unfold mat_dim in HdMk; lia]. }
             f_equal. rewrite (madd_mod_sound_gen p _ _ Hv). f_equal.
             - apply mmul_mod_sound; [exact Hv| |].
               + destruct HsA as [HdA HwA]. destruct HsM as [HdM _]. intros i Hi.
                 rewrite HwA; [symmetry; exact HdM|unfold mat_dim in HdA; lia].
               + destruct HsM as [HdM HwM]. intros j Hj.
                 rewrite HwM; [symmetry; exact HdM|unfold mat_dim in HdM; lia].
             - apply mscale_mod_sound; exact Hv. }
           rewrite Htrace_eq. unfold c_new.
           rewrite negmod63_Z_to_mod63; [|exact Hv].
           apply Uint63.to_Z_inj.
           rewrite Z_to_mod63_spec; [|exact Hv].
           set (pv := Uint63.to_Z p).
           rewrite (divmod63_spec p (-tr) k Hv); [reflexivity|lia|lia| |].
           ++ apply Z.divide_opp_r. exact Hkdiv.
           ++ apply Hfermat; lia.
Qed.

(* ================================================================== *)
(* Section 7: Main theorem                                             *)
(* ================================================================== *)

Theorem char_poly_mod_sound (p : int) (M : list (list Z)) :
  valid_prime p ->
  square_mat (List.length M) M ->
  (Z.of_nat (List.length M) + 1 < Uint63.to_Z p)%Z ->
  (* FL divisibility for M (holds by Newton's identity / fl_divisibility_L2) *)
  fl_all_divisible (List.length M) Z.one M
    (meye (List.length M)) (mzero (List.length M)) Z.one ->
  (* Fermat condition (holds when to_Z p is prime) *)
  (forall j : Z, (0 < j < Uint63.to_Z p)%Z ->
    (j * j ^ (Uint63.to_Z p - 2)) mod Uint63.to_Z p = 1 mod Uint63.to_Z p)%Z ->
  List.map (Z_to_mod63 p) (char_poly_int M) = char_poly_mod p M.
Proof.
  intros Hv Hsq Hbound Hfldiv Hfermat.
  unfold char_poly_int, char_poly_mod.
  set (n := List.length M).
  assert (Hmd : mat_dim M = n) by (unfold mat_dim; reflexivity).
  rewrite Hmd.
  rewrite List.map_app. simpl.
  f_equal.
  - (* FL loop part *)
    rewrite <- (meye_mod_eq p n Hv). rewrite <- (mzero_mod_eq p n Hv).
    replace ((1 mod p)%uint63) with (Z_to_mod63 p Z.one).
    2:{ apply Uint63.to_Z_inj. rewrite Z_to_mod63_spec; [|exact Hv]. rewrite mod_spec. reflexivity. }
    replace 1%uint63 with (Z_to_mod63 p Z.one).
    2:{ apply Uint63.to_Z_inj. rewrite Z_to_mod63_spec; [|exact Hv].
        change (to_Z 1) with 1%Z. unfold Z.one. rewrite Z.mod_small; [reflexivity|destruct Hv as [H1 H2]; lia]. }
    destruct n as [|n']; [reflexivity|].
    apply fl_loop_mod_sound with (n := S n').
    + exact Hv.
    + lia.
    + rewrite <- Hmd. exact Hsq.
    + (* square_mat (S n') (meye (S n')) *)
      split.
      * unfold mat_dim, meye.
        enough (forall i, List.length (meye_aux (S n') i) = i) as H by exact (H (S n')).
        induction i; [reflexivity|]. simpl. rewrite List.length_app. simpl. rewrite IHi. lia.
      * intros i Hi. unfold meye.
        enough (forall j k, (k < j)%nat -> (j <= S n')%nat ->
          List.length (List.nth k (meye_aux (S n') j) []) = S n') as H
          by exact (H (S n') i Hi (Nat.le_refl _)).
        induction j; intros k Hk Hj; [lia|].
        simpl. destruct (Nat.lt_ge_cases k j).
        -- rewrite List.app_nth1; [apply IHj; lia|].
           enough (List.length (meye_aux (S n') j) = j) by lia.
           clear. induction j; [reflexivity|]. simpl. rewrite List.length_app. simpl. rewrite IHj. lia.
        -- assert (k = j) by lia. subst k.
           rewrite List.app_nth2.
           ++ enough (Hlen : List.length (meye_aux (S n') j) = j).
              { rewrite Hlen. rewrite Nat.sub_diag. simpl.
                clear -n'. revert j. induction n'; intros j; destruct j; simpl; try lia.
                ** enough (forall m, List.length (zrow m) = m) by (rewrite H; lia).
                   induction m; [reflexivity|]. simpl. f_equal. exact IHm.
                ** specialize (IHn' j). lia. }
              clear. induction j; [reflexivity|]. simpl. rewrite List.length_app. simpl. rewrite IHj. lia.
           ++ enough (List.length (meye_aux (S n') j) = j) by lia.
              clear. induction j; [reflexivity|]. simpl. rewrite List.length_app. simpl. rewrite IHj. lia.
    + (* square_mat (S n') (mzero (S n')) *)
      split.
      * unfold mat_dim, mzero.
        enough (forall r c, List.length (mzero_aux r c) = r) as H by exact (H (S n') (S n')).
        induction r; intros c; [reflexivity|]. simpl. f_equal. apply IHr.
      * intros i Hi. unfold mzero.
        enough (forall r c k, (k < r)%nat -> List.length (List.nth k (mzero_aux r c) []) = c) as H
          by exact (H (S n') (S n') i Hi).
        induction r; intros c k Hk; [lia|].
        destruct k; simpl.
        -- clear. induction c; [reflexivity|]. simpl. f_equal. exact IHc.
        -- apply IHr. lia.
    + unfold Z.one; lia.
    + unfold Z.one, mat_dim in *; lia.
    + rewrite <- Hmd. exact Hfldiv.
    + exact Hfermat.
  - (* Leading coefficient: Z_to_mod63 p 1 = 1 mod p *)
    f_equal.
    apply Uint63.to_Z_inj.
    rewrite Z_to_mod63_spec; [|exact Hv].
    rewrite mod_spec. reflexivity.
Qed.

(* ================================================================== *)
(* Section 8: fl_all_divisible from fl_divisibility_L2                  *)
(*                                                                     *)
(* Bridge between CRTBridge's step-by-step fl_all_divisible and        *)
(* CharPoly's fl_divisibility_L2 (which proves divisibility at any     *)
(* step index using Newton's identities).                              *)
(* ================================================================== *)

(* The FL loop intermediate states match fl_state from CharPoly.v.
   fl_all_divisible tracks: at step j, (j | trace(A * M_j)).
   fl_divisibility_L2 proves: for any k <= n, k | trace(M * fl_M_int_k(M,k)).
   The connection: M_j in fl_all_divisible = fl_M_int_k(A, j).

   This bridge requires showing by induction that fl_all_divisible's
   M_prev/c_prev match fl_M_int_k/fl_c_int_k at each step.
   The proof uses fl_state's definition (which mirrors fl_all_divisible). *)

Lemma fl_all_divisible_from_L2 (M : list (list Z)) (n : nat) :
  mat_dim M = n ->
  (forall i, (i < List.length M)%nat -> List.length (List.nth i M []) = n) ->
  fl_all_divisible n Z.one M (meye n) (mzero n) Z.one.
Proof.
  intros Hdim Hwf.
  (* The FL loop starts with M_prev = mzero n, c_prev = 1, k = 1.
     At each step j (1-indexed): M_j = madd(mmul M M_{j-1})(mscale c_{j-1} I),
     and we need j | trace(mmul M M_j).
     This matches fl_state j M = (fl_M_int_k M j, fl_c_int_k M j),
     and fl_divisibility_L2 gives Z.rem(trace(mmul M (fl_M_int_k M j)))(j) = 0.
     The bridge is by induction showing the states agree. *)
  cut (forall steps j, (j + steps <= n)%nat ->
    fl_all_divisible steps (Z.of_nat (S j)) M (meye (mat_dim M))
      (fst (fl_state j M)) (snd (fl_state j M))).
  { intros H. rewrite <- Hdim in *. exact (H (mat_dim M) 0%nat (Nat.le_refl _)). }
  induction steps as [|s IH]; intros j Hj.
  - exact I.
  - simpl. split.
    + destruct (fl_state j M) as [Mj cj] eqn:HFS.
      simpl fst. simpl snd.
      (* Now create Hdiv with the destructed form *)
      pose proof (@fl_divisibility_L2 M n (S j) Hdim Hwf) as Hdiv.
      assert (H1 : is_true (ssrnat.leq 1 (S j))) by reflexivity.
      assert (H2 : is_true (ssrnat.leq (S j) n))
        by (unfold is_true, ssrnat.leq; apply Nat.eqb_eq; unfold ssrnat.subn; lia).
      specialize (Hdiv H1 H2).
      unfold fl_M_int_k in Hdiv. simpl fl_state in Hdiv. rewrite HFS in Hdiv. simpl fst in Hdiv.
      apply Z.rem_divide in Hdiv; [exact Hdiv|lia].
    + replace (Z.of_nat (S j) + 1)%Z with (Z.of_nat (S (S j))) by lia.
      specialize (IH (S j) ltac:(lia)).
      destruct (fl_state j M) as [Mj cj] eqn:HFS.
      simpl fst in *. simpl snd in *. rewrite HFS in IH. simpl in IH.
      replace (Z.pos (PosDef.Pos.of_succ_nat j + 1)) with
        (Z.pos (PosDef.Pos.succ (PosDef.Pos.of_succ_nat j))) by lia.
      exact IH.
Qed.

(* ================================================================== *)
(* Section 9: Concrete verification for A_int                          *)
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
(* 1. char_poly_int_agrees_710 (from CharPolyAgree.v, Qed) tells us:   *)
(*      forall p in crt_primes_all,                                    *)
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
(*      forall p in crt_primes_all, forall k,                          *)
(*        (char_poly_int A_int)[k] mod p                               *)
(*        = charpoly_of_A_int[k] mod p                                 *)
(*                                                                     *)
(* 5. Product of 710 primes > 2^{21000} >> max coefficient magnitude   *)
(*    => by CRT, char_poly_int A_int = charpoly_of_A_int over Z.      *)
(*                                                                     *)
(* Similarly for matrix_identity_Z.                                    *)
(* ================================================================== *)

Close Scope uint63_scope.
