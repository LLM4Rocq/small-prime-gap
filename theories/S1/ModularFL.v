(* ===================================================================
   ModularFL.v -- Axiom-free, stdlib-Z modular Faddeev-LeVerrier.

   This is the pure-Z replacement for the dropped Uint63 backend
   (ModularArith / CRTBridge).  Every matrix / scalar operation is
   performed modulo a prime p over Stdlib's Z (Z.modulo); fast modular
   exponentiation (powmodZ) keeps intermediate values bounded so the
   whole pipeline reduces under vm_compute.

   Main result (mirrors CRTBridge.char_poly_mod_sound, Uint63 stripped):

     char_poly_modZ_sound :
       forall (p:Z)(M:mat),
         Znumtheory.prime p ->
         square_mat (length M) M ->
         (Z.of_nat (length M) + 1 < p)%Z ->
         fl_all_divisible (length M) 1 M (meye (length M)) (mzero (length M)) 1 ->
         char_poly_modZ p M = map (fun c => c mod p) (char_poly_int M).

   The division step is justified by Fermat's little theorem
   (Fermat.fermat_Z) through the pure-Z lemma mfl_div_mod_fermat,
   ported verbatim from CRTBridge ~line 537.  The bridge from Stdlib's
   Znumtheory.prime to MathComp's prime is PrimeCheck.Zprime_to_ssrprime.

   No Uint63 / PrimInt63 / native_compute / Axiom / Parameter appears.
   =================================================================== *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

From PrimeGapS1 Require Import IntMat CharPoly Fermat FLDiv PrimeCheck.
From Stdlib Require Znumtheory.

(* ================================================================== *)
(* Section 0: modular scalar arithmetic over Z                         *)
(* ================================================================== *)

Definition addmodZ (p a b : Z) : Z := (a + b) mod p.
Definition mulmodZ (p a b : Z) : Z := (a * b) mod p.
Definition negmodZ (p a : Z) : Z := (- a) mod p.

(* Fast modular exponentiation (binary), reducing at each squaring. *)
Fixpoint powmodZ_pos (p base : Z) (e : positive) : Z :=
  match e with
  | xH => base mod p
  | xO e' => let h := powmodZ_pos p base e' in mulmodZ p h h
  | xI e' => let h := powmodZ_pos p base e' in mulmodZ p base (mulmodZ p h h)
  end.

Definition powmodZ (p base e : Z) : Z :=
  match e with
  | Z0     => 1 mod p
  | Zpos q => powmodZ_pos p base q
  | Zneg _ => 1 mod p
  end.

(* Fermat inverse: a^(p-2) mod p. *)
Definition invmodZ (p a : Z) : Z := powmodZ p a (p - 2).

Definition divmodZ (p a k : Z) : Z := mulmodZ p a (invmodZ p k).

(* ================================================================== *)
(* Section 1: modular matrix operations over `mat = list (list Z)`     *)
(* ================================================================== *)

Definition reduceZ (p : Z) (M : mat) : mat :=
  map (map (fun c => c mod p)) M.

Fixpoint vaddZ (p : Z) (xs ys : list Z) : list Z :=
  match xs, ys with
  | nil, _ => ys
  | _, nil => xs
  | x :: xs', y :: ys' => addmodZ p x y :: vaddZ p xs' ys'
  end.

Definition vscaleZ (p c : Z) (xs : list Z) : list Z :=
  map (fun x => mulmodZ p c x) xs.

Fixpoint maddZ (p : Z) (A B : mat) : mat :=
  match A, B with
  | nil, _ => B
  | _, nil => A
  | r1 :: A', r2 :: B' => vaddZ p r1 r2 :: maddZ p A' B'
  end.

Definition mscaleZ (p c : Z) (A : mat) : mat := map (vscaleZ p c) A.

Fixpoint dotmodZ (p : Z) (xs ys : list Z) : Z :=
  match xs, ys with
  | nil, _ => 0
  | _, nil => 0
  | x :: xs', y :: ys' => addmodZ p (mulmodZ p x y) (dotmodZ p xs' ys')
  end.

Definition mmulZ (p : Z) (A B : mat) : mat :=
  let Bt := mtrans B in
  map (fun row => map (fun col => dotmodZ p row col) Bt) A.

Fixpoint mtraceZ_aux (p : Z) (i : nat) (m : mat) : Z :=
  match m with
  | nil => 0
  | row :: rest => addmodZ p (nth_Z row i) (mtraceZ_aux p (S i) rest)
  end.

Definition mtraceZ (p : Z) (m : mat) : Z := mtraceZ_aux p 0 m.

(* ================================================================== *)
(* Section 2: the modular FL loop and the modular char. poly           *)
(* ================================================================== *)

Fixpoint fl_modZ_loop (p : Z) (steps : nat) (k : Z)
  (A I_n M_prev : mat) (c_prev : Z) (acc : list Z) : list Z :=
  match steps with
  | O => acc
  | S s =>
      let M_k   := maddZ p (mmulZ p A M_prev) (mscaleZ p c_prev I_n) in
      let tr    := mtraceZ p (mmulZ p A M_k) in
      let c_new := divmodZ p (negmodZ p tr) k in
      fl_modZ_loop p s (k + 1) A I_n M_k c_new (c_new :: acc)
  end.

Definition char_poly_modZ (p : Z) (M : mat) : list Z :=
  let n := mat_dim M in
  fl_modZ_loop p n 1%Z (reduceZ p M) (reduceZ p (meye n)) (reduceZ p (mzero n))
    (1 mod p) []
  ++ [1 mod p].

(* ================================================================== *)
(* Section 3: power identities (pure-Z, ported from CRTBridge)         *)
(* ================================================================== *)

Local Lemma mfl_Z_pow_xI_eq (b : Z) (pos : positive) :
  b * (b ^ Z.pos pos * b ^ Z.pos pos) = b ^ Z.pos pos~1.
Proof.
  change (Z.pos pos~1) with (2 * Z.pos pos + 1)%Z.
  replace (2 * Z.pos pos + 1)%Z with (1 + Z.pos pos + Z.pos pos)%Z by lia.
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_add_r; [|lia|lia].
  rewrite Z.pow_1_r. ring.
Qed.

Local Lemma mfl_Z_pow_xO_eq (b : Z) (pos : positive) :
  b ^ Z.pos pos * b ^ Z.pos pos = b ^ Z.pos pos~0.
Proof.
  change (Z.pos pos~0) with (2 * Z.pos pos)%Z.
  replace (2 * Z.pos pos)%Z with (Z.pos pos + Z.pos pos)%Z by lia.
  rewrite Z.pow_add_r; [|lia|lia]. reflexivity.
Qed.

Local Lemma mfl_powmodZ_pos_spec (p base : Z) (e : positive) :
  (0 < p)%Z -> powmodZ_pos p base e = (base ^ Z.pos e) mod p.
Proof.
  intros Hp. induction e as [e IH|e IH|].
  - cbn [powmodZ_pos]. unfold mulmodZ. rewrite IH.
    rewrite <- Zmult_mod. rewrite Zmult_mod_idemp_r. rewrite mfl_Z_pow_xI_eq.
    reflexivity.
  - cbn [powmodZ_pos]. unfold mulmodZ. rewrite IH.
    rewrite <- Zmult_mod. rewrite mfl_Z_pow_xO_eq. reflexivity.
  - cbn [powmodZ_pos]. change (Z.pos 1) with 1%Z. rewrite Z.pow_1_r. reflexivity.
Qed.

Local Lemma mfl_invmodZ_spec (p a : Z) :
  (2 < p)%Z -> invmodZ p a = (a ^ (p - 2)) mod p.
Proof.
  intros Hp. unfold invmodZ.
  remember (p - 2)%Z as e eqn:E.
  destruct e as [|q|q]; try lia.
  cbn [powmodZ]. rewrite mfl_powmodZ_pos_spec by lia.
  reflexivity.
Qed.

(* ================================================================== *)
(* Section 4: division soundness via Fermat                            *)
(* ================================================================== *)

(* Pure-Z port of CRTBridge.div_mod_fermat (~line 537). *)
Local Lemma mfl_div_mod_fermat (a k p : Z) :
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

Local Lemma mfl_divmodZ_spec (p a k : Z) :
  is_true (prime.prime (Z.to_nat p)) ->
  (2 < p)%Z -> (0 < k)%Z -> (k < p)%Z -> (k | a)%Z ->
  divmodZ p (a mod p) k = (a / k) mod p.
Proof.
  intros Hpr Hp Hk Hkp Hdvd.
  unfold divmodZ, mulmodZ.
  rewrite (mfl_invmodZ_spec p k) by lia.
  symmetry. apply mfl_div_mod_fermat; [lia|lia|exact Hdvd|].
  apply fermat_Z; [lia|exact Hpr|lia].
Qed.

(* ================================================================== *)
(* Section 5: reduceZ commutes with the matrix operations             *)
(* ================================================================== *)

Local Lemma mfl_nth_Z_map_mod (p : Z) (row : list Z) (i : nat) :
  (p <> 0)%Z ->
  nth_Z (map (fun c => c mod p) row) i = (nth_Z row i) mod p.
Proof.
  intros Hp. unfold nth_Z.
  destruct (Nat.ltb i (length row)) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    rewrite <- (map_nth (fun c => c mod p) row 0 i).
    apply nth_indep. rewrite length_map. exact Hlt.
  - apply Nat.ltb_ge in Hlt.
    rewrite nth_overflow; [|rewrite length_map; exact Hlt].
    rewrite nth_overflow; [|exact Hlt].
    symmetry. apply Z.mod_0_l; exact Hp.
Qed.

Local Lemma mfl_dotmodZ_sound (p : Z) (xs ys : list Z) :
  (p <> 0)%Z ->
  dotmodZ p (map (fun c => c mod p) xs) (map (fun c => c mod p) ys)
  = (dot_int xs ys) mod p.
Proof.
  intros Hp. revert ys. induction xs as [|x xs' IH]; intros [|y ys']; simpl.
  - symmetry; apply Z.mod_0_l; exact Hp.
  - symmetry; apply Z.mod_0_l; exact Hp.
  - symmetry; apply Z.mod_0_l; exact Hp.
  - unfold addmodZ, mulmodZ. rewrite IH.
    rewrite <- Zmult_mod. rewrite <- Zplus_mod. reflexivity.
Qed.

Local Lemma mfl_vscaleZ_sound (p c : Z) (xs : list Z) :
  map (fun a => a mod p) (vscale c xs)
  = vscaleZ p (c mod p) (map (fun a => a mod p) xs).
Proof.
  induction xs as [|x xs' IH]; [reflexivity|].
  simpl. f_equal; [|exact IH].
  unfold mulmodZ. apply Zmult_mod.
Qed.

Local Lemma mfl_mscaleZ_sound (p c : Z) (A : mat) :
  reduceZ p (mscale c A) = mscaleZ p (c mod p) (reduceZ p A).
Proof.
  unfold reduceZ, mscale, mscaleZ. rewrite !map_map.
  apply map_ext. intros row. cbn beta.
  apply (mfl_vscaleZ_sound p c row).
Qed.

Local Lemma mfl_vaddZ_sound (p : Z) (xs ys : list Z) :
  map (fun a => a mod p) (vadd xs ys)
  = vaddZ p (map (fun a => a mod p) xs) (map (fun a => a mod p) ys).
Proof.
  revert ys. induction xs as [|x xs' IH]; intros [|y ys']; simpl; try reflexivity.
  f_equal; [|exact (IH ys')].
  unfold addmodZ. apply Zplus_mod.
Qed.

Local Lemma mfl_maddZ_sound (p : Z) (A B : mat) :
  reduceZ p (madd A B) = maddZ p (reduceZ p A) (reduceZ p B).
Proof.
  revert B. unfold reduceZ.
  induction A as [|ra A' IH]; intros [|rb B']; simpl; try reflexivity.
  f_equal; [|exact (IH B')].
  apply (mfl_vaddZ_sound p ra rb).
Qed.

(* ---- transpose commutes with reduceZ ---- *)

Local Lemma mfl_reduceZ_all_empty (p : Z) (M : mat) :
  all_empty (reduceZ p M) = all_empty M.
Proof.
  unfold reduceZ. induction M as [|row rest IH]; [reflexivity|].
  destruct row as [|x xs]; simpl; [exact IH | reflexivity].
Qed.

Local Lemma mfl_reduceZ_heads (p : Z) (M : mat) :
  (p <> 0)%Z ->
  heads (reduceZ p M) = map (fun c => c mod p) (heads M).
Proof.
  intros Hp. unfold reduceZ. induction M as [|row rest IH]; [reflexivity|].
  destruct row as [|x xs]; simpl; rewrite IH;
    (reflexivity || (f_equal; symmetry; apply Z.mod_0_l; exact Hp)).
Qed.

Local Lemma mfl_reduceZ_tails (p : Z) (M : mat) :
  reduceZ p (tails M) = tails (reduceZ p M).
Proof.
  unfold reduceZ. induction M as [|row rest IH]; [reflexivity|].
  destruct row as [|x xs]; simpl; rewrite IH; reflexivity.
Qed.

Local Lemma mfl_reduceZ_mtrans_fuel (p : Z) (fuel : nat) (M : mat) :
  (p <> 0)%Z ->
  mtrans_fuel fuel (reduceZ p M) = reduceZ p (mtrans_fuel fuel M).
Proof.
  intros Hp. revert M. induction fuel as [|f IH]; intros M; [reflexivity|].
  cbn [mtrans_fuel].
  rewrite (mfl_reduceZ_all_empty p M).
  destruct (all_empty M) eqn:Hae.
  - reflexivity.
  - rewrite (mfl_reduceZ_heads p M Hp).
    rewrite <- (mfl_reduceZ_tails p M).
    rewrite (IH (tails M)).
    reflexivity.
Qed.

Local Lemma mfl_mtrans_cons (r : list Z) (rest : mat) :
  mtrans (r :: rest) = mtrans_fuel (length r) (r :: rest).
Proof. reflexivity. Qed.

Local Lemma mfl_mtrans_reduceZ (p : Z) (M : mat) :
  (p <> 0)%Z ->
  mtrans (reduceZ p M) = reduceZ p (mtrans M).
Proof.
  intros Hp. destruct M as [|row rest].
  - reflexivity.
  - transitivity (reduceZ p (mtrans_fuel (length row) (row :: rest))).
    + replace (reduceZ p (row :: rest))
        with ((map (fun c => c mod p) row) :: reduceZ p rest) by reflexivity.
      rewrite mfl_mtrans_cons, length_map.
      replace ((map (fun c => c mod p) row) :: reduceZ p rest)
        with (reduceZ p (row :: rest)) by reflexivity.
      apply (mfl_reduceZ_mtrans_fuel p (length row) (row :: rest) Hp).
    + rewrite mfl_mtrans_cons. reflexivity.
Qed.

Local Lemma mfl_mmul_row_sound (p : Z) (row : list Z) (Bt : mat) :
  (p <> 0)%Z ->
  map (fun col => dotmodZ p (map (fun c => c mod p) row) col)
      (map (map (fun c => c mod p)) Bt)
  = map (fun c => c mod p) (map (fun col => dot_int row col) Bt).
Proof.
  intros Hp. induction Bt as [|col cols IH]; [reflexivity|].
  simpl. f_equal; [|exact IH].
  apply mfl_dotmodZ_sound; exact Hp.
Qed.

Local Lemma mfl_mmulZ_sound (p : Z) (A B : mat) :
  (p <> 0)%Z ->
  mmulZ p (reduceZ p A) (reduceZ p B) = reduceZ p (mmul A B).
Proof.
  intros Hp. unfold mmulZ, mmul.
  rewrite (mfl_mtrans_reduceZ p B Hp).
  unfold reduceZ.
  rewrite !map_map.
  apply map_ext. intros row. cbn beta.
  apply (mfl_mmul_row_sound p row (mtrans B) Hp).
Qed.

Local Lemma mfl_mtraceZ_aux_sound (p : Z) (M : mat) (i : nat) :
  (p <> 0)%Z ->
  mtraceZ_aux p i (reduceZ p M) = (mtrace_aux i M) mod p.
Proof.
  intros Hp. revert i. induction M as [|row rest IH]; intros i.
  - simpl. symmetry. apply Z.mod_0_l; exact Hp.
  - replace (reduceZ p (row :: rest))
      with ((map (fun c => c mod p) row) :: reduceZ p rest) by reflexivity.
    cbn [mtraceZ_aux mtrace_aux].
    unfold addmodZ.
    rewrite (mfl_nth_Z_map_mod p row i Hp).
    rewrite IH.
    rewrite <- Zplus_mod. reflexivity.
Qed.

Local Lemma mfl_mtraceZ_sound (p : Z) (M : mat) :
  (p <> 0)%Z -> mtraceZ p (reduceZ p M) = (mtrace M) mod p.
Proof.
  intros Hp. unfold mtraceZ, mtrace. apply mfl_mtraceZ_aux_sound; exact Hp.
Qed.

Local Lemma mfl_negmodZ_mod (p a : Z) :
  negmodZ p (a mod p) = (- a) mod p.
Proof.
  unfold negmodZ.
  rewrite <- (Z.sub_0_l (a mod p)).
  rewrite Zminus_mod_idemp_r.
  rewrite Z.sub_0_l. reflexivity.
Qed.

(* ================================================================== *)
(* Section 6: square_mat for meye / mzero                              *)
(* ================================================================== *)

Local Lemma mfl_length_zrow (n : nat) : length (zrow n) = n.
Proof. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

Local Lemma mfl_length_eye_row (n i : nat) : length (eye_row n i) = n.
Proof.
  revert i. induction n as [|k IH]; intros [|i]; simpl; try reflexivity.
  - f_equal. apply mfl_length_zrow.
  - f_equal. apply IH.
Qed.

Local Lemma mfl_square_mat_meye (n : nat) : square_mat n (meye n).
Proof.
  split; [apply mat_dim_meye|].
  intros i Hi. unfold meye.
  assert (Hic : (i < n)%nat) by lia.
  rewrite (nth_meye_aux n i n [] Hic (Nat.le_refl n)).
  apply mfl_length_eye_row.
Qed.

Local Lemma mfl_square_mat_mzero (n : nat) : square_mat n (mzero n).
Proof.
  split; [apply mat_dim_mzero|].
  intros i Hi. unfold mzero.
  assert (Hic : (i < n)%nat) by lia.
  rewrite (nth_mzero_aux_is_zrow n n i [] Hic).
  apply mfl_length_zrow.
Qed.

(* ================================================================== *)
(* Section 7: unfolding lemmas for the FL loops                        *)
(* ================================================================== *)

Local Lemma mfl_fl_modZ_loop_S
  (p : Z) (s : nat) (k : Z) (A I_n M_prev : mat) (c_prev : Z) (acc : list Z) :
  fl_modZ_loop p (S s) k A I_n M_prev c_prev acc =
  fl_modZ_loop p s (k + 1) A I_n
    (maddZ p (mmulZ p A M_prev) (mscaleZ p c_prev I_n))
    (divmodZ p (negmodZ p
       (mtraceZ p (mmulZ p A
          (maddZ p (mmulZ p A M_prev) (mscaleZ p c_prev I_n))))) k)
    ((divmodZ p (negmodZ p
       (mtraceZ p (mmulZ p A
          (maddZ p (mmulZ p A M_prev) (mscaleZ p c_prev I_n))))) k) :: acc).
Proof. reflexivity. Qed.

Local Lemma mfl_fl_loop_S
  (s : nat) (k : Z) (A I_n M_prev : mat) (c_prev : Z) (acc : list Z) :
  fl_loop (S s) k A I_n M_prev c_prev acc =
  fl_loop s (k + 1) A I_n
    (madd (mmul A M_prev) (mscale c_prev I_n))
    (Z.div (Z.opp
       (mtrace (mmul A (madd (mmul A M_prev) (mscale c_prev I_n))))) k)
    ((Z.div (Z.opp
       (mtrace (mmul A (madd (mmul A M_prev) (mscale c_prev I_n))))) k) :: acc).
Proof. reflexivity. Qed.

Local Lemma mfl_fl_all_divisible_S
  (s : nat) (k : Z) (A I_n M_prev : mat) (c_prev : Z) :
  fl_all_divisible (S s) k A I_n M_prev c_prev ->
  (k | mtrace (mmul A (madd (mmul A M_prev) (mscale c_prev I_n))))%Z /\
  fl_all_divisible s (k + 1) A I_n
    (madd (mmul A M_prev) (mscale c_prev I_n))
    (Z.div (Z.opp
       (mtrace (mmul A (madd (mmul A M_prev) (mscale c_prev I_n))))) k).
Proof. intro H; exact H. Qed.

(* ================================================================== *)
(* Section 8: the modular FL loop is sound                             *)
(* ================================================================== *)

Local Lemma mfl_fl_modZ_loop_sound :
  forall (steps : nat) (k : Z) (A I_n M_prev : mat) (c_prev : Z) (acc : list Z)
         (p : Z) (n : nat),
  (1 < p)%Z ->
  is_true (prime.prime (Z.to_nat p)) ->
  (0 < n)%nat ->
  square_mat n A -> square_mat n I_n -> square_mat n M_prev ->
  (0 < k)%Z ->
  (k + Z.of_nat steps < p)%Z ->
  fl_all_divisible steps k A I_n M_prev c_prev ->
  fl_modZ_loop p steps k (reduceZ p A) (reduceZ p I_n) (reduceZ p M_prev)
    (c_prev mod p) (map (fun c => c mod p) acc)
  = map (fun c => c mod p) (fl_loop steps k A I_n M_prev c_prev acc).
Proof.
  induction steps as [|st IH];
    intros k A I_n M_prev c_prev acc p n Hp Hpr Hn HsA HsI HsM Hk Hkb Hdiv.
  - reflexivity.
  - rewrite mfl_fl_modZ_loop_S, mfl_fl_loop_S.
    assert (Hp0 : (p <> 0)%Z) by lia.
    assert (Hst0 : (0 <= Z.of_nat st)%Z) by apply Zle_0_nat.
    assert (Hss : Z.of_nat (S st) = (Z.of_nat st + 1)%Z)
      by (rewrite Nat2Z.inj_succ; lia).
    destruct (mfl_fl_all_divisible_S st k A I_n M_prev c_prev Hdiv) as [Hkdiv Hrest].
    set (M_k := madd (mmul A M_prev) (mscale c_prev I_n)) in *.
    set (tr := mtrace (mmul A M_k)) in *.
    set (c_new := Z.div (Z.opp tr) k) in *.
    (* the modular M_k is reduceZ of M_k *)
    assert (HMk : maddZ p (mmulZ p (reduceZ p A) (reduceZ p M_prev))
                    (mscaleZ p (c_prev mod p) (reduceZ p I_n)) = reduceZ p M_k).
    { unfold M_k.
      rewrite (mfl_mmulZ_sound p A M_prev Hp0).
      rewrite <- (mfl_mscaleZ_sound p c_prev I_n).
      rewrite <- (mfl_maddZ_sound p (mmul A M_prev) (mscale c_prev I_n)).
      reflexivity. }
    rewrite HMk.
    (* the modular c_new equals c_new mod p *)
    assert (Hcnew : divmodZ p
       (negmodZ p (mtraceZ p (mmulZ p (reduceZ p A) (reduceZ p M_k)))) k
       = c_new mod p).
    { rewrite (mfl_mmulZ_sound p A M_k Hp0).
      rewrite (mfl_mtraceZ_sound p (mmul A M_k) Hp0).
      fold tr.
      rewrite mfl_negmodZ_mod.
      unfold c_new.
      apply mfl_divmodZ_spec.
      - exact Hpr.
      - lia.
      - exact Hk.
      - lia.
      - apply Z.divide_opp_r. exact Hkdiv. }
    rewrite Hcnew.
    apply (IH (k + 1) A I_n M_k c_new (c_new :: acc) p n).
    + exact Hp.
    + exact Hpr.
    + exact Hn.
    + exact HsA.
    + exact HsI.
    + apply square_mat_madd.
      * apply square_mat_mmul; [lia | exact HsA | exact HsM].
      * apply square_mat_mscale; exact HsI.
    + lia.
    + lia.
    + exact Hrest.
Qed.

(* ================================================================== *)
(* Section 9: main theorem                                             *)
(* ================================================================== *)

Theorem char_poly_modZ_sound (p : Z) (M : mat) :
  Znumtheory.prime p ->
  square_mat (length M) M ->
  (Z.of_nat (length M) + 1 < p)%Z ->
  fl_all_divisible (length M) 1%Z M (meye (length M)) (mzero (length M)) 1%Z ->
  char_poly_modZ p M = map (fun c => c mod p) (char_poly_int M).
Proof.
  intros Hprime Hsq Hbound Hfldiv.
  assert (Hp1 : (1 < p)%Z) by (destruct Hprime as [Hgt _]; exact Hgt).
  assert (Hpr : is_true (prime.prime (Z.to_nat p)))
    by (apply Zprime_to_ssrprime; [lia | exact Hprime]).
  unfold char_poly_modZ, char_poly_int. cbv zeta.
  unfold mat_dim.
  change Z.one with 1%Z.
  rewrite map_app.
  f_equal.
  (* the leading coefficient [1 mod p] is closed by f_equal;
     only the coefficient list remains *)
  destruct (length M) as [|n'] eqn:HL.
  - reflexivity.
  - apply (mfl_fl_modZ_loop_sound (S n') 1%Z M (meye (S n')) (mzero (S n'))
             1%Z [] p (S n')).
    + exact Hp1.
    + exact Hpr.
    + lia.
    + exact Hsq.
    + apply mfl_square_mat_meye.
    + apply mfl_square_mat_mzero.
    + lia.
    + lia.
    + exact Hfldiv.
Qed.

Print Assumptions char_poly_modZ_sound.
