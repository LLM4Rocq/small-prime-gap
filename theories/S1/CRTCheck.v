(* ============================================================== *)
(*  CRTCheck.v                                                      *)
(*                                                                  *)
(*  CRT (Chinese Remainder Theorem) helper lemmas used by CRTLift.v *)
(*  to lift modular agreement (over 710 Uint63 primes) to identity  *)
(*  over Z.                                                         *)
(*                                                                  *)
(*  The headline maynard_M105_certified takes the IVT route through *)
(*  CertL1.maynard_L1_concrete; chain entries 1..42 of the shipped  *)
(*  Sturm chain are not consumed by the headline.  The 10-prime PRS *)
(*  cross-check that earlier validated those entries was retired in *)
(*  the cleanup branch.                                             *)
(* ============================================================== *)

From Stdlib Require Import Uint63 ZArith List Bool Lia Znumtheory.
Import ListNotations.
From PrimeGapS1 Require Import IntPoly.

(* --- Maximum absolute coefficient of a list Z polynomial ------- *)

Definition max_abs_coeff (p : pol) : Z :=
  List.fold_left (fun acc c => Z.max acc (Z.abs c)) p 0%Z.

Open Scope Z_scope.

(* --- Arithmetic helpers ---------------------------------------- *)

(* A multiple of P that is smaller than P/2 in absolute value
   must be zero. *)
Lemma small_multiple_zero : forall c P : Z,
  (P | c)%Z -> (0 < P)%Z -> (2 * Z.abs c < P)%Z -> c = 0%Z.
Proof.
  intros c P [k Hk] HP Hlt. subst c.
  rewrite Z.abs_mul in Hlt.
  assert (Z.abs k = 0)%Z by nia. lia.
Qed.

(* If a | n and b | n and gcd(a,b) = 1, then a*b | n. *)
Lemma coprime_div_mul : forall a b n : Z,
  (a | n)%Z -> (b | n)%Z -> rel_prime a b -> (a * b | n)%Z.
Proof.
  intros a b n [j Hj] Hb Hrel. subst n.
  assert (Hbj : (b | j)%Z).
  { apply Gauss with (b := a).
    rewrite Z.mul_comm. exact Hb.
    exact (rel_prime_sym _ _ Hrel). }
  destruct Hbj as [m Hm]. subst j.
  exists m. ring.
Qed.

(* --- Polynomial helpers ---------------------------------------- *)

(* If every element of a list is 0, drop_leading_zeros returns []. *)
Lemma drop_leading_zeros_all_zero : forall l : list Z,
  (forall c, In c l -> c = 0%Z) -> drop_leading_zeros l = [].
Proof.
  induction l; intros H; simpl; auto.
  rewrite (H a (or_introl eq_refl)). simpl.
  apply IHl. intros c Hc. apply H. right. exact Hc.
Qed.

(* If every coefficient of a polynomial is 0, its normal form is []. *)
Lemma all_zero_pnorm_nil : forall p : pol,
  (forall c, In c p -> c = 0%Z) -> pnorm p = [].
Proof.
  intros p H. unfold pnorm.
  rewrite drop_leading_zeros_all_zero.
  - reflexivity.
  - intros c Hc. apply H. apply in_rev. exact Hc.
Qed.

(* --- max_abs_coeff properties ---------------------------------- *)

(* The fold computing max_abs_coeff is monotone in the accumulator. *)
Lemma fold_left_Zmax_abs_mono : forall (l : list Z) (a1 a2 : Z),
  (a1 <= a2)%Z ->
  (fold_left (fun a c => Z.max a (Z.abs c)) l a1 <=
   fold_left (fun a c => Z.max a (Z.abs c)) l a2)%Z.
Proof.
  induction l; intros a1 a2 Hle; simpl.
  - exact Hle.
  - apply IHl. lia.
Qed.

Lemma fold_left_Zmax_abs_ge : forall (l : list Z) (acc : Z),
  (acc <= fold_left (fun a c => Z.max a (Z.abs c)) l acc)%Z.
Proof.
  induction l; intros acc; simpl.
  - lia.
  - apply Z.le_trans with (Z.max acc (Z.abs a)).
    + lia.
    + apply IHl.
Qed.

(* max_abs_coeff bounds the absolute value of every element. *)
Lemma max_abs_coeff_bound : forall (p : pol) (c : Z),
  In c p -> (Z.abs c <= max_abs_coeff p)%Z.
Proof.
  unfold max_abs_coeff. induction p as [|a p IHp]; intros c Hc.
  - destruct Hc.
  - simpl. destruct Hc as [-> | Hc].
    + apply Z.le_trans with (Z.max 0 (Z.abs c)).
      * lia.
      * apply fold_left_Zmax_abs_ge.
    + apply Z.le_trans with
        (fold_left (fun acc c0 => Z.max acc (Z.abs c0)) p 0%Z).
      * apply IHp. exact Hc.
      * apply fold_left_Zmax_abs_mono. lia.
Qed.

(* --- CRT product helpers --------------------------------------- *)

(* fold_left Z.mul can be factored: fold(l, a) = a * fold(l, 1). *)
Lemma fold_left_mul_assoc : forall (l : list Z) (a : Z),
  fold_left Z.mul l a = (a * fold_left Z.mul l 1)%Z.
Proof.
  induction l as [|x l IHl]; intros a.
  - simpl. lia.
  - change (fold_left Z.mul (x :: l) a) with (fold_left Z.mul l (Z.mul a x)).
    change (fold_left Z.mul (x :: l) 1%Z) with (fold_left Z.mul l (Z.mul 1 x)).
    rewrite IHl. rewrite (IHl (Z.mul 1 x)). nia.
Qed.

(* A prime p cannot divide a different prime q. *)
Lemma prime_not_divide_other_prime : forall p q : Z,
  prime p -> prime q -> p <> q -> ~ (p | q)%Z.
Proof.
  intros p q Hp Hq Hneq Hdiv.
  assert (Hp1 : (1 < p)%Z) by (destruct Hp; lia).
  assert (Hq1 : (1 < q)%Z) by (destruct Hq; lia).
  destruct Hdiv as [k Hk].
  assert (Hk_pos : (0 < k)%Z) by nia.
  assert (Hlt : (p < q)%Z \/ p = q) by nia.
  destruct Hlt as [Hlt | Hlt]; [| lia].
  assert (Hrange : (1 <= p < q)%Z) by lia.
  destruct Hq as [_ Hq2]. specialize (Hq2 _ Hrange).
  destruct Hq2 as [_ _ Hgcd].
  assert (Hdivpq : (p | q)%Z) by (exists k; lia).
  assert (Hdivpp : (p | p)%Z) by (exists 1%Z; lia).
  specialize (Hgcd _ Hdivpp Hdivpq).
  destruct Hgcd as [m Hm].
  assert (m = 0 \/ m >= 1 \/ m <= -1)%Z by lia.
  destruct H as [H|[H|H]]; nia.
Qed.

(* A prime p that does not appear in a list of primes qs cannot
   divide the product of qs. *)
Lemma prime_not_divide_prime_product : forall (p : Z) (qs : list Z),
  prime p ->
  (forall q, In q qs -> prime q) ->
  ~ In p qs ->
  ~ (p | fold_left Z.mul qs 1)%Z.
Proof.
  induction qs as [|q qs IHqs]; intros Hp Hprimes Hnotin Hdiv.
  - simpl in Hdiv. destruct Hdiv as [k Hk].
    assert (Hp1 : (1 < p)%Z) by (destruct Hp; lia).
    assert (k = 0 \/ k >= 1 \/ k <= -1)%Z by lia.
    destruct H as [H|[H|H]]; nia.
  - simpl in Hdiv. rewrite fold_left_mul_assoc in Hdiv.
    assert (Hpq : p <> q) by (intro; subst; apply Hnotin; left; reflexivity).
    assert (Hprime_q : prime q) by (apply Hprimes; left; reflexivity).
    apply prime_mult in Hdiv; [| exact Hp].
    destruct Hdiv as [Hdiv | Hdiv].
    + replace (match q with 0 => 0 | Z.pos y' => Z.pos y'
               | Z.neg y' => Z.neg y' end) with q in Hdiv
        by (destruct q; reflexivity).
      exact (prime_not_divide_other_prime p q Hp Hprime_q Hpq Hdiv).
    + apply IHqs; auto.
      * intros r Hr. apply Hprimes. right. exact Hr.
      * intro. apply Hnotin. right. exact H.
Qed.

(* If all primes in a NoDup list divide c, then their product divides c. *)
Lemma all_primes_divide_product : forall (ps : list Z) (c : Z),
  NoDup ps ->
  (forall p, In p ps -> prime p) ->
  (forall p, In p ps -> (p | c)%Z) ->
  (fold_left Z.mul ps 1 | c)%Z.
Proof.
  induction ps as [|p ps IHps]; intros c Hnd Hprimes Hdivs.
  - simpl. exists c. lia.
  - simpl. rewrite fold_left_mul_assoc.
    replace (match p with 0 => 0 | Z.pos y' => Z.pos y'
             | Z.neg y' => Z.neg y' end) with p
      by (destruct p; reflexivity).
    apply coprime_div_mul.
    + apply Hdivs. left. reflexivity.
    + apply IHps.
      * inversion Hnd; assumption.
      * intros q Hq. apply Hprimes. right. exact Hq.
      * intros q Hq. apply Hdivs. right. exact Hq.
    + apply prime_rel_prime.
      * apply Hprimes. left. reflexivity.
      * apply prime_not_divide_prime_product.
        -- apply Hprimes. left. reflexivity.
        -- intros q Hq. apply Hprimes. right. exact Hq.
        -- inversion Hnd; assumption.
Qed.
