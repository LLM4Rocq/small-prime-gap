(* PrimeCheck.v — Z-level trial division primality checker.
   Proves check_prime_Z_sound for Stdlib's Znumtheory.prime, then
   bridges to MathComp's ssrnat.prime via check_prime_Z_mc. *)

From Stdlib Require Import ZArith List Lia Bool Znumtheory.

Fixpoint check_no_divisor (p d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => negb (Z.eqb (Z.modulo p d) 0) && check_no_divisor p (d + 1) f
  end.

Definition check_prime_Z (p : Z) : bool :=
  (1 <? p)%Z && check_no_divisor p 2 (Z.to_nat (Z.sqrt p - 1)).

Lemma check_no_divisor_sound p d fuel :
  check_no_divisor p d fuel = true ->
  forall k, (d <= k < d + Z.of_nat fuel)%Z -> (Z.modulo p k <> 0)%Z.
Proof.
  revert d. induction fuel as [|f IH]; intros d Hcheck k Hk; [lia|].
  simpl in Hcheck. apply Bool.andb_true_iff in Hcheck. destruct Hcheck as [Hcur Hrest].
  apply negb_true_iff in Hcur. apply Z.eqb_neq in Hcur.
  destruct (Z.eq_dec k d) as [->|]; [exact Hcur | apply (IH _ Hrest k); lia].
Qed.

Lemma check_prime_Z_sound p : check_prime_Z p = true -> Znumtheory.prime p.
Proof.
  unfold check_prime_Z. intros H.
  apply Bool.andb_true_iff in H. destruct H as [Hgt1 Hnd]. apply Z.ltb_lt in Hgt1.
  constructor; [lia|].
  intros n Hn. destruct Hn as [Hn1 Hn2].
  apply Zgcd_1_rel_prime.
  set (g := Z.gcd n p).
  destruct (Z.eq_dec g 1) as [|Hne]; [assumption|exfalso].
  pose proof (Z.gcd_nonneg n p) as Hnn. fold g in Hnn.
  pose proof (Z.gcd_divide_l n p) as Hgn. fold g in Hgn.
  pose proof (Z.gcd_divide_r n p) as Hgp. fold g in Hgp.
  assert (Hg2 : (2 <= g)%Z).
  { assert (g <> 0)%Z by (intro; subst g; destruct Hgn as [q Hq]; lia). lia. }
  destruct Hgp as [q Hq].
  assert (Hq_pos : (0 < q)%Z) by nia.
  pose proof (Z.sqrt_spec p ltac:(lia)) as [Hlo Hhi].
  assert (Hor : (g <= Z.sqrt p \/ q <= Z.sqrt p)%Z).
  { destruct (Z.le_gt_cases g (Z.sqrt p)); [left; assumption|right].
    destruct (Z.le_gt_cases q (Z.sqrt p)); [assumption|exfalso].
    assert (g * q >= (Z.sqrt p + 1) * (Z.sqrt p + 1))%Z by nia. lia. }
  destruct Hor as [Hle | Hle].
  - assert (Hmod : Z.modulo p g <> 0%Z).
    { apply (check_no_divisor_sound p 2 _ Hnd).
      pose proof (Z.sqrt_nonneg p). rewrite Z2Nat.id; lia. }
    apply Hmod. rewrite Hq. apply Z.mod_mul. lia.
  - assert (Hq2 : (2 <= q)%Z).
    { pose proof (Z.gcd_divide_l n p) as Hgn2. fold g in Hgn2.
      destruct Hgn2 as [r Hr].
      assert (1 <= r)%Z by nia. assert (g <= n)%Z by nia. nia. }
    assert (Hmod : Z.modulo p q <> 0%Z).
    { apply (check_no_divisor_sound p 2 _ Hnd).
      pose proof (Z.sqrt_nonneg p). rewrite Z2Nat.id; lia. }
    apply Hmod. rewrite Hq. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(* Bridge to MathComp's ssrnat.prime *)
From mathcomp Require Import all_boot.

Lemma Zprime_to_ssrprime (p : Z) :
  (1 < p)%Z -> Znumtheory.prime p -> prime (Z.to_nat p).
Proof.
  move=> Hp1 Hzp.
  have Hp2 : (1 < Z.to_nat p)%coq_nat by lia.
  apply/primeP; split; [by apply/ltP|].
  move=> d Hd; apply/orP.
  have /dvdnP [q Hq] := Hd.
  rewrite mulnE in Hq.
  have Hdz : (Z.of_nat d | p)%Z.
  { by exists (Z.of_nat q); rewrite -Nat2Z.inj_mul -Hq Z2Nat.id; lia. }
  have Hd_le : (d <= Z.to_nat p)%coq_nat.
  { by apply/leP; apply: dvdn_leq Hd; apply/ltP; lia. }
  case: (Nat.eq_dec d 1) => [->|Hne1]; [by left|].
  case: (Nat.eq_dec d (Z.to_nat p)) => [->|Hne2]; [by right|].
  exfalso.
  have Hd_ge2 : (2 <= Z.of_nat d)%Z.
  { have Hd0 : d <> O by move=> Hd0; rewrite Hd0 /= in Hq; lia.
    lia. }
  have Hd_bound : (1 <= Z.of_nat d < p)%Z by lia.
  case: Hzp => _ Hrel.
  have Hrp := Hrel (Z.of_nat d) Hd_bound.
  have Hgcd1 : Z.gcd (Z.of_nat d) p = 1%Z by apply: Zis_gcd_gcd; [lia|].
  have Hgcd_ge : (Z.of_nat d <= Z.gcd (Z.of_nat d) p)%Z.
  { apply: Z.divide_pos_le; [lia|].
    by apply: Z.gcd_greatest; [exists 1; lia|]. }
  lia.
Qed.

Lemma check_prime_Z_mc p : check_prime_Z p = true -> prime (Z.to_nat p).
Proof.
  intro H. apply Zprime_to_ssrprime.
  - unfold check_prime_Z in H. apply Bool.andb_true_iff in H.
    destruct H as [H _]. apply Z.ltb_lt in H. lia.
  - exact (check_prime_Z_sound _ H).
Qed.
