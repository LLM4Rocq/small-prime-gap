(* Fermat.v — Fermat's little theorem at the nat level.
   For prime p and 0 < k < p: k * k^(p-2) = 1 %[mod p].
   Proved via expf_card from mathcomp.field.finfield. *)

From mathcomp Require Import all_boot all_algebra zmodp.
From mathcomp.field Require Import finfield.
Import GRing.Theory.
Open Scope ring_scope.

Lemma fermat_mod (p' : nat) (Hp : prime p'.+2) (k : nat) :
  (0 < k < p'.+2)%N -> k * k ^ (p'.+2 - 2) = 1 %[mod p'.+2].
Proof.
  set p := p'.+2. move=> /andP [Hk0 Hkp].
  have Hp1 : (1 < p)%N := prime_gt1 Hp.
  have -> : (k * k ^ (p - 2) = k ^ p.-1)%N.
  { by rewrite -expnS /p subn2. }
  have Hpdiv : pdiv p = p by rewrite pdiv_id.
  have HZt : (Zp_trunc (pdiv p)).+2 = p by rewrite Hpdiv /Zp_trunc /p.
  suff H : (k ^ p.-1)%:R = 1 :> 'F_p.
  { have Hval := congr1 val H.
    move: Hval. rewrite /= !Zp_nat /inZp /= Hpdiv /Zp_trunc /p /=.
    rewrite /eqn. done. }
  have Hexp := @expf_card _ (k%:R : 'F_p).
  rewrite card_ord HZt in Hexp.
  have Hunit : (k%:R : 'F_p) \is a GRing.unit.
  { rewrite GRing.unitfE. apply/negP => /eqP Habs.
    have Hv := congr1 val Habs.
    move: Hv. rewrite /= !Zp_nat /inZp /= Hpdiv /Zp_trunc /p /= modn_small //.
    move=> Hk0'. rewrite Hk0' in Hk0. done. }
  have Hstep : (k%:R : 'F_p) ^+ p = k%:R ^+ p.-1 * k%:R
    by rewrite -GRing.exprSr prednK // prime_gt0.
  rewrite Hstep in Hexp.
  have H1 : (k%:R : 'F_p) ^+ p.-1 = 1
    by apply (GRing.mulIr Hunit); rewrite mul1r.
  by rewrite natrX H1.
Qed.

(* Bridge helpers — proved BEFORE ZArith import to avoid %N scope clash *)

Lemma expn_pow (a b : nat) : expn a b = Nat.pow a b.
Proof. by elim: b => [|n IH] //=; rewrite expnS IH. Qed.

Lemma fermat_dvdn (pp kn : nat) :
  prime pp.+2 ->
  (0 < kn < pp.+2)%N ->
  dvdn pp.+2 (muln kn (expn kn pp) - 1).
Proof.
  intros Hprime Hbnd.
  have Hfm := fermat_mod pp Hprime kn Hbnd.
  rewrite subn2 in Hfm.
  have Hge : (1 <= muln kn (expn kn pp))%N.
  { have /andP [Hk _] := Hbnd.
    by rewrite muln_gt0 expn_gt0 Hk. }
  rewrite -(eqn_mod_dvd _ Hge). by apply/eqP.
Qed.

From Stdlib Require Import ZArith Lia.

Lemma fermat_Z (pv : Z) :
  (1 < pv)%Z ->
  prime (Z.to_nat pv) ->
  forall j : Z, (0 < j < pv)%Z ->
  ((j * j ^ (pv - 2)) mod pv = 1 mod pv)%Z.
Proof.
  intros Hp1 Hprime j [Hj0 Hjp].
  remember (Z.to_nat j) as kn eqn:Hkn.
  remember (Z.to_nat pv) as pn eqn:Hpn.
  assert (Hexists: exists pp, pn = S (S pp)) by (exists (pn - 2)%coq_nat; lia).
  destruct Hexists as [pp Hpp].
  assert (Hprime' : prime pp.+2) by (rewrite -Hpp; exact Hprime).
  assert (Hkn_pos : (0 < kn)%coq_nat) by (subst kn; lia).
  assert (Hkn_lt : (kn < pp.+2)%coq_nat) by (subst kn pn; lia).
  assert (HbndN : is_true (ltn 0 kn && ltn kn pp.+2)) by (apply/andP; split; apply/ltP; assumption).
  pose proof (fermat_dvdn pp kn Hprime' HbndN) as Hdvd.
  move/dvdnP: Hdvd => [q Hq].
  rewrite mulnE expn_pow in Hq.
  assert (Hge : (1 <= kn * kn ^ pp)%coq_nat).
  { apply Nat.mul_pos_pos; [exact Hkn_pos |].
    clear -Hkn_pos. induction pp as [|m IH]; simpl; lia. }
  set (prod := (kn * kn ^ pp)%coq_nat) in *.
  assert (Hnat_eq : prod = 1 + q * S (S pp)) by lia.
  assert (HZ : (Z.of_nat pp.+2 | Z.of_nat kn * Z.of_nat kn ^ Z.of_nat pp - 1)%Z)
    by (exists (Z.of_nat q); lia).
  replace pv with (Z.of_nat pp.+2) by lia.
  replace j with (Z.of_nat kn) by lia.
  replace (Z.of_nat pp.+2 - 2)%Z with (Z.of_nat pp) by lia.
  rewrite <- Nat2Z.inj_pow <- Nat2Z.inj_mul.
  change 1%Z with (Z.of_nat 1).
  apply Z.mod_divide_iff; [lia|exact HZ].
Qed.
