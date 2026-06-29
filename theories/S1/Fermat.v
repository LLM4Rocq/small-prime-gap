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

(* MathComp-level: fermat_mod → dvdn → nat equality *)
Lemma fermat_nat_eq (pp kn : nat) :
  prime pp.+2 ->
  (0 < kn < pp.+2)%N ->
  exists q, Nat.mul kn (Nat.pow kn pp) = Nat.add 1 (Nat.mul q (S (S pp))).
Proof.
  move=> Hprime Hbnd.
  have Hfm := fermat_mod pp Hprime kn Hbnd.
  rewrite subn2 in Hfm.
  have Hge : (1 <= muln kn (expn kn pp))%N.
  { have /andP [Hk _] := Hbnd.
    by rewrite muln_gt0 expn_gt0 Hk. }
  have Hdvd : dvdn pp.+2 (muln kn (expn kn pp) - 1).
  { by rewrite -(eqn_mod_dvd _ Hge); apply/eqP. }
  move/dvdnP: Hdvd => [q Hq].
  exists q.
  (* subnK Hge : 1 + (muln kn (expn kn pp) - 1) = muln kn (expn kn pp);
     rewrite Hq inside flips the LHS to 1 + muln q pp.+2.
     Then addnC/addnE/mulnE/expn_pow shifts to Stdlib ops. *)
  have HK := subnK Hge.
  rewrite Hq addnC addnE !mulnE expn_pow in HK.
  by rewrite -HK.
Qed.

From Stdlib Require Import ZArith Lia.

Lemma fermat_Z (pv : Z) :
  (1 < pv)%Z ->
  prime (Z.to_nat pv) ->
  forall j : Z, (0 < j < pv)%Z ->
  ((j * j ^ (pv - 2)) mod pv = 1 mod pv)%Z.
Proof.
  move=> Hp1 Hprime j [Hj0 Hjp].
  set kn := Z.to_nat j.
  set pn := Z.to_nat pv.
  have [pp Hpp] : exists pp, pn = S (S pp) by exists (pn - 2)%coq_nat; lia.
  have Hprime' : prime pp.+2 by rewrite -Hpp; exact Hprime.
  have Hkn_pos : (0 < kn)%coq_nat by rewrite /kn; lia.
  have Hkn_lt : (kn < S (S pp))%coq_nat by rewrite /kn -Hpp /pn; lia.
  have HbndN : is_true (ltn 0 kn && ltn kn pp.+2)
    by apply/andP; split; apply/ltP.
  have [q Hq] := fermat_nat_eq pp kn Hprime' HbndN.
  (* Hq : Nat.mul kn (Nat.pow kn pp) = Nat.add 1 (Nat.mul q (S (S pp))) *)
  replace pv with (Z.of_nat (S (S pp))) by lia.
  replace j with (Z.of_nat kn) by lia.
  replace (Z.of_nat (S (S pp)) - 2)%Z with (Z.of_nat pp) by lia.
  rewrite -Nat2Z.inj_pow -Nat2Z.inj_mul.
  change 1%Z with (Z.of_nat 1).
  by rewrite Hq Nat2Z.inj_add Nat2Z.inj_mul Z_mod_plus_full.
Qed.
