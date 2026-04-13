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
