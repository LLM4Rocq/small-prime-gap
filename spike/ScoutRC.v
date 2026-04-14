(* Scout spike: test feasibility of mathcomp-real-closed paths. *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.real_closed Require Import polyrcf qe_rcf qe_rcf_th realalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* === (1) char_poly of a small rational matrix — can it reduce? === *)

(* A 3x3 symmetric rational matrix. *)
Definition M3 : 'M[rat]_3 :=
  \matrix_(i, j) (if (i == j :> nat) then 2%:Q
                  else if (i + j == 1)%N then 1%:Q
                       else if (i + j == 2)%N then 0%:Q
                            else 0%:Q).

Definition cp3 : {poly rat} := char_poly M3.

(* Try to evaluate char_poly at x=0 — we expect -det(M3). *)
(* Commented out — enable locally to try vm_compute. *)
(* Time Eval vm_compute in (cp3.[0]). *)

(* === (2) QE via qe_rcf.rcf_sat on a tiny formula === *)

(* We want to know whether rcf_sat actually reduces.
   Formula:  exists x, x*x == 5  (over realalg).
   This is True since sqrt 5 exists in realalg. *)

(* Check that the QE decision procedure has the expected type. *)
Check @rcf_sat.
Check @rcf_satP.

(* === (3) realalg as rcfType === *)
Check (realalg : rcfType).

(* === (4) Sturm-bridge: does the lemma composition give us root counts? === *)

Section SturmBridge.
Variable R : rcfType.
Variable p : {poly R}.
Variable a b : R.

(* Compose taq_cindex + changes_itv_mods_cindex:
   taq (roots p a b) 1 = cindex a b (p^`() * 1) p = cindex a b p^`() p.
   And changes_itv_mods a b p p^`() = cindex a b p^`() p (under endpoint conditions).
   So size (roots p a b) relates to changes_itv_mods. *)

Check @taq_cindex R a b p 1.
Check @changes_itv_mods_cindex R a b.
Check @poly_ivtoo R p a b.
Check @in_roots R p a b.
End SturmBridge.
