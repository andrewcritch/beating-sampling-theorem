import BstLean.Part138Hell
import BstLean.Part138Gauss
import BstLean.Part138Mix
import BstLean.Part138Cheap
import BstLean.Part138Joint
import BstLean.Part138Num
import BstLean.Part138Two

/-!
# Part 138: the stand-in with a constant scalar (the cheap stand-in)

Role: `delegations/statements/p138-spec.md`. Report: `delegations/answers/p138-spec-opus.md`.
The centre is the exact mean hidden vector `h̄` of Parts 134, 136 (NOT the arithmetic centre of
the programs).

* `Part138Hell`: item 1, the Hellinger inequality for two means (`hellMean138`).
* `Part138Gauss`: item 2, two isotropic Gaussian vectors with one centre (`gaussScale138`,
  `hellG`, `hellG_le`).
* `Part138Mix`: the cheap stand-in `cheapIn`, and the general comparison `cheap_mix`.
* `Part138Cheap`: item 3 for fixed `(M₁, M₂)` (`cheapMean138`, `cheapStandIn138`).
* `Part138Joint`: items 3 and 4 over the whole `W` (`cheapStandIn138_joint`,
  `cheapStandIn138_tail`, `good138`, `cheapStandIn138_event`).
* `Part138Num`: the explicit second term `3760·B²·n/m` (`EH_le`, `cheapStandIn138_num`).
* `Part138Two`: item 5, the scalar from one uniform input (`cheapTwo138`, `cheapTwo138_tail`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part138

#print axioms cs_sq
#print axioms hell_core
#print axioms hell_fn
#print axioms hellMean138
#print axioms hellSq_nonneg
#print axioms hellMean138_bdd
#print axioms gauss1_density
#print axioms integral_root1
#print axioms stdGauss_scale
#print axioms integral_scale
#print axioms aff_densN
#print axioms gauss_scale_hell
#print axioms hellG_le_two
#print axioms hellG_nonneg
#print axioms one_sub_pow_le
#print axioms hellG_le
#print axioms gaussScale138
#print axioms gaussScale138_sph
#print axioms pt_hell
#print axioms mix_cs
#print axioms cheap_mix
#print axioms hell_ratio
#print axioms tau0_sq
#print axioms tau0_pos
#print axioms wbar_window
#print axioms good_pt
#print axioms cheapMean138
#print axioms cheapStandIn138
#print axioms cheapStandIn138_bdd
#print axioms Hbar_mean
#print axioms cheapStandIn138_joint
#print axioms cheapStandIn138_total
#print axioms cheapStandIn138_tail
#print axioms good138_prob
#print axioms cheapStandIn138_event
#print axioms cRho_ge
#print axioms Omega2_le
#print axioms Beta_le
#print axioms EH_le
#print axioms n_div_mW_sq
#print axioms cheapStandIn138_num
#print axioms cheapStandIn138_total_num
#print axioms cheapStandIn138_tail_num
#print axioms cheapStandIn138_event_num
#print axioms cheap_fixed
#print axioms good_pt1
#print axioms Gm_mean
#print axioms K1fun_int
#print axioms cheapTwo138
#print axioms cheapTwo138_tail
#print axioms EH1_le
#print axioms cheapTwo138_tail_num
