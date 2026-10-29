import BstLean.Part140Norm
import BstLean.Part140Det
import BstLean.Part140Dist
import BstLean.Part140Frame
import BstLean.Part140Tau
import BstLean.Part140Cheap
import BstLean.Part140Err
import BstLean.Part140Final
import BstLean.Part140Sample
import BstLean.Part140Sharp
import BstLean.Part140TwoStage
import BstLean.Part140Joint
import BstLean.Part140Cost
import BstLean.Part140Prog

/-!
# Part 140: a stand-in estimate with a COMPUTED centre succeeds

Role: `delegations/statements/p140-spec.md`. Report: `delegations/answers/p140-spec-opus.md`.
The centre is `b̂ = ψ_s(M₂ h̄₁)` (`bhat`, Part 137) and the scalar is
`τ̂₀² = t|b̂|²·max(0, t|b̂|²/(γκ₁²) − 1)` (`tauHat`): functions of first-pass quantities of
`(M₁, M₂)`; the exact mean hidden vector `h̄` is used in proofs only.

* `Part140Norm`: `‖t|b̂|² − γκ₁‖₂ ≤ γ·cB` (`bhatNorm_L2`).
* `Part140Det`: the deterministic reduction for a general centre (`det_frame_b`, `frameB_num`).
* `Part140Dist` (item 1): `centreDist_gen`, `centreDist140`, `goodDist_prob`, `Bh_window`.
* `Part140Frame` (item 2): `goodHat`, `goodHat_prob`, `lamHat140`, `standInHat140`.
* `Part140Joint` (item 2, joint and tail; item 1, the event): `standInHat140_joint`,
  `standInHat140_tail`, `centreEvent140`.
* `Part140Tau`, `Part140Cheap`: the scalar `tauHat` and the Hellinger term (`cheapStandInHat`,
  `HbarH_mean`, `EHH_le`).
* `Part140Err`, `Part140Final` (item 3): `errVecHat`, `hatSucceeds140`, `hatExplicit140`.
* `Part140Sample`, `Part140Sharp`, `Part140TwoStage`: `sampleHat140`, `hatExplicit140_99`,
  `optAHat140`.
* `Part140Cost`, `Part140Prog` (item 4): `hatProg`, `preProg`, `cost140`, `progSucceeds140`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part140 in
#print axioms q1_eq
open BstLean.Part140 in
#print axioms kap1_ge
open BstLean.Part140 in
#print axioms kap1_le
open BstLean.Part140 in
#print axioms bhatNorm_cond
open BstLean.Part140 in
#print axioms bhatNorm_L2
open BstLean.Part140 in
#print axioms cB_sq_le
open BstLean.Part140 in
#print axioms det_frame_b
open BstLean.Part140 in
#print axioms sphere_cov
open BstLean.Part140 in
#print axioms sphere_frame_b
open BstLean.Part140 in
#print axioms cov_of_good
open BstLean.Part140 in
#print axioms frameB_of_good
open BstLean.Part140 in
#print axioms frameB_num
open BstLean.Part140 in
#print axioms Xh_L2
open BstLean.Part140 in
#print axioms Hh_L2
open BstLean.Part140 in
#print axioms dist2_L2
open BstLean.Part140 in
#print axioms centreDist_gen
open BstLean.Part140 in
#print axioms centreDist140
open BstLean.Part140 in
#print axioms distBad_gen
open BstLean.Part140 in
#print axioms goodDist_prob
open BstLean.Part140 in
#print axioms errT_mean
open BstLean.Part140 in
#print axioms errT_bad
open BstLean.Part140 in
#print axioms Bh_window_gen
open BstLean.Part140 in
#print axioms Bh_window
open BstLean.Part140 in
#print axioms goodT_prob
open BstLean.Part140 in
#print axioms goodHat_meas
open BstLean.Part140 in
#print axioms goodHat_prob
open BstLean.Part140 in
#print axioms kap1_window
open BstLean.Part140 in
#print axioms frameHat140
open BstLean.Part140 in
#print axioms lamHat140
open BstLean.Part140 in
#print axioms standInHat140
open BstLean.Part140 in
#print axioms standInVarHat140
open BstLean.Part140 in
#print axioms standInHat140_joint
open BstLean.Part140 in
#print axioms standInHat140_tail
open BstLean.Part140 in
#print axioms centreEvent140
open BstLean.Part140 in
#print axioms tauH_sq
open BstLean.Part140 in
#print axioms lamH_L2
open BstLean.Part140 in
#print axioms tauFluctH_gen
open BstLean.Part140 in
#print axioms tauBadH_gen
open BstLean.Part140 in
#print axioms B0_window
open BstLean.Part140 in
#print axioms w0H_window
open BstLean.Part140 in
#print axioms tauHat_sq
open BstLean.Part140 in
#print axioms tauHat_pos
open BstLean.Part140 in
#print axioms good_ptH
open BstLean.Part140 in
#print axioms cheapMeanHat
open BstLean.Part140 in
#print axioms cheapStandInHat
open BstLean.Part140 in
#print axioms HbarH_mean
open BstLean.Part140 in
#print axioms EHH_le
open BstLean.Part140 in
#print axioms goodWH_prob
open BstLean.Part140 in
#print axioms errFixedHat
open BstLean.Part140 in
#print axioms errVecHat_lint
open BstLean.Part140 in
#print axioms errVecHat
open BstLean.Part140 in
#print axioms errTailHat
open BstLean.Part140 in
#print axioms hatSucceeds140_formula
open BstLean.Part140 in
#print axioms hatSucceeds140
open BstLean.Part140 in
#print axioms hatSucceeds140_all
open BstLean.Part140 in
#print axioms hatSucceeds140_frontier
open BstLean.Part140 in
#print axioms hatSucceeds140_99
open BstLean.Part140 in
#print axioms hatExplicit140_core
open BstLean.Part140 in
#print axioms hatExplicit140
open BstLean.Part140 in
#print axioms errSampleHat_lint
open BstLean.Part140 in
#print axioms sampleHat140
open BstLean.Part140 in
#print axioms goodHat_prob_sharp
open BstLean.Part140 in
#print axioms badHat_prob_sharp
open BstLean.Part140 in
#print axioms hatExplicit140_sharp
open BstLean.Part140 in
#print axioms hatExplicit140_99
open BstLean.Part140 in
#print axioms optAHat140
open BstLean.Part140 in
#print axioms optAHat140_explicit
open BstLean.Part140 in
#print axioms optAHat140_explicit_frontier
open BstLean.Part140 in
#print axioms tauOf_bhat
open BstLean.Part140 in
#print axioms hatProg_eval
open BstLean.Part140 in
#print axioms hatProg_eval_sphPt
open BstLean.Part140 in
#print axioms hatProg_cost
open BstLean.Part140 in
#print axioms preProg_eval_a
open BstLean.Part140 in
#print axioms preProg_eval_s
open BstLean.Part140 in
#print axioms preProg_cost
open BstLean.Part140 in
#print axioms costHat_ge
open BstLean.Part140 in
#print axioms cost140
open BstLean.Part140 in
#print axioms gProg_eq
open BstLean.Part140 in
#print axioms preHat_null
open BstLean.Part140 in
#print axioms progSucceeds140
open BstLean.Part140 in
#print axioms cost140_focus
open BstLean.Part140 in
#print axioms cost140_vs_sample
