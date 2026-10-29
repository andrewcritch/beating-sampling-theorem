import BstLean.Part141Defs
import BstLean.Part141Atom
import BstLean.Part141Atom2
import BstLean.Part141Shift
import BstLean.Part141Centre
import BstLean.Part141Tau
import BstLean.Part141Err
import BstLean.Part141Final
import BstLean.Part141Sample
import BstLean.Part141Cost
import BstLean.Part141Prog

/-!
# Part 141: a fully ARITHMETIC one-pass program succeeds

Role: `delegations/statements/p141-spec.md`. Report: `delegations/answers/p141-spec-opus.md`.
The centre is `b̃ = bA` (a finite ReLU sum with rational atoms and weights, and the rational
constant `cA n` in the place of `c_N`) and the scalar is `τ̃₀ = tauA`
(`τ̃₀² = t|b̃|²·max(0, t|b̃|²·c̃₁ − 1)`, `c̃₁ = c1A n` rational). The route is a perturbation from
Part 140 (centre `b̂ = ψ_s(M₂h̄₁)`, scalar `τ̂₀`) by two Hellinger steps.

* `Part141Defs`: `atomSum`, `zQ`, `quant`, `pR`, `pQ`, `aOf`, `sOf`, `bOf`.
* `Part141Atom` (item 1, first order): `atomSum141`, `psiS_lip_x`, `psiS_lip_s`, `pQ_sum`.
* `Part141Atom2` (item 1, second order): `mR`, `zM`, `atomSum2_141`.
* `Part141Shift`: `gaussShift141`, `cheapShift141` (Hellinger inequality for a change of centre).
* `Part141Centre` (item 2, general form): `centre_pt`, `centre_mean`.
* `Part141Tau` (items 1, 2): the constants `qA`, `hA`, `RA`, `DA`, `LA`, `cA`, `c1A`, `zA`, `pA`;
  `atomErrA`, `bA`, `tauA`, `centreArith141`, `goodA`, `goodA_prob`, `scalarA`, `KA_le`.
* `Part141Err` (item 3): `gA`, `diffFixedA`, `diffVecA_lint`, `errVecA`, `errTailA`.
* `Part141Final` (item 3): `arithSucceeds141`, `arithExplicit141_99`, `optA141`.
* `Part141Sample`: `sampleA141`.
* `Part141Cost`, `Part141Prog` (item 4): `arithProg`, `arithProg_eval`, `arithCost141`,
  `arithProg141`, `arithProgSucceeds141`, `arithProgExplicit141_99`, `arithCost141_focus`,
  `arithCost141_frontier`, `arithCost141_ratio`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part141 in
#print axioms psiS_lip_x
open BstLean.Part141 in
#print axioms psiS_lip_s
open BstLean.Part141 in
#print axioms pQ_sum
open BstLean.Part141 in
#print axioms pQ_sum_real
open BstLean.Part141 in
#print axioms pQ_nonneg
open BstLean.Part141 in
#print axioms pQ_nonneg_real
open BstLean.Part141 in
#print axioms atom_couple
open BstLean.Part141 in
#print axioms atom_round
open BstLean.Part141 in
#print axioms atomSum141
open BstLean.Part141 in
#print axioms atom_couple2
open BstLean.Part141 in
#print axioms atom_ratAtoms
open BstLean.Part141 in
#print axioms atom_round_gen
open BstLean.Part141 in
#print axioms atomSum2_141
open BstLean.Part141 in
#print axioms stdGauss_shift
open BstLean.Part141 in
#print axioms integral_shift
open BstLean.Part141 in
#print axioms aff_densSN
open BstLean.Part141 in
#print axioms gaussShift141
open BstLean.Part141 in
#print axioms cheapShift141
open BstLean.Part141 in
#print axioms cN_sq_le
open BstLean.Part141 in
#print axioms sOf_cN
open BstLean.Part141 in
#print axioms aOf_cN
open BstLean.Part141 in
#print axioms centre_pt
open BstLean.Part141 in
#print axioms layer_sq
open BstLean.Part141 in
#print axioms GamS_mean
open BstLean.Part141 in
#print axioms aOne_mean
open BstLean.Part141 in
#print axioms centre_mean
open BstLean.Part141 in
#print axioms tauN
open BstLean.Part141 in
#print axioms normSq_diff_sq
open BstLean.Part141 in
#print axioms hell_frac
open BstLean.Part141 in
#print axioms K_num
open BstLean.Part141 in
#print axioms atomErrA
open BstLean.Part141 in
#print axioms cA_le
open BstLean.Part141 in
#print axioms cA_ge
open BstLean.Part141 in
#print axioms c1A_err
open BstLean.Part141 in
#print axioms centreArith141
open BstLean.Part141 in
#print axioms goodA_prob_gen
open BstLean.Part141 in
#print axioms goodA_prob
open BstLean.Part141 in
#print axioms scalarA
open BstLean.Part141 in
#print axioms tauA_pos
open BstLean.Part141 in
#print axioms KA_le
open BstLean.Part141 in
#print axioms sqInt_cheapIn
open BstLean.Part141 in
#print axioms diff_pt
open BstLean.Part141 in
#print axioms diffFixedM
open BstLean.Part141 in
#print axioms diffFixedA
open BstLean.Part141 in
#print axioms diffVecA_lint
open BstLean.Part141 in
#print axioms errVecA_lint
open BstLean.Part141 in
#print axioms errVecA
open BstLean.Part141 in
#print axioms errTailA
open BstLean.Part141 in
#print axioms badA_prob_gen
open BstLean.Part141 in
#print axioms badA_prob
open BstLean.Part141 in
#print axioms arithSucceeds141_core
open BstLean.Part141 in
#print axioms arithSucceeds141_formula
open BstLean.Part141 in
#print axioms arithSucceeds141
open BstLean.Part141 in
#print axioms arithSucceeds141_all
open BstLean.Part141 in
#print axioms arithSucceeds141_frontier
open BstLean.Part141 in
#print axioms arithSucceeds141_99
open BstLean.Part141 in
#print axioms arithExplicit141_core
open BstLean.Part141 in
#print axioms arithExplicit141
open BstLean.Part141 in
#print axioms arithExplicit141_sharp
open BstLean.Part141 in
#print axioms arithExplicit141_99
open BstLean.Part141 in
#print axioms optA141
open BstLean.Part141 in
#print axioms optA141_explicit
open BstLean.Part141 in
#print axioms gA_eq
open BstLean.Part141 in
#print axioms errSampleA_lint
open BstLean.Part141 in
#print axioms errSampleTailA
open BstLean.Part141 in
#print axioms sampleA141
open BstLean.Part141 in
#print axioms preProg_eval_a'
open BstLean.Part141 in
#print axioms preProg_eval_s'
open BstLean.Part141 in
#print axioms atomStage_eval
open BstLean.Part141 in
#print axioms atomStage_cost
open BstLean.Part141 in
#print axioms arithProg_eval
open BstLean.Part141 in
#print axioms arithProg_eval_sphPt
open BstLean.Part141 in
#print axioms arithProg_cost_eq
open BstLean.Part141 in
#print axioms arithProg_cost
open BstLean.Part141 in
#print axioms arithCost141
open BstLean.Part141 in
#print axioms gProgA_eq
open BstLean.Part141 in
#print axioms preA_null
open BstLean.Part141 in
#print axioms zeroPtA_null
open BstLean.Part141 in
#print axioms arithProgSucceeds141
open BstLean.Part141 in
#print axioms arithCost141_focus
open BstLean.Part141 in
#print axioms RA_le
open BstLean.Part141 in
#print axioms RA_frontier
open BstLean.Part141 in
#print axioms hA_frontier
open BstLean.Part141 in
#print axioms LA_frontier
open BstLean.Part141 in
#print axioms arithCost141_frontier
open BstLean.Part141 in
#print axioms arithCost141_ratio
open BstLean.Part141 in
#print axioms worldEntries141
open BstLean.Part141 in
#print axioms arithProgExplicit141_core
open BstLean.Part141 in
#print axioms arithProgExplicit141_99
