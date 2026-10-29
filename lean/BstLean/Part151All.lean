import BstLean.Part151Cond
import BstLean.Part151Inputs
import BstLean.Part151LevelK
import BstLean.Part151SA
import BstLean.Part151TR2
import BstLean.Part151ST2
import BstLean.Part151Poinc2
import BstLean.Part151U5
import BstLean.Part151S4
import BstLean.Part151V
import BstLean.Part151JF4c
import BstLean.Part151G2
import BstLean.Part151Glue

/-!
# Part 151: the frame of Theorem 5 in Lean — the structure of the error, the final Gaussian step,
the `F`-stage lemmas, and a Lean level with the Gaussian last step

Role: `delegations/statements/p151-spec.md`. Report: `delegations/answers/p151-spec-opus.md`.
Paper source: `proofs/option-n/theorem5-00-main.tex` and the files it inputs.
Do not use `sorry`, `native_decide` or `axiom`.

Files and headlines (namespace `BstLean.Part151`):

* `Part151Gauss` (item 2): `PhiBar`, `gauss_abs_tail`, `gaussStep`, `finalStep`,
  `finalStep_success`: the final Gaussian step with the union bound, abstract form.
* `Part151Tail`: `tail_le_exp`, `tail_le_mills1`, `tail_le_mills3` (the bound (G4)).
* `Part151Struct` (item 1): `Fix`, `Row`, `Joint`, `fixP`, `rowP`, `jointP`, `joint_map`,
  `dHat`, `vHat`, `linJ`, `struct151` (Lemma ST (a)), `row_gauss`, `linJ_gauss`.
* `Part151Cond` (item 3): `H1`, `H2`, `H3`, `cond151_gen`, `cond151`, `condProg151`,
  `cond151_exp`, `cond151_mills`, `H2_of_joint`.
* `Part151Inputs` (item 3): `H3_lean`, `H1_lean`, `finalStepR`, `condLean151`,
  `condLeanSamp151`, `condLeanProg151` (H2 is the only hypothesis that is not a Lean theorem).
* `Part151R` (item 4a): Lemma R (ii), (iii).
* `Part151FStage`, `Part151TR`, `Part151TR2` (item 4c): Lemma TR, mean form and with its charges.
* `Part151SA` (item 4b): Lemma SA without Jacobians.
* `Part151ST`: Lemma ST (b), (c), equation (Tm).
* `Part151U` (item 4d): Lemma U, mean form.
* `Part151Poinc`: the Gaussian Poincaré inequality for a Lipschitz function.
* `Part151Moment`, `Part151Kap`, `Part151Weak`, `Part151Level`, `Part151LevelNum`,
  `Part151LevelK` (item 5): `markov_no_gain`, `two_PhiBar_le_kap`, `two_PhiBar_le_third`,
  `gaussStepMoment`, `finalStepMoment`, `lint_vHat`, `weakI`, `gaussLevel151_formula`,
  `gaussLevel151` (`3/4`), `gaussLevel151_third` (`0.786`).
-/

open BstLean.Part151

-- item 2
#print axioms gauss_abs_tail
#print axioms gaussStep
#print axioms finalStep
#print axioms finalStep_success
#print axioms tail_le_exp
#print axioms tail_le_mills1
#print axioms tail_le_mills3
#print axioms two_tail_three
#print axioms two_tail_four
#print axioms two_PhiBar_le_exp
#print axioms two_PhiBar_le_mills
-- item 1
#print axioms joint_map
#print axioms struct151
#print axioms row_gauss
#print axioms linJ_gauss
#print axioms measurable_dHat
#print axioms measurable_linJ
-- item 3
#print axioms cond151_gen
#print axioms cond151
#print axioms condProg151
#print axioms cond151_exp
#print axioms cond151_mills
#print axioms H2_of_joint
#print axioms spreadLean151
#print axioms H3_lean
#print axioms wBad151
#print axioms wStageLean151
#print axioms H1_lean
#print axioms finalStepR
#print axioms condLean151
#print axioms condLeanSamp151
#print axioms condLeanProg151
-- item 4 (a)
#print axioms lemmaR_ii
#print axioms lemmaR_iii_le
#print axioms lemmaR_iii_mean
#print axioms lemmaR_iii_sq
#print axioms lemmaR_iii_four
#print axioms QR_mean
#print axioms QR_sq
#print axioms QR_four
#print axioms lemmaR_row_mean
#print axioms lemmaR_row_sq
#print axioms lemmaR_row_four
-- item 4 (c)
#print axioms gauss_sq_lintegral
#print axioms row_sq_lintegral
#print axioms hid2_lip
#print axioms pair_struct
#print axioms lemmaTR_mean
#print axioms sum_four_pi
#print axioms tail_pi
#print axioms tail_pi_U
#print axioms gaussMat_rows
#print axioms tail_rows
#print axioms lemmaTR_T2
#print axioms lemmaTR_T1
#print axioms lemmaTR
-- item 4 (b)
#print axioms mean_sq_pi
#print axioms lemmaSA_fixed
#print axioms lemmaSA_fixed_int
#print axioms lemmaSA_mean
#print axioms gamK_eq_gaussMat
#print axioms lemmaSA_lip
#print axioms lemmaSA_conc
#print axioms Ts_mean_le
#print axioms lemmaSA_conc'
-- Lemma ST (b), (c), equation (Tm), the feature energy
#print axioms lemmaST_c
#print axioms lemmaVA_b
#print axioms exists_dir
#print axioms lemmaST_b
#print axioms Dc_eq
#print axioms lemmaTm
#print axioms lemmaFE
#print axioms lemmaFE_gauss
#print axioms lemmaSA_event
-- item 4 (d)
#print axioms dU_coord
#print axioms lemmaU_fixed
#print axioms lemmaU_mean
#print axioms lemmaU_fixedF
#print axioms condConc
#print axioms dU_diff_sq
#print axioms lemmaU_ii
#print axioms TU_lip
#print axioms cross_glue_lip
#print axioms TU_glue_lip
#print axioms lemmaU_EU
#print axioms dU_condMean
#print axioms lemmaU_Ecross
#print axioms TU_condMean_le
#print axioms lemmaU_events
#print axioms poincU
#print axioms grad_bound
#print axioms ae_good
#print axioms lemmaU_i
#print axioms lemmaU_i_events
#print axioms lemmaU_JU
-- Lemma J, Lemma SA (i), Lemma JF
#print axioms jac_at
#print axioms lemmaJ
#print axioms lemmaJ_gauss
#print axioms lemmaJ_shift
#print axioms gradSq_hid2
#print axioms gradSq_hid2_ae
#print axioms lemmaSA_i
#print axioms half_lint
#print axioms lemmaJF_inner
#print axioms lemmaJF_mean
#print axioms sumQ_sq
#print axioms sumQ_four
#print axioms lemmaJF_T2
#print axioms lemmaJF_T1
#print axioms lemmaJF
#print axioms four_centred
#print axioms lemmaJF4_inner
#print axioms Wd_mean
#print axioms lemmaJF4_W
#print axioms lemmaJF4
#print axioms lemmaJF4_charge
-- Lemma S and the inverse moments
#print axioms lemmaS
#print axioms lemmaS_vol
#print axioms lemmaS_core
#print axioms ball_prob_le
#print axioms inv_moment
#print axioms inv_moment_paper
#print axioms inv_moment_lint
#print axioms inv_moment4
#print axioms inv_moment4_paper
#print axioms inv_moment4_lint
#print axioms laplace_one
#print axioms laplace_vec
-- Lemma V, abstract form
#print axioms stepV_2a
#print axioms stepV_2b
#print axioms stepV_3
#print axioms lemmaV_abs
#print axioms lemmaV_abs_n
-- the Poincaré inequality for a Lipschitz function
#print axioms poincare_lip
#print axioms energy_lip
#print axioms poincare_lip_le
#print axioms poincare_lip_L
#print axioms poincare_lip_scaled
#print axioms poincare_mat
#print axioms poincare_mean_pi
-- item 5
#print axioms markov_no_gain
#print axioms tail_le_conv2
#print axioms two_PhiBar_le_kap
#print axioms two_PhiBar_le_third
#print axioms gauss_abs_tail_moment
#print axioms gaussStepMoment
#print axioms finalStepMoment
#print axioms lint_vHat
#print axioms weakI
#print axioms gaussLevel151_formula
#print axioms pFail7_num
#print axioms gaussLevel151_of_kap
#print axioms gaussLevel151
#print axioms gaussLevel151_third
-- the Gaussian step for the `W` term; the unconditional level 4/5
#print axioms wStruct151
#print axioms linW_gauss
#print axioms lint_vW
#print axioms wStageGauss151
#print axioms condLean151G
#print axioms condLeanSamp151G
#print axioms condLeanProg151G
#print axioms gaussLevel151G_formula
#print axioms pFail7G_num
#print axioms gaussLevel151G_of_kap
#print axioms gaussLevel151_45
-- the glue from a family of `A`-stage events, one for each stand-in input, to the event `X12`
#print axioms prod_fst_real
#print axioms triple_W_real
#print axioms wBadW151
#print axioms wBadWA151
#print axioms tauWA_pos_of_good
#print axioms measurable_cenTau
#print axioms X12fam_meas
#print axioms X12famW_meas
#print axioms X12_of_family_window
#print axioms X12_of_family
#print axioms triple_WA12_real
