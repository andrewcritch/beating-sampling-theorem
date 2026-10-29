import BstLean.Part153Asm
import BstLean.Part153Bin
import BstLean.Part153Cen
import BstLean.Part153Conc
import BstLean.Part153Cr
import BstLean.Part153Dec
import BstLean.Part153EN
import BstLean.Part153Energy
import BstLean.Part153Final
import BstLean.Part153Inv
import BstLean.Part153JDefs
import BstLean.Part153Lp
import BstLean.Part153Norms
import BstLean.Part153Norms2
import BstLean.Part153Op
import BstLean.Part153PP
import BstLean.Part153PPs
import BstLean.Part153PPs2
import BstLean.Part153PPs3
import BstLean.Part153PPs4
import BstLean.Part153Pt
import BstLean.Part153S
import BstLean.Part153SJ
import BstLean.Part153SL
import BstLean.Part153Sc
import BstLean.Part153Weak

/-!
# Part 153 (file `All`): the audit of the headline statements

Role: `delegations/statements/p153-spec.md`. Every name below must give
`[propext, Classical.choice, Quot.sound]` and nothing else.
-/

open BstLean.Part153

-- definitional links with Part 149 (the hidden vectors of `A` at the stand-in input)
example {n : ℕ} (A₁ : Matrix (Fin (BstLean.Part130.mA n)) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ)
    (ξ : Fin n → ℝ) : sq1 A₁ c τ ξ = nrm (BstLean.Part149.a1 c τ A₁ ξ) / √(n : ℝ) := rfl

-- file `Asm`
#print axioms BstLean.Part153.prod_real_le_of_fibre
#print axioms BstLean.Part153.prod_real_fst
#print axioms BstLean.Part153.measurable_N2_joint
#print axioms BstLean.Part153.measurable_N1
#print axioms BstLean.Part153.measurable_int_N2
#print axioms BstLean.Part153.measurable_Pb_joint
#print axioms BstLean.Part153.measurable_int_Pb
#print axioms BstLean.Part153.measurable_gO_A1
#print axioms BstLean.Part153.measurable_opN_A1
#print axioms BstLean.Part153.measurable_sqrt_GamS
#print axioms BstLean.Part153.measurable_Xi4
#print axioms BstLean.Part153.measurableSet_GoodA
#print axioms BstLean.Part153.GoodA_prob
#print axioms BstLean.Part153.GoodA_op
#print axioms BstLean.Part153.GoodA_energy
#print axioms BstLean.Part153.GoodA_norms
#print axioms BstLean.Part153.GoodA_be
#print axioms BstLean.Part153.GoodA_EN_iii
#print axioms BstLean.Part153.GoodA_Xi
#print axioms BstLean.Part153.Xi4_weak_prob
#print axioms BstLean.Part153.measurableSet_GoodAw
#print axioms BstLean.Part153.GoodAw_prob
#print axioms BstLean.Part153.GoodAw_Xi
-- file `Bin`
#print axioms BstLean.Part153.cnt_tail
#print axioms BstLean.Part153.cnt_tail_lower
#print axioms BstLean.Part153.nrm_moment
#print axioms BstLean.Part153.nrm_reluV_moment
#print axioms BstLean.Part153.nrm_moment_lintegral
#print axioms BstLean.Part153.nrm_reluV_moment_lintegral
#print axioms BstLean.Part153.lintegral_pow_add_le
#print axioms BstLean.Part153.lintegral_pow_const_mul_le
#print axioms BstLean.Part153.lintegral_pow_split_le
#print axioms BstLean.Part153.lintegral_pow_split_le'
-- file `Cen`
#print axioms BstLean.Part153.Pb_lip
#print axioms BstLean.Part153.GamBar_le
#print axioms BstLean.Part153.sO2_nonneg
#print axioms BstLean.Part153.Ebe_prob
#print axioms BstLean.Part153.psi_sq_row
#print axioms BstLean.Part153.rb_eq
#print axioms BstLean.Part153.rb_bounds
#print axioms BstLean.Part153.eb_le
-- file `Conc`
#print axioms conc_upper_strict
#print axioms conc_lower_strict
#print axioms conc_abs_strict
-- file `Cr`
#print axioms resCov_le_cr
#print axioms resCov_le_of_cr
-- file `Dec`
#print axioms gaussMat_transpose
#print axioms opN_transpose
#print axioms gaussMat_vecMul
#print axioms gaussMat_transpose_mulVec
#print axioms gaussMat_cols_map
#print axioms gaussMat_split
#print axioms eq_vecMulVec_add_mul_projT
#print axioms gaussMat_decomp
#print axioms gaussMat_decomp'
#print axioms gaussMat_decomp_self
-- file `EN`
#print axioms GamS_eq_gO
#print axioms EN_iii
-- file `Energy`
#print axioms integral_swap_of_nonneg
#print axioms sqrtGam_lip
#print axioms GamS_mean
#print axioms sqrtGam_mean
#print axioms Ee_prob
#print axioms Ee_bounds
#print axioms Ee_delta
#print axioms Ee_delta_12
-- file `Final`
#print axioms AStage_prob
#print axioms AStage_Xi
#print axioms AStage_eb
#print axioms AStage_bounds
#print axioms AStage16_prob
#print axioms AStage16_Xi
#print axioms measurableSet_GoodAs
#print axioms AStage_weak_prob
#print axioms AStage_weak_eb
-- file `Inv`
#print axioms invMoment_le
#print axioms invMoment_one_le
#print axioms invMoment_two_le
#print axioms ae_normSq_ne_zero
-- file `Lp`
#print axioms abs_lpNorm_sub_le
#print axioms lpNorm_le_mul
#print axioms lpNorm_nat_pow
#print axioms eLpNorm_nat_pow
#print axioms mean_lpNorm_le
-- file `Norms`
#print axioms BstLean.Part153.x4n_le
#print axioms BstLean.Part153.N1_lip
#print axioms BstLean.Part153.N1_event
#print axioms BstLean.Part153.N1_mean2
#print axioms BstLean.Part153.N1_mean4
#print axioms BstLean.Part153.N12_event
#print axioms BstLean.Part153.N14_event
#print axioms BstLean.Part153.N2_lip
#print axioms BstLean.Part153.lpNorm_sq1_le_one_add
#print axioms BstLean.Part153.lpNorm_sq1_le_opN
#print axioms BstLean.Part153.N22_event
#print axioms BstLean.Part153.N24_event
-- file `Norms2`
#print axioms BstLean.Part153.N2_mean2
#print axioms BstLean.Part153.N2_mean4
#print axioms BstLean.Part153.N22_le_bar
#print axioms BstLean.Part153.N24_le_bar
#print axioms BstLean.Part153.int_sq2_sq_le
#print axioms BstLean.Part153.int_abs_sq2_sq_sub_one_le
-- file `Op`
#print axioms Eop_prob
#print axioms Eop_sq
#print axioms covH_le
#print axioms covH_le_Eop
#print axioms int_normSq_shift
#print axioms GamS_le
#print axioms GamS_le_Eop
#print axioms fro_le
#print axioms fro_le_Eop
-- file `PP`
#print axioms opN_mul_le
#print axioms jacT_le
#print axioms opN_jacT_le
#print axioms opN_mul_moment
#print axioms lemmaPP_i_weak
#print axioms lemmaPP_i_weak_integral
#print axioms markov_Xi
#print axioms lemmaPP_ii_Xi4
#print axioms lemmaPP_ii_XiS
#print axioms lemmaPP_Xi4_weak
#print axioms lemmaPP_XiS_weak
-- file `PPs`
#print axioms opN_rowsel_moment
#print axioms opN_jacT_le_split
#print axioms stepA
#print axioms stepA_hat
-- file `PPs2`
#print axioms stepB
#print axioms lemmaPP_i_sharp
#print axioms lemmaPP_Xi4_sharp
#print axioms lemmaPP_XiS_sharp
-- file `PPs3`
#print axioms gaussMomConst_160_le
#print axioms jS_160_le
#print axioms lemmaPP_numeric
#print axioms cov_le_of_Xi4
#print axioms var_lip_le_of_Xi4
#print axioms cov_le_on_event
#print axioms var_lip_le_on_event
-- file `PPs4`
#print axioms gaussMomConst_200_le
#print axioms lemmaPP_numeric_8192
#print axioms lemmaPP_numeric_16384
#print axioms cov_le_on_event_8192
#print axioms var_lip_le_on_event_8192
-- file `Pt`
#print axioms BstLean.Part153.pi_finset_moments
#print axioms BstLean.Part153.relu_std_core
#print axioms BstLean.Part153.relu_std_dev2
#print axioms BstLean.Part153.relu_std_dev4
#print axioms BstLean.Part153.relu_norm_dev2
#print axioms BstLean.Part153.relu_norm_dev4
-- file `S`
#print axioms BstLean.Part153.sphPt_dist_le
#print axioms BstLean.Part153.gradSq_le_of_local
#print axioms BstLean.Part153.gradSq_sph_le
#print axioms BstLean.Part153.lemmaS_grad
#print axioms BstLean.Part153.lemmaS_weak
#print axioms BstLean.Part153.ae_normSq_ne
-- file `SJ`
#print axioms opN_jacT_le_sj
#print axioms hid2_sph_local
#print axioms gradSq_jac_le
#print axioms lemmaS_jac_full
#print axioms lemmaS_jac
#print axioms XiS_le_Xi4
#print axioms XiS_le_op
#print axioms weak_var_le
#print axioms cov_hid2_le
-- file `SL`
#print axioms hid2_shift_local_sl
#print axioms gradSq_loc_le_sl
#print axioms lemmaS_loc_sl
#print axioms lemmaS_loc_meas_sl
#print axioms lemmaS_loc_unif_sl
#print axioms lemmaS_jac_sl
-- file `Sc`
#print axioms psiG_mul_le
#print axioms Vr_add_ge
#print axioms Vr_nonneg
#print axioms Vr_le_one
#print axioms sO2_mean
#print axioms sO2_var
#print axioms Esc_prob_gen
#print axioms Esc_prob
-- file `Weak`
#print axioms Eop2_prob
#print axioms XiS_le_weak
#print axioms weak_var_event
#print axioms Cweak_le
