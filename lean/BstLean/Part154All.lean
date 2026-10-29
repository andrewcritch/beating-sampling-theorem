import BstLean.Part154Top
import BstLean.Part154Top2
import BstLean.Part154Top8
import BstLean.Part154Final

/-!
# Part 154: index and audit

Role: `delegations/statements/p154-spec.md`. The mean-field lemma (Lemma MF) and the centre
errors of Theorem 5 (`proofs/option-n/theorem5-06-centre.tex`, `theorem5-12-finite-centre.tex`),
and the level `99/100` for every `n ≥ 16384` with no hypothesis (`theorem5_154`), through the
frame of Part 151.

Every line below must print `[propext, Classical.choice, Quot.sound]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part154

-- item 1: Lemma PR
#print axioms Ures_eq
#print axioms Ures_nonneg
#print axioms Ures_le_K0
#print axioms K0_lt
#print axioms PR_scalar
#print axioms PR_i
#print axioms PRvec_of
#print axioms PRvecAbs_of
#print axioms PRvec_K0
#print axioms PRvecAbs_K0
#print axioms kappa_chord
#print axioms PR_ii
-- item 2: Lemma L1 (c), Lemma HS
#print axioms hsH_mean
#print axioms measurable_hsH
#print axioms hsH_lip
#print axioms EH_prob
#print axioms EH_bound
-- item 3: Lemma MF
#print axioms MFHyp.F1
#print axioms MFHyp.F2
#print axioms MFHyp.F3
#print axioms MFHyp.F4a
#print axioms MFHyp.F4b
#print axioms MFHyp.F4c
#print axioms MFHyp.sig_int
#print axioms psiS_closed
#print axioms PhiG_diff_le
#print axioms G_taylor
#print axioms G_rough
#print axioms MFHyp.YF_mean
#print axioms MFHyp.YF_var_le
#print axioms MFHyp.YF_bias
#print axioms MFHyp.lin_term
#print axioms MFHyp.DF_decomp
#print axioms MFHyp.int_decomp
#print axioms MFHyp.lemmaMF_bias
#print axioms MFHyp.lemmaMF_K
#print axioms MFHyp.lemmaMF
#print axioms MFHyp.lemmaMF_cross
-- item 4: Lemma MA, Lemma MP
#print axioms fbar_fA
#print axioms sF2_fA
#print axioms M1_fA
#print axioms DF_row
#print axioms rows_mean
#print axioms var_sq_le_of_lip
#print axioms piBar_mono
#print axioms MFHyp_fA
#print axioms QB_div_mono
#print axioms MA_i
#print axioms MA_cross
#print axioms hbar2_lip
#print axioms dC_lip
#print axioms Ph_lip
#print axioms ED_prob
#print axioms EPi_prob
#print axioms EPb_prob
#print axioms Ph_var
#print axioms Pb_var
#print axioms radius_le
#print axioms MA_ii
#print axioms MA_iv
#print axioms MP_a
#print axioms MP_b
#print axioms MP_b_final
-- item 5: Proposition FC, Lemma TF
#print axioms EChi_prob
#print axioms FC_iii
#print axioms TF_vec
-- item 6: the events and the numbers
#print axioms GoodC_prob
#print axioms GoodC_HS
#print axioms GoodC_centre
#print axioms rhoBar_lt
#print axioms xiCn_le
#print axioms eMP_le
#print axioms x1_le
#print axioms x2_le
#print axioms plow_ge
#print axioms epsJ_le
#print axioms ebo_le
#print axioms centre154
#print axioms centre154_prob
#print axioms GoodC16_prob
#print axioms GoodC16_centre
#print axioms xiCn_le16
#print axioms x1_le16
#print axioms x2_le16
#print axioms epsJ_le16
#print axioms Nbar_le16
#print axioms measurableSet_SC16
#print axioms measurableSet_Wd16
#print axioms Wd16_prob
#print axioms phi_poincare
#print axioms A12_of_GoodC16
#print axioms frame154
#print axioms theorem5_154
#print axioms theorem5_154_sharp'
#print axioms theorem5_154_sharp
#print axioms theorem5_154_996
#print axioms theorem5_154_995
-- the route for n ≥ 8192
#print axioms GoodC8_centre
#print axioms xiCn_le8
#print axioms x1_le8
#print axioms x2_le8
#print axioms ebo_le8
#print axioms Nbar_le8
#print axioms measurableSet_Wd8
#print axioms Wd8_prob
#print axioms measurableSet_SC8
#print axioms A12_of_GoodC8
#print axioms theorem5_154_8192'
#print axioms theorem5_154_8192
