import BstLean.Part151All
import BstLean.Part151ON
import BstLean.Part151Sharp
import BstLean.Part151VA2
import BstLean.Part151Num99
import BstLean.Part151VB
import BstLean.Part151Num99V
import BstLean.Part151G3
import BstLean.Part151Num99GV

/-!
# Part 151, second audit module: the files that import Part 152

`Part151ON` (Lemma ON, from Gordon's bound `opN_tail'` of `Part152Op`) and `Part151Sharp` (the
concentration events of Lemma SA and Lemma U with the sharp constant of `Part152GC`) import
files of Part 152, which another agent wrote. `Part151VA`, `VAmeas`, `VAprob`, `VAprob2`,
`VAfin`, `VA2` (Proposition VA (b): the hypothesis H2 from hypotheses on the `A` stage) and
`Part151Br` (Lemma Cr, the event `E_c`, Lemma V step 1) import them. `Part151All` does not
depend on Part 152.
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part151

#print axioms hid2_lip_op
#print axioms lip_of_EON
#print axioms EON_prob
#print axioms lemmaON
#print axioms tF_LF_sq
#print axioms lemmaSA_conc_sharp
#print axioms lemmaSA_conc'_sharp
#print axioms condConc_sharp
#print axioms lemmaU_EU_sharp
#print axioms lemmaU_Ecross_sharp
#print axioms lemmaU_events_sharp
#print axioms lemmaSA_Es
#print axioms lemmaU_EUc
#print axioms lemmaU_Ecrossc
-- Proposition VA (b)
#print axioms vHat_le_of_good
#print axioms meas_PhiU
#print axioms meas_wX
#print axioms prob_slice
#print axioms fix_map_theta
#print axioms fix_map_A3
#print axioms prob_X12
#print axioms prob_X3
#print axioms prob_ON
#print axioms prob_Tm
#print axioms prob_FE
#print axioms prob_JU
#print axioms prob_s
#print axioms prob_U
#print axioms EVA_meas
#print axioms good_of_EVA
#print axioms H2_of_Astage
#print axioms theorem5_frame
-- the bridges
#print axioms lemmaCr_gen
#print axioms lemmaCr
#print axioms lemmaEc_gen
#print axioms lemmaEc
#print axioms Dc_le_Dv
#print axioms energy_le
#print axioms Dv_eq
-- hypotheses on (W, A₁, A₂) only
#print axioms H2_of_Astage'
#print axioms X3c_prob
#print axioms H2_of_A12
#print axioms theorem5_frameA12
#print axioms theorem5_frameProg
#print axioms H2_of_A12_Cr
#print axioms theorem5_frameA12_Cr
-- the level 99/100 from the `A`-stage constants of the document
#print axioms two_PhiBar_seven_half
#print axioms vbar_num
#print axioms total_le
#print axioms theorem5_cond_99
#print axioms theorem5_cond_99_samp
-- Lemma V in the frame
#print axioms v1V_mean
#print axioms Dv_le_of_V
#print axioms theorem5_frameA12_V
#print axioms theorem5_frameProg_V
#print axioms theorem5_frameA12_V_Cr
-- the level 99/100 from the primitive quantities of the event table
#print axioms DvV_num
#print axioms vbar_num'
#print axioms total_le'
#print axioms theorem5_cond_99_V
#print axioms theorem5_cond_99_V_samp
-- the conditional levels with the Gaussian step for the `W` term
#print axioms theorem5_frameProgG
#print axioms total_leG
#print axioms total_leG2
#print axioms theorem5_cond_99G
#print axioms theorem5_cond_995G
-- the strongest conditional statements: primitive hypotheses, Gaussian step for the `W` term
#print axioms theorem5_cond_99GV
#print axioms theorem5_cond_99GV_samp
#print axioms theorem5_cond_995GV
