import BstLean.Part150Centre
import BstLean.Part150Prog4

/-!
# Part 150, items 3 and 4: audit of the headline statements

Item 3 (`Part150CDefs`, `Part150Centre`): the finite centre against the oracle centre.
Item 4 (`Part150Prog`, `Part150Prog2`, `Part150Prog3`, `Part150Prog4`): the arithmetic pass over
`A` as a straight-line program, its value and its operation count.
Do not use `sorry`, `native_decide` or `axiom`.
-/

open BstLean.Part150

#print axioms c_binW_sum
#print axioms c_binMean_var_nonneg
#print axioms hT_sub_hO
#print axioms hT_sub_hO_sq
#print axioms sT2_eq_var
#print axioms sT2_nonneg
#print axioms sT2_le
#print axioms gT_sub_gO
#print axioms sT2_sub_sO2
#print axioms secondLayer_coord
#print axioms bT_sub_bO
#print axioms bT_sub_bO_nrm
#print axioms BstLean.Part130.RProg.eval_stage
#print axioms op1Stage_eval
#print axioms dotStage_eval
#print axioms sumStage_eval
#print axioms firstLayer_h
#print axioms firstLayer_g
#print axioms passProg_eval_c
#print axioms passProg_eval_sig
#print axioms passProgZ_eval_c
#print axioms passProgZ_eval_sig
#print axioms passProgZ_eval_zeta
#print axioms passProgZ_eval_zeta_one
#print axioms passProgZ_eval_zeta_zero
#print axioms passAll_cost_eq
#print axioms passProg_cost
#print axioms passProg_cost_paper
#print axioms passProg_cost_le_paper
#print axioms passProgZ_cost_paper
#print axioms gA150_eval_gen
#print axioms gA150_eval
#print axioms gA150_eval_one
#print axioms gA150_eval_zero
#print axioms gA150_cost
#print axioms gA150_cost_paper
