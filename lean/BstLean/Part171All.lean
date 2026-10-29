import BstLean.Part171Tay
import BstLean.Part171Row
import BstLean.Part171Swap
import BstLean.Part171Bias
import BstLean.Part171Inst
import BstLean.Part171Zeta
import BstLean.Part171Mom
import BstLean.Part171Node
import BstLean.Part171Stat
import BstLean.Part171Num
import BstLean.Part171End
import BstLean.Part171Meas
import BstLean.Part171Op
import BstLean.Part171Red
import BstLean.Part171Fin
import BstLean.Part171Gen
import BstLean.Part171Var

/-!
# Part 171: the bias hypothesis in Lean, third part (top module)

Role: `delegations/statements/p171-spec.md`. Paper: `proofs/option-n/theorem7-08-bias.tex`
(the Taylor biases `t7:p08:T`, `t7:p08:U`, the bias moments `t7:p08:biasmom`).

Part 170's remaining bias moments `BiasMomF … 0.004` and `BiasMomW … 0.02` are PROVED on an
explicit measurable first-layer statistics event. The end theorem
`BstLean.Part171.classifier_paper_final80k` (every `n ≥ 80 000`) has one remaining hypothesis:
the charge of that statistics event (`≤ 0.0006`) at every World datum in the window.
No proof is left open; no `native_decide` or `axiom` is used.
-/

#print axioms BstLean.Part171.G_taylor_gen
#print axioms BstLean.Part171.G_rough_gen
#print axioms BstLean.Part171.G2_closed
#print axioms BstLean.Part171.G2_taylor
#print axioms BstLean.Part171.G2_rough
#print axioms BstLean.Part171.bias_split
#print axioms BstLean.Part171.rowF
#print axioms BstLean.Part171.rowW
#print axioms BstLean.Part171.int_gaussMat_coord
#print axioms BstLean.Part171.swap_row
#print axioms BstLean.Part171.biasF_rows
#print axioms BstLean.Part171.biasW_rows
#print axioms BstLean.Part171.M0_mulVec
#print axioms BstLean.Part171.row_stat
#print axioms BstLean.Part171.zeta_mom
#print axioms BstLean.Part171.zeta_mom4
#print axioms BstLean.Part171.zeta_mom8
#print axioms BstLean.Part171.TF_le
#print axioms BstLean.Part171.TW_le
#print axioms BstLean.Part171.pow8_three
#print axioms BstLean.Part171.zeta_poly
#print axioms BstLean.Part171.node_biasF
#print axioms BstLean.Part171.node_biasW
#print axioms BstLean.Part171.lint_sum_bound
#print axioms BstLean.Part171.biasMomF_of_stat
#print axioms BstLean.Part171.biasMomW_of_stat
#print axioms BstLean.Part171.numF
#print axioms BstLean.Part171.numW
#print axioms BstLean.Part171.biasMomF_stat
#print axioms BstLean.Part171.biasMomW_stat
#print axioms BstLean.Part171.classifier_paper_stat80k
#print axioms BstLean.Part171.measurableSet_StatEv
#print axioms BstLean.Part171.classifier_paper_statN80k
#print axioms BstLean.Part171.vsig2_upper
#print axioms BstLean.Part171.biasMomF_statOp
#print axioms BstLean.Part171.biasMomW_statOp
#print axioms BstLean.Part171.measurableSet_StatEvOp
#print axioms BstLean.Part171.classifier_paper_statOp80k
#print axioms BstLean.Part171.pyth
#print axioms BstLean.Part171.vsig2_eq
#print axioms BstLean.Part171.hUN_eq_DstN
#print axioms BstLean.Part171.q2_eq_dot
#print axioms BstLean.Part171.ls_dot
#print axioms BstLean.Part171.DstN_le_tan
#print axioms BstLean.Part171.measurableSet_StatEvOp2
#print axioms BstLean.Part171.biasMomF_statOp2
#print axioms BstLean.Part171.biasMomW_statOp2
#print axioms BstLean.Part171.classifier_paper_final80k
#print axioms BstLean.Part171.measurableSet_StatEvOpG
#print axioms BstLean.Part171.classifier_paper_gen80k
#print axioms BstLean.Part171.int_wT_eq
#print axioms BstLean.Part171.V2N_eq
#print axioms BstLean.Part171.piN_le
