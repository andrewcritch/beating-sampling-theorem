import BstLean.Part169Num

/-!
# Part 169: the bias hypothesis in Lean, first part

No proof is left open; no `native_decide` or `axiom` is used.

* `Part169Pass`: the stored tables as the paper's conditional passes (`passF`, `passW`,
  `paperDesignP`, `mixP_eq`).
* `Part169End`: the end theorem with these tables (`classifier_paper_pass80k`) and with a
  separate bias event (`classifier_paper_bias80k`).
* `Part169Price`: the deterministic bias price (`hell_price_pt`, `bias_price`, `bias_price_L8`).
* `Part169Ineq`: Minkowski, Hölder, Jensen and Markov on a set of mass at most one.
* `Part169Scale`: the scale price `B_S` and the exceptional mass (`scale_pt`, `scale_L2`,
  `scale_mass`).
* `Part169Comp`: `P_B` from the moment inputs (`bias_price_paper`).
* `Part169Red`: `BIASP` from the moment inputs (`biasP_of_inputs`).
* `Part169In`: the inputs that hold on the good set (`Sb_lower`, `cA_input`).
* `Part169Mom`: the end theorem with `BIAS_hyp` replaced by the moment inputs
  (`classifier_paper_mom80k`).
* `Part169Grid`, `Part169Lip`, `Part169Rule`, `Part169Asm`: the nearest node, the grid error,
  the finite-rule error and the assembly `a_f = A + g_f + r_f`, `a_ω = A + g_ω + r_ω`.
* `Part169Int`: the integrability items of `MomIn` are theorems (`momIn_of_momB`,
  `classifier_paper_momB80k`).
* `Part169Op`: the operator events and the bulk on the good set (`opB_goodD`, `bulk_of_window`),
  and the end theorem with the exact-rule errors (`momB_of_momX`, `classifier_paper_momX80k`).
* `Part169Sig`: the upper bound of `ς²` with no new event (`vsig2_le`, `hvs_goodD`) and the end
  theorem with the remaining inputs `MomY` (`classifier_paper_momY80k`).
* `Part169Var`: `V = Var_v f`, `0 ≤ V ≤ v_max`, `‖nV‖_2 ≤ C_v`, `|f̄| ≤ H_f` on the good set
  (`VR_eq`, `VR_le`, `VR_L2`, `fbR_le`), and the end theorem with `BIAS_hyp` reduced to the
  exact-rule `L⁸` bounds (`classifier_paper_exact80k`).
* `Part169Num`: the numerical condition `P_B ≤ 0.004295²` from the linear condition
  `A_ω + 8.06A_f ≤ 0.72`, every `n ≥ 80 000` (`PB_le`), and the end theorem
  `classifier_paper_A80k`.
-/

#print axioms BstLean.Part169.measurable_passF
#print axioms BstLean.Part169.measurable_passW
#print axioms BstLean.Part169.mixP_eq
#print axioms BstLean.Part169.passF_eq
#print axioms BstLean.Part169.classifier_paper_pass80k
#print axioms BstLean.Part169.classifier_paper_bias80k
#print axioms BstLean.Part169.hell_price_pt
#print axioms BstLean.Part169.hell_price_loc
#print axioms BstLean.Part169.bias_price
#print axioms BstLean.Part169.sq_int_le_of_pow8
#print axioms BstLean.Part169.pow4_int_le_of_pow8
#print axioms BstLean.Part169.bias_price_L8
#print axioms BstLean.Part169.int_sq_add
#print axioms BstLean.Part169.int_pow6_add
#print axioms BstLean.Part169.int_pow6_of_pow8
#print axioms BstLean.Part169.int_sq_mul_le
#print axioms BstLean.Part169.int_pow6_mul_le
#print axioms BstLean.Part169.markov_on
#print axioms BstLean.Part169.scale_pt
#print axioms BstLean.Part169.scale_L2
#print axioms BstLean.Part169.scale_mass
#print axioms BstLean.Part169.bias_price_paper
#print axioms BstLean.Part169.sA_eq
#print axioms BstLean.Part169.biasP_of_inputs
#print axioms BstLean.Part169.Sb_lower
#print axioms BstLean.Part169.cA_input
#print axioms BstLean.Part169.biasP_goodD
#print axioms BstLean.Part169.classifier_paper_mom80k
#print axioms BstLean.Part169.nodeIdx_near
#print axioms BstLean.Part169.gIdx_near
#print axioms BstLean.Part169.xLat_sub_le
#print axioms BstLean.Part169.fbar_lip
#print axioms BstLean.Part169.wbar_lip
#print axioms BstLean.Part169.fbR_eq
#print axioms BstLean.Part169.grid_f
#print axioms BstLean.Part169.grid_w
#print axioms BstLean.Part169.rule_f
#print axioms BstLean.Part169.rule_w
#print axioms BstLean.Part169.int_pow8_add_const
#print axioms BstLean.Part169.hF8_of_exact
#print axioms BstLean.Part169.hW8_of_exact
#print axioms BstLean.Part169.momIn_of_momB
#print axioms BstLean.Part169.classifier_paper_momB80k
#print axioms BstLean.Part169.opB_of_opN
#print axioms BstLean.Part169.opB_goodD
#print axioms BstLean.Part169.qB_pos
#print axioms BstLean.Part169.bulk_of_window
#print axioms BstLean.Part169.momB_of_momX
#print axioms BstLean.Part169.classifier_paper_momX80k
#print axioms BstLean.Part169.dir_sq_mean
#print axioms BstLean.Part169.var_le_mse
#print axioms BstLean.Part169.vsig2_le
#print axioms BstLean.Part169.hvs_goodD
#print axioms BstLean.Part169.classifier_paper_momY80k
#print axioms BstLean.Part169.VR_eq
#print axioms BstLean.Part169.VR_le
#print axioms BstLean.Part169.eR_le
#print axioms BstLean.Part169.VR_L2
#print axioms BstLean.Part169.fbR_le
#print axioms BstLean.Part169.classifier_paper_exact80k
#print axioms BstLean.Part169.PB_bound
#print axioms BstLean.Part169.HfN_le
#print axioms BstLean.Part169.c1F_le
#print axioms BstLean.Part169.c2F_le
#print axioms BstLean.Part169.Jz_ge
#print axioms BstLean.Part169.gf_le
#print axioms BstLean.Part169.rf_le
#print axioms BstLean.Part169.gw_le
#print axioms BstLean.Part169.rw_le
#print axioms BstLean.Part169.PB_le
#print axioms BstLean.Part169.classifier_paper_A80k
