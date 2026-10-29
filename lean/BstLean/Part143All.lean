import BstLean.Part143Step1
import BstLean.Part143Final
import BstLean.Part143FinalL

/-!
# Part 143: index and axiom audit

Role: `delegations/statements/p143-spec.md`. Level `99/100` for the arithmetic one-pass program
of Part 141 (unchanged) inside the frontier interval: every `n ≥ 13225`, `k ≥ 100n`.

Files: `Part143Spread` (factor 2 of the spread), `Part143Core` (formula), `Part143HidK1`,
`Part143HidK`, `Part143HidC`, `Part143HidC2`, `Part143HidCL` (probabilities of the hidden
events), `Part143Lam`, `Part143Var`, `Part143Var2`, `Part143LamL`, `Part143Num` (stand-in
factor), `Part143LinC`, `Part143AgentC`, `Part143AgentCL` (centred part of the Agent link),
`Part143FC`, `Part143Asm` (link of `F`, orthogonal assembly), `Part143World`, `Part143WorldL`
(inputs and World network), `Part143Big`, `Part143BigL` (constants), `Part143Step1`,
`Part143Final`, `Part143FinalL` (headlines).
-/

open BstLean.Part143

#print axioms spreadLow_dist2
#print axioms spreadLow143_of
#print axioms progDist143
#print axioms good136_prob143
#print axioms errK_mean143
#print axioms errD_mean143
#print axioms goodHat_compl143
#print axioms goodHat_compl143s
#print axioms goodHat_compl143L
#print axioms frameHat143
#print axioms frameHat143L
#print axioms errSampleTailAL
#print axioms errSampleTailA143
#print axioms errSampleTailA143L
#print axioms XAL143_16
#print axioms XAL143_L
#print axioms cLin_integral
#print axioms cLin_L2
#print axioms linRem_L2
#print axioms cAg_integral
#print axioms cAg_L2
#print axioms agent_rem_L2
#print axioms cF_L2
#print axioms rF_L2
#print axioms cF_integral_tail
#print axioms BstLean.Part143.L2le.add_orth
#print axioms chord_pW
#print axioms kernDist143_of
#print axioms kernDist143_focus
#print axioms world_bias
#print axioms tX_L2_bias
#print axioms tX_L2_143s
#print axioms tau143s_le
#print axioms tau143s_leL
#print axioms kernDist143
#print axioms eD143_16
#print axioms eD143_L
#print axioms arithProgSucceeds143a
#print axioms arithProg143a_99
#print axioms arithProgSucceeds143
#print axioms arithProg143_99
#print axioms arithProgSucceeds143L
#print axioms arithProg143L_99
