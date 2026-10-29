import BstLean.Part160Defs
import BstLean.Part160Split
import BstLean.Part160Lib
import BstLean.Part160Event
import BstLean.Part160Ledger
import BstLean.Part160Mass4
import BstLean.Part160Mass8
import BstLean.Part160Mass
import BstLean.Part160Cov
import BstLean.Part160Eb
import BstLean.Part160Dmat
import BstLean.Part160Final
import BstLean.Part160Supply
import BstLean.Part160Cov8
import BstLean.Part160Ledger2
import BstLean.Part160Best
import BstLean.Part160Split2
import BstLean.Part160Split3
import BstLean.Part160Sc
import BstLean.Part160ScTab
import BstLean.Part160ScLo
import BstLean.Part160MFAll
import BstLean.Part160MFAll2
import BstLean.Part160Theta
import BstLean.Part160Ledger3
import BstLean.Part160Ledger4
import BstLean.Part160Best2
import BstLean.Part160Best3
import BstLean.Part160Best4
import BstLean.Part160Best5
import BstLean.Part160Ledger5
import BstLean.Part160Comb

/-!
# Part 160: the Agent frame hypothesis of the classifier theorem

Top module. Role: `delegations/statements/p160-spec.md`; report:
`delegations/answers/p160-spec-opus.md`. Do not use `sorry`, `native_decide` or `axiom`.

Headlines (namespace `BstLean.Part160`):

* `frameA_of_three` (`Split`): `FRAME_A_hyp` from `COV_hyp`, `CENTRE_hyp`, `MASS_hyp`.
* `classifier_networks_frameconst` (`Ledger`): the ledger with a free frame constant.
* `frameA_16384` (`Supply`): the Agent frame bound `10.6/n`, every `n ≥ 16 384`.
* `classifier_agentframe_sharp8`, `classifier_paper_agentframe` (`Final`): the conditional
  classifier theorem without the Agent frame hypothesis, every `n ≥ 75 000` (scaled ledger).
* `classifier_networks_frameconst2`, `classifier_frame_<tag>` (`Ledger2`): the ledger with the
  best exponents for a table of frame constants.
* `classifier_agentframe_46500` (`Best`), `classifier_agentframe2_30500` (`Best2`),
  `classifier_agentframe3_28000` (`Best3`): intermediate forms.
* `frame_split2`, `frameA_point2`, `frameA_point3` (`Split2`, `Split3`): the frame split of
  second order.
* `lemmaMF_int`, `centre16_int`, `centre16_D`, `centre22k_D_k` (`MF…`): the centre charge with
  the integrated remainder and the smaller deviation.
* `eb16_sharp_k`, `eb16_lower_k` (`ScTab`, `ScLo`): the centre energy from both sides.
* **`frameA4f_16384`** (`Best4`): the Agent frame bound `3.6/n`, every `n ≥ 16 384`.
* **`classifier_agentframe4_24500`, `classifier_paper_agentframe4_24500`** (`Best4`): the
  conditional classifier theorem without the Agent frame hypothesis, every `n ≥ 24 500`.
* **`frameA5f_16384`** (`Best5`): `3.3/n`, every `n ≥ 16 384`; **`classifier_agentframe5_23000`**:
  every `n ≥ 23 000`.
* **`classifier_paper_comb23`**, `classifier_paper_comb` (`Comb`): with the World stage of Part 159, for `paperDesign` and
  every `n ≥ 24 500`; the only remaining hypothesis is `REPLA_mix_hyp`.
-/

open BstLean.Part160 in
#print axioms frameA_of_three
open BstLean.Part160 in
#print axioms frameA_paper_numbers
open BstLean.Part160 in
#print axioms classifier_networks_frameconst
open BstLean.Part160 in
#print axioms classifier_networks_frameconst_kappa
open BstLean.Part160 in
#print axioms classifier_networks_frameconst_success
open BstLean.Part160 in
#print axioms EA16_charge_num
open BstLean.Part160 in
#print axioms events_with_agent
open BstLean.Part160 in
#print axioms paperDesign_agentCentre
open BstLean.Part160 in
#print axioms lipD_fourth_sharp
open BstLean.Part160 in
#print axioms lipD_eighth
open BstLean.Part160 in
#print axioms SXi8_charge
open BstLean.Part160 in
#print axioms SXi_charge
open BstLean.Part160 in
#print axioms XiS_noncentral
open BstLean.Part160 in
#print axioms kappa_quad
open BstLean.Part160 in
#print axioms eb16
open BstLean.Part160 in
#print axioms cov_hid2_le_D
open BstLean.Part160 in
#print axioms mass_bound_gen
open BstLean.Part160 in
#print axioms frameA_lib
open BstLean.Part160 in
#print axioms frameA_sharp
open BstLean.Part160 in
#print axioms frameA_sharp8
open BstLean.Part160 in
#print axioms classifier_agentframe_lib
open BstLean.Part160 in
#print axioms classifier_agentframe_sharp
open BstLean.Part160 in
#print axioms classifier_agentframe_sharp8
open BstLean.Part160 in
#print axioms classifier_paper_agentframe
open BstLean.Part160 in
#print axioms mass_hyp_16384
open BstLean.Part160 in
#print axioms frameA_16384
open BstLean.Part160 in
#print axioms Xi4_noncentral
open BstLean.Part160 in
#print axioms Xi8_noncentral
open BstLean.Part160 in
#print axioms classifier_networks_frameconst2
open BstLean.Part160 in
#print axioms classifier_frame_75
open BstLean.Part160 in
#print axioms classifier_frame_4
open BstLean.Part160 in
#print axioms frameA_46500
open BstLean.Part160 in
#print axioms classifier_agentframe_46500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe_46500
open BstLean.Part160 in
#print axioms frame_split2
open BstLean.Part160 in
#print axioms resid_fourth
open BstLean.Part160 in
#print axioms gap_sq
open BstLean.Part160 in
#print axioms frameA_point2
open BstLean.Part160 in
#print axioms frameA_point3
open BstLean.Part160 in
#print axioms sigD_mean_sq_le
open BstLean.Part160 in
#print axioms Ures_exp
open BstLean.Part160 in
#print axioms lemmaMF_int
open BstLean.Part160 in
#print axioms MA_i_int
open BstLean.Part160 in
#print axioms centre16_int
open BstLean.Part160 in
#print axioms centre50k_int
open BstLean.Part160 in
#print axioms centre16_D
open BstLean.Part160 in
#print axioms centre22k_D_46
open BstLean.Part160 in
#print axioms centre22k_D_54
open BstLean.Part160 in
#print axioms SD'_charge
open BstLean.Part160 in
#print axioms sO2_mean_sharp
open BstLean.Part160 in
#print axioms SSc_charge_num
open BstLean.Part160 in
#print axioms eb16_sharp
open BstLean.Part160 in
#print axioms eb16_sharp_46
open BstLean.Part160 in
#print axioms eb16_sharp_54
open BstLean.Part160 in
#print axioms eb16_lower
open BstLean.Part160 in
#print axioms eb16_lower_46
open BstLean.Part160 in
#print axioms eb16_lower_54
open BstLean.Part160 in
#print axioms SScU_charge_num
open BstLean.Part160 in
#print axioms XiS_theta
open BstLean.Part160 in
#print axioms Xi4_theta
open BstLean.Part160 in
#print axioms Xi8_theta
open BstLean.Part160 in
#print axioms classifier_frame_335
open BstLean.Part160 in
#print axioms classifier_frame_45
open BstLean.Part160 in
#print axioms classifier_frame_560
open BstLean.Part160 in
#print axioms frameA2_30500
open BstLean.Part160 in
#print axioms classifier_agentframe2_30500
open BstLean.Part160 in
#print axioms frameA3_28000
open BstLean.Part160 in
#print axioms classifier_agentframe3_28000
open BstLean.Part160 in
#print axioms frameA4_24500
open BstLean.Part160 in
#print axioms frameA4f_16384
open BstLean.Part160 in
#print axioms classifier_agentframe4_24500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe4_24500
open BstLean.Part160 in
#print axioms classifier_paper_comb
open BstLean.Part160 in
#print axioms window_paper
open BstLean.Part160 in
#print axioms frameA5f_16384
open BstLean.Part160 in
#print axioms frameA5_23000
open BstLean.Part160 in
#print axioms classifier_agentframe5_23000
open BstLean.Part160 in
#print axioms classifier_paper_agentframe5_23000
open BstLean.Part160 in
#print axioms classifier_paper_comb23
open BstLean.Part160 in
#print axioms centre16_BD
open BstLean.Part160 in
#print axioms centre22k_46
open BstLean.Part160 in
#print axioms BstLean.Part160.MFB.hsH_mean_B
