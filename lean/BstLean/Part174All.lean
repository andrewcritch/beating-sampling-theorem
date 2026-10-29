import BstLean.Part174Wfl
import BstLean.Part174Mass
import BstLean.Part174T172
import BstLean.Part174U55T172
import BstLean.Part174End
import BstLean.Part174CapEnd

/-!
# Part 174: top module

No proof is left open; no `native_decide` or `axiom` is used.

Imports every Part 174 module and prints the axioms of the headline results.

* `Wfl`: the energy fluctuation allowance `WflR` without the factor `√3` (`exWn_mom_r`).
* `Mass`: the mass below the floor with `s0P = 0.5097`.
* `Root`, `T166` … `T172`: the chain of Part 173 (59 000) re-proved for `n ≥ 57 000`, namespace
  `BstLean.Part174.N57`; end theorem `BstLean.Part174.N57.classifier_paper_uncond57k`.
* `U55Root`, `U55T166` … `U55T172`: the same chain for `n ≥ 55 000` with the mass of file `Mass`,
  namespace `BstLean.Part174.N55`; end theorem `BstLean.Part174.N55.classifier_paper_uncond55k`.
* `CapNum`, `CapNode`, `CapGood`, `CapEnd`: Markov thresholds growing like `n^{1/64}`; the theorem
  for `n ≥ 10¹⁹` with no upper end, and **`BstLean.Part174.Cap.classifier_paper_uncond_nocap`**
  (every `n ≥ 55 000`, no upper end).
* `End`: `classifier_paper_uncond_57000` and its comparison with Parts 172 and 173.
-/

-- file `Wfl`
#print axioms BstLean.Part174.pair_comb
#print axioms BstLean.Part174.plane_mom4
#print axioms BstLean.Part174.flQ_mean_int
#print axioms BstLean.Part174.M0_eq
#print axioms BstLean.Part174.pyth_PQ
#print axioms BstLean.Part174.GR_int_gen
#print axioms BstLean.Part174.outer_r
#print axioms BstLean.Part174.exWn_mom_r
-- file `Mass`
#print axioms BstLean.Part174.mass_order40P
#print axioms BstLean.Part174.mass_of_goodCP
#print axioms BstLean.Part174.classifier_paper_free23_mass40P
-- the 57 000 chain
#print axioms BstLean.Part174.N57.classifier_paper_uncond57k
#print axioms BstLean.Part174.N57.classifier_paper_bias_num57k
#print axioms BstLean.Part174.N57.PB_le
#print axioms BstLean.Part174.N57.WflR_le
#print axioms BstLean.Part174.N57.FflQ_le
#print axioms BstLean.Part174.N57.roomE57_ge
#print axioms BstLean.Part174.N57.theta_mom
#print axioms BstLean.Part174.N57.cert_charge_47
#print axioms BstLean.Part174.N57.root_core57
#print axioms BstLean.Part174.N57.betaM_4691_57
#print axioms BstLean.Part174.N57.stat_charge
#print axioms BstLean.Part174.N57.en_num57
-- the 55 000 chain
#print axioms BstLean.Part174.N55.classifier_paper_uncond55k
#print axioms BstLean.Part174.N55.classifier_paper_bias_num55k
#print axioms BstLean.Part174.N55.PB_le
#print axioms BstLean.Part174.N55.WflR_le
#print axioms BstLean.Part174.N55.FflQ_le
#print axioms BstLean.Part174.N55.roomE55_ge
#print axioms BstLean.Part174.N55.theta_mom
#print axioms BstLean.Part174.N55.cert_charge_47
#print axioms BstLean.Part174.N55.root_core55
#print axioms BstLean.Part174.N55.betaMP_4691_55
#print axioms BstLean.Part174.N55.X2_num
#print axioms BstLean.Part174.N55.stat_charge
#print axioms BstLean.Part174.N55.en_num55
-- file `End`
#print axioms BstLean.Part174.classifier_paper_uncond_57000
#print axioms BstLean.Part174.uncond_57000_eq_172
#print axioms BstLean.Part174.uncond_57000_eq_173
#print axioms BstLean.Part174.classifier_paper_uncond_55000
#print axioms BstLean.Part174.uncond_55000_eq_172
#print axioms BstLean.Part174.uncond_55000_eq_173
-- the cap (files `Cap*`)
#print axioms BstLean.Part174.Cap.stat_chargeK
#print axioms BstLean.Part174.Cap.classifier_paper_uncond_large
#print axioms BstLean.Part174.Cap.classifier_paper_uncond_nocap
#print axioms BstLean.Part174.Cap.uncond_nocap_eq_172
