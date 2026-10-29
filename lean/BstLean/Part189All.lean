import BstLean.Part189Bridge
import BstLean.Part189Schedule
import BstLean.Part189Search

/-!
Part 189: the paper allowance count and the annotated operation schedule.
The schedule has explicit named reserves. No theorem in this module
identifies its value with `progOut (paperDesignP n)`.
-/

namespace BstLean.Part189
noncomputable section

theorem orderedWork_lt_8000 {n : ℕ} (hn : 8000 ≤ n) :
    ((orderedWork n).cost : ℝ) < (10003 / 10000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  have h : ((orderedWork n).cost : ℝ) ≤ (paperCount n : ℝ) := by
    exact_mod_cast orderedWork_le hn
  exact lt_of_le_of_lt h (paperCount_lt_8000 hn)

theorem paperCount_lt_integer {n : ℤ} (hn : 8000 ≤ n) :
    (paperCount n.toNat : ℝ) < (10003 / 10000 : ℝ) * (2 * (n : ℝ) ^ 7) := by
  have hnat : 8000 ≤ n.toNat := by omega
  have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
  have hr : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast he
  rw [← hr]
  exact paperCount_lt_8000 hnat

theorem comparison_ratio {n : ℕ} (hn : 8000 ≤ n) :
    (113865 / 100 : ℝ) < 1139 * (exactSampleCount n : ℝ) / (paperCount n : ℝ) := by
  have hp : (0 : ℝ) < paperCount n := by
    have h : 0 < paperCount n := by unfold paperCount; omega
    exact_mod_cast h
  apply (lt_div_iff₀ hp).mpr
  have h := comparison_1139 hn
  nlinarith

end
end BstLean.Part189

#print axioms BstLean.Part189.conditional_atoms
#print axioms BstLean.Part189.paperCount_eq
#print axioms BstLean.Part189.half_power
#print axioms BstLean.Part189.widthF_le
#print axioms BstLean.Part189.widthW_le
#print axioms BstLean.Part189.paperCount_le_polynomial
#print axioms BstLean.Part189.paperCount_lt_of_certificate
#print axioms BstLean.Part189.paperCount_lt_8000
#print axioms BstLean.Part189.paperCount_lt_8355
#print axioms BstLean.Part189.paperCount_lt_8514
#print axioms BstLean.Part189.paperCount_lt_9963
#print axioms BstLean.Part189.paperCount_lt_10301
#print axioms BstLean.Part189.paperCount_lt_11364
#print axioms BstLean.Part189.paperCount_lt_11883
#print axioms BstLean.Part189.paperCount_lt_12225
#print axioms BstLean.Part189.paperCount_lt_13225
#print axioms BstLean.Part189.paperCount_lt_13483
#print axioms BstLean.Part189.paperCount_lt_14152
#print axioms BstLean.Part189.paperCount_lt_15324
#print axioms BstLean.Part189.paperCount_lt_15469
#print axioms BstLean.Part189.oddAsinLength_le
#print axioms BstLean.Part189.oddPiLength_le
#print axioms BstLean.Part189.worldPiLength_spec
#print axioms BstLean.Part189.worldKappaLength_spec
#print axioms BstLean.Part189.worldConstantCount_le
#print axioms BstLean.Part189.binomialSetup_cost
#print axioms BstLean.Part189.binomialSetupConstant_cost
#print axioms BstLean.Part189.twoMomentAtom_cost
#print axioms BstLean.Part189.worldWork_cost
#print axioms BstLean.Part189.worldWork_le
#print axioms BstLean.Part189.agentWork_cost
#print axioms BstLean.Part189.agentWork_le
#print axioms BstLean.Part189.sphereRowWork_even
#print axioms BstLean.Part189.sphereRowWork_odd
#print axioms BstLean.Part189.sphereRowWork_le
#print axioms BstLean.Part189.nodeWork_cost
#print axioms BstLean.Part189.nodeWork_le
#print axioms BstLean.Part189.gridWork_le
#print axioms BstLean.Part189.setupWork_cost
#print axioms BstLean.Part189.drawWork_cost
#print axioms BstLean.Part189.outputWork_cost
#print axioms BstLean.Part189.orderedWork_cost
#print axioms BstLean.Part189.orderedWork_le
#print axioms BstLean.Part189.agentReference_cost
#print axioms BstLean.Part189.classifierReference_cost
#print axioms BstLean.Part189.searchIterations_le
#print axioms BstLean.Part189.searchPrice_le
#print axioms BstLean.Part189.latitudeCount_le
#print axioms BstLean.Part189.conversionCount_le
#print axioms BstLean.Part189.drawExtraCount_le
#print axioms BstLean.Part189.exactSampleCount_eq
#print axioms BstLean.Part189.exactSampleCount_ge
#print axioms BstLean.Part189.comparison_1139
#print axioms BstLean.Part189.orderedWork_lt_8000
#print axioms BstLean.Part189.paperCount_lt_integer
#print axioms BstLean.Part189.comparison_ratio
