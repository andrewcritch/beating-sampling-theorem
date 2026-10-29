import BstLean.Part264FiniteCentre
import BstLean.Part264EnergyLower
import BstLean.Part263Coverage
/-! Actual 12226 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12226 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12226 12226 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12226.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12226 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12226 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12226 := gPlus_lower 12226
end BstLean.Part264
