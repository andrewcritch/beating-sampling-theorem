import BstLean.Part264FiniteCentre
import BstLean.Part264EnergyLower
import BstLean.Part263Coverage
/-! Actual 12227 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part264b.N12227
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12227 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12227 12227 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12227.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12227 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12227 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12227 := gPlus_lower 12227
end BstLean.Part264b.N12227
