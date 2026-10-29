import BstLean.Part292ScalarBounds
import BstLean.Part292PlaneNorm
import BstLean.Part292Charge

/-! Uniform rational coefficient caps and the final order-104 row prices. -/
namespace BstLean.Part292
open Real MeasureTheory
open BstLean.Part213 BstLean.Part239 BstLean.Part228

theorem low_scalar_caps {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    locationA x ≤ 3587 / 10^6 ∧ locationB x ≤ 1253 / 10^6 ∧ locationC x ≤ 402 / 10^6 ∧
    energyA x ≤ 20342 / 10^7 ∧ energyB x ≤ 1605 / 10^6 ∧ energyC x ≤ 782 / 10^6 := by
  exact ⟨(locationA_bounds hx).2.trans (by norm_num),
    (locationB_bounds hx).2.trans (by norm_num),
    (locationC_bounds hx).2.trans (by norm_num),
    (energyA_bounds hx).2.trans (by norm_num),
    (energyB_bounds hx).2.trans (by norm_num),
    (energyC_bounds hx).2.trans (by norm_num)⟩

theorem low_scalar_guards {x : ℝ} (hx : Bounds x 0 (1/8000)) :
    (39106 / 10^5 : ℝ) ≤ qLower x ∧ qUpper x ≤ 60444 / 10^5 ∧
    lambdaScaled x ≤ 20242 / 10^4 ∧ sigmaScaled x ≤ 20003 / 10^4 ∧
    (70688 / 10^5 : ℝ) ≤ sigmaFloorScaled x ∧
    0 < gapScaled x ∧ exceptionalScaled x ≤ 8 * 10^14 ∧
    nodeMoment12 x ≤ 53274 / 10^5 := by
  exact ⟨(by linarith [(qLower_bounds hx).1]),
    (qUpper_bounds hx).2.trans (by norm_num),
    (lambdaScaled_bounds hx).2.trans (by norm_num),
    (sigmaScaled_bounds hx).2.trans (by norm_num),
    (by linarith [(sigmaFloorScaled_bounds hx).1]),
    (by linarith [(gapScaled_bounds hx).1]),
    (exceptionalScaled_bounds hx).2.trans (by norm_num),
    (nodeMoment12_bounds hx).2.trans (by norm_num)⟩

theorem rayleigh_mean_cap : sqrt (π / 2) ≤ 6267 / 5000 := by
  apply (sqrt_le_iff).mpr
  constructor
  · norm_num
  · nlinarith [pi_lt_d6]

theorem location_row_price_cap {a b c r : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hr0 : 0 ≤ r)
    (ha : a ≤ 36 / 10000) (hb : b ≤ 126 / 100000) (hc : c ≤ 41 / 100000)
    (hr : r ≤ (9 / 2) / 8000) :
    collectedSecond a b c + r * radiusPolynomialRoot104 a b c ^ 2 ≤
      (635 / 100000 : ℝ) ^ 2 := by
  have hsecond := collectedSecond_mono ha0 hb0 hc0 ha hb hc
  have hroot := radiusPolynomialRoot104_upper ha0 hb0 hc0
  have hroot' : radiusPolynomialRoot104 a b c ≤
      (36 / 10000 : ℝ) + (126 / 100000) * (6361 / 1000) + (41 / 100000) * 79 := by
    exact hroot.trans (by gcongr)
  have hsq := pow_le_pow_left₀ (radiusPolynomialRoot104_nonneg a b c) hroot' 2
  have hproduct := mul_le_mul hr hsq (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ (9 / 2) / 8000)
  have hsecond' : collectedSecond (36 / 10000) (126 / 100000) (41 / 100000) ≤
      (36 / 10000 : ℝ)^2 + 2*(36/10000)*(126/100000)*(6267/5000) +
      2*((126/100000)^2+2*(36/10000)*(41/100000)) +
      6*(126/100000)*(41/100000)*(6267/5000)+8*(41/100000)^2 := by
    unfold collectedSecond
    gcongr <;> exact rayleigh_mean_cap
  have hnum : ((36 / 10000 : ℝ)^2 + 2*(36/10000)*(126/100000)*(6267/5000) +
      2*((126/100000)^2+2*(36/10000)*(41/100000)) +
      6*(126/100000)*(41/100000)*(6267/5000)+8*(41/100000)^2) +
      ((9/2)/8000)*((36/10000)+(126/100000)*(6361/1000)+(41/100000)*79)^2 ≤
      (635/100000)^2 := by norm_num
  linarith

theorem energy_row_price_cap {a b c r : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hr0 : 0 ≤ r)
    (ha : a ≤ 205 / 100000) (hb : b ≤ 161 / 100000) (hc : c ≤ 79 / 100000)
    (hr : r ≤ (63 / 10) / 8000) :
    a + b * sqrt (π / 2) + 2*c + r * radiusPolynomialRoot104 a b c ≤ 575 / 100000 := by
  have hroot := radiusPolynomialRoot104_upper ha0 hb0 hc0
  have hroot' : radiusPolynomialRoot104 a b c ≤
      (205 / 100000 : ℝ) + (161 / 100000) * (6361 / 1000) + (79 / 100000) * 79 := by
    exact hroot.trans (by gcongr)
  have hproduct := mul_le_mul hr hroot' (radiusPolynomialRoot104_nonneg a b c)
    (by norm_num : (0 : ℝ) ≤ (63 / 10) / 8000)
  have hmean := mul_le_mul hb rayleigh_mean_cap (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 161 / 100000)
  have hnum : (205 / 100000 : ℝ) + (161 / 100000)*(6267/5000) + 2*(79/100000) +
      ((63/10)/8000)*((205/100000)+(161/100000)*(6361/1000)+(79/100000)*79) ≤ 575/100000 := by
    norm_num
  linarith

end BstLean.Part292

/-- info: 'BstLean.Part292.low_scalar_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.low_scalar_caps
