import BstLean.Part239WeightedRA

/-! Small rational caps for the plane-radius norms at orders 104 and 208. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part213 BstLean.Part239
open BstLean.Part223 (MomentBound)
open BstLean.Part186.RA (ρ2)
open BstLean.Part152

theorem planeRadius_even (j : ℕ) :
    ∫ p, planeRadius p ^ (2 * j) ∂ρ2 = 2 ^ j * (j.factorial : ℝ) := by
  rw [planeRadius_gamma]
  have he : (((2 * j : ℕ) : ℝ) + 2) / 2 = (j : ℝ) + 1 := by push_cast; ring
  rw [show -(((2 * j : ℕ) : ℝ) + 2) / 2 = -((j : ℝ) + 1) by rw [neg_div, he],
    he, Gamma_nat_eq_factorial, rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    rpow_add (by norm_num : (0 : ℝ) < 1 / 2), rpow_natCast, rpow_one]
  simp only [mul_inv_rev, inv_div, div_one, ← inv_pow, one_div, inv_inv]
  ring

theorem planeRadius_moment (j : ℕ) (hj : 1 ≤ j) :
    MomentBound ρ2 (2 * j) planeRadius (gaussMomConst j) := by
  refine ⟨BstLean.Part186.RA.measurable_RR.sqrt, gaussMomConst_nonneg _, ?_⟩
  have hnonneg (p : ℝ × ℝ) : 0 ≤ planeRadius p := sqrt_nonneg _
  simp_rw [abs_of_nonneg (hnonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (planeRadius_integrable _)
    (Filter.Eventually.of_forall fun _ => pow_nonneg (sqrt_nonneg _) _),
    planeRadius_even, gaussMomConst_pow hj]

theorem plane_norm104_cap : gaussMomConst 52 ≤ 6361 / 1000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (104 : ℕ) ≠ 0) (by norm_num)
  rw [gaussMomConst_pow (by norm_num : 1 ≤ (52 : ℕ))]
  norm_num [Nat.factorial]

theorem plane_norm208_squared_cap : gaussMomConst 104 ^ 2 ≤ 79 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (104 : ℕ) ≠ 0) (by norm_num)
  rw [← pow_mul, gaussMomConst_pow (by norm_num : 1 ≤ (104 : ℕ))]
  norm_num [Nat.factorial]

theorem radiusPolynomialRoot104_upper {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    radiusPolynomialRoot104 a b c ≤ a + b * (6361 / 1000) + c * 79 := by
  have hg52 := gaussMomConst_nonneg 52
  have hg104 := gaussMomConst_nonneg 104
  have h0 : MomentBound ρ2 104 (fun _ : ℝ × ℝ => a) a := by
    refine ⟨measurable_const, ha, ?_⟩
    simp [abs_of_nonneg ha]
  have h1 := ((planeRadius_moment 52 (by norm_num)).scale hb)
  have h2 := (((planeRadius_moment 104 (by norm_num)).power (k := 104) (r := 2)).scale hc)
  have h := (h0.add (by norm_num) h1).add (by norm_num) h2
  have hp : ∫⁻ p, ENNReal.ofReal (|radiusPolynomial a b c p| ^ 104) ∂ρ2 ≤
      ENNReal.ofReal ((a + b * gaussMomConst 52 + c * gaussMomConst 104 ^ 2) ^ 104) := by
    simpa only [radiusPolynomial] using h.moment
  rw [← radiusPolynomialRoot104_lintegral] at hp
  have hsum : 0 ≤ a + b * gaussMomConst 52 + c * gaussMomConst 104 ^ 2 :=
    add_nonneg (add_nonneg ha (mul_nonneg hb hg52)) (mul_nonneg hc (sq_nonneg _))
  have hr := (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hsum 104)).mp hp
  have hbnd := le_of_pow_le_pow_left₀ (by norm_num : (104 : ℕ) ≠ 0)
    hsum hr
  exact hbnd.trans (by gcongr <;> first | exact plane_norm104_cap | exact plane_norm208_squared_cap)

end BstLean.Part292

/-- info: 'BstLean.Part292.radiusPolynomialRoot104_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.radiusPolynomialRoot104_upper
