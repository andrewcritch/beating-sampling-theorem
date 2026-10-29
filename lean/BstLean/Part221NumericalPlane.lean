import BstLean.Part221PlaneMoment
import BstLean.Part221FirstLayerEvent

/-! Rational enclosures for the order-160 plane and first-layer factors. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part152 BstLean.Part209 BstLean.Part212

lemma gaussMomConst80_le_eight : gaussMomConst 80 ≤ 8 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 8)
  rw [show 160 = 2 * 80 from rfl, gaussMomConst_pow (by norm_num)]
  norm_num

lemma twoGaussConst40_le_six : twoGaussConst 40 ≤ 6 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 6)
  rw [show 80 = 2 * 40 from rfl, twoGaussConst_pow (by norm_num)]
  norm_num

theorem countPlaneSquared160_frontier {n : ℕ} (hn : 8000 ≤ n) :
    countPlaneSquared160 n ≤ 503 / 1000 * (n : ℝ) ^ 2 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : activeB n 40 ≤ 3 * (n : ℝ) := by
    unfold activeB
    have := mul_le_mul_of_nonneg_left twoGaussConst40_le_six
      (show (0 : ℝ) ≤ n / 2 by positivity)
    linarith
  have hn2 : 8000 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs : √((n : ℝ) ^ 2 / 2 + activeB n 40) ≤ 708 / 1000 * (n : ℝ) := by
    apply sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hb, hn2]
  have htwo : √(2 : ℝ) ≤ 3 / 2 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]
  have hsum : √((n : ℝ) ^ 2 / 2 + activeB n 40) + √2 + gaussMomConst 80 ≤
      1773 / 2500 * (n : ℝ) := by linarith [gaussMomConst80_le_eight]
  have hg0 := gaussMomConst_nonneg 80
  unfold countPlaneSquared160
  calc
    _ ≤ (1773 / 2500 * (n : ℝ)) ^ 2 := pow_le_pow_left₀
      (by positivity) hsum 2
    _ ≤ _ := by nlinarith [sq_nonneg (n : ℝ)]

theorem planeEigenMoment160_frontier {n : ℕ} (hn : 8000 ≤ n) :
    PlaneEigenMoment160 (mA n) (503 / 1000 * (n : ℝ) ^ 2) := by
  exact (planeEigenMoment160_count (by omega : 1 ≤ n)).trans
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (countPlaneSquared160_pos n).le
      (countPlaneSquared160_frontier hn) 80))

lemma exactRadiusSquared160_frontier {n : ℕ} (hn : 8000 ≤ n) :
    exactRadius (n - 1 - 1) 80 ^ 2 ≤ 10201 / 10000 := by
  have he : n - 1 - 1 = n - 2 := by omega
  rw [he]
  have hr0 : 0 ≤ exactRadius (n - 2) 80 := by
    unfold exactRadius
    exact div_nonneg (rpow_nonneg (radialProduct_pos (by omega : 1 ≤ n - 2) 80).le _)
      (sqrt_nonneg _)
  have h := pow_le_pow_left₀ hr0 (exactRadius_order160_frontier hn) 2
  norm_num at h ⊢
  exact h

theorem firstLayerSquared160_frontier {n : ℕ} (hn : 8000 ≤ n) :
    firstLayerSquared160 n (111 / 100 * (n : ℝ)) ≤ 453 / 200 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : firstLayerSquared160 n (111 / 100 * (n : ℝ)) =
      exactRadius (n - 1 - 1) 80 ^ 2 * (111 / 50) := by
    unfold firstLayerSquared160
    field_simp
    <;> ring
  rw [he]
  nlinarith only [exactRadiusSquared160_frontier hn]

theorem eigenPlaneSquared160_frontier {n : ℕ} (hn : 8000 ≤ n) :
    eigenPlaneSquared160 n (111 / 100 * (n : ℝ)) (503 / 1000 * (n : ℝ) ^ 2) ≤ 57 / 25 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : eigenPlaneSquared160 n (111 / 100 * (n : ℝ)) (503 / 1000 * (n : ℝ) ^ 2) =
      exactRadius (n - 1 - 1) 80 ^ 2 * (55833 / 25000) := by
    unfold eigenPlaneSquared160 mA
    push_cast
    field_simp
    <;> ring
  rw [he]
  nlinarith only [exactRadiusSquared160_frontier hn]

end BstLean.Part221
