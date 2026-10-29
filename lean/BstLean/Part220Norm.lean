import BstLean.Part220Statistics
import BstLean.Part213Norm

/-! Order16 supplies imply order8 node bounds on measures with mass at most one. -/
namespace BstLean.Part220
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

theorem node_moment16_to8 {G : Type*} [MeasurableSpace G] (ν : Measure G)
    (hmass : ν Set.univ ≤ 1) {f : G → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B)
    (h16 : ∫⁻ g, ENNReal.ofReal (|f g| ^ 16) ∂ν ≤ ENNReal.ofReal (B ^ 16)) :
    ∫⁻ g, ENNReal.ofReal (|f g| ^ 8) ∂ν ≤ ENNReal.ofReal (B ^ 8) := by
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (f := f)
    (by norm_num : (8 : ℝ≥0∞) ≤ 16) hf.aestronglyMeasurable
  have hm : ν Set.univ ^ (1 / (8 : ℝ≥0∞).toReal - 1 / (16 : ℝ≥0∞).toReal) ≤ 1 := by
    calc
      _ ≤ (1 : ℝ≥0∞) ^ (1 / (8 : ℝ≥0∞).toReal - 1 / (16 : ℝ≥0∞).toReal) := by
        exact ENNReal.rpow_le_rpow hmass (by norm_num)
      _ = 1 := by simp
  have hn : eLpNorm f (8 : ℝ≥0∞) ν ≤ ENNReal.ofReal B := by
    refine hc.trans ((mul_le_mul' (BstLean.Part213.moment_norm_bound hf
      (by norm_num : (16 : ℕ) ≠ 0) hB h16) hm).trans ?_)
    simp
  have h := pow_le_pow_left' hn 8
  have he : eLpNorm f (8 : ℝ≥0∞) ν ^ (8 : ℕ) =
      ∫⁻ g, ENNReal.ofReal (|f g| ^ 8) ∂ν := by
    simpa using BstLean.Part153.eLpNorm_nat_pow (μ := ν)
      (by norm_num : (8 : ℕ) ≠ 0) hf.aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow hB] at h
  exact h

noncomputable def statisticsConstant (B : ℝ) : ℝ := (30000 : ℝ) ^ (64 : ℝ)⁻¹ * B

lemma statisticsConstant_pow (B : ℝ) : statisticsConstant B ^ 64 = 30000 * B ^ 64 := by
  have hp : ((30000 : ℝ) ^ (64 : ℝ)⁻¹) ^ (64 : ℕ) = 30000 := by
    simpa using Real.rpow_inv_natCast_pow (x := (30000 : ℝ)) (n := 64)
      (by norm_num) (by norm_num)
  rw [statisticsConstant, mul_pow, hp]

lemma statisticsConstant_pos {B : ℝ} (hB : 0 < B) : 0 < statisticsConstant B := by
  unfold statisticsConstant
  positivity

/-- The exact threshold spends one ten-thousandth on all three statistics. -/
lemma three_statistics_price {B : ℝ} (hB : 0 < B) :
    3 * (B / statisticsConstant B) ^ 64 = 1 / 10000 := by
  rw [div_pow, statisticsConstant_pow]
  field_simp [ne_of_gt hB]
  ring

/-- The actual bounded direction fields have a low-dimension event at charge one ten-thousandth. -/
theorem weighted_statistics_oneTenThousand {n q J : ℕ} (hn : 4 ≤ n) (hq : 1 ≤ q)
    (wr : BstLean.Part157.WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (node : Fin J → ℕ)
    (hs : ∀ g, BstLean.Part169.nodeS (BstLean.Part170.mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {H : ℝ}
    (hB : 0 < BstLean.Part172.fr_X n q (BstLean.Part170.tA n) * H)
    (hH : 0 ≤ H)
    (h64 : ∫⁻ g, ENNReal.ofReal
      ((1 - BstLean.Part169.nodeS (BstLean.Part170.mkR wr (0, 0)) (node g) ^ 2) ^ 64)
      ∂ν ≤ ENNReal.ofReal (H ^ 64)) :
    (BstLean.Part130.gaussMat (BstLean.Part130.mA n) n (2 / (n : ℝ))).real
      (⋃ i, momentBad (ν.prod (BstLean.Part29.stdGauss (Fin (n - 1))))
        (statisticsError wr node i) 64
        (statisticsConstant (BstLean.Part172.fr_X n q (BstLean.Part170.tA n) * H))) ≤
      1 / 10000 := by
  have h := weighted_statistics_charge64 hn hq wr hc ν node hs hH
    (statisticsConstant_pos hB) h64
  rwa [three_statistics_price hB] at h

#print axioms node_moment16_to8
#print axioms statisticsConstant_pow
#print axioms three_statistics_price
#print axioms weighted_statistics_oneTenThousand
end BstLean.Part220
