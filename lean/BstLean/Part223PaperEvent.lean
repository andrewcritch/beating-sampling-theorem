import BstLean.Part223PaperConstant

/-! The paper's order256 threshold supplies the weighted event on 8000 through 16384. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part170 (tA mkR)
open BstLean.Part212 (exactRadius)
open BstLean.Part152 (gaussMomConst gaussMomConst_nonneg)
open BstLean.Part220

theorem frameConstant256_le_paperLJ {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 16384) :
    frameConstant256 n 2 1 ≤ paperLJ256 n ^ 2 := by
  have h := maximumFactor_le_paperSquare hn hn'
  have hc : 0 ≤ exactRadius (n - 1 - 1) 128 ^ 2 * (2 / (n : ℝ)) := by positivity
  have H := mul_le_mul_of_nonneg_left h hc
  unfold frameConstant256 paperLJ256
  rw [mul_pow, mul_pow, sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ))]
  norm_num only [Nat.cast_ofNat, mul_one] at H ⊢
  convert H using 1 <;> ring

theorem activationBound_eq_paperFactor {n : ℕ} (hn : 1 ≤ n) :
    activationBound n = paperActivationFactor n ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h20 : (0 : ℝ) < sqrt 2 := sqrt_pos.mpr (by norm_num)
  have ht : tA n = 2 / (n : ℝ) ^ 2 := by simp [tA, mA]
  have hs : sqrt ((mA n : ℝ) / 2) = (n : ℝ) / sqrt 2 := by
    rw [show (mA n : ℝ) = (n : ℝ) ^ 2 by simp [mA],
      sqrt_div (sq_nonneg _) _, sqrt_sq (Nat.cast_nonneg n)]
  have he : ((n : ℝ) * tA n / 2) * (2 / (n : ℝ)) = (sqrt 2 / (n : ℝ)) ^ 2 := by
    rw [ht, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [hn0.ne'] <;> ring
  calc
    activationBound n = (((n : ℝ) * tA n / 2) * (2 / (n : ℝ))) *
        (sqrt ((mA n : ℝ) / 2) + gaussMomConst 128) ^ 2 := by
      unfold activationBound
      ring
    _ = ((sqrt 2 / (n : ℝ)) * ((n : ℝ) / sqrt 2 + gaussMomConst 128)) ^ 2 := by
      rw [he, hs, mul_pow]
    _ = paperActivationFactor n ^ 2 := by
      congr 1
      unfold paperActivationFactor
      field_simp [hn0.ne', h20.ne'] <;> ring

lemma paperActivationFactor_ge_one (n : ℕ) : 1 ≤ paperActivationFactor n := by
  have hk := gaussMomConst_nonneg 128
  unfold paperActivationFactor
  have h : 0 ≤ sqrt 2 * gaussMomConst 128 / (n : ℝ) := by positivity
  linarith

theorem paperStatisticsBound_le_paperBound {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 16384) :
    paperStatisticsBound n 2 ≤ paperBound256 n := by
  have hact : 1 ≤ paperActivationFactor n ^ 2 := by
    have h := paperActivationFactor_ge_one n
    nlinarith
  unfold paperStatisticsBound paperBound256
  rw [activationBound_eq_paperFactor (by omega), max_eq_right hact]
  exact mul_le_mul_of_nonneg_right (frameConstant256_le_paperLJ hn hn') (sq_nonneg _)

/-- The paper coefficient pays the three weighted statistics once on the stated frontier range.
The fields retain the installed zero convention. -/
theorem paperCoefficient_statistics_oneTenThousand {n J : ℕ}
    (hn : 8000 ≤ n) (hn' : n ≤ 16384)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (paperStatisticsEvent wr ν node (statisticsConstant (paperBound256 n)))ᶜ ≤
        1 / 10000 := by
  have hbound := paperStatisticsBound_le_paperBound hn hn'
  have hp : 0 < paperBound256 n :=
    (paperStatisticsBound_pos (by omega : 4 ≤ n) (by norm_num : 1 ≤ 2)).trans_le hbound
  have hC := statisticsConstant_pos hp
  have h := paperStatistics_charge (by omega : 4 ≤ n) (by norm_num : 1 ≤ 2)
    wr hc ν hmass node hs hC
  refine h.trans ?_
  calc
    _ ≤ 3 * (paperBound256 n / statisticsConstant (paperBound256 n)) ^ 64 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀
        (div_nonneg (paperStatisticsBound_nonneg n 2) hC.le)
        (div_le_div_of_nonneg_right hbound hC.le) 64
    _ = 1 / 10000 := three_statistics_price hp

#print axioms frameConstant256_le_paperLJ
#print axioms activationBound_eq_paperFactor
#print axioms paperStatisticsBound_le_paperBound
#print axioms paperCoefficient_statistics_oneTenThousand
end BstLean.Part223
