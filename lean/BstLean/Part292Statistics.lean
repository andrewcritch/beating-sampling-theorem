import BstLean.Part292Activation
import BstLean.Part292Frame
import BstLean.Part292Mixed

/-! Actual first-matrix fields at order 416, uniformly on the low band. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part172
open BstLean.Part170 (mkR tA)
open BstLean.Part171 (tA_nonneg)
open BstLean.Part161 (uHat xLat)
open BstLean.Part223

theorem paperPsi_moment832 {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (wr : WRet n) (hc : wr.2 ≠ 0) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    ∫⁻ A, ENNReal.ofReal (|paperPsi wr g i A v| ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal ((24933 / 10000 : ℝ) ^ 832) := by
  simp_rw [Even.pow_abs (by decide : Even 832)]
  apply latitude_first_layer1664 hn hn' hc hs hv
  · exact fun A => paperDirection_bound (by omega) wr g i A v
  · intro A A' hx hu hr
    exact congrArg (fun z => (sqrt (tA n))⁻¹ • z)
      (BstLean.Part220.statisticsField_admissible (by omega) wr hc g i v A A' hx hu hr)

theorem activationWeight_moment832 {n : ℕ} (hn : 8000 ≤ n) (wr : WRet n) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (v : Fin (n - 1) → ℝ) :
    ∫⁻ A, ENNReal.ofReal (|activationWeight wr g A v| ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal ((10103 / 10000 : ℝ) ^ 832) := by
  have hk : 0 ≤ (n : ℝ) * tA n / 2 := by
    have := tA_nonneg n
    positivity
  simp_rw [Even.pow_abs (by decide : Even 832), activationWeight, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg hk 832)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl (activation_even_moment (by norm_num : 1 ≤ (832 : ℕ))
    (normSq_xLat_le' (by omega) _ hs v) (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ)))).trans ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg hk 832), ← mul_pow]
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (by positivity) (activation_constant_band hn) 832

theorem paperWeight_moment832 {n : ℕ} (hn : 8000 ≤ n) (wr : WRet n) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3) (v : Fin (n - 1) → ℝ) :
    ∫⁻ A, ENNReal.ofReal (|paperWeight wr g i A v| ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal ((10103 / 10000 : ℝ) ^ 832) := by
  unfold paperWeight
  split_ifs
  · exact activationWeight_moment832 hn wr g hs v
  · simp only [abs_one, one_pow, ENNReal.ofReal_one, lintegral_one, measure_univ]
    simpa only [one_pow, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) ≤ 10103 / 10000) 832)

theorem paperField_moment416 {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (wr : WRet n) (hc : wr.2 ≠ 0) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    ∫⁻ A, ENNReal.ofReal (|paperField wr g i A v| ^ 416)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal ((251898099 / 100000000 : ℝ) ^ 416) := by
  unfold paperField
  have h := product_moment416 (gaussMat (mA n) n (2 / (n : ℝ)))
    (f := fun A => paperPsi wr g i A v) (g := fun A => paperWeight wr g i A v)
    (A := 24933 / 10000) (B := 10103 / 10000)
    (paperPsi_measurable wr g i).of_uncurry_right (paperWeight_measurable wr g i v)
    (by norm_num) (by norm_num) (paperPsi_moment832 hn hn' wr hc g hs i hv)
    (paperWeight_moment832 hn wr g hs i v)
  convert h using 1 <;> norm_num

theorem paperLatitude_moment416 {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (wr : WRet n) (hc : wr.2 ≠ 0) (g : ℕ)
    (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1) (i : Fin 3) :
    ∫⁻ A, latitudeStatistic416 (stdGauss (Fin (n - 1))) (paperField wr g i A)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤ ENNReal.ofReal ((251898099 / 100000000 : ℝ) ^ 416) := by
  apply latitudeStatistic416_moment _ _ (paperField_measurable wr g i)
  have hz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 := BstLean.Part168.stdGauss_zero (by omega : 1 ≤ n - 1)
    rw [ae_iff]
    simpa using h0
  filter_upwards [hz] with v hv
  exact paperField_moment416 hn hn' wr hc g hs i hv

end BstLean.Part292

/-- info: 'BstLean.Part292.paperLatitude_moment416' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.paperLatitude_moment416
