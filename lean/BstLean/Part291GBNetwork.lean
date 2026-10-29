import BstLean.Part291GBReal
import BstLean.Part291EnergyMoment
import BstLean.Part291WeightVariance

namespace BstLean.BlueprintLow
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part153 BstLean.Part157
open BstLean.Part160 BstLean.Part188 BstLean.Part229

theorem residualTest_energy_bound {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1) (ξ : Fin n → ℝ) :
    residualTest D c v ξ ^ 2 ≤ (n : ℝ) * inputEnergy D c ξ := by
  have h := sum_mul_sq_le (res (D.bA c.1 c.2.1.1) (hStand D c ξ)) v
  rw [hv, mul_one] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold inputEnergy
  rw [mul_div_cancel₀ _ hn0]
  exact h.trans (normSq_res_le _ _)

/-- GB for the actual capped residual test. The only second-moment input is
the unweighted residual second moment, supplied separately by covariance and
full-centre estimates. All derivative and energy moments are actual network fields. -/
theorem gb_network_cap {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1)
    {a d M H U : ℝ} (hd : 0 < d) (had : d ≤ a) (hU : 0 ≤ U)
    (hM : DirectionMoment D c M) (hH : EnergyMoment D c H)
    (hsecond : (∫ ξ, residualTest D c v ξ ^ 2 ∂stdGauss (Fin n)) ≤ U) :
    (∫ ξ, capEnergy a d (centreCoordinate D c) (residualTest D c v) ξ
      ∂stdGauss (Fin n)) ≤
      (U / d) ^ (41 / 45 : ℝ) *
        (((n : ℝ) / d) * ((a - d) / d ^ 2) ^ (45 / 4 : ℝ) *
          (((1 + H) ^ 32) ^ (1 / 16 : ℝ) *
            ((M / n) ^ 12) ^ (15 / 16 : ℝ))) ^ (4 / 45 : ℝ) := by
  let μ := stdGauss (Fin n)
  let f := centreCoordinate D c
  let z := residualTest D c v
  let g := BstLean.Part151.gradSq f
  let F := (a - d) / d ^ 2
  let V := fun ξ => weightSq a d (f ξ) * z ξ ^ 2
  let Z := fun ξ => F * g ξ
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hg := BstLean.Part151.measurable_gradSq f
  have hg0 : ∀ ξ, 0 ≤ g ξ := BstLean.Part151.gradSq_nonneg f
  have hfm : Measurable f := measurable_centreCoordinate D c
  obtain ⟨K, hK, hzm, hzb⟩ := residualTest_bound hn D c v
  have hqm : Measurable (fun ξ => weightSq a d (f ξ)) := by
    unfold weightSq
    fun_prop
  have hq0 : ∀ ξ, 0 ≤ weightSq a d (f ξ) := fun _ => weightSq_nonneg hd
  have hqi : ∀ ξ, weightSq a d (f ξ) ≤ 1 / d := fun _ => weightSq_le_inv hd
  have hVm : Measurable V := hqm.mul (hzm.pow_const 2)
  have hZm : Measurable Z := hg.const_mul F
  have hV0 : ∀ ξ, 0 ≤ V ξ := fun ξ => mul_nonneg (hq0 ξ) (sq_nonneg _)
  have hZ0 : ∀ ξ, 0 ≤ Z ξ := fun ξ => mul_nonneg hF (hg0 ξ)
  have hz2 : ∀ ξ, z ξ ^ 2 ≤ K ^ 2 := fun ξ => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hzb ξ) 2
  have hVB : ∀ ξ, V ξ ≤ (1 / d) * K ^ 2 := fun ξ =>
    mul_le_mul (hqi ξ) (hz2 ξ) (sq_nonneg _) (by positivity)
  have hiV : Integrable V μ := integrable_of_abs_bound μ hVm
    (fun ξ => by rw [abs_of_nonneg (hV0 ξ)]; exact hVB ξ)
  have hiz2 : Integrable (fun ξ => z ξ ^ 2) μ := integrable_of_abs_bound μ
    (hzm.pow_const 2) (fun ξ => by rw [abs_of_nonneg (sq_nonneg _)]; exact hz2 ξ)
  have hL : (∫ ξ, V ξ ∂μ) ≤ U / d := by
    have h := integral_mono hiV (hiz2.const_mul (1 / d))
      (fun ξ => mul_le_mul_of_nonneg_right (hqi ξ) (sq_nonneg _))
    rw [integral_const_mul] at h
    exact h.trans (by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      mul_le_mul_of_nonneg_left hsecond (show 0 ≤ (1 : ℝ) / d by positivity))
  have hVω : ∀ ξ, V ξ ≤ ((n : ℝ) / d) * inputEnergy D c ξ := by
    intro ξ
    have hh := mul_le_mul (hqi ξ) (residualTest_energy_bound hn D c v hv ξ)
      (sq_nonneg (z ξ)) (show 0 ≤ (1 : ℝ) / d by positivity)
    convert hh using 1 <;> ring
  have hω := inputEnergy_moment16 D c hH
  have hbound := gb_moment_bound_real μ V Z (inputEnergy D c) g
    hVm hZm (measurable_inputEnergy D c) hg hV0 hZ0
    (inputEnergy_nonneg D c) hg0 (by positivity) hF (by positivity)
    (by positivity) (by positivity) hVω (fun _ => le_rfl) hiV hω.1 hM.2.1 hL hω.2 hM.2.2
  have hig := (direction_gradient_first D c hM).1
  have hiVZ : Integrable (fun ξ => V ξ * Z ξ) μ := by
    apply Integrable.mono' (hig.const_mul ((1 / d) * K ^ 2 * F))
      (hVm.mul hZm).aestronglyMeasurable
    apply ae_of_all
    intro ξ
    rw [Real.norm_eq_abs]
    change |V ξ * Z ξ| ≤ ((1 / d) * K ^ 2 * F) * g ξ
    rw [abs_of_nonneg (mul_nonneg (hV0 ξ) (hZ0 ξ))]
    calc
      _ ≤ ((1 / d) * K ^ 2) * (F * g ξ) :=
        mul_le_mul_of_nonneg_right (hVB ξ) (hZ0 ξ)
      _ = _ := by ring
  have hcapm : Measurable (capEnergy a d f z) :=
    BstLean.Part130.measurable_normSq.comp ((hzm.mul ((capSlope_measurable a d).comp
      (measurable_centreCoordinate D c))).smul (gradientVector_measurable f))
  have hcap : ∀ ξ, capEnergy a d f z ξ ≤ V ξ * Z ξ := capEnergy_pointwise f z hd had
  have hicap : Integrable (capEnergy a d f z) μ := by
    apply hiVZ.mono' hcapm.aestronglyMeasurable
    exact ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ capEnergy a d f z ξ from normSq_nonneg _)]
      exact hcap ξ
  exact (integral_mono hicap hiVZ hcap).trans hbound

end BstLean.BlueprintLow
