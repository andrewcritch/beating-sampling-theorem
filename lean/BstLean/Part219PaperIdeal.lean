import BstLean.Part219IdealNorm
import BstLean.Part219PaperCoefficients

/-! The paper's deterministic ideal average, with its explicit constants. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (thetaC)
open BstLean.Part29 (stdGauss)

noncomputable def paperInputAllowance (n : ℕ) (θ : ℝ) : ℝ :=
  kernelSlope (1 - θ) * paperAmplitude n θ * latitudeAllowance n 12 θ +
    (77 / 100) * √(radiusCoefficient n 24 θ / n) *
      (√(radiusCoefficient n 1 θ / n) +
        paperAmplitude n θ * (BstLean.Part195.rotationConstant 24 * latitudeAllowance n 24 θ) +
        2 * paperBias n θ)

noncomputable def paperIdeal (n : ℕ) (θ e : ℝ) : ℝ :=
  kernelSlope (1 - θ) * paperAmplitude n θ * radiusCoefficient n 48 θ *
      √(1 + 47 / n) / √e +
    (77 / 100) * √(radiusCoefficient n 24 θ) / √e *
      (√(radiusCoefficient n 1 θ / n) + paperAmplitude n θ *
        BstLean.Part195.rotationConstant 24 * radiusCoefficient n 96 θ *
          √(1 + 95 / n) / √(n : ℝ) + 2 * paperBias n θ)

lemma nrm_smul_sphPt {n : ℕ} (c : Fin n → ℝ) : nrm c • sphPt c = c := by
  by_cases hc : normSq c = 0
  · have hz := normSq_eq_zero hc
    rw [hz]
    simp [nrm, normSq]
  · have hN : nrm c ≠ 0 := (sqrt_pos.mpr
      (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hc))).ne'
    rw [sphPt_eq' hc, smul_smul]
    change (nrm c * (1 / nrm c)) • c = c
    rw [mul_one_div_cancel hN, one_smul]

theorem ideal_norm_paper {n : ℕ} (hn : 195 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ)
    (hq : 1 - thetaC c τ ∈ Icc (0 : ℝ) (27 / 50)) :
    eLpNorm (idealSize c τ) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (paperInputAllowance n (thetaC c τ)) := by
  let u := sphPt c
  let a := nrm c
  have hu : normSq u = 1 := normSq_sphPt (by omega) c
  have ha : 0 ≤ a := nrm_nonneg c
  have hc : a • u = c := nrm_smul_sphPt c
  have hi := ideal_norm_actual_coefficient hn hu ha hτ (q := 1 - thetaC c τ)
    (by simpa only [hc] using hq)
  rw [hc] at hi
  have hα := inputMean_paper_amplitude (by omega) hu ha hτ
  have hb := inputMean_paper_square_bias (by omega) hu ha hτ
  rw [hc] at hα hb
  refine hi.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold idealAllowance paperInputAllowance
  have h12 := latitudeAllowance_nonneg (k := 12) (by omega) c hτ
  have h24 := latitudeAllowance_nonneg (k := 24) (by omega) c hτ
  have hmain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hα.2 (kernelSlope_nonneg (1 - thetaC c τ))) h12
  have hcentre := mul_le_mul_of_nonneg_right hα.2
    (mul_nonneg (BstLean.Part195.rotationConstant_nonneg 24) h24)
  have hbracket := add_le_add (add_le_add
    (le_refl (√(radiusCoefficient n 1 (thetaC c τ) / n))) hcentre) hb
  exact add_le_add hmain (mul_le_mul_of_nonneg_left hbracket
    (mul_nonneg (by norm_num) (sqrt_nonneg _)))

lemma paperInputAllowance_nonneg {n : ℕ} (hn : 195 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) : 0 ≤ paperInputAllowance n (thetaC c τ) := by
  have h12 := latitudeAllowance_nonneg (k := 12) (by omega) c hτ
  have h24 := latitudeAllowance_nonneg (k := 24) (by omega) c hτ
  have hR : 0 ≤ radiusCoefficient n 4 (thetaC c τ) := by
    have hh : 0 ≤ radiusCoefficient n 4 (thetaC c τ) / n := by
      rw [radiusCoefficient_identity (by omega) c hτ]
      have hnR : (10 : ℝ) < n := by exact_mod_cast (show 10 < n by omega)
      exact div_nonneg (sq_nonneg _) (add_nonneg (normSq_nonneg _)
        (mul_nonneg (by norm_num; linarith) (sq_nonneg _)))
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simpa only [zero_mul, div_mul_cancel₀ _ hnR.ne'] using
      mul_le_mul_of_nonneg_right hh hnR.le
  have ht := (theta_range (by omega) c hτ).1.le
  have hb : 0 ≤ paperBias n (thetaC c τ) := by unfold paperBias; positivity
  have hk := kernelSlope_nonneg (1 - thetaC c τ)
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperInputAllowance paperAmplitude
  positivity

theorem paperIdeal_identity {n : ℕ} (hn : 195 ≤ n) (c : Fin n → ℝ)
    {τ e : ℝ} (hτ : 0 < τ) (he : 0 < e) :
    √(n : ℝ) / √e * paperInputAllowance n (thetaC c τ) = paperIdeal n (thetaC c τ) e := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have hE : √e ≠ 0 := (sqrt_pos.mpr he).ne'
  have hR : 0 ≤ radiusCoefficient n 24 (thetaC c τ) := by
    have hh : 0 ≤ radiusCoefficient n 24 (thetaC c τ) / n := by
      rw [radiusCoefficient_identity (by omega) c hτ]
      have hn50 : (50 : ℝ) < n := by exact_mod_cast (show 50 < n by omega)
      exact div_nonneg (sq_nonneg _) (add_nonneg (normSq_nonneg _)
        (mul_nonneg (by norm_num; linarith) (sq_nonneg _)))
    simpa only [zero_mul, div_mul_cancel₀ _ hnR.ne'] using
      mul_le_mul_of_nonneg_right hh hnR.le
  unfold paperInputAllowance paperIdeal
  rw [latitudeAllowance_paper (by omega), latitudeAllowance_paper (by omega), sqrt_div hR]
  norm_num
  field_simp
  <;> ring

/-- This is the paper statement: the scaled order-24 ideal norm is at most D_main + D_rem. -/
theorem ideal_norm_paper_scaled {n : ℕ} (hn : 195 ≤ n) (c : Fin n → ℝ)
    {τ e : ℝ} (hτ : 0 < τ) (he : 0 < e)
    (hq : 1 - thetaC c τ ∈ Icc (0 : ℝ) (27 / 50)) :
    eLpNorm (fun x => (√(n : ℝ) / √e) * idealSize c τ x) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (paperIdeal n (thetaC c τ) e) := by
  rw [eLpNorm_mul_nonneg _ _ _ (by positivity)]
  have h := mul_le_mul_right (ideal_norm_paper hn c hτ hq) (ENNReal.ofReal (√(n : ℝ) / √e))
  rw [← ENNReal.ofReal_mul (by positivity), paperIdeal_identity hn c hτ he] at h
  exact h

#print axioms ideal_norm_paper
#print axioms paperIdeal_identity
#print axioms ideal_norm_paper_scaled
end BstLean.Part219
