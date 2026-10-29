import BstLean.Part198Phi
import BstLean.Part198Radial

/-! A sharp Gaussian row variance estimate with its radial cutoff integrated. -/
namespace BstLean.Part198
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part154
open BstLean.Part153 (rowLaw nrm nrm_sq PhiG)
open BstLean.Part160.MFB

theorem sharp_row_variance {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (hc : 0 < normSq c) {τ : ℝ} (hτ : 0 < τ)
    (b : Fin n → ℝ) {S0 : ℝ} (hS0 : 0 < S0) (hS : S0 ≤ (n : ℝ) - 2 * √((n : ℝ) * 12)) :
    Integrable (fun a => (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a))) (rowLaw n) ∧
    1 / 4 * (2 / (n : ℝ)) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ - rexp (-12) * normSq b) ≤
      ∫ a, (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℝ, s0 = 2 / (n : ℝ) * S0 := ⟨_, rfl⟩
  have hs0p : 0 < s0 := by rw [hs0]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = (2 / π) / (τ ^ 2 * s0) := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  obtain ⟨iD, eD⟩ := rl_dot2 hn b
  have hpm := meas_pR c τ
  have hGm : Measurable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2) := (meas_dot'_L1c b).pow_const 2
  have hBad : MeasurableSet {a : Fin n → ℝ | normSq a < s0} :=
    measurableSet_lt continuous_normSq.measurable measurable_const
  obtain ⟨ind, hind⟩ : ∃ ind : (Fin n → ℝ) → ℝ,
      ind = Set.indicator {a : Fin n → ℝ | normSq a < s0} (fun _ => (1 : ℝ)) := ⟨_, rfl⟩
  have hindm : Measurable ind := by rw [hind]; exact measurable_const.indicator hBad
  have hind01 : ∀ a, ind a = 0 ∨ ind a = 1 := by
    intro a; rw [hind]; by_cases h : a ∈ {a : Fin n → ℝ | normSq a < s0}
    · right; exact Set.indicator_of_mem h _
    · left; exact Set.indicator_of_notMem h _
  -- the pointwise bound
  have hpt : ∀ a : Fin n → ℝ, 1 / 4 * ((b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) -
      (b ⬝ᵥ a) ^ 2 * ind a) ≤ (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a)) := by
    intro a
    have h1 := PhiG_variance_lower (a ⬝ᵥ c / nrm (τ • a))
    have hG : 0 ≤ (b ⬝ᵥ a) ^ 2 := sq_nonneg _
    have h2 : rexp (-(μ * (a ⬝ᵥ c) ^ 2)) - ind a ≤ rexp (-(2 / π) * (a ⬝ᵥ c / nrm (τ • a)) ^ 2) := by
      by_cases hb : a ∈ {a : Fin n → ℝ | normSq a < s0}
      · have : ind a = 1 := by rw [hind]; exact Set.indicator_of_mem hb _
        rw [this]
        have h3 : rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by have := mul_nonneg hμ0.le (sq_nonneg (a ⬝ᵥ c)); linarith)
        have := Real.exp_pos (-(2 / π) * (a ⬝ᵥ c / nrm (τ • a)) ^ 2)
        linarith
      · have h0 : ind a = 0 := by rw [hind]; exact Set.indicator_of_notMem hb _
        rw [h0, sub_zero]
        have hA : s0 ≤ normSq a := not_lt.mp hb
        apply Real.exp_le_exp.mpr
        have ha0 : 0 < normSq a := hs0p.trans_le hA
        have hdiv := div_le_div_of_nonneg_left (sq_nonneg (a ⬝ᵥ c))
          (show 0 < τ ^ 2 * s0 by positivity)
          (mul_le_mul_of_nonneg_left hA (sq_nonneg τ))
        have hmul := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 2 / π by positivity)
        rw [div_pow, nrm_sq, normSq_smul, hμ]
        ring_nf at hmul ⊢
        linarith only [hmul]
    unfold pR
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (by linarith : rexp
      (-(2 / π) * (a ⬝ᵥ c / nrm (τ • a)) ^ 2) ≤ 4 * (PhiG (a ⬝ᵥ c / nrm (τ • a)) *
        (1 - PhiG (a ⬝ᵥ c / nrm (τ • a)))))) hG
    nlinarith
  -- integrability
  have hF1m : Measurable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2))) :=
    hGm.mul (Real.measurable_exp.comp ((((meas_dot_L1c c).pow_const 2).const_mul μ).neg))
  have iF1 : Integrable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)))
      (rowLaw n) := by
    refine Integrable.mono' iD hF1m.aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by have := mul_nonneg hμ0.le (sq_nonneg (a ⬝ᵥ c)); linarith)
  have iF2 : Integrable (fun a : Fin n → ℝ => (b ⬝ᵥ a) ^ 2 * ind a) (rowLaw n) := by
    refine Integrable.mono' iD (hGm.mul hindm).aestronglyMeasurable (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rcases hind01 a with h | h <;> rw [h] <;> norm_num
  have iT : Integrable (fun a => (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a))) (rowLaw n) := by
    refine Integrable.mono' iD (hGm.mul (hpm.mul (measurable_const.sub hpm))).aestronglyMeasurable
      (ae_of_all _ fun a => ?_)
    have hp0 := pR_nonneg c τ a
    have hp1 := pR_le_one c τ a
    have hq : 0 ≤ pR c τ a * (1 - pR c τ a) := mul_nonneg hp0 (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hq)]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    nlinarith
  refine ⟨iT, ?_⟩
  -- the main integral
  have hI1 : 2 / (n : ℝ) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
      (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹) ≤
      ∫ a, (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ∂rowLaw n := by
    rw [rl_int hF1m]
    have e : ∀ z : Fin n → ℝ, (b ⬝ᵥ (√(2 / (n : ℝ)) • z)) ^ 2 *
        rexp (-(μ * ((√(2 / (n : ℝ)) • z) ⬝ᵥ c) ^ 2)) =
        2 / (n : ℝ) * ((z ⬝ᵥ b) ^ 2 * rexp (-(μ * (2 / (n : ℝ)) * (z ⬝ᵥ c) ^ 2))) := by
      intro z
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, mul_pow, mul_pow,
        Real.sq_sqrt (by positivity), dotProduct_comm b z]
      have : μ * (2 / (n : ℝ) * (z ⬝ᵥ c) ^ 2) = μ * (2 / (n : ℝ)) * (z ⬝ᵥ c) ^ 2 := by ring
      rw [this]; ring
    simp_rw [e]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := gauss_weighted_lower c hc b (ν := μ * (2 / (n : ℝ))) (by positivity)
    have e2 : μ * (2 / (n : ℝ)) * normSq c = (2 / π) * normSq c / (τ ^ 2 * S0) := by
      rw [hμ, hs0]; field_simp
    rw [e2] at h
    exact h
  -- the bad set
  have hI2 : ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n ≤
      rexp (-12) * (2 / (n : ℝ) * normSq b) := by
    rw [hind, hs0]
    exact row_radial_cutoff_LM hn b hS0.le hS
  have hfin0 := integral_mono ((iF1.sub iF2).const_mul (1 / 4)) iT hpt
  have hc1 : ∫ a, 1 / 4 * ((b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) -
      (b ⬝ᵥ a) ^ 2 * ind a) ∂rowLaw n =
      1 / 4 * (∫ a, (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ∂rowLaw n -
        ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n) := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub iF1 iF2
  have hfin : 1 / 4 * (∫ a, (b ⬝ᵥ a) ^ 2 * rexp (-(μ * (a ⬝ᵥ c) ^ 2)) ∂rowLaw n -
        ∫ a, (b ⬝ᵥ a) ^ 2 * ind a ∂rowLaw n) ≤
      ∫ a, (b ⬝ᵥ a) ^ 2 * (pR c τ a * (1 - pR c τ a)) ∂rowLaw n := by
    rw [← hc1]; exact hfin0
  refine le_trans ?_ hfin
  have : 1 / 4 * (2 / (n : ℝ)) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹ - rexp (-12) * normSq b) =
      1 / 4 * (2 / (n : ℝ) * ((normSq b - (b ⬝ᵥ c) ^ 2 / normSq c) *
        (√(1 + 2 * ((2 / π) * normSq c / (τ ^ 2 * S0))))⁻¹) - rexp (-12) * (2 / (n : ℝ) * normSq b)) := by
    ring
  rw [this]
  linarith

#print axioms sharp_row_variance
end BstLean.Part198
