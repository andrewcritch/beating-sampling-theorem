import BstLean.Part209Tail

/-! Gaussian tail integration for nonnegative variables, including discontinuous counts. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part152

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem gaussian_tail_even_moment {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {L K : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (htail : ∀ t : ℝ, 0 < t → μ.real {ω | t < X ω} ≤ K * exp (-t ^ 2 / (2 * L ^ 2)))
    {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun ω => X ω ^ (2 * P)) μ ∧
    (∫ ω, X ω ^ (2 * P) ∂μ) ≤ K * (L ^ (2 * P) * (2 ^ P * (P.factorial : ℝ))) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P ≠ 0)
  let g : ℝ → ℝ := fun t => (2 * (q : ℝ) + 2) * t ^ (2 * q + 1)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g t := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact ae_of_all _ fun t ht => by dsimp [g]; have : 0 < t := ht; positivity
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μ (f := X) (g := g)
    (ae_of_all _ hX0) hX.aemeasurable (fun t _ => hg.intervalIntegrable _ _) hg0
  have hint : ∀ t : ℝ, ∫ u in (0 : ℝ)..t, g u = t ^ (2 * (q + 1)) := by
    intro t
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have he : ((2 * q + 1 : ℕ) : ℝ) + 1 = 2 * (q : ℝ) + 2 := by push_cast; ring
    rw [he, zero_pow (by omega), sub_zero, mul_div_cancel₀ _ (by positivity)]
    congr 1
  simp only [hint] at key
  obtain ⟨hiG, heG⟩ := gauss_moment_integral hL q
  let F : ℝ → ℝ := fun t => K * (exp (-t ^ 2 / (2 * L ^ 2)) * g t)
  have hFi : IntegrableOn F (Ioi 0) := hiG.const_mul K
  have hF0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ F t := by
    filter_upwards [hg0] with t ht
    exact mul_nonneg hK (mul_nonneg (exp_pos _).le ht)
  have hFe : (∫ t in Ioi (0 : ℝ), F t) =
      K * (L ^ (2 * (q + 1)) * (2 ^ (q + 1) * ((q + 1).factorial : ℝ))) := by
    rw [integral_const_mul, heG]
  have hb : (∫⁻ ω, ENNReal.ofReal (X ω ^ (2 * (q + 1))) ∂μ) ≤
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), F t) := by
    rw [key, ofReal_integral_eq_lintegral_ofReal hFi hF0]
    apply lintegral_mono_ae
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine ae_of_all _ fun t ht => ?_
    have ht' : 0 < t := ht
    rw [← ofReal_measureReal (μ := μ)]
    have h := mul_le_mul' (ENNReal.ofReal_le_ofReal (htail t ht'))
      (le_rfl : ENNReal.ofReal (g t) ≤ ENNReal.ofReal (g t))
    refine h.trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg hK (exp_pos _).le)]
    congr 1
    dsimp [F]
    ring
  have hi : Integrable (fun ω => X ω ^ (2 * (q + 1))) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hX.pow_const _).aestronglyMeasurable
      (ae_of_all _ fun ω => pow_nonneg (hX0 ω) _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => pow_nonneg (hX0 ω) _), hFe] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

end BstLean.Part209
