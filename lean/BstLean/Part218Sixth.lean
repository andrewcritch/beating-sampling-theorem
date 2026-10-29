import BstLean.Part218Coupling
import BstLean.Part213Norm

/-! A sharp sixth-moment supply for the actual World row discrepancy. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part139 BstLean.Part205 BstLean.Part214

theorem sixth_from_coupling {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {D R : Ω → ℝ}
    (mR : Measurable R) (hR : ∀ x, 0 ≤ R x)
    (iR : Integrable (fun x => R x ^ 3) μ)
    (iD : Integrable (fun x => D x ^ 6) μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : (∫ x, R x ^ 3 ∂μ) ≤ a ^ 6)
    (hD : ∀ x, |D x| ≤ √(R x) + b) :
    √(∫ x, D x ^ 6 ∂μ) ≤ (a + b) ^ 3 := by
  have hp : ∀ x, |√(R x)| ^ 6 = R x ^ 3 := by
    intro x
    rw [abs_of_nonneg (sqrt_nonneg _), show (6 : ℕ) = 2 * 3 by decide,
      pow_mul, sq_sqrt (hR x)]
  have hr : (∫⁻ x, ENNReal.ofReal (|√(R x)| ^ 6) ∂μ) ≤ ENNReal.ofReal (a ^ 6) := by
    simp_rw [hp]
    rw [← ofReal_integral_eq_lintegral_ofReal iR (Filter.Eventually.of_forall fun x =>
      pow_nonneg (hR x) 3)]
    exact ENNReal.ofReal_le_ofReal hM
  have hc : (∫⁻ _ : Ω, ENNReal.ofReal (|b| ^ 6) ∂μ) ≤ ENNReal.ofReal (b ^ 6) := by
    simp [abs_of_nonneg hb]
  have hm := BstLean.Part213.moment_minkowski (mR.sqrt) measurable_const
    (by norm_num : 1 ≤ (6 : ℕ)) ha hb hr hc
  have h6 : ENNReal.ofReal (∫ x, D x ^ 6 ∂μ) ≤ ENNReal.ofReal ((a + b) ^ 6) := by
    rw [ofReal_integral_eq_lintegral_ofReal iD
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine (lintegral_mono fun x => ?_).trans hm
    apply ENNReal.ofReal_le_ofReal
    rw [← show |D x| ^ 6 = D x ^ 6 from Even.pow_abs (by decide) _]
    apply pow_le_pow_left₀ (abs_nonneg _)
    exact (hD x).trans (le_abs_self _)
  have h6R := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ (a + b) ^ 6)).mp h6
  apply (sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  convert h6R using 1 <;> ring

variable {N m : ℕ}

lemma centeredFirst_trace (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin N) ℝ) :
    (∑ i, ∫ u, centeredFirst M i u ^ 2 ∂uniformSphere N) = worldSigma M ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hc : ∀ i, Continuous (fun u : Fin N → ℝ => reluV (M.mulVec u) i) :=
    fun i => (continuous_apply i).comp (continuous_h1_u M)
  have he : ∀ i, (∫ u, centeredFirst M i u ^ 2 ∂uniformSphere N) =
      (∫ u, reluV (M.mulVec u) i ^ 2 ∂uniformSphere N) - h1bar M i ^ 2 := by
    intro i
    obtain ⟨_, h⟩ := integral_sq_sub_const (sphere_cont_integrable hN (hc i))
      (sphere_cont_integrable hN ((hc i).pow 2)) (h1bar M i)
    change (∫ u, centeredFirst M i u ^ 2 ∂uniformSphere N) = _ at h
    have hh : (∫ u, reluV (M.mulVec u) i ∂uniformSphere N) = h1bar M i := rfl
    rw [hh] at h
    nlinarith only [h]
  rw [worldSigma_sq hN hm, firstQ]
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact (integral_finsetSum _ (fun i _ => sphere_cont_integrable hN ((hc i).pow 2))).symm

/-- The bound uses the actual covariance Frobenius norm and includes zero covariance. -/
theorem rowDiscrepancy_sixth (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin N) ℝ) {F : ℝ} (hF : 0 ≤ F)
    (hFrob : (∑ i, ∑ j, (∫ u, centeredFirst M i u * centeredFirst M j u
      ∂uniformSphere N) ^ 2) ≤ F ^ 2) :
    √(∫ ξ, rowDiscrepancy M ξ ^ 6 ∂stdGauss (Fin m)) ≤
      (√(worldSigma M ^ 2 + 2 * F) + worldSigma M * √(2 / π)) ^ 3 := by
  have hs : 0 ≤ worldSigma M := by unfold worldSigma sS; positivity
  obtain ⟨hi, hb⟩ := gram_cubic_le (uniformSphere N) (centeredFirst M)
    (centeredFirst_memLp hN M) (centeredFirst_trace hN hm M) hF hFrob
  apply sixth_from_coupling (centeredGram_measurable hN M) (centeredGram_nonneg M)
    hi (rowDiscrepancy_six_integrable hN hm M) (sqrt_nonneg _) (by positivity)
    ?_ (rowDiscrepancy_coupling hN M)
  have hp : √(worldSigma M ^ 2 + 2 * F) ^ 6 = (worldSigma M ^ 2 + 2 * F) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, sq_sqrt (by positivity)]
  rw [hp]
  exact hb

end BstLean.Part218
#print axioms BstLean.Part218.rowDiscrepancy_sixth
