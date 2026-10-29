import BstLean.Part205Weighted
import BstLean.Part205Row

/-! Identify the normalized weighted mean with the original conditional kernel difference. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137 BstLean.Part139

lemma kernelPhi_scale {k : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : Fin k → ℝ) :
    kernelPhi (a • x) (b • y) = a * b * kernelPhi x y := by
  have h0 : (∫ ξ, relu (dotp ξ x) * relu (dotp ξ y) ∂BstLean.Part29.stdGauss (Fin k)) =
      kernelPhi x y / 2 := by
    simpa [dotp] using (rowPair137 (by norm_num : (0 : ℝ) ≤ 1) x y).2.1
  have h1 : (∫ ξ, relu (dotp ξ (a • x)) * relu (dotp ξ (b • y))
      ∂BstLean.Part29.stdGauss (Fin k)) = kernelPhi (a • x) (b • y) / 2 := by
    simpa [dotp] using (rowPair137 (by norm_num : (0 : ℝ) ≤ 1) (a • x) (b • y)).2.1
  simp_rw [dotp_scale_right, relu_mul_of_nonneg ha, relu_mul_of_nonneg hb] at h1
  have he : (fun ξ => a * relu (dotp ξ x) * (b * relu (dotp ξ y))) =
      fun ξ => (a * b) * (relu (dotp ξ x) * relu (dotp ξ y)) := by funext ξ; ring
  rw [he, integral_const_mul, h0] at h1
  linarith

lemma kernelPhi_energy {k : ℕ} {Q : ℝ} (hQ : 0 ≤ Q) (x y : Fin k → ℝ)
    (hx : normSq x = Q) (hy : normSq y = Q) :
    kernelPhi x y = Q * kappa (dotp x y / Q) := by
  unfold kernelPhi
  rw [hx, hy, Real.mul_self_sqrt hQ]

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (g : Ω → Fin m → ℝ)

noncomputable def kernelDifference (σ : ℝ) : ℝ :=
  (∫ p : Ω × Ω, kernelPhi (g p.1) (g p.2) ∂μ.prod μ) -
    2 * (∫ x, kernelPhi (Fin.cons 0 (g x)) (Fin.cons σ (meanV μ g)) ∂μ) +
    kernelPhi (smoothP (meanV μ g) σ) (smoothP' (meanV μ g) σ)

lemma kernelDifference_weighted {Q σ : ℝ} (hm : 1 ≤ m) (hQ : 0 < Q)
    (hσ : normSq (meanV μ g) + σ ^ 2 = Q) :
    kernelDifference μ g σ = Q * weightedDelta μ Q g := by
  let z := normalizeInput Q g
  let a := radialWeight Q g
  have hnorm : ∀ x, normSq (z x) = Q := normalizeInput_normSq Q g hm hQ
  have hp : ∀ p : Ω × Ω, kernelPhi (g p.1) (g p.2) =
      Q * (a p.1 * a p.2 * kappa (pairCorr Q g p)) := by
    intro p
    rw [normalizeInput_factor Q g hQ p.1, normalizeInput_factor Q g hQ p.2,
      kernelPhi_scale (radialWeight_nonneg Q g hQ p.1) (radialWeight_nonneg Q g hQ p.2),
      kernelPhi_energy hQ.le _ _ (hnorm p.1) (hnorm p.2)]
    dsimp [a, pairCorr]
    ring
  have hc : ∀ x, kernelPhi (Fin.cons 0 (g x)) (Fin.cons σ (meanV μ g)) =
      Q * (a x * kappa (singleCorr μ Q g x)) := by
    intro x
    have hf : Fin.cons 0 (g x) = a x • (Fin.cons 0 (z x) : Fin (m + 1) → ℝ) := by
      have hgx := normalizeInput_factor Q g hQ x
      rw [hgx]
      ext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [a, z]
    have hn1 : normSq (Fin.cons 0 (z x)) = Q := by rw [normSq_cons, hnorm]; simp
    have hn2 : normSq (Fin.cons σ (meanV μ g)) = Q := by rw [normSq_cons]; linarith
    rw [hf, show (Fin.cons σ (meanV μ g)) = (1 : ℝ) • Fin.cons σ (meanV μ g) by simp,
      kernelPhi_scale (radialWeight_nonneg Q g hQ x) (by norm_num),
      kernelPhi_energy hQ.le _ _ hn1 hn2, dotp_cons]
    simp only [zero_mul, zero_add, mul_one]
    dsimp [a, z, singleCorr]
    ring
  have hs : kernelPhi (smoothP (meanV μ g) σ) (smoothP' (meanV μ g) σ) =
      Q * kappa (normSq (meanV μ g) / Q) := by
    rw [kernelPhi_energy hQ.le _ _
      (by rw [smoothP_normSq]; exact hσ) (by rw [smoothP'_normSq]; exact hσ), smoothing_dot]
  unfold kernelDifference weightedDelta
  simp_rw [hp, hc, hs]
  rw [integral_const_mul, integral_const_mul]
  ring

theorem kernel_mean_bound (hg : ∀ j, BM (fun x => g x j)) {Q σ : ℝ}
    (hm : 1 ≤ m) (hQ : 0 < Q) (hQeq : ∫ x, normSq (g x) ∂μ = Q)
    (hσ : normSq (meanV μ g) + σ ^ 2 = Q)
    (hr0 : 0 < normSq (meanV μ g) / Q) (hr1 : normSq (meanV μ g) / Q < 1 / 2) :
    kernelDifference μ g σ / Q ≤
      meanBound (normSq (meanV μ g) / Q) (covarianceT μ g Q) (radialNu μ Q g) := by
  rw [kernelDifference_weighted μ g hm hQ hσ, mul_div_cancel_left₀ _ hQ.ne']
  exact weighted_mean_bound μ Q g hg hm hQ hQeq hr0 hr1

end
end BstLean.Part205

#print axioms BstLean.Part205.kernelPhi_scale
#print axioms BstLean.Part205.kernel_mean_bound
