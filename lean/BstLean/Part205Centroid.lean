import BstLean.Part205Moments

/-! The normalized centre shift supplies the linear Taylor term. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137 BstLean.Part139

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (Q : ℝ) (g : Ω → Fin m → ℝ)

lemma normalized_linear_identity (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q) :
    (∫ p, pairCorr Q g p ∂μ.prod μ) - 2 * (∫ x, singleCorr μ Q g x ∂μ) +
      normSq (meanV μ g) / Q =
    normSq (meanV μ (normalizeInput Q g) - meanV μ g) / Q := by
  have hz := normalizeInput_bm Q g hg hm hQ
  unfold pairCorr singleCorr
  rw [integral_div, integral_div, dotp_pair_mean μ (normalizeInput Q g) hz,
    dotp_mean_right μ (normalizeInput Q g) hz, normSq_sub_eq]
  ring

lemma normalized_centroid_bound (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q) :
    normSq (meanV μ (normalizeInput Q g) - meanV μ g) ≤ Q * radialNu μ Q g ^ 2 := by
  let z := normalizeInput Q g
  let a := radialWeight Q g
  have hz := normalizeInput_bm Q g hg hm hQ
  have ha := radialWeight_bm Q g hg
  have hi : ∀ j, Integrable (fun x => ((1 - a x) • z x) j ^ 2) μ := by
    intro j
    exact (((BM.const 1).sub ha).mul (hz j)).sq.integrable μ
  have h := radial_centroid_bound (μ := μ)
    (Filter.Eventually.of_forall (normalizeInput_normSq Q g hm hQ)) hi
  have hmEq : (fun j => ∫ x, ((1 - a x) • z x) j ∂μ) =
      meanV μ z - meanV μ g := by
    ext j
    have he : (fun x => ((1 - a x) • z x) j) = fun x => z x j - g x j := by
      funext x
      have hf := congrFun (normalizeInput_factor Q g hQ x) j
      simp only [Pi.smul_apply, smul_eq_mul] at hf ⊢
      dsimp [a, z] at *
      linarith
    rw [he, integral_sub ((hz j).integrable μ) ((hg j).integrable μ)]
    rfl
  rw [hmEq] at h
  have he : (fun x => (a x - 1) ^ 2) = fun x => (1 - a x) ^ 2 := by funext x; ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (radial_L2 μ Q g hg hQ).le hQ.le)

lemma original_mean_energy_le (hg : ∀ j, BM (fun x => g x j))
    (hQeq : ∫ x, normSq (g x) ∂μ = Q) : normSq (meanV μ g) ≤ Q := by
  rw [← hQeq]
  exact vector_mean_sq_le (fun j => (hg j).sq.integrable μ)

/-- The full unweighted term is bounded by the pair Taylor remainder and the centroid shift. -/
theorem normalized_unweighted_mean (hg : ∀ j, BM (fun x => g x j)) (hm : 1 ≤ m) (hQ : 0 < Q)
    (hQeq : ∫ x, normSq (g x) ∂μ = Q)
    (hr0 : 0 < normSq (meanV μ g) / Q) (hr1 : normSq (meanV μ g) / Q < 1 / 2) :
    (∫ p, BstLean.Part130.kappa (pairCorr Q g p) ∂μ.prod μ) -
      2 * (∫ x, BstLean.Part130.kappa (singleCorr μ Q g x) ∂μ) +
      BstLean.Part130.kappa (normSq (meanV μ g) / Q) ≤
    endpointK (normSq (meanV μ g) / Q) *
      (√(covarianceT μ g Q) + √2 * radialNu μ Q g) ^ 2 +
        slopeK (normSq (meanV μ g) / Q) * radialNu μ Q g ^ 2 := by
  have hH := original_mean_energy_le μ Q g hg hQeq
  have hc := pairCorr_bm Q g hg hm hQ
  have hd := singleCorr_bm μ Q g hg hm hQ
  have h := unweighted_taylor_mean (μ := μ) hc.1 hd.1
    (Filter.Eventually.of_forall fun p => abs_le.mp (pairCorr_abs Q g hm hQ p))
    (Filter.Eventually.of_forall fun x => abs_le.mp (singleCorr_abs μ Q g hm hQ hH x)) hr0 hr1
  rw [normalized_linear_identity μ Q g hg hm hQ] at h
  have hs : normSq (meanV μ (normalizeInput Q g) - meanV μ g) / Q ≤ radialNu μ Q g ^ 2 := by
    exact (div_le_iff₀ hQ).mpr (by
      simpa [mul_comm] using normalized_centroid_bound μ Q g hg hm hQ)
  have hk := (BstLean.Part130.kappa_deriv_bounds (normSq (meanV μ g) / Q)).1
  change 0 ≤ slopeK (normSq (meanV μ g) / Q) at hk
  have hp := (normalized_pair_L2 μ Q g hg hm hQ hQeq).le
  have hK := endpointK_nonneg hr0 hr1
  have h1 := mul_le_mul_of_nonneg_left hs hk
  have h2 := mul_le_mul_of_nonneg_left hp hK
  linarith

end
end BstLean.Part205

#print axioms BstLean.Part205.normalized_centroid_bound
#print axioms BstLean.Part205.normalized_unweighted_mean
