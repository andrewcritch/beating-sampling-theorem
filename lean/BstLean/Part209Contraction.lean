import BstLean.Part209Mean

/-! The conditional mean contracts the second feature length. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

variable {n m p : ℕ}

lemma kernelSlope_add_radial_le (r : ℝ) :
    kernelSlope r + sqrt (1 - r ^ 2) / π ≤ 1 := by
  have h := Real.sin_le (Real.arccos_nonneg r)
  rw [Real.sin_arccos] at h
  unfold kernelSlope
  rw [← add_div, div_le_one Real.pi_pos]
  linarith

/-- The closed derivative vector has length at most the second feature length. -/
theorem kernelVector_le (a b : Fin m → ℝ) : nrm (kernelVector a b) ≤ nrm b := by
  by_cases ha : a = 0
  · subst a
    simpa [kernelVector_zero_left, nrm, normSq] using nrm_nonneg b
  have hna : nrm a ≠ 0 := (BstLean.Part132.nrm_pos_of_ne
    (fun h => ha (normSq_eq_zero h))).ne'
  have hc : 0 ≤ nrm b / nrm a * sqrt (1 - pairCos a b ^ 2) / π := by
    exact div_nonneg (mul_nonneg (div_nonneg (nrm_nonneg b) (nrm_nonneg a))
      (sqrt_nonneg _)) pi_pos.le
  have hk : 0 ≤ kernelSlope (pairCos a b) := (kappa_deriv_bounds _).1
  rw [kernelVector, if_neg ha]
  calc nrm (kernelSlope (pairCos a b) • b +
        (nrm b / nrm a * sqrt (1 - pairCos a b ^ 2) / π) • a)
      ≤ nrm (kernelSlope (pairCos a b) • b) +
          nrm ((nrm b / nrm a * sqrt (1 - pairCos a b ^ 2) / π) • a) := nrm_add_le _ _
    _ = (kernelSlope (pairCos a b) + sqrt (1 - pairCos a b ^ 2) / π) * nrm b := by
      rw [nrm_smul, nrm_smul, abs_of_nonneg hk, abs_of_nonneg hc]
      field_simp
      <;> ring
    _ ≤ nrm b := by
      simpa using mul_le_mul_of_nonneg_right (kernelSlope_add_radial_le (pairCos a b)) (nrm_nonneg b)

/-- This is the conditional middle-matrix contraction needed on the low-length complement. -/
theorem pairMean_he_le (hp : 1 ≤ p) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) :
    nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ≤
      opN (firstTangent A₁ x) * nrm (reluV (A₁ *ᵥ x')) := by
  rw [pairMean_he hp]
  exact (nrm_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_left (kernelVector_le _ _) (opN_nonneg _))

lemma firstTangent_eq_tanB (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    firstTangent A₁ x = (tanB A₁ x)ᵀ := by
  unfold firstTangent tanB
  congr 2
  ext i l
  simp [BstLean.Part151.maskedF, Matrix.diagonal_mul]

lemma opN_firstTangent_le (A₁ : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin n → ℝ} (hx : normSq x = 1) : opN (firstTangent A₁ x) ≤ opN A₁ := by
  rw [firstTangent_eq_tanB, opN_transpose]
  exact opN_tanB_le A₁ hx

/-- A first-layer envelope has no second-layer operator norm. -/
theorem pairMean_he_coarse_le (hp : 1 ≤ p) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    {x : Fin n → ℝ} (hx : normSq x = 1) (x' : Fin n → ℝ) :
    nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ≤ opN A₁ ^ 2 * nrm x' := by
  calc nrm (pairMean (p := p) (2 / (p : ℝ)) A₁ x x') ≤
      opN (firstTangent A₁ x) * nrm (reluV (A₁ *ᵥ x')) := pairMean_he_le hp A₁ x x'
    _ ≤ opN A₁ * (opN A₁ * nrm x') :=
      mul_le_mul (opN_firstTangent_le A₁ hx)
        ((nrm_reluV_le _).trans (nrm_mulVec_le _ _)) (nrm_nonneg _) (opN_nonneg _)
    _ = _ := by ring

end BstLean.Part209
