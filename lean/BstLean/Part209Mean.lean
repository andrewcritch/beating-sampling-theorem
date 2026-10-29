import BstLean.Part209Matrix

/-! The closed conditional pair mean with the first layer fixed. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200
open BstLean.Part151 (mask jac maskedF)

variable {n m p : ℕ}

lemma measurable_pairMean (v : ℝ) (x x' : Fin n → ℝ) :
    Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => pairMean (p := p) v A₁ x x') :=
  (measurable_pairVector x x').stronglyMeasurable.integral_prod_right'.measurable

/-- The transpose of the masked first layer followed by the input tangent projection. -/
noncomputable def firstTangent (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin m) ℝ := (maskedF A₁ x * projT x)ᵀ

lemma jacT_row (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin p) (Fin m) ℝ)
    (x : Fin n → ℝ) (j : Fin p) (l : Fin n) :
    jacT A₁ A₂ x j l = mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) j) *
      (A₂ *ᵥ firstTangent A₁ x l) j := by
  simp only [jacT, jac, firstTangent, maskedF, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- Both features and both masks retain the same two weight matrices. -/
lemma pairVector_eq_sum (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ) (l : Fin n) :
    pairVector A₁ A₂ x x' l = ∑ j,
      mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) j) * (A₂ *ᵥ firstTangent A₁ x l) j *
        relu ((A₂ *ᵥ reluV (A₁ *ᵥ x')) j) := by
  change (∑ j, jacT A₁ A₂ x j l * hid2 A₁ A₂ x' j) = _
  simp only [jacT_row, hid2, reluV]

/-- Conditional integrability holds for all inputs, without a unit-length premise. -/
theorem pairVector_integrable {v : ℝ} (hv : 0 ≤ v)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) :
    Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ => pairVector A₁ A₂ x x')
      (gaussMat p m v) := by
  apply Integrable.of_eval
  intro l
  simp only [pairVector_eq_sum]
  exact integrable_finsetSum _ fun j _ => matrix_row_integrable hv _ _ _ j

/-- The paper conditional mean formula, for arbitrary finite widths and nonnegative variance.
Zero features use `kernelVector`'s zero convention. Nonzero parallel features are included. -/
theorem pairMean_closed {v : ℝ} (hv : 0 ≤ v)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) :
    pairMean (p := p) v A₁ x x' = ((p : ℝ) * v / 2) •
      (firstTangent A₁ x *ᵥ kernelVector (reluV (A₁ *ᵥ x)) (reluV (A₁ *ᵥ x'))) := by
  funext l
  have hi := pairVector_integrable (p := p) hv A₁ x x'
  have he := (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi
  change (∫ A₂ : Matrix (Fin p) (Fin m) ℝ, pairVector A₁ A₂ x x' l ∂gaussMat p m v) =
    pairMean (p := p) v A₁ x x' l at he
  rw [← he]
  simp_rw [pairVector_eq_sum]
  rw [matrix_pair_mean hv]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, dotp]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- At He variance, the second-layer width cancels exactly. -/
theorem pairMean_he (hp : 1 ≤ p) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) :
    pairMean (p := p) (2 / (p : ℝ)) A₁ x x' =
      firstTangent A₁ x *ᵥ kernelVector (reluV (A₁ *ᵥ x)) (reluV (A₁ *ᵥ x')) := by
  rw [pairMean_closed (by positivity)]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have he : (p : ℝ) * (2 / (p : ℝ)) / 2 = 1 := by field_simp
  rw [he, one_smul]

/-- The displayed closed formula for nonzero first-layer features. -/
theorem pairMean_he_nonzero (hp : 1 ≤ p) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) (ha : reluV (A₁ *ᵥ x) ≠ 0) :
    pairMean (p := p) (2 / (p : ℝ)) A₁ x x' = firstTangent A₁ x *ᵥ
      (kernelSlope (pairCos (reluV (A₁ *ᵥ x)) (reluV (A₁ *ᵥ x'))) • reluV (A₁ *ᵥ x') +
      (nrm (reluV (A₁ *ᵥ x')) / nrm (reluV (A₁ *ᵥ x)) *
        sqrt (1 - pairCos (reluV (A₁ *ᵥ x)) (reluV (A₁ *ᵥ x')) ^ 2) / π) •
          reluV (A₁ *ᵥ x)) := by
  rw [pairMean_he hp, kernelVector, if_neg ha]

/-- The centered vector is integrable for each fixed first layer. -/
theorem pairVector_centered_integrable {v : ℝ} (hv : 0 ≤ v)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) :
    Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ =>
      pairVector A₁ A₂ x x' - pairMean (p := p) v A₁ x x') (gaussMat p m v) :=
  (pairVector_integrable hv A₁ x x').sub (integrable_const _)

/-- Centering uses the exact conditional mean under the same second-layer distribution. -/
theorem pairVector_centered_mean {v : ℝ} (hv : 0 ≤ v)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) :
    (∫ A₂ : Matrix (Fin p) (Fin m) ℝ,
      pairVector A₁ A₂ x x' - pairMean (p := p) v A₁ x x' ∂gaussMat p m v) = 0 := by
  rw [integral_sub (pairVector_integrable hv A₁ x x') (integrable_const _)]
  simp [pairMean]

end BstLean.Part209
