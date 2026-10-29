import BstLean.Part209Row

/-! The closed gated-row mean for the actual Gaussian matrix distribution. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)
open BstLean.Part151 (mask measurable_mask)

variable {d p : ℕ}

noncomputable def gatedRow (a b u w : Fin d → ℝ) : ℝ :=
  mask (dotp w a) * dotp w u * relu (dotp w b)

lemma measurable_gatedRow (a b u : Fin d → ℝ) : Measurable (gatedRow a b u) :=
  ((measurable_mask.comp (measurable_dot_left a)).mul (measurable_dot_left u)).mul
    (measurable_relu.comp (measurable_dot_left b))

lemma gatedRow_zero_left (b u w : Fin d → ℝ) : gatedRow 0 b u w = 0 := by
  simp [gatedRow, dotp, mask]

lemma kernelVector_zero_left (b : Fin d → ℝ) : kernelVector 0 b = 0 := by
  simp [kernelVector]

lemma gatedRow_smul {v : ℝ} (hv : 0 ≤ v) (a b u w : Fin d → ℝ) :
    gatedRow a b u (sqrt v • w) = v * gatedRow a b u w := by
  by_cases hv0 : v = 0
  · subst v
    simp [gatedRow, dotp, mask]
  have hsv : 0 < sqrt v := sqrt_pos.mpr (lt_of_le_of_ne hv (Ne.symm hv0))
  have hd : ∀ z : Fin d → ℝ, dotp (sqrt v • w) z = sqrt v * dotp w z := by
    intro z
    simp only [dotp, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
  simp only [gatedRow, hd, mask_mul_pos hsv, relu_mul_of_nonneg hsv.le]
  have hs := Real.sq_sqrt hv
  calc mask (dotp w a) * (sqrt v * dotp w u) * (sqrt v * relu (dotp w b)) =
      (sqrt v) ^ 2 * (mask (dotp w a) * dotp w u * relu (dotp w b)) := by ring
    _ = _ := by rw [hs]

lemma gatedRow_integrable (a b u : Fin d → ℝ) :
    Integrable (gatedRow a b u) (stdGauss (Fin d)) := by
  by_cases ha : a = 0
  · subst a
    have he : gatedRow 0 b u = fun _ => 0 := funext (gatedRow_zero_left b u)
    rw [he]
    exact integrable_const 0
  · exact (row_pair_derivative_integral ha b u).1

theorem gatedRow_mean (a b u : Fin d → ℝ) :
    (∫ w, gatedRow a b u w ∂stdGauss (Fin d)) = dotp (kernelVector a b) u / 2 := by
  by_cases ha : a = 0
  · subst a
    simp [gatedRow_zero_left, kernelVector_zero_left, dotp]
  · exact row_pair_mean ha b u

/-- Each row has an integrable gated derivative, including a zero first vector. -/
theorem matrix_row_integrable {v : ℝ} (hv : 0 ≤ v) (a b u : Fin d → ℝ) (j : Fin p) :
    Integrable (fun M : Matrix (Fin p) (Fin d) ℝ =>
      mask ((M *ᵥ a) j) * (M *ᵥ u) j * relu ((M *ᵥ b) j)) (gaussMat p d v) := by
  change Integrable (fun M => gatedRow a b u (rowOf j M)) (gaussMat p d v)
  apply (integrable_map_measure (measurable_gatedRow a b u).aestronglyMeasurable
    (measurable_rowOf j).aemeasurable).mp
  rw [gaussMat_row]
  apply (integrable_map_measure (measurable_gatedRow a b u).aestronglyMeasurable
    (measurable_const_smul _).aemeasurable).mpr
  change Integrable (fun w => gatedRow a b u (sqrt v • w)) (stdGauss (Fin d))
  simp_rw [gatedRow_smul hv]
  exact (gatedRow_integrable a b u).const_mul v

/-- The closed mean uses the actual variance and needs no nonzero feature premise. -/
theorem matrix_row_mean {v : ℝ} (hv : 0 ≤ v) (a b u : Fin d → ℝ) (j : Fin p) :
    (∫ M : Matrix (Fin p) (Fin d) ℝ,
      mask ((M *ᵥ a) j) * (M *ᵥ u) j * relu ((M *ᵥ b) j) ∂gaussMat p d v) =
      v / 2 * dotp (kernelVector a b) u := by
  change (∫ M, gatedRow a b u (rowOf j M) ∂gaussMat p d v) = _
  rw [← integral_map (measurable_rowOf j).aemeasurable
    (measurable_gatedRow a b u).aestronglyMeasurable, gaussMat_row,
    integral_map (measurable_const_smul _).aemeasurable
      (measurable_gatedRow a b u).aestronglyMeasurable]
  simp_rw [gatedRow_smul hv]
  rw [integral_const_mul, gatedRow_mean]
  ring

/-- Summing the shared-weight row means gives the conditional derivative contraction. -/
theorem matrix_pair_mean {v : ℝ} (hv : 0 ≤ v) (a b u : Fin d → ℝ) :
    (∫ M : Matrix (Fin p) (Fin d) ℝ,
      ∑ j, mask ((M *ᵥ a) j) * (M *ᵥ u) j * relu ((M *ᵥ b) j) ∂gaussMat p d v) =
      (p : ℝ) * v / 2 * dotp (kernelVector a b) u := by
  rw [integral_finsetSum _ (fun j _ => matrix_row_integrable hv a b u j)]
  simp_rw [matrix_row_mean hv]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end BstLean.Part209
