import BstLean.Part219Pointwise

/-! The ideal average splits at a fixed kernel argument before any probability payment. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200 BstLean.Part215
open BstLean.Part29 (stdGauss)

noncomputable def kernelSlope (r : ℝ) : ℝ :=
  BstLean.Part145.kg (kappa r) * BstLean.Part145.kg r

lemma kernelSlope_nonneg (r : ℝ) : 0 ≤ kernelSlope r :=
  mul_nonneg (BstLean.Part145.kg_nonneg _) (BstLean.Part145.kg_nonneg _)

lemma kernelSlope_le_one (r : ℝ) : kernelSlope r ≤ 1 := by
  have h := mul_le_mul (BstLean.Part145.kg_le_one (kappa r))
    (BstLean.Part145.kg_le_one r) (BstLean.Part145.kg_nonneg r) zero_le_one
  simpa only [kernelSlope, mul_one] using h

lemma continuous_kernelSlope : Continuous kernelSlope := by
  unfold kernelSlope BstLean.Part145.kg
  exact ((continuous_const.sub (continuous_arccos.comp continuous_kappa)).div_const π).mul
    ((continuous_const.sub continuous_arccos).div_const π)

/-- The tangent length is exact, including coincident and opposite unit inputs. -/
theorem projected_unit_length {n : ℕ} {x z : Fin n → ℝ}
    (hx : normSq x = 1) (hz : normSq z = 1) :
    nrm (projT x *ᵥ z) = √(1 - (x ⬝ᵥ z) ^ 2) := by
  unfold nrm
  congr 1
  rw [projT_mulVec_sj, normSq_sub_smul, hx, hz, dotProduct_comm z x]
  ring

noncomputable def idealRemainder {n : ℕ} (q : ℝ) (x z : Fin n → ℝ) : Fin n → ℝ :=
  (kernelSlope (x ⬝ᵥ z) - kernelSlope q) • (projT x *ᵥ z)

lemma pairIdeal_split {n : ℕ} (q : ℝ) (x z : Fin n → ℝ) :
    BstLean.Part200.pairIdeal x z =
      kernelSlope q • (projT x *ᵥ z) + idealRemainder q x z := by
  unfold BstLean.Part200.pairIdeal idealRemainder kernelSlope
  rw [← add_smul]
  congr 1
  ring

theorem idealRemainder_length {n : ℕ} (q : ℝ) {x z : Fin n → ℝ}
    (hx : normSq x = 1) (hz : normSq z = 1) :
    nrm (idealRemainder q x z) =
      |kernelSlope (x ⬝ᵥ z) - kernelSlope q| * √(1 - (x ⬝ᵥ z) ^ 2) := by
  rw [idealRemainder, nrm_smul, projected_unit_length hx hz]

lemma idealRemainder_le_one {n : ℕ} (q : ℝ) {x z : Fin n → ℝ}
    (hx : normSq x = 1) (hz : normSq z = 1) :
    nrm (idealRemainder q x z) ≤ 1 := by
  have hc : |kernelSlope (x ⬝ᵥ z) - kernelSlope q| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [kernelSlope_nonneg (x ⬝ᵥ z), kernelSlope_nonneg q,
      kernelSlope_le_one (x ⬝ᵥ z), kernelSlope_le_one q]
  have ht : nrm (projT x *ᵥ z) ≤ 1 := by
    simpa only [nrm, hz, sqrt_one] using nrm_projT_le hx z
  rw [idealRemainder, nrm_smul]
  exact (mul_le_mul hc ht (nrm_nonneg _) zero_le_one).trans_eq (by ring)

lemma continuous_idealRemainder {n : ℕ} (q : ℝ) (x : Fin n → ℝ) :
    Continuous (idealRemainder q x) := by
  unfold idealRemainder
  have hd : Continuous (fun z : Fin n → ℝ => x ⬝ᵥ z) := by
    unfold dotProduct
    fun_prop
  exact ((continuous_kernelSlope.comp hd).sub continuous_const).smul
    (continuous_const.matrix_mulVec continuous_id)

lemma integrable_standPoint {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (standPoint c τ) (stdGauss (Fin n)) := by
  have hnrm : Integrable (fun z => nrm (standPoint c τ z)) (stdGauss (Fin n)) := by
    have he : (fun z => nrm (standPoint c τ z)) = fun _ => (1 : ℝ) := by
      funext z
      simp only [nrm, standPoint, normSq_sphPt hn, sqrt_one]
    rw [he]
    exact integrable_const _
  exact integrable_vector_of_nrm (measurable_standPoint c τ) hnrm

noncomputable def inputMean {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Fin n → ℝ :=
  ∫ z, standPoint c τ z ∂stdGauss (Fin n)

lemma integral_matrix {X : Type*} [MeasurableSpace X] {μ : Measure X} {n m : ℕ}
    (J : Matrix (Fin m) (Fin n) ℝ) {f : X → Fin n → ℝ} (hf : Integrable f μ) :
    (∫ z, J *ᵥ f z ∂μ) = J *ᵥ (∫ z, f z ∂μ) := by
  let T : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toLinearMap := Matrix.mulVecLin J
      cont := continuous_const.matrix_mulVec continuous_id }
  exact T.integral_comp_comm hf

/-- The split uses the actual mean under the same normalized Gaussian input distribution. -/
theorem ideal_average_split {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ q : ℝ)
    (ξ : Fin n → ℝ) :
    idealInputAverage c τ ξ = kernelSlope q • (projT (standPoint c τ ξ) *ᵥ inputMean c τ) +
      ∫ z, idealRemainder q (standPoint c τ ξ) (standPoint c τ z) ∂stdGauss (Fin n) := by
  set x := standPoint c τ ξ
  have hx : normSq x = 1 := normSq_sphPt hn _
  have hR := (continuous_idealRemainder q x).measurable.comp (measurable_standPoint c τ)
  have hRN : Integrable (fun z => nrm (idealRemainder q x (standPoint c τ z)))
      (stdGauss (Fin n)) :=
    Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hR).sqrt.aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
        exact idealRemainder_le_one q hx (normSq_sphPt hn _))
  have hRi := integrable_vector_of_nrm hR hRN
  let T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    { toLinearMap := Matrix.mulVecLin (projT x)
      cont := continuous_const.matrix_mulVec continuous_id }
  have hPi := T.integrable_comp (integrable_standPoint hn c τ)
  have hsum := integral_add (hPi.smul (kernelSlope q)) hRi
  change (∫ z, kernelSlope q • (projT x *ᵥ standPoint c τ z) +
    idealRemainder q x (standPoint c τ z) ∂stdGauss (Fin n)) = _ at hsum
  simp_rw [← pairIdeal_split] at hsum
  change idealInputAverage c τ ξ =
    (∫ z, kernelSlope q • (projT x *ᵥ standPoint c τ z) ∂stdGauss (Fin n)) +
      ∫ z, idealRemainder q x (standPoint c τ z) ∂stdGauss (Fin n) at hsum
  rw [integral_smul, integral_matrix _ (integrable_standPoint hn c τ)] at hsum
  exact hsum

/-- The uncharged remainder retains the exact scalar weighted secant integrand. -/
theorem ideal_average_remainder_bound {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) (τ q : ℝ)
    (ξ : Fin n → ℝ) :
    nrm (idealInputAverage c τ ξ -
      kernelSlope q • (projT (standPoint c τ ξ) *ᵥ inputMean c τ)) ≤
    ∫ z, |kernelSlope (standPoint c τ ξ ⬝ᵥ standPoint c τ z) - kernelSlope q| *
      √(1 - (standPoint c τ ξ ⬝ᵥ standPoint c τ z) ^ 2) ∂stdGauss (Fin n) := by
  set x := standPoint c τ ξ
  have hx : normSq x = 1 := normSq_sphPt hn _
  have hR := (continuous_idealRemainder q x).measurable.comp (measurable_standPoint c τ)
  have hRN : Integrable (fun z => nrm (idealRemainder q x (standPoint c τ z)))
      (stdGauss (Fin n)) :=
    Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hR).sqrt.aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
        exact idealRemainder_le_one q hx (normSq_sphPt hn _))
  rw [ideal_average_split hn c τ q ξ, add_sub_cancel_left]
  have h := nrm_integral_le (integrable_vector_of_nrm hR hRN) hRN
  refine h.trans_eq ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => idealRemainder_length q hx (normSq_sphPt hn _)

#print axioms projected_unit_length
#print axioms ideal_average_split
#print axioms ideal_average_remainder_bound
end BstLean.Part219
