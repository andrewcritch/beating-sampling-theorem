import BstLean.Part215Actual

/-! The pair average is the tangent Jacobian applied to the actual hidden mean. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200
open BstLean.Part29 (stdGauss)

theorem pairInputError_integrable {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) (a : AgentPair n) (ξ : Fin n → ℝ) :
    Integrable (fun ξ' => pairInputError c τ a ξ ξ') (stdGauss (Fin n)) := by
  have hm : Measurable (fun ξ' => pairInputError c τ a ξ ξ') := by
    have h := (measurable_pairInputError c τ).comp
      (show Measurable (fun ξ' : Fin n → ℝ => ((a, ξ), ξ')) from
        measurable_const.prodMk measurable_id)
    simpa only [Function.comp_def] using h
  have hiN : Integrable (fun ξ' => nrm (pairInputError c τ a ξ ξ')) (stdGauss (Fin n)) :=
    Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hm).sqrt.aestronglyMeasurable
      _ (ae_of_all _ fun ξ' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
        exact pairInputError_le hn c τ a ξ ξ')
  exact integrable_vector_of_nrm hm hiN

theorem pairInputIdeal_integrable {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    Integrable (fun ξ' => pairIdeal (standPoint c τ ξ) (standPoint c τ ξ'))
      (stdGauss (Fin n)) := by
  have hm : Measurable (fun ξ' => pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')) := by
    have hp : Measurable (fun ξ' : Fin n → ℝ =>
        (standPoint c τ ξ, standPoint c τ ξ')) :=
      measurable_const.prodMk (measurable_standPoint c τ)
    have h := continuous_pairIdeal.measurable.comp
      hp
    simpa only [Function.comp_def] using h
  have hiN : Integrable (fun ξ' => nrm (pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')))
      (stdGauss (Fin n)) :=
    Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hm).sqrt.aestronglyMeasurable
      1 (ae_of_all _ fun ξ' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
        exact pairIdeal_le (normSq_sphPt hn _) (normSq_sphPt hn _))
  exact integrable_vector_of_nrm hm hiN

/-- This identity keeps the same two matrices at both inputs. -/
theorem mean_tangent_identity {n : ℕ} (hn : 1 ≤ n)
    (c : Fin n → ℝ) (τ : ℝ) (a : AgentPair n) (ξ : Fin n → ℝ) :
    inputErrorAverage c τ a ξ + idealInputAverage c τ ξ =
      (n : ℝ)⁻¹ • ((jacT a.1 a.2 (standPoint c τ ξ))ᵀ *ᵥ hid2Mean_cr a.1 a.2 c τ) := by
  have hE := pairInputError_integrable hn c τ a ξ
  have hI := pairInputIdeal_integrable hn c τ ξ
  have hsum := integral_add hE hI
  change (∫ ξ', pairInputError c τ a ξ ξ' +
    pairIdeal (standPoint c τ ξ) (standPoint c τ ξ') ∂stdGauss (Fin n)) =
    inputErrorAverage c τ a ξ + idealInputAverage c τ ξ at hsum
  rw [← hsum]
  have he : (fun ξ' => pairInputError c τ a ξ ξ' +
      pairIdeal (standPoint c τ ξ) (standPoint c τ ξ')) =
      fun ξ' => (n : ℝ)⁻¹ • pairVector a.1 a.2 (standPoint c τ ξ) (standPoint c τ ξ') := by
    funext ξ'
    unfold pairInputError
    abel
  rw [he]
  have hi : Integrable (fun ξ' => (n : ℝ)⁻¹ •
      pairVector a.1 a.2 (standPoint c τ ξ) (standPoint c τ ξ')) (stdGauss (Fin n)) := by
    rw [← he]
    exact hE.add hI
  ext i
  have hproj := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi
  change (∫ ξ', ((n : ℝ)⁻¹ • pairVector a.1 a.2
      (standPoint c τ ξ) (standPoint c τ ξ')) i ∂stdGauss (Fin n)) =
    (∫ ξ', (n : ℝ)⁻¹ • pairVector a.1 a.2
      (standPoint c τ ξ) (standPoint c τ ξ') ∂stdGauss (Fin n)) i at hproj
  rw [← hproj]
  simp only [Pi.smul_apply, smul_eq_mul, pairVector, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, standPoint]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun j _ =>
    (integrable_hid2_coord_cr hn a.1 a.2 c τ j).const_mul (jacT a.1 a.2 (sphPt (c + τ • ξ)) j i)]
  simp only [integral_const_mul, hid2Mean_cr, standPoint]

#print axioms mean_tangent_identity
end BstLean.Part215
