import BstLean.Part216PlaneEnergy
import BstLean.Part216WeightedEnergy
import BstLean.Part170DecW

/-! Complete rows give the centred energy of an assembled Gaussian matrix. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170 BstLean.Part202 BstLean.Part216
open BstLean.Part184 (rowE rowG)

variable {V P : Type*} [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ρ : Measure P} [IsProbabilityMeasure ρ] {d m : ℕ}
variable {a : V → Fin d → ℝ} {ell : ℝ}

noncomputable def matrixEnergyError (μ : Measure V) (a : V → Fin d → ℝ)
    (ψ : ℝ → ℝ) {N : ℕ} (M : (Fin N → Fin d → ℝ)) : ℝ :=
  ∑ j, ((∫ v, relu (M j ⬝ᵥ a v) ^ 2 ∂μ) - ψ (M j ⬝ᵥ vmean μ a))

noncomputable def assembledMatrix (S : RowSplit μ ρ a m ell) {N : ℕ}
    (y : Fin N → P × (Fin m → ℝ)) : (Fin N → Fin d → ℝ) :=
  fun j => S.assemble (y j)

lemma assembledMatrix_gaussian (S : RowSplit μ ρ a m ell) (N : ℕ) :
    Measure.map (assembledMatrix S)
      (Measure.pi fun _ : Fin N => ρ.prod (stdGauss (Fin m))) =
        Measure.pi (fun _ : Fin N => stdGauss (Fin d)) := by
  change Measure.map (fun y : Fin N → P × (Fin m → ℝ) => fun j => S.assemble (y j))
    (Measure.pi fun _ : Fin N => ρ.prod (stdGauss (Fin m))) =
      Measure.pi (fun _ : Fin N => stdGauss (Fin d))
  rw [Measure.pi_map_pi (μ := fun _ : Fin N => ρ.prod (stdGauss (Fin m)))
    (hμ := fun _ => by rw [S.gaussian_assemble]; infer_instance)
    (fun _ => S.measurable_assemble.aemeasurable)]
  simp_rw [S.gaussian_assemble]

lemma row_assembled_mean (S : RowSplit μ ρ a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (ξ : P) (η : Fin m → ℝ) :
    S.assemble (ξ, η) ⬝ᵥ vmean μ a = ∫ v, S.c ξ v ∂μ := by
  obtain ⟨Kc, hKc⟩ := S.bounded_c ξ
  obtain ⟨Kw, hKw⟩ := S.bounded_w
  have hc : Measurable (S.c ξ) := S.measurable_c.of_uncurry_left
  have hi : Integrable (S.c ξ) μ :=
    (integrable_const Kc).mono' hc.aestronglyMeasurable
      (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hKc v)
  have hw : Integrable (fun v => η ⬝ᵥ S.w v) μ :=
    int_comp_bdd S.measurable_w hKw (continuous_const.dotProduct continuous_id)
  rw [← int_dot ha hK]
  simp_rw [← S.row_identity]
  rw [integral_add hi hw, int_dot S.measurable_w hKw]
  have hz : vmean μ S.w = 0 := funext S.mean_w
  rw [hz, dotProduct_zero, add_zero]

lemma rowEnergy_integrable (S : RowSplit μ ρ a m ell) (ξ : P) :
    Integrable (rowE μ (S.c ξ) S.w 1) (stdGauss (Fin m)) := by
  obtain ⟨Kc, hKc⟩ := S.bounded_c ξ
  obtain ⟨Kw, hKw⟩ := S.bounded_w
  have hc : Measurable (S.c ξ) := S.measurable_c.of_uncurry_left
  simpa only [pow_one] using BstLean.Part184.rowE_pow_integrable hc S.measurable_w
    hKc hKw S.mean_w (sq_nonneg ell) S.covariance_w (by norm_num : (0 : ℝ) ≤ 1) 1

lemma matrixEnergyError_rows (S : RowSplit μ ρ a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (ψ : ℝ → ℝ) {N : ℕ}
    (y : Fin N → P × (Fin m → ℝ)) :
    matrixEnergyError μ a ψ (assembledMatrix S y) =
      ∑ j, (rowE μ (S.c (y j).1) S.w 1 (y j).2 - ψ (∫ v, S.c (y j).1 v ∂μ)) := by
  unfold matrixEnergyError assembledMatrix
  apply Finset.sum_congr rfl
  intro j _
  rw [row_assembled_mean S ha hK]
  unfold rowE rowG
  simp only [sqrt_one, one_mul, S.row_identity]

/-- The Gaussian stand-in term cancels inside the conditional mean.
This identity permits any stand-in function of the retained first-layer mean. -/
theorem matrixEnergyError_centred (S : RowSplit μ ρ a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (ψ : ℝ → ℝ) {N : ℕ}
    (y : Fin N → P × (Fin m → ℝ)) :
    matrixEnergyError μ a ψ (assembledMatrix S y) -
      (∫ η, matrixEnergyError μ a ψ
        (assembledMatrix S (fun j => ((y j).1, η j)))
          ∂(Measure.pi fun _ : Fin N => stdGauss (Fin m))) = wholeRowSum S N y := by
  simp_rw [matrixEnergyError_rows S ha hK]
  have hi : ∀ j : Fin N, Integrable
      (fun η : Fin N → Fin m → ℝ => rowE μ (S.c (y j).1) S.w 1 (η j) -
        ψ (∫ v, S.c (y j).1 v ∂μ)) (Measure.pi fun _ : Fin N => stdGauss (Fin m)) := by
    intro j
    exact ((measurePreserving_eval (fun _ : Fin N => stdGauss (Fin m)) j).integrable_comp_of_integrable
      (rowEnergy_integrable S (y j).1)).sub (integrable_const _)
  rw [integral_finsetSum _ fun j _ => hi j, ← Finset.sum_sub_distrib]
  unfold wholeRowSum rowFluct
  apply Finset.sum_congr rfl
  intro j _
  have him : Integrable (fun η : Fin N → Fin m → ℝ => rowE μ (S.c (y j).1) S.w 1 (η j))
      (Measure.pi fun _ : Fin N => stdGauss (Fin m)) :=
    (measurePreserving_eval (fun _ : Fin N => stdGauss (Fin m)) j).integrable_comp_of_integrable
      (rowEnergy_integrable S (y j).1)
  rw [integral_sub him (integrable_const _), integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_comp_eval (μ := fun _ : Fin N => stdGauss (Fin m))
    (i := j) (rowEnergy_integrable S (y j).1).aestronglyMeasurable]
  ring

theorem matrixEnergyError_order18 (S : RowSplit μ ρ a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (ψ : ℝ → ℝ) (n : ℕ) :
    ∫⁻ y, ENNReal.ofReal (|matrixEnergyError μ a ψ (assembledMatrix S y) -
      (∫ η, matrixEnergyError μ a ψ (assembledMatrix S (fun j => ((y j).1, η j)))
        ∂(Measure.pi fun _ : Fin (n ^ 2) => stdGauss (Fin m)))| ^ 18)
      ∂(Measure.pi fun _ : Fin (n ^ 2) => ρ.prod (stdGauss (Fin m))) ≤
    ENNReal.ofReal ((rowScale μ a ell *
      (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
        BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18) := by
  simp_rw [matrixEnergyError_centred S ha hK]
  exact whole_sum_order18_width S ha hK n

#print axioms assembledMatrix_gaussian
#print axioms matrixEnergyError_centred
#print axioms matrixEnergyError_order18
end BstLean.Part223
