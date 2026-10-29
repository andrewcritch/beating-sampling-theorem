import BstLean.Part223Projection

/-! The energy moment transfers to a common original Gaussian matrix distribution. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170 BstLean.Part202 BstLean.Part216

variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
variable {d : ℕ} {a : V → Fin d → ℝ}

noncomputable def replaceMatrix {N : ℕ} (h g : Fin d → ℝ)
    (M η : (Fin N → Fin d → ℝ)) : (Fin N → Fin d → ℝ) :=
  fun j => replaceTransverse h g (M j) (η j)

noncomputable def canonicalEnergyFluct (μ : Measure V) (a : V → Fin d → ℝ)
    (h : Fin d → ℝ) (ψ : ℝ → ℝ) {N : ℕ} (M : (Fin N → Fin d → ℝ)) : ℝ :=
  matrixEnergyError μ a ψ M -
    ∫ η, matrixEnergyError μ a ψ (replaceMatrix h (vmean μ a) M η)
      ∂(Measure.pi fun _ : Fin N => stdGauss (Fin d))

lemma measurable_matrixEnergyError (ha : Measurable a) {ψ : ℝ → ℝ} (hψ : Measurable ψ)
    (N : ℕ) : Measurable (matrixEnergyError μ a ψ (N := N)) := by
  apply Finset.measurable_sum
  intro j _
  have hm : Measurable (fun p : (Fin N → Fin d → ℝ) × V =>
      relu (p.1 j ⬝ᵥ a p.2) ^ 2) :=
    (measurable_relu.comp (measurable_dot
      ((measurable_pi_apply j).comp measurable_fst) (ha.comp measurable_snd))).pow_const 2
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.sub
    (hψ.comp (measurable_dot (measurable_pi_apply j) measurable_const))

lemma measurable_canonicalEnergyFluct (ha : Measurable a) (h : Fin d → ℝ)
    {ψ : ℝ → ℝ} (hψ : Measurable ψ) (N : ℕ) :
    Measurable (canonicalEnergyFluct μ a h ψ (N := N)) := by
  have hrep : Measurable (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) =>
      replaceMatrix h (vmean μ a) p.1 p.2) := by
    apply Measurable.of_eval
    intro j
    change Measurable (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) =>
      replaceTransverse h (vmean μ a) (p.1 j) (p.2 j))
    have hev : Measurable (fun p : (Fin N → Fin d → ℝ) × (Fin N → Fin d → ℝ) =>
        (p.1 j, p.2 j)) := by fun_prop
    exact (continuous_replaceTransverse h (vmean μ a)).measurable.comp hev
  have hi : Measurable (fun M : (Fin N → Fin d → ℝ) =>
      ∫ η : Fin N → Fin d → ℝ, matrixEnergyError μ a ψ
        (replaceMatrix h (vmean μ a) M η)
        ∂(Measure.pi fun _ : Fin N => stdGauss (Fin d))) :=
    (((measurable_matrixEnergyError (μ := μ) ha hψ N).comp hrep).stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi fun _ : Fin N => stdGauss (Fin d))).measurable
  exact (measurable_matrixEnergyError ha hψ N).sub hi

theorem canonicalEnergyFluct_assembled (ha : Measurable a) {K : ℝ}
    (hK : ∀ v, ‖a v‖ ≤ K) (h : Fin d → ℝ) (ell : ℝ)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ ell ^ 2 * normSq e)
    (ψ : ℝ → ℝ) {N : ℕ}
    (y : Fin N → ((Fin 1 → ℝ) × (Fin 1 → ℝ)) × (Fin d → ℝ)) :
    canonicalEnergyFluct μ a h ψ (assembledMatrix (planeSplit ha hK h ell hCov) y) =
      wholeRowSum (planeSplit ha hK h ell hCov) N y := by
  have he : ∀ η : Fin N → Fin d → ℝ,
      replaceMatrix h (vmean μ a) (assembledMatrix (planeSplit ha hK h ell hCov) y) η =
        assembledMatrix (planeSplit ha hK h ell hCov) (fun j => ((y j).1, η j)) := by
    intro η
    funext j
    exact replaceTransverse_assembled h (vmean μ a) (y j).1 (y j).2 (η j)
  unfold canonicalEnergyFluct
  simp_rw [he]
  exact matrixEnergyError_centred _ ha hK ψ y

/-- This is a supplied moment on the original matrix distribution, with no assumed marginal identity. -/
theorem canonicalEnergyFluct_order18 (ha : Measurable a) {K : ℝ}
    (hK : ∀ v, ‖a v‖ ≤ K) (h : Fin d → ℝ) (ell : ℝ)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ ell ^ 2 * normSq e)
    {ψ : ℝ → ℝ} (hψ : Measurable ψ) (n : ℕ) :
    ∫⁻ M, ENNReal.ofReal (|canonicalEnergyFluct μ a h ψ M| ^ 18)
      ∂(Measure.pi fun _ : Fin (n ^ 2) => stdGauss (Fin d)) ≤
      ENNReal.ofReal ((rowScale μ a ell *
        (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
          BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18) := by
  let S := planeSplit ha hK h ell hCov
  have hm : Measurable (assembledMatrix S (N := n ^ 2)) :=
    Measurable.of_eval fun j => S.measurable_assemble.comp (measurable_pi_apply j)
  have hF : Measurable (fun M : Fin (n ^ 2) → Fin d → ℝ =>
      ENNReal.ofReal (|canonicalEnergyFluct μ a h ψ M| ^ 18)) :=
    (measurable_canonicalEnergyFluct ha h hψ _).abs.pow_const 18 |>.ennreal_ofReal
  rw [← assembledMatrix_gaussian S (n ^ 2), lintegral_map hF hm]
  change (∫⁻ y, ENNReal.ofReal (|canonicalEnergyFluct μ a h ψ
    (assembledMatrix (planeSplit ha hK h ell hCov) y)| ^ 18)
    ∂(Measure.pi fun _ : Fin (n ^ 2) =>
      ((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin d)))) ≤ _
  simp_rw [canonicalEnergyFluct_assembled ha hK h ell hCov ψ]
  exact whole_sum_order18_width S ha hK n

#print axioms canonicalEnergyFluct_assembled
#print axioms canonicalEnergyFluct_order18
end BstLean.Part223
