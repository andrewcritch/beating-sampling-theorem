import BstLean.Part216EnergyMoment

/-! The order18 BE supply for the constructed two-direction Gaussian plane split. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part202

variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
variable {d : ℕ} {a : V → Fin d → ℝ}

/-- This supply uses the actual plane construction, rather than an assumed row moment. -/
theorem plane_energy_order18 (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (h : Fin d → ℝ) (ell : ℝ)
    (hCov : ∀ e, ∫ v, (e ⬝ᵥ (a v - BstLean.Part170.vmean μ a)) ^ 2 ∂μ ≤ ell ^ 2 * BstLean.Part130.normSq e)
    (n : ℕ) :
    ∫⁻ q, ENNReal.ofReal
      (|wholeRowSum (planeSplit ha hK h ell hCov) (n ^ 2) q| ^ 18)
      ∂(Measure.pi fun _ : Fin (n ^ 2) =>
        ((stdGauss (Fin 1)).prod (stdGauss (Fin 1))).prod (stdGauss (Fin d))) ≤
      ENNReal.ofReal ((rowScale μ a ell *
        (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
          BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18) :=
  whole_sum_order18_width (planeSplit ha hK h ell hCov) ha hK n

#print axioms plane_energy_order18
end BstLean.Part216
