import BstLean.Part56Defs
import Mathlib.Probability.Moments.Covariance

/-! Auxiliary coefficient estimates and endpoint cases for Gaussian maximal correlation. -/

namespace BstLean.Part56

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (varU)

/-- Cauchy--Schwarz for real square-integrable observables. -/
theorem mc56_cauchy_schwarz {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F G : α → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    |∫ x, F x * G x ∂μ| ≤
      Real.sqrt (∫ x, F x ^ 2 ∂μ) * Real.sqrt (∫ x, G x ^ 2 ∂μ) := by
  let f := hF.toLp F
  let g := hG.toLp G
  have hi : inner ℝ f g = ∫ x, F x * G x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
    simp [f, g, hx, hy, mul_comm]
  have hnF : ‖f‖ = Real.sqrt (∫ x, F x ^ 2 ∂μ) := by
    have he : ‖f‖ ^ 2 = ∫ x, F x ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with x hx
      simp [f, hx]
    rw [← he, Real.sqrt_sq (norm_nonneg f)]
  have hnG : ‖g‖ = Real.sqrt (∫ x, G x ^ 2 ∂μ) := by
    have he : ‖g‖ ^ 2 = ∫ x, G x ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hG.coeFn_toLp] with x hx
      simp [g, hx]
    rw [← he, Real.sqrt_sq (norm_nonneg g)]
  rw [← hi, ← hnF, ← hnG]
  exact abs_real_inner_le_norm f g

/-- The usual covariance bound, with constant one. -/
theorem mc56_covariance (n : ℕ) (Φ Ψ : (Fin n → ℝ) → ℝ)
    (hΦ : MemLp Φ 2 (stdGauss (Fin n))) (hΨ : MemLp Ψ 2 (stdGauss (Fin n))) :
    |(∫ g, Φ g * Ψ g ∂stdGauss (Fin n)) -
      (∫ g, Φ g ∂stdGauss (Fin n)) * (∫ g, Ψ g ∂stdGauss (Fin n))| ≤
      Real.sqrt (varU (stdGauss (Fin n)) Φ) *
        Real.sqrt (varU (stdGauss (Fin n)) Ψ) := by
  have hc := ProbabilityTheory.covariance_eq_sub hΦ hΨ
  simp only [Pi.mul_apply] at hc
  rw [← hc]
  exact mc56_cauchy_schwarz _ _
    (hΦ.sub (memLp_const _)) (hΨ.sub (memLp_const _))

/-- The perfectly correlated case follows from Cauchy--Schwarz. -/
theorem mc56_one (n : ℕ) (Φ Ψ : (Fin n → ℝ) → ℝ)
    (hΦ : MemLp Φ 2 (stdGauss (Fin n))) (hΨ : MemLp Ψ 2 (stdGauss (Fin n))) :
    |(∫ g, ∫ h, Φ g * Ψ ((1 : ℝ) • g + Real.sqrt (1 - (1 : ℝ) ^ 2) • h)
        ∂stdGauss (Fin n) ∂stdGauss (Fin n)) -
      (∫ g, Φ g ∂stdGauss (Fin n)) * (∫ g, Ψ g ∂stdGauss (Fin n))| ≤
      |(1 : ℝ)| * Real.sqrt (varU (stdGauss (Fin n)) Φ) *
        Real.sqrt (varU (stdGauss (Fin n)) Ψ) := by
  simpa using mc56_covariance n Φ Ψ hΦ hΨ

/-- Reflection preserves the product standard Gaussian. -/
theorem mc56_neg_preserving (n : ℕ) :
    MeasurePreserving (fun g : Fin n → ℝ => -g)
      (stdGauss (Fin n)) (stdGauss (Fin n)) := by
  change MeasurePreserving (fun g i => -g i)
    (Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1)
    (Measure.pi fun _ => ProbabilityTheory.gaussianReal 0 1)
  apply measurePreserving_pi
  intro i
  exact ⟨by fun_prop, by simp [ProbabilityTheory.gaussianReal_map_neg]⟩

/-- The perfectly anticorrelated case follows from reflection and Cauchy--Schwarz. -/
theorem mc56_neg_one (n : ℕ) (Φ Ψ : (Fin n → ℝ) → ℝ)
    (hΦ : MemLp Φ 2 (stdGauss (Fin n))) (hΨ : MemLp Ψ 2 (stdGauss (Fin n))) :
    |(∫ g, ∫ h, Φ g * Ψ ((-1 : ℝ) • g + Real.sqrt (1 - (-1 : ℝ) ^ 2) • h)
        ∂stdGauss (Fin n) ∂stdGauss (Fin n)) -
      (∫ g, Φ g ∂stdGauss (Fin n)) * (∫ g, Ψ g ∂stdGauss (Fin n))| ≤
      |(-1 : ℝ)| * Real.sqrt (varU (stdGauss (Fin n)) Φ) *
        Real.sqrt (varU (stdGauss (Fin n)) Ψ) := by
  have hm := mc56_neg_preserving n
  have he (F : (Fin n → ℝ) → ℝ) (hF : AEStronglyMeasurable F (stdGauss (Fin n))) :
      (∫ g, F (-g) ∂stdGauss (Fin n)) = ∫ g, F g ∂stdGauss (Fin n) :=
    hm.integral_comp (Homeomorph.neg (Fin n → ℝ)).measurableEmbedding F
  have hmean := he Ψ hΨ.aestronglyMeasurable
  have hvar : varU (stdGauss (Fin n)) (fun g => Ψ (-g)) =
      varU (stdGauss (Fin n)) Ψ := by
    unfold varU
    rw [hmean]
    exact he _ ((hΨ.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2)
  have h := mc56_covariance n Φ (fun g => Ψ (-g)) hΦ
    (hΨ.comp_measurePreserving hm)
  rw [hmean, hvar] at h
  simpa using h

/-- The independent case does not require square integrability. -/
theorem mc56_zero (n : ℕ) (Φ Ψ : (Fin n → ℝ) → ℝ) :
    |(∫ g, ∫ h, Φ g * Ψ ((0 : ℝ) • g + Real.sqrt (1 - (0 : ℝ) ^ 2) • h)
        ∂stdGauss (Fin n) ∂stdGauss (Fin n)) -
      (∫ g, Φ g ∂stdGauss (Fin n)) * (∫ g, Ψ g ∂stdGauss (Fin n))| ≤
      |(0 : ℝ)| * Real.sqrt (varU (stdGauss (Fin n)) Φ) *
        Real.sqrt (varU (stdGauss (Fin n)) Ψ) := by
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, Real.sqrt_one,
    zero_smul, one_smul, zero_add, integral_const_mul, integral_mul_const,
    sub_self, abs_zero, zero_mul, le_refl]

/-- In dimension zero every observable is constant. -/
theorem mc56_dim_zero (ρ : ℝ) (Φ Ψ : (Fin 0 → ℝ) → ℝ) :
    |(∫ g, ∫ h, Φ g * Ψ (ρ • g + Real.sqrt (1 - ρ ^ 2) • h)
        ∂stdGauss (Fin 0) ∂stdGauss (Fin 0)) -
      (∫ g, Φ g ∂stdGauss (Fin 0)) * (∫ g, Ψ g ∂stdGauss (Fin 0))| ≤
      |ρ| * Real.sqrt (varU (stdGauss (Fin 0)) Φ) *
        Real.sqrt (varU (stdGauss (Fin 0)) Ψ) := by
  let z : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hΦ : Φ = fun _ => Φ z := funext fun x => congrArg Φ (Subsingleton.elim x z)
  have hΨ : Ψ = fun _ => Ψ z := funext fun x => congrArg Ψ (Subsingleton.elim x z)
  rw [hΦ, hΨ]
  simp [varU]

end BstLean.Part56
