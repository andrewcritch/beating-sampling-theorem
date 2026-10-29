import BstLean.Part56RKGErr_PairLaw
import BstLean.Part56RKGErr_Polynomial
import Mathlib.Probability.Moments.Covariance

/-! Maximal correlation applied to the joint law of residual evaluations. -/
namespace BstLean.Part56.RKGErr

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD)
open BstLean.Part41 (Mono Tens fval varU colM)
open BstLean.Part53 (linZ nsq)

variable {n d : ℕ}

theorem varU_scaled_eq_cvar (k : ℕ) (f0 : ℝ) (T : Tens n) (a : ℝ) (y : Fin n → ℝ) :
    varU (stdGauss (Fin n)) (fun g => fval k f0 T (y + a • g)) = cvarG k f0 T a y := by
  have h := fval_scaled_memLp k f0 T a y
  rw [varU, ← variance_eq_integral h.aemeasurable, variance_eq_sub h]
  rfl

theorem cvar_nonneg (k : ℕ) (f0 : ℝ) (T : Tens n) (a : ℝ) (y : Fin n → ℝ) :
    0 ≤ cvarG k f0 T a y := by
  rw [← varU_scaled_eq_cvar]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem linear_variance_eq_cvar (k : ℕ) (f0 : ℝ) (T : Tens n)
    (ψ : Mono n d → ℝ) (a : ℝ) (hψ : nsq ψ = a ^ 2) (y : Fin n → ℝ) :
    (∫ W, (fval k f0 T (y + linZ W ψ) -
      ∫ V, fval k f0 T (y + linZ V ψ) ∂stdGauss (CoefIdxD n d)) ^ 2
        ∂stdGauss (CoefIdxD n d)) = cvarG k f0 T a y := by
  have hμ := fval_linear_memLp k f0 T ψ y
  have hm := linear_marginal_integral ψ a hψ
    (fun u => fval k f0 T (y + u)) ((fval_continuous k f0 T).measurable.comp (by fun_prop))
  have hs := linear_marginal_integral ψ a hψ
    (fun u => fval k f0 T (y + u) ^ 2) (((fval_continuous k f0 T).pow 2).measurable.comp (by fun_prop))
  rw [← variance_eq_integral hμ.aemeasurable, variance_eq_sub hμ]
  simp only [Pi.pow_apply]
  rw [hm, hs]
  rfl

/-- Lemma MC applies to any two linear evaluations with the matching Gram entries. -/
theorem linear_covariance_bound (hMC : LemmaMC56)
    (k : ℕ) (f0 : ℝ) (T : Tens n) (ψ χ : Mono n d → ℝ)
    (a b ρ : ℝ) (hρ : |ρ| ≤ 1) (hψ : nsq ψ = a ^ 2) (hχ : nsq χ = b ^ 2)
    (hcross : (∑ p, ψ p * χ p) = a * b * ρ) (y z : Fin n → ℝ) :
    |(∫ W, fval k f0 T (y + linZ W ψ) * fval k f0 T (z + linZ W χ)
        ∂stdGauss (CoefIdxD n d)) -
      (∫ W, fval k f0 T (y + linZ W ψ) ∂stdGauss (CoefIdxD n d)) *
        (∫ W, fval k f0 T (z + linZ W χ) ∂stdGauss (CoefIdxD n d))| ≤
      |ρ| * Real.sqrt (cvarG k f0 T a y) * Real.sqrt (cvarG k f0 T b z) := by
  let q := Real.sqrt (1 - ρ ^ 2)
  have hq : ρ ^ 2 + q ^ 2 = 1 := by
    have hs : 0 ≤ 1 - ρ ^ 2 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
    rw [show q ^ 2 = 1 - ρ ^ 2 from Real.sq_sqrt hs]
    ring
  let F : ((Fin n ⊕ Fin n) → ℝ) → ℝ := fun u =>
    fval k f0 T (y + fun i => u (.inl i)) * fval k f0 T (z + fun i => u (.inr i))
  have hFm : Measurable F := by
    exact ((fval_continuous k f0 T).measurable.comp (by fun_prop)).mul
      ((fval_continuous k f0 T).measurable.comp (by fun_prop))
  have hLm : Measurable (linearPair ψ χ) := by
    apply Measurable.of_eval
    intro i
    cases i <;> simp only [linearPair, Sum.elim_inl, Sum.elim_inr, linZ, colM] <;> fun_prop
  have hRm : Measurable (pairModel (n := n) a b ρ q) := by
    apply Measurable.of_eval
    intro i
    cases i <;> simp only [pairModel, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul] <;> fun_prop
  have hlaw := linearPair_law ψ χ a b ρ q hψ hχ hcross hq
  have hiL : Integrable (F ∘ linearPair ψ χ) (stdGauss (CoefIdxD n d)) := by
    exact (fval_linear_memLp k f0 T ψ y).integrable_mul (fval_linear_memLp k f0 T χ z)
  have hiMap : Integrable F
      (((stdGauss (Fin n)).prod (stdGauss (Fin n))).map (pairModel a b ρ q)) := by
    rw [← hlaw]
    exact (integrable_map_measure hFm.aestronglyMeasurable hLm.aemeasurable).2 hiL
  have hiR : Integrable (F ∘ pairModel a b ρ q)
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))) :=
    (integrable_map_measure hFm.aestronglyMeasurable hRm.aemeasurable).1 hiMap
  have hprod :
      (∫ W, fval k f0 T (y + linZ W ψ) * fval k f0 T (z + linZ W χ)
        ∂stdGauss (CoefIdxD n d)) =
      ∫ g, ∫ h, fval k f0 T (y + a • g) *
        fval k f0 T (z + b • (ρ • g + q • h)) ∂stdGauss (Fin n) ∂stdGauss (Fin n) := by
    calc
      _ = ∫ u, F u ∂(stdGauss (CoefIdxD n d)).map (linearPair ψ χ) :=
        (integral_map hLm.aemeasurable hFm.aestronglyMeasurable).symm
      _ = ∫ p, F (pairModel a b ρ q p) ∂(stdGauss (Fin n)).prod (stdGauss (Fin n)) := by
        rw [hlaw]
        exact integral_map hRm.aemeasurable hFm.aestronglyMeasurable
      _ = _ := by
        exact integral_prod _ hiR
  have hmψ := linear_marginal_integral ψ a hψ
    (fun u => fval k f0 T (y + u)) ((fval_continuous k f0 T).measurable.comp (by fun_prop))
  have hmχ := linear_marginal_integral χ b hχ
    (fun u => fval k f0 T (z + u)) ((fval_continuous k f0 T).measurable.comp (by fun_prop))
  rw [hprod, hmψ, hmχ]
  have hm := hMC n ρ hρ (fun g => fval k f0 T (y + a • g))
    (fun g => fval k f0 T (z + b • g))
    (fval_scaled_memLp k f0 T a y) (fval_scaled_memLp k f0 T b z)
  simpa only [varU_scaled_eq_cvar, q] using hm

end BstLean.Part56.RKGErr
