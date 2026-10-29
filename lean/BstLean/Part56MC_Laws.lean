import BstLean.Part56Defs
import Mathlib.Probability.Independence.Basic

/-! Marginal law of a correlated pair of standard Gaussian vectors. -/

namespace BstLean.Part56

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open scoped NNReal

private theorem scalar_mix (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) (gaussianReal 0 1) := by
  have hx : HasLaw (fun p : ℝ × ℝ => a * p.1)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    convert gaussianReal_const_mul
      (measurePreserving_fst.hasLaw : HasLaw (fun p : ℝ × ℝ => p.1)
        (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1))) a using 1 <;> simp
  have hy : HasLaw (fun p : ℝ × ℝ => b * p.2)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    convert gaussianReal_const_mul
      (measurePreserving_snd.hasLaw : HasLaw (fun p : ℝ × ℝ => p.2)
        (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1))) b using 1 <;> simp
  have hind : IndepFun (fun p : ℝ × ℝ => a * p.1) (fun p => b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    indepFun_prod (by fun_prop) (by fun_prop)
  have hv : NNReal.mk (a ^ 2) (sq_nonneg a) + NNReal.mk (b ^ 2) (sq_nonneg b) = 1 :=
    NNReal.eq hab
  refine ⟨by fun_prop, ?_⟩
  have hs := gaussianReal_add_gaussianReal_of_indepFun hind hx hy
  rw [zero_add, hv] at hs
  convert hs using 1

theorem mc56_mix_preserving {ι : Type*} [Fintype ι] (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    MeasurePreserving (fun p : (ι → ℝ) × (ι → ℝ) => a • p.1 + b • p.2)
      ((stdGauss ι).prod (stdGauss ι)) (stdGauss ι) := by
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)).symm
  have hm := measurePreserving_pi (fun _ : ι => (gaussianReal 0 1).prod (gaussianReal 0 1))
    (fun _ : ι => gaussianReal 0 1) (fun _ => scalar_mix a b hab)
  convert hm.comp he using 1 <;> rfl

theorem mc56_rho_mix_preserving {ι : Type*} [Fintype ι] (ρ : ℝ) (hρ : |ρ| ≤ 1) :
    MeasurePreserving
      (fun p : (ι → ℝ) × (ι → ℝ) => ρ • p.1 + Real.sqrt (1 - ρ ^ 2) • p.2)
      ((stdGauss ι).prod (stdGauss ι)) (stdGauss ι) := by
  apply mc56_mix_preserving
  have h : 0 ≤ 1 - ρ ^ 2 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hρ
    nlinarith
  rw [Real.sq_sqrt h]
  ring

end BstLean.Part56
