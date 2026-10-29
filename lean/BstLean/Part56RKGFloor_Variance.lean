import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The exact variance identity used by the floor proof. -/

namespace BstLean.Part56.FloorAux

open MeasureTheory ProbabilityTheory

/-- Orthogonality converts squared prediction error to a difference of energies. -/
theorem orthogonal_error_energy {β : Type*} [MeasurableSpace β]
    (ν : Measure β) (B G : β → ℝ) (hB : MemLp B 2 ν) (hG : MemLp G 2 ν)
    (ho : (∫ r, (B r - G r) * G r ∂ν) = 0) :
    (∫ r, (B r - G r) ^ 2 ∂ν) = (∫ r, B r ^ 2 ∂ν) - ∫ r, G r ^ 2 ∂ν := by
  have hi : Integrable (fun r => (B r - G r) * G r) ν :=
    (hB.sub hG).integrable_mul hG
  calc
    (∫ r, (B r - G r) ^ 2 ∂ν) =
        ∫ r, (B r ^ 2 - G r ^ 2) - 2 * ((B r - G r) * G r) ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun r => by ring)
    _ = (∫ r, B r ^ 2 ∂ν) - ∫ r, G r ^ 2 ∂ν := by
      rw [integral_sub (f := fun r => B r ^ 2 - G r ^ 2)
        (g := fun r => 2 * ((B r - G r) * G r))
        (hB.integrable_sq.sub hG.integrable_sq) (hi.const_mul 2),
        integral_sub hB.integrable_sq hG.integrable_sq, integral_const_mul, ho]
      ring

/-- Exchange the two expectations in the exact conditional-variance identity.
The section hypotheses and product hypotheses justify every integral exchange. -/
theorem variance_exchange {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : β → α → ℝ)
    (hF : Integrable (fun p : β × α => F p.1 p.2) (ν.prod μ))
    (hFsq : Integrable (fun p : β × α => F p.1 p.2 ^ 2) (ν.prod μ))
    (hx : ∀ r, MemLp (F r) 2 μ)
    (hr : ∀ x, MemLp (fun r => F r x) 2 ν)
    (ha : MemLp (fun x => ∫ r, F r x ∂ν) 2 μ)
    (hb : MemLp (fun r => ∫ x, F r x ∂μ) 2 ν) :
    (∫ r, variance (F r) μ ∂ν) =
      (∫ x, variance (fun r => F r x) ν ∂μ) -
        variance (fun r => ∫ x, F r x ∂μ) ν +
        variance (fun x => ∫ r, F r x ∂ν) μ := by
  have hmean := integral_integral_swap hF
  have hsecond := integral_integral_swap (f := fun r x => F r x ^ 2) hFsq
  have hl : (fun r => variance (F r) μ) =
      fun r => (∫ x, F r x ^ 2 ∂μ) - (∫ x, F r x ∂μ) ^ 2 := by
    funext r
    exact variance_eq_sub (hx r)
  have hr' : (fun x => variance (fun r => F r x) ν) =
      fun x => (∫ r, F r x ^ 2 ∂ν) - (∫ r, F r x ∂ν) ^ 2 := by
    funext x
    exact variance_eq_sub (hr x)
  rw [hl, hr', integral_sub hFsq.integral_prod_left hb.integrable_sq,
    integral_sub hFsq.integral_prod_right ha.integrable_sq,
    variance_eq_sub hb, variance_eq_sub ha]
  simp only [Pi.pow_apply]
  rw [hsecond, hmean]
  ring

/-- The exact identity implies the floor once the conditional error is bounded. -/
theorem floor_of_variance_exchange {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : β → α → ℝ)
    (hF : Integrable (fun p : β × α => F p.1 p.2) (ν.prod μ))
    (hFsq : Integrable (fun p : β × α => F p.1 p.2 ^ 2) (ν.prod μ))
    (hx : ∀ r, MemLp (F r) 2 μ)
    (hr : ∀ x, MemLp (fun r => F r x) 2 ν)
    (ha : MemLp (fun x => ∫ r, F r x ∂ν) 2 μ)
    (hb : MemLp (fun r => ∫ x, F r x ∂μ) 2 ν)
    (δ : ℝ)
    (he : variance (fun r => ∫ x, F r x ∂μ) ν ≤
      δ * ∫ x, variance (fun r => F r x) ν ∂μ) :
    (1 - δ) * (∫ x, variance (fun r => F r x) ν ∂μ) ≤
      ∫ r, variance (F r) μ ∂ν := by
  have hi := variance_exchange μ ν F hF hFsq hx hr ha hb
  have hn : 0 ≤ variance (fun x => ∫ r, F r x ∂ν) μ := variance_nonneg _ _
  nlinarith

end BstLean.Part56.FloorAux
