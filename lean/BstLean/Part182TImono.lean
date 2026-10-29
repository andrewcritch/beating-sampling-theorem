import BstLean.Part182Def

/-!
# Part 182 (file `TImono`): monotonicity of `TI_hyp` in `λ` and `δ`

No proof is left open; no `native_decide` or `axiom` is used.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part153 (nuA)

variable {n : ℕ}

/-- A larger pair constant and a larger charge keep `TI_hyp`. -/
theorem TI_hyp_mono {cm cp lam lam' δ δ' : ℝ} (hl : lam ≤ lam') (hd : δ ≤ δ')
    (h : TI_hyp n cm cp lam δ) : TI_hyp n cm cp lam' δ' := by
  intro x x' hx hx' h1 h2
  refine le_trans (measureReal_mono (fun θ hθ => ?_) (measure_ne_top _ _)) ((h x x' hx hx' h1 h2).trans hd)
  have hθ' : (n : ℝ) * lam' < _ := hθ
  show (n : ℝ) * lam < _
  have : (n : ℝ) * lam ≤ (n : ℝ) * lam' := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
  linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms TI_hyp_mono
