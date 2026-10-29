import BstLean.Part182Def
import BstLean.Part160Dmat

/-!
# Part 182 (file `Poin`): the Poincaré inequality with the exact gradient, for `Dq`

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:dual`, first inequality
`t_A Cov_x(h) ≼ D`. The proof is already in Lean: Part 160 (file `Dmat`) defines
`Dquad A₁ A₂ c τ v = t·τ²·∫ |v ᵥ* 𝒥(x)Π_x|²/|y|² dξ` and proves `cov_hid2_le_D` (exact gradient
`gradSq_dot_le`, Gaussian Poincaré `lemmaS_grad`) and `cov_at_of_Dquad`. The quadratic form `Dq`
of this part (file `Def`) is `Dquad` by definition (`Dq_eq_Dquad`, `rfl`). This file states the
results for `Dq`.

* `Dq_eq_Dquad`: `Dq = Dquad` (`rfl`).
* `integrable_Dq`: the integrand of `Dq` is integrable (`n ≥ 4`).
* **`cov_le_Dq`**: `t·Var_ξ ⟨w, h(x)⟩ ≤ Dq w` (every `A₁`, `A₂`, `c`, `τ > 0`, `n ≥ 6`).
* `Dq_le_XiS`: `Dq w ≤ Ξ·|w|²`.
* **`cov_at_of_Dq`**: `COV_at D c N` from `Dq w ≤ N·(γ_A/n)·|w|²` for every `w`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part157
open BstLean.Part153 (nrm jacT XiS)

variable {n m : ℕ}

/-- `Dq` is Part 160's `Dquad`. -/
theorem Dq_eq_Dquad (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (v : Fin m → ℝ) :
    Dq A₁ A₂ c τ v = BstLean.Part160.Dquad A₁ A₂ c τ v := rfl

/-- The integrand of `Dq` is integrable (`n ≥ 4`). -/
theorem integrable_Dq (hn : 4 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (v : Fin m → ℝ) :
    Integrable (fun ξ : Fin n → ℝ => normSq (vecMul v (jacT A₁ A₂ (sphPt (c + τ • ξ)))) *
      (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) :=
  BstLean.Part160.integrable_Dquad hn A₁ A₂ c hτ v

/-- **The Poincaré inequality with the exact gradient**: `t·Var_ξ ⟨w, h(x)⟩ ≤ Dq w`. -/
theorem cov_le_Dq (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (w : Fin m → ℝ) :
    2 / (m : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      Dq A₁ A₂ c τ w :=
  BstLean.Part160.cov_hid2_le_D hn A₁ A₂ c hτ w

/-- `Dq w ≤ Ξ·|w|²`. -/
theorem Dq_le_XiS (hn : 4 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (w : Fin m → ℝ) :
    Dq A₁ A₂ c τ w ≤ XiS A₁ A₂ c τ * normSq w :=
  BstLean.Part160.Dquad_le_XiS hn A₁ A₂ c hτ w

/-- **`COV_at D c N` from the quadratic form `Dq`**. -/
theorem cov_at_of_Dq (hn : 6 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {N : ℝ}
    (hX : ∀ w : Fin (mA n) → ℝ, Dq c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) w ≤
      N * (2 / (n : ℝ)) / n * normSq w) :
    BstLean.Part160.COV_at D c N :=
  BstLean.Part160.cov_at_of_Dquad hn D c hτ hX

end BstLean.Part182

open BstLean.Part182 in
#print axioms cov_le_Dq
open BstLean.Part182 in
#print axioms cov_at_of_Dq
open BstLean.Part182 in
#print axioms integrable_Dq
open BstLean.Part182 in
#print axioms Dq_le_XiS
