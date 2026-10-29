import BstLean.Part187All
import BstLean.Part153Final
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4

/-! Part 187 (file `Part188R153Final`): copy of `Part153Final` re-proved at the floor `16200 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part188.Base153_R
open BstLean.Part153 BstLean.Part153.R

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150




theorem AStage16_prob {n : ℕ} (hn : 16200 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodAs16 n c τ)ᶜ ≤
      Real.exp (-(n : ℝ) / 2) + 7 * Real.exp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 :=
  GoodA_prob (by omega) c τ (Esc_prob (by omega) c hτ) (lemmaPP_numeric_16200 hn c hτ)

theorem AStage16_Xi {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodAs16 n c τ) :
    XiS A₁ A₂ c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n :=
  (GoodA_Xi (by omega) hτ (fun θ hθ => hθ) h).1


end BstLean.Part188.Base153_R
