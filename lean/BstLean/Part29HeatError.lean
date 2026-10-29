import BstLean.Part29ExactFormula
import BstLean.Part29GramRaw

/-!
# Part 29, layer L2: the heat branch's error in raw coefficients

The heat branch `ĝ''` evaluates the exact formula with the Gram term `⟨F, K⟩` replaced by a constant
`Kbar` (its mean over `M`). With `Q_k = symOfRaw (a k)`, the error `B − ĝ''` is
`2/(n(n+2))` times the `F ⊗ Λ`-weighted quadratic form of the raw coefficients, minus `Kbar`.
-/

namespace BstLean.Part29

open MeasureTheory

variable {n : ℕ}

/-- The `F ⊗ Λ`-weighted quadratic form of the raw quadratic coefficients `a`. -/
noncomputable def gramRaw (F : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ k, ∑ l, F k l * (∑ i, a k i i * a l i i +
    (1 / 2) * ∑ i, ∑ j, (if i < j then a k i j * a l i j else 0))

/-- **The heat branch's error.** -/
theorem heat_error (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → Fin n → Fin n → ℝ) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (Kbar : ℝ) :
    let Q : Fin n → Matrix (Fin n) (Fin n) ℝ := fun k => symOfRaw (a k)
    let t : Fin n → ℝ := fun k => ∑ i, Q k i i
    let ν : Fin n → ℝ := fun k => c k + t k / n
    let H : ℝ := f0 + ∑ k, g k * ν k + ∑ k, ∑ l, F k l * ν k * ν l
        + (∑ k, ∑ l, F k l * ∑ i, L k i * L l i) / n
        + 2 / ((n : ℝ) * (n + 2)) * (Kbar - (∑ k, ∑ l, F k l * t k * t l) / n)
    ∫ x, funF f0 g F (mapM c L Q x) ∂μ - H = 2 / ((n : ℝ) * (n + 2)) * (gramRaw F a - Kbar) := by
  intro Q t ν H
  have hB := exact_formula hn μ hμ c L Q (fun k => symOfRaw_isSymm (a k)) f0 g F hF
  simp only at hB
  rw [hB]
  have hK : ∑ k, ∑ l, F k l * (∑ i, ∑ j, Q k i j * Q l j i) = gramRaw F a := by
    unfold gramRaw
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Q]
    rw [trace_mul_symOfRaw]
  rw [hK]
  simp only [H]
  ring

end BstLean.Part29
