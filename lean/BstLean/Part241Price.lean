import BstLean.Part169Comp

/-! Free-epsilon squared prices on the same finite input distribution. -/
namespace BstLean.Part241
open MeasureTheory Real

/-- The scale bound retains the bias floor and the variance allowance. -/
noncomputable def scaleBound (n : ℕ) (d aw af H Cv : ℝ) : ℝ :=
  (aw + 2 * H * af + af ^ 2 / n + Cv) / d

/-- The regular squared price. -/
noncomputable def regularPrice (n : ℕ) (χ d ε aw af H Cv : ℝ) : ℝ :=
  (χ / (2 * (2 - ε) * d) * af ^ 2 + scaleBound n d aw af H Cv ^ 2 /
    (8 * (1 - ε))) / n

/-- The exceptional input mass uses the orders six and four. -/
noncomputable def exceptionalMass (n : ℕ) (d ε vmax aw af H : ℝ) : ℝ :=
  ((aw + 2 * H * af) / (99 / 100 * d * n * (ε - vmax / d))) ^ 6 +
    (af ^ 2 / (1 / 100 * d * n ^ 2 * (ε - vmax / d))) ^ 4

/-- Integrate the squared prices before taking one square root. -/
noncomputable def squaredPrice (n : ℕ) (χ d ε vmax aw af H Cv : ℝ) : ℝ :=
  regularPrice n χ d ε aw af H Cv + 2 * exceptionalMass n d ε vmax aw af H

noncomputable def biasRoot (n : ℕ) (χ d ε vmax aw af H Cv : ℝ) : ℝ :=
  √(squaredPrice n χ d ε vmax aw af H Cv)

theorem squaredPrice_eq_PB (n : ℕ) (χ d ε vmax aw af H Cv : ℝ) :
    squaredPrice n χ d ε vmax aw af H Cv = BstLean.Part169.PB n χ d ε vmax aw af H Cv := rfl

/-- The variance allowance `Cv = Cstar/(n-3)` gives the paper's scale formula. -/
theorem scaleBound_paper (n : ℕ) (d aw af H Cstar : ℝ) :
    scaleBound n d aw af (1 + H) (Cstar / ((n : ℝ) - 3)) =
    (aw + 2 * (1 + H) * af + af ^ 2 / n + Cstar / ((n : ℝ) - 3)) / d := rfl

theorem exceptionalMass_nonneg (n : ℕ) (d ε vmax aw af H : ℝ) :
    0 ≤ exceptionalMass n d ε vmax aw af H := by
  unfold exceptionalMass
  positivity

theorem regularPrice_nonneg (n : ℕ) {χ d ε aw af H Cv : ℝ}
    (hχ : 0 ≤ χ) (hd : 0 < d) (hε : ε < 1) :
    0 ≤ regularPrice n χ d ε aw af H Cv := by
  unfold regularPrice
  have : 0 < 2 - ε := by linarith
  have : 0 < 1 - ε := by linarith
  positivity

theorem squaredPrice_nonneg (n : ℕ) {χ d ε vmax aw af H Cv : ℝ}
    (hχ : 0 ≤ χ) (hd : 0 < d) (hε : ε < 1) :
    0 ≤ squaredPrice n χ d ε vmax aw af H Cv :=
  add_nonneg (regularPrice_nonneg n hχ hd hε)
    (mul_nonneg (by norm_num) (exceptionalMass_nonneg n d ε vmax aw af H))

end BstLean.Part241
