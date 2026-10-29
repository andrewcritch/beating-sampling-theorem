import BstLean.Part29Main
import BstLean.Part29Sphere

/-!
# Part 29 in Lean, with no remaining hypotheses on the law of `x`

`proofs/option-m/29-explicit-22-at-100.tex`. For `x` uniform on the Euclidean unit sphere of `ℝⁿ`
(`uniformSphere n`), `n ≥ 100`, and `M = Z / ‖Z‖` with `Z` standard Gaussian on the raw coefficient space of a
quadratic map (so `M` is uniform on its coefficient sphere), each approximate branch of part 29 is within
`ε · sd` of `B = E_x f(m_M(x))` with probability at least `1 − δ` once `ε²` passes its threshold. With
`exact_formula` for the exact branch and `Part29Certificate.lean` for the overlap of the three windows at every
`n ≥ 100`, this is part 29's theorem; the cost counts remain the paper's model.
-/

namespace BstLean.Part29

open MeasureTheory

variable {n : ℕ}

theorem part29_heat (hn : 100 ≤ n) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (hv : 0 < frobSq F) (δ ε : ℝ) (hδ : eta n < δ)
    (hε : 32 * Lam n / ((n : ℝ) ^ 2 * (n + 2) ^ 2 * kappa n * (δ - eta n)) ≤ ε ^ 2) :
    stdGauss (CoefIdx n) {Z | Z ≠ 0 ∧
      ε ^ 2 * varOf (uniformSphere n) f0 g F (unitOf Z) <
        (Bof (uniformSphere n) f0 g F (unitOf Z) - Hof f0 g F (unitOf Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  have h1 : 1 ≤ n := by omega
  haveI := uniformSphere_isProbability n h1
  exact heat_branch hn (uniformSphere n) (uniformSphere_moments n h1) (uniformSphere_parity n h1)
    f0 g F hF hv δ ε hδ hε

theorem part29_U2 (hn : 100 ≤ n) (f0 : ℝ) (g : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : F.IsSymm) (hv : 0 < frobSq F) (δ ε : ℝ) (hδ : eta n < δ)
    (hε : 8 * sN n / (kappa n * (δ - eta n)) ≤ ε ^ 2) :
    stdGauss (CoefIdx n) {Z | Z ≠ 0 ∧
      ε ^ 2 * varOf (uniformSphere n) f0 g F (unitOf Z) <
        (Bof (uniformSphere n) f0 g F (unitOf Z) - Uof f0 g F (unitOf Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  have h1 : 1 ≤ n := by omega
  haveI := uniformSphere_isProbability n h1
  exact U2_branch hn (uniformSphere n) (uniformSphere_moments n h1) (uniformSphere_parity n h1)
    f0 g F hF hv δ ε hδ hε

end BstLean.Part29
