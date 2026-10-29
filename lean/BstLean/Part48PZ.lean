import BstLean.Part48Defs
import BstLean.Part48Var

/-!
# Part 48, wave 1: Paley–Zygmund from the fourth moment (omQ4 §3, eq. 5) — proved

Specification: `delegations/answers/p48-spec-opus.md`, §3 and §5.

Claim. If `E P² > 0` and `E P⁴ ≤ K (E P²)²`, then `γ{P² ≥ E P²/2} ≥ 1/(4K)`.

Route used (no Cauchy–Schwarz). If `K ≤ 0` the left side is `0`. Else put `c = 2KE`. Pointwise,
`P² ≤ P⁴/(2c) + (c/2)·1_G + E/2` (AM–GM on `G`, and `P² < E/2` off `G`). Integrate:
`E ≤ E/4 + KE·γ(G) + E/2`, so `γ(G) ≥ 1/(4K)`. Integrability: `gauss_poly_integrable` (`Part48Var`).

Do not use `native_decide` or `axiom` anywhere.
-/

namespace BstLean.Part48

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

/-- **Paley–Zygmund**: `γ{P² ≥ E P²/2} ≥ 1/(4K)` when `E P² > 0` and `E P⁴ ≤ K (E P²)²`. -/
theorem pz_lower {ι : Type} [Fintype ι] (P : MvPolynomial ι ℝ) (K : ℝ)
    (hE : 0 < ∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι)
    (hK : ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
      K * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2) :
    ENNReal.ofReal (1 / (4 * K)) ≤
      stdGauss ι {z | (∫ z', (MvPolynomial.eval z' P) ^ 2 ∂stdGauss ι) / 2 ≤ (MvPolynomial.eval z P) ^ 2} := by
  set E := ∫ z', (MvPolynomial.eval z' P) ^ 2 ∂stdGauss ι with hEdef
  set G := {z | E / 2 ≤ (MvPolynomial.eval z P) ^ 2} with hG
  rcases le_or_gt K 0 with hK0 | hK0
  · have : 1 / (4 * K) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
    rw [ENNReal.ofReal_eq_zero.mpr this]; exact bot_le
  set c := 2 * K * E with hc
  have hc0 : 0 < c := by positivity
  have hGm : MeasurableSet G :=
    measurableSet_le measurable_const ((MvPolynomial.continuous_eval P).pow 2).measurable
  have hi2 : Integrable (fun z => (MvPolynomial.eval z P) ^ 2) (stdGauss ι) := by
    have := gauss_poly_integrable (P ^ 2); simpa only [map_pow] using this
  have hi4 : Integrable (fun z => (MvPolynomial.eval z P) ^ 4) (stdGauss ι) := by
    have := gauss_poly_integrable (P ^ 4); simpa only [map_pow] using this
  have hind : Integrable (G.indicator (fun _ => (1 : ℝ))) (stdGauss ι) :=
    (integrable_const (1 : ℝ)).indicator hGm
  have hpt : ∀ z, (MvPolynomial.eval z P) ^ 2 ≤
      (MvPolynomial.eval z P) ^ 4 / (2 * c) + (c / 2) * G.indicator (fun _ => (1 : ℝ)) z + E / 2 := by
    intro z
    have h4 : 0 ≤ (MvPolynomial.eval z P) ^ 4 / (2 * c) := by positivity
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      have : (MvPolynomial.eval z P) ^ 2 ≤ (MvPolynomial.eval z P) ^ 4 / (2 * c) + c / 2 := by
        rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((MvPolynomial.eval z P) ^ 2 - c)]
      linarith
    · rw [Set.indicator_of_notMem hz]
      simp only [hG, Set.mem_ofPred_eq, not_le] at hz
      linarith
  have hA : Integrable (fun z => (MvPolynomial.eval z P) ^ 4 / (2 * c)) (stdGauss ι) := hi4.div_const _
  have hB : Integrable (fun z => (c / 2) * G.indicator (fun _ => (1 : ℝ)) z) (stdGauss ι) :=
    hind.const_mul _
  have hAB : Integrable (fun z => (MvPolynomial.eval z P) ^ 4 / (2 * c) +
      (c / 2) * G.indicator (fun _ => (1 : ℝ)) z) (stdGauss ι) := hA.add hB
  have hAB' : Integrable (fun z => (MvPolynomial.eval z P) ^ 4 / (2 * c) +
      (c / 2) * G.indicator (fun _ => (1 : ℝ)) z + E / 2) (stdGauss ι) := hAB.add (integrable_const _)
  have hint := integral_mono hi2 hAB' hpt
  rw [integral_add hAB (integrable_const _), integral_add hA hB, integral_div, integral_const_mul,
    integral_indicator_const (1 : ℝ) hGm, integral_const] at hint
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hint
  rw [← hEdef] at hint
  set g := (stdGauss ι G).toReal with hg
  have h1 : (∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι) / (2 * c) ≤ E / 4 := by
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ K * E ^ 2 := hK
      _ = E / 4 * (2 * c) := by rw [hc]; ring
  have hgK : 1 / (4 * K) ≤ g := by
    rw [div_le_iff₀ (by positivity)]
    have : E / 4 ≤ c / 2 * g := by linarith
    rw [hc] at this
    nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top (stdGauss ι) G)]
  exact ENNReal.ofReal_le_ofReal hgK

end BstLean.Part48
