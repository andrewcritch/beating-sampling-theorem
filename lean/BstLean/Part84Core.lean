import BstLean.Part84Defs

/-!
# Part 84: the assembly of the failure bound from the interfaces

* `GaussModel.mono`: the constants of the Gaussian model can be enlarged.
* `fail84_core`: from the polar reduction, the sphere step and the scale tail:
  `P(fail) ≤ p₀ + C/n`.

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part84

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part81 (WIdx)

variable {n d : ℕ}

/-- The constants of the Gaussian model can be enlarged. -/
theorem GaussModel.mono {k : ℕ} {c1 cV efl c1' cV' efl' : ℝ} (h : GaussModel n d k c1 cV efl)
    (h1 : c1 ≤ c1') (hV : cV ≤ cV') (he : efl ≤ efl') : GaussModel n d k c1' cV' efl' := by
  intro P hP lam hlam
  obtain ⟨L, Vb, hL, hVb, i1, i2, b1, b2⟩ := h P hP lam hlam
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨L, Vb, hL, ?_, i1, i2, ?_, ?_⟩
  · have : (1 - efl') * L ≤ (1 - efl) * L := mul_le_mul_of_nonneg_right (by linarith) hL
    linarith
  · refine b1.trans (mul_le_mul_of_nonneg_right ?_ hL)
    exact div_le_div_of_nonneg_right h1 hn0
  · refine b2.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg L))
    exact div_le_div_of_nonneg_right hV hn0

/-- The bound of the sphere step. -/
noncomputable def p0 (n k : ℕ) (c1 cV efl ε κ : ℝ) : ℝ :=
  5 / 2 * ((k : ℝ) + 1) ^ 2 * c1 / (n * (ε ^ 2 * κ)) +
    5 / 2 * (2 * (k : ℝ) + 1) ^ 2 * cV / (n * (1 - efl - κ) ^ 2)

/-- **The failure bound from the interfaces.** -/
theorem fail84_core (n d k : ℕ) (c1 cV efl C ε κ : ℝ) (hε : 0 < ε) (hκ : 0 < κ)
    (hefl : efl + κ < 1)
    (hPol : PolarRed n d k) (hRem : RemezStep n d k c1 cV efl) (hTail : TailIface n d C)
    (hdeg : ∀ (c : Mono n k → ℝ) (u : Fin n → ℝ) (ρ : ℝ), (Pu n d k c u ρ).totalDegree ≤ k)
    (c : Mono n k → ℝ) :
    stdGauss (CoefIdxD n d) (SphereFail n d k ε c) ≤
      ENNReal.ofReal (p0 n k c1 cV efl ε κ) + ENNReal.ofReal (C / n) := by
  classical
  set S : Set ((Fin n → ℝ) × (WIdx n d → ℝ)) :=
    {p | 1 / (n : ℝ) < |lam0 n d p.1 (radF53 p.2) ^ 2 - 1|} with hS
  have hpt : ∀ (u : Fin n → ℝ) (W' : WIdx n d → ℝ),
      stdGauss (WIdx n d) (badSet n d k ε c u (radF53 W')) ≤
        ENNReal.ofReal (p0 n k c1 cV efl ε κ) + S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W') := by
    intro u W'
    by_cases h : (u, W') ∈ S
    · rw [Set.indicator_of_mem h]
      exact (prob_le_one).trans le_add_self
    · rw [Set.indicator_of_notMem h, add_zero]
      have h' : |lam0 n d u (radF53 W') ^ 2 - 1| ≤ 1 / (n : ℝ) := by
        simpa [hS, not_lt] using h
      exact hRem (Pu n d k c u (radF53 W')) (hdeg c u _) (lam0 n d u (radF53 W')) h' ε κ hε hκ hefl
  refine (hPol ε c).trans ?_
  calc ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
        stdGauss (WIdx n d) (badSet n d k ε c u (radF53 W')) ∂stdGauss (WIdx n d)
        ∂stdGauss (Fin n)
      ≤ ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
          (ENNReal.ofReal (p0 n k c1 cV efl ε κ) + S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W'))
          ∂stdGauss (WIdx n d) ∂stdGauss (Fin n) :=
        lintegral_mono fun u => lintegral_mono fun W' => hpt u W'
    _ = ENNReal.ofReal (p0 n k c1 cV efl ε κ) +
          ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W')
            ∂stdGauss (WIdx n d) ∂stdGauss (Fin n) := by
        have e1 : ∀ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
            (ENNReal.ofReal (p0 n k c1 cV efl ε κ) + S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W'))
            ∂stdGauss (WIdx n d) =
            ENNReal.ofReal (p0 n k c1 cV efl ε κ) +
              ∫⁻ W' : WIdx n d → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W')
                ∂stdGauss (WIdx n d) := by
          intro u
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        simp_rw [e1]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (p0 n k c1 cV efl ε κ) + ENNReal.ofReal (C / n) := by
        gcongr
        exact hTail

end BstLean.Part84
