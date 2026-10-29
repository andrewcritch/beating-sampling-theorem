import BstLean.Part88Defs

/-!
# Part 88: the assembly of the failure bound from the interfaces, and the program clause

* `fail88_core`: from the polar reduction, a sphere step with any bound `p`, and the scale tail:
  `P(fail) ≤ p + C/n`.
* `part88_of_fail`: Theorem 4's statement at accuracy `ε` from the failure bound.
* `DW_ge_cube`: `D_W ≥ n³/2` for `d ≥ 2`.

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part88

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono heavyCount)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part59
open BstLean.Part81 (WIdx)
open BstLean.Part84

variable {n d : ℕ}

/-- **The failure bound from the interfaces**, for a sphere step with the bound `p`. -/
theorem fail88_core (n d k : ℕ) (p C ε : ℝ)
    (hPol : PolarRed n d k)
    (hStep : ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ k → ∀ lam : ℝ,
      |lam ^ 2 - 1| ≤ 1 / (n : ℝ) →
      stdGauss (WIdx n d) {W | ε ^ 2 * VW P lam (Real.sqrt (DW n d) • unitF53 W) <
          errW P lam (Real.sqrt (DW n d) • unitF53 W) ^ 2} ≤ ENNReal.ofReal p)
    (hTail : TailIface n d C)
    (hdeg : ∀ (c : Mono n k → ℝ) (u : Fin n → ℝ) (ρ : ℝ), (Pu n d k c u ρ).totalDegree ≤ k)
    (c : Mono n k → ℝ) :
    stdGauss (CoefIdxD n d) (SphereFail n d k ε c) ≤
      ENNReal.ofReal p + ENNReal.ofReal (C / n) := by
  classical
  set S : Set ((Fin n → ℝ) × (WIdx n d → ℝ)) :=
    {q | 1 / (n : ℝ) < |lam0 n d q.1 (radF53 q.2) ^ 2 - 1|} with hS
  have hpt : ∀ (u : Fin n → ℝ) (W' : WIdx n d → ℝ),
      stdGauss (WIdx n d) (badSet n d k ε c u (radF53 W')) ≤
        ENNReal.ofReal p + S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W') := by
    intro u W'
    by_cases h : (u, W') ∈ S
    · rw [Set.indicator_of_mem h]
      exact (prob_le_one).trans le_add_self
    · rw [Set.indicator_of_notMem h, add_zero]
      have h' : |lam0 n d u (radF53 W') ^ 2 - 1| ≤ 1 / (n : ℝ) := by
        simpa [hS, not_lt] using h
      exact hStep (Pu n d k c u (radF53 W')) (hdeg c u _) (lam0 n d u (radF53 W')) h'
  refine (hPol ε c).trans ?_
  calc ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
        stdGauss (WIdx n d) (badSet n d k ε c u (radF53 W')) ∂stdGauss (WIdx n d)
        ∂stdGauss (Fin n)
      ≤ ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
          (ENNReal.ofReal p + S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W'))
          ∂stdGauss (WIdx n d) ∂stdGauss (Fin n) :=
        lintegral_mono fun u => lintegral_mono fun W' => hpt u W'
    _ = ENNReal.ofReal p +
          ∫⁻ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W')
            ∂stdGauss (WIdx n d) ∂stdGauss (Fin n) := by
        have e1 : ∀ u : Fin n → ℝ, ∫⁻ W' : WIdx n d → ℝ,
            (ENNReal.ofReal p + S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W'))
            ∂stdGauss (WIdx n d) =
            ENNReal.ofReal p +
              ∫⁻ W' : WIdx n d → ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, W')
                ∂stdGauss (WIdx n d) := by
          intro u
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        simp_rw [e1]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal p + ENNReal.ofReal (C / n) := by
        gcongr
        exact hTail

/-- Theorem 4's statement at accuracy `ε` from the failure bound. -/
theorem part88_of_fail (n d k : ℕ) (ε : ℝ) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hn : 3 * k + 6 * d + 20 ≤ n)
    (hfail : ∀ c : Mono n k → ℝ,
      stdGauss (CoefIdxD n d) (SphereFail n d k ε c) ≤ ENNReal.ofReal (1 / 100)) :
    ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ c : Mono n k → ℝ, TopNZ k c →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varP (uniformSphere n) k c (unitOfD Z) <
            (BP (uniformSphere n) k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n d k hn1 hd hk
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 k ε pg.cost hcost
    ((costG59_lt_twoPp n d k hd hn).trans_le (twoPp_le_baselineF n d k ε)), ?_⟩
  intro c _
  have heval : ∀ M : CoefIdxD n d → ℝ, pg.eval (inp59 c M) () = g0Q n d k c M := by
    intro M
    rw [hspec, (cv59_inp k c M).1, (cv59_inp k c M).2]
  simp only [heval]
  exact hfail c

/-- `D_W ≥ n³/2` for `d ≥ 2`. -/
theorem DW_ge_cube (n d : ℕ) (hd : 2 ≤ d) : (n : ℝ) ^ 3 / 2 ≤ DW n d := by
  rw [DW_eq, BstLean.Part36.DD_eq]
  have hc := Nat.choose_le_choose n (show n + 2 ≤ n + d by omega)
  rw [Nat.choose_symm_add (a := n) (b := 2), Nat.choose_symm_add (a := n) (b := d)] at hc
  have h2 : ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two]; push_cast; ring
  have hc' : ((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 ≤ ((n + d).choose d : ℝ) := by
    rw [← h2]; exact_mod_cast hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hc' hn0, mul_nonneg hn0 hn0]

end BstLean.Part88
