import BstLean.Part84Arith

/-!
# Part 84: the failure bound `≤ 1/100` from the interfaces, and the program clause

* `fail84_iface`: from the interface statements (each proved in its own file) and
  `n ≥ thr84 d k K4`: the failure probability on the coefficient sphere is `≤ 1/100`.
* `part84_of_fail`: the statement of Theorem 4 from the failure bound (program `g₀`, cost).

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part84

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono heavyCount)
open BstLean.Part59
open BstLean.Part81 (WIdx FeatOp)

/-- The failure bound from the interfaces. `hGM` is the Gaussian-model theorem, `hRS` the sphere
step, in the form in which their files prove them. -/
theorem fail84_iface (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K4 : ℝ) (hK4 : 0 ≤ K4)
    (hN : thr84 d k K4 ≤ (n : ℝ))
    (hGM : 4 * (4 * (k : ℝ) + 5) ^ 2 * aK n d k ≤ 1 / 2 →
      GaussModel n d k (c1F d (101 / 100))
        (K4 * (4 * (101 / 100) + 2 * c1F d (101 / 100) ^ 2 / n))
        (12 * k * aK n d k + c1F d (101 / 100) / n))
    (hRS : ∀ c1 cV efl : ℝ, 0 ≤ c1 → 0 ≤ cV → GaussModel n d k c1 cV efl →
      RemezStep n d k c1 cV efl)
    (hPol : PolarRed n d k) (hTail : TailIface n d 33)
    (hdeg : ∀ (c : Mono n k → ℝ) (u : Fin n → ℝ) (ρ : ℝ), (Pu n d k c u ρ).totalDegree ≤ k)
    (c : Mono n k → ℝ) :
    stdGauss (CoefIdxD n d) (SphereFail n d k (1 / 2) c) ≤ ENNReal.ofReal (1 / 100) := by
  obtain ⟨h1, h2, h3, h4⟩ := arith84 n d k K4 hK4 hk hd hN
  have hG := (hGM h1).mono (le_refl _) h3 h2
  have hR := hRS _ _ _ (c1F_le d hd).1 (by positivity) hG
  have hf := fail84_core n d k _ _ _ 33 (1 / 2) (3 / 10) (by norm_num) (by norm_num)
    (by norm_num) hPol hR hTail hdeg c
  refine hf.trans ?_
  have hn0 : (0 : ℝ) ≤ 33 / (n : ℝ) := by positivity
  have hp0 : 0 ≤ p0 n k (c1F d (101 / 100)) (5 * K4) (1 / 10) (1 / 2) (3 / 10) := by
    have := (c1F_le d hd).1
    unfold p0; positivity
  rw [← ENNReal.ofReal_add hp0 hn0]
  exact ENNReal.ofReal_le_ofReal h4

/-- Theorem 4's statement from the failure bound. -/
theorem part84_of_fail (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (hn : 3 * k + 6 * d + 20 ≤ n)
    (hfail : ∀ c : Mono n k → ℝ,
      stdGauss (CoefIdxD n d) (SphereFail n d k (1 / 2) c) ≤ ENNReal.ofReal (1 / 100)) :
    ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k (1 / 2) ∧
      ∀ c : Mono n k → ℝ, TopNZ k c →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) k c (unitOfD Z) <
            (BP (uniformSphere n) k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n d k hn1 hd hk
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 k (1 / 2) pg.cost hcost
    ((costG59_lt_twoPp n d k hd hn).trans_le (twoPp_le_baselineF n d k (1 / 2))), ?_⟩
  intro c _
  have heval : ∀ M : CoefIdxD n d → ℝ, pg.eval (inp59 c M) () = g0Q n d k c M := by
    intro M
    rw [hspec, (cv59_inp k c M).1, (cv59_inp k c M).2]
  simp only [heval]
  exact hfail c

end BstLean.Part84
