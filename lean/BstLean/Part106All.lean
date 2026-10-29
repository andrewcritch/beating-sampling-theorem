import BstLean.Part106Exact
import BstLean.Part106Spread

/-!
# Part 106: the program `g`, its accuracy relative to the spread of the stand-in, and its cost

Report: `delegations/answers/p106-spec-opus.md`. Modules:
* `Part106Defs`: definitions (`phiAF`, `standIn`, `gVal`).
* `Part106Cost`: the program `gProg` of the cost model, its value and its cost; a lower bound
  for every program that computes one sample of `s_B`.
* `Part106Thm0`: Theorem 0 for the Gaussian version of `W`.
* `Part106Gauss`, `Part106Gauss2`: facts about Gaussians (domination, chi-square).
* `Part106Sphere`, `Part106Exact`: Theorem 0 for the sphere version of `W`.
* `Part106Spread`: what the spread of the stand-in is.

This file joins the accuracy statements with the program of the cost model:
* `main_gauss`: Gaussian version of `W`, `r = 2`, all four degree pairs: the explicit program
  `gProg` is within `(1/2)·sd_ν` of `B(W, A, F)` with probability at least `99/100`, and its cost
  is below the cost of every program of the model that computes one sample of `s_B`.
* `main_sphere`: the same for the sphere version of `W` (the distribution of the north star),
  with the program `gProgFix` that computes its noise level from a rational constant.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part106

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Cost BstLean.Part105

/-- **The program `g` for the Gaussian version of `W`: accuracy and cost** (`r = 2`,
`d_A, d_F ∈ {3, 4}`, `n ≥ 4096`, `834 ≤ k ≤ n²`). `W : ℝ^{2n} → ℝⁿ` has degree `2d_A`; its
coefficients of degree `0` and `1` are those of the fixed `b0`; its coefficients of degree `2` to
`2d_A` are Gaussian (Bombieri–Weyl, parameter `σ`). The program `gProg` reads the coefficients of
degree `0` and `1` of `b0`, the number `τ = √(2d_A − 1)·σ`, `A`, `F` and `k` blocks of random
inputs.
1. With probability at least `99/100` over the coefficients of degree `≥ 2` and the blocks:
   `|g − B(W, A, F)| ≤ (1/2)·sd_ν`.
2. The cost of the program is below the cost of every program of the cost model that computes
   one sample `F(A(W(u)/|W(u)|))` for all inputs. -/
theorem main_gauss (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 834 ≤ k) (hk2 : k ≤ n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4) (σ : ℝ)
    (b0 : CoefIdx (2 * n) n (2 * dA) → ℝ) (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    99 / 100 ≤
      ((bwGauss (2 * n) n (2 * dA) σ).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |(gProg 2 n dA dF k).eval
                (gInVal (fun a => b0 (a, mono0 (2 * n) (2 * dA)))
                  (fun a j => b0 (a, mono1 (2 * n) (2 * dA)
                    (by rcases hdA with h | h <;> omega) j))
                  (tauOf (2 * dA) σ) A F (fun i => (p.2 i).1) (fun i => (p.2 i).2)) () -
              ∫ x, phiAF A F x ∂muW (mixW b0 p.1)| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW b0 (tauOf (2 * dA) σ)])} ∧
    ∀ p : SProg (SampleIn 2 n dA dF) Unit,
      (∀ u W A F, p.eval (sampleVal u W A F) () =
        bwEval F (bwEval A (sphProj (bwEval W u))) 0) →
      (gProg 2 n dA dF k).cost < p.cost := by
  refine ⟨?_, fun p hp => gProg_cost_lt_any n k dA dF hn hk2 hdA hdF p hp⟩
  simp_rw [gProg_eval_gVal]
  rcases hdA with rfl | rfl
  · exact thm0_core (N := 2 * n) (d := 2 * 3) (by omega) (by norm_num) σ b0 A F hk
      ((lam0_bound n (by omega)).trans (lam_num hn))
  · exact thm0_core (N := 2 * n) (d := 2 * 4) (by omega) (by norm_num) σ b0 A F hk
      ((lam0_bound8 n (by omega)).trans (lam_num8 hn))

/-- **The program `g` for the sphere version of `W`: accuracy and cost** (`r = 2`,
`d_A, d_F ∈ {3, 4}`, `n ≥ 4096`, `1200 ≤ k < n²`). `W : ℝ^{2n} → ℝⁿ` of degree `2d_A` has the
Bombieri–Weyl sphere distribution. The program `gProgFix` reads the coefficients of degree `0`
and `1` of `W`, `A`, `F` and `k` blocks of random inputs; it computes its noise level
`τ_0 = tauPaper (2n) n (2d_A)` as the square root of the rational constant
`tauPaperSq = (2d_A − 1)/D_W`.
1. With probability at least `99/100` over all the coefficients of `W` and the blocks:
   `|g − B(W, A, F)| ≤ (1/2)·sd_ν`, `sd_ν` the spread under the stand-in at the level `τ_0`.
2. The cost of the program is below the cost of every program of the cost model that computes
   one sample `F(A(W(u)/|W(u)|))` for all inputs. -/
theorem main_sphere (n k dA dF : ℕ) (hn : 4096 ≤ n) (hk : 1200 ≤ k) (hk2 : k < n ^ 2)
    (hdA : dA = 3 ∨ dA = 4) (hdF : dF = 3 ∨ dF = 4)
    (A : CoefIdx n n dA → ℝ) (F : CoefIdx n 1 dF → ℝ) :
    99 / 100 ≤
      ((bwSphere (2 * n) n (2 * dA)).prod
        (Measure.pi fun _ : Fin k => (uniformSphere (2 * n)).prod (stdGauss (Fin n)))).real
        {p | |(gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).eval
                (gInVal (fun a => p.1 (a, mono0 (2 * n) (2 * dA)))
                  (fun a j => p.1 (a, mono1 (2 * n) (2 * dA)
                    (by rcases hdA with h | h <;> omega) j))
                  0 A F (fun i => (p.2 i).1) (fun i => (p.2 i).2)) () -
              ∫ x, phiAF A F x ∂muW p.1| ≤
          1 / 2 * Real.sqrt (Var[phiAF A F; nuW p.1 (tauPaper (2 * n) n (2 * dA))])} ∧
    ∀ p : SProg (SampleIn 2 n dA dF) Unit,
      (∀ u W A F, p.eval (sampleVal u W A F) () =
        bwEval F (bwEval A (sphProj (bwEval W u))) 0) →
      (gProgFix (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k).cost < p.cost := by
  have hd1 : 1 ≤ 2 * dA := by rcases hdA with h | h <;> omega
  refine ⟨?_, fun p hp => ?_⟩
  · simp_rw [gProgFix_eval, ← tauPaper_eq_sqrt (2 * n) n (2 * dA) hd1, gProg_eval_gVal]
    rcases hdA with rfl | rfl
    · exact thm0_sphere_core (d := 2 * 3) (by norm_num) hn hk A F
        (lam0_bound n (by omega)) (card_six_ge hn)
    · exact thm0_sphere_core (d := 2 * 4) (by norm_num) hn hk A F
        (lam0_eight_le (by omega)) (card_eight_ge hn)
  · have h1 := gProgFix_cost (tauPaperSq (2 * n) n (2 * dA)) 2 n dA dF k
    have h2 := gCost_lt_lower n (k + 1) dA dF hn (by omega) hdA hdF
    have h3 := sample_lower p hp (by rcases hdA with h | h <;> omega)
      (by rcases hdF with h | h <;> omega)
    rw [card_coefIdx] at h3
    have h4 : gCost k 2 n dA dF + 1 ≤ gCost (k + 1) 2 n dA dF := by
      unfold gCost
      nlinarith
    omega

end BstLean.Part106

#print axioms BstLean.Part106.main_gauss
#print axioms BstLean.Part106.main_sphere
