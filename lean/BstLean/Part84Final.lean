import BstLean.Part84Asm
import BstLean.Part84Rep
import BstLean.Part84Scale
import BstLean.Part84Decor
import BstLean.Part84Mom
import BstLean.Part84Poly
import BstLean.Part84Gauss
import BstLean.Part84Remez
import BstLean.Part84Polar
import BstLean.Part84Tail

/-!
# Part 84: Theorem 4 for uniform `D` at every degree pair, from any fourth-moment constant

`part84_of`: for every `d_M = d ≥ 1`, `d_f = k ≥ 1`, every constant `K4` with `Fourth84 k K4`
(`E P⁴ ≤ K4 (E P²)²` for Gaussian polynomials of degree `≤ k`), and every `n ≥ thr84 d k K4`:
Theorem 4's conclusion at `ε = 1/2`, failure `≤ 1/100`.

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part84

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono heavyCount)
open BstLean.Part59

theorem thr84_ge (d k : ℕ) (K4 : ℝ) (hK4 : 0 ≤ K4) :
    (5000 : ℝ) ≤ thr84 d k K4 ∧ (3 * (k : ℝ) + 6 * d + 20) ≤ thr84 d k K4 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold thr84
  have t1 : 0 ≤ 80 * (k : ℝ) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 * (4 * (k : ℝ) + 5) ^ 4 := by positivity
  have t2 : 0 ≤ 143000 * (2 * (d : ℝ) + 2) ^ 4 := by positivity
  have t4 : 0 ≤ 3500 * (2 * (k : ℝ) + 1) ^ 2 * K4 := by positivity
  have t3 : 3 * (k : ℝ) + 6 * d + 20 ≤ 871000 * ((k : ℝ) + 1) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 := by
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) := by linarith
    have h2 : (2 : ℝ) ≤ (2 * (d : ℝ) + 2) := by linarith
    have h3 : ((k : ℝ) + 1) * (2 * (d : ℝ) + 2) ≤ (((k : ℝ) + 1) * (2 * (d : ℝ) + 2)) ^ 2 := by
      have : (1 : ℝ) ≤ ((k : ℝ) + 1) * (2 * (d : ℝ) + 2) := by nlinarith
      nlinarith
    have h4 : (((k : ℝ) + 1) * (2 * (d : ℝ) + 2)) ^ 2 =
        ((k : ℝ) + 1) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 := by ring
    have h5 : 3 * (k : ℝ) + 6 * d + 20 ≤ 20 * (((k : ℝ) + 1) * (2 * (d : ℝ) + 2)) := by nlinarith
    nlinarith
  have t3' : 0 ≤ 871000 * ((k : ℝ) + 1) ^ 2 * (2 * (d : ℝ) + 2) ^ 2 := by positivity
  constructor <;> linarith

/-- **Theorem 4, uniform `D`, every degree pair, from a fourth-moment constant.** -/
theorem part84_of (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K4 : ℝ) (hK4 : 0 ≤ K4)
    (h4 : Fourth84 k K4) (n : ℕ) (hN : thr84 d k K4 ≤ (n : ℝ)) :
    ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k (1 / 2) ∧
      ∀ c : Mono n k → ℝ, TopNZ k c →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          (1 / 2 : ℝ) ^ 2 * varP (uniformSphere n) k c (unitOfD Z) <
            (BP (uniformSphere n) k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  obtain ⟨g1, g2⟩ := thr84_ge d k K4 hK4
  have hn5 : 5000 ≤ n := by exact_mod_cast g1.trans hN
  have hnc : 3 * k + 6 * d + 20 ≤ n := by exact_mod_cast g2.trans hN
  have hn1 : 1 ≤ n := by omega
  have hRep := repIface n d hn1 hd
  have hPoly := polyRep n d hn1
  have hF := BstLean.Part81.featOpU n d hn5
  refine part84_of_fail n d k hd hk hnc (fun c => ?_)
  refine fail84_iface n d k hd hk K4 hK4 hN ?_ ?_ (polarRed n d k hn1 hd)
    (tailIface n d hd (by omega)) (Pu_degree n d k) c
  · intro ha
    exact gaussModel n d k hd hk (by omega) (101 / 100) K4 (by norm_num) hK4 hRep
      (scaleIface n k) (decorIface n d hn1 hd (101 / 100) (by norm_num) hRep hF)
      (fubIface n d hn1) (momIface n hn1) (deltaIface n d hd (by omega)) hPoly h4 ha
  · intro c1 cV efl hc1 hcV hG
    exact remezStep n d k hn1 hk c1 cV efl hc1 hcV (card_WIdx_ge n d hd (by omega)) hG
      (radPoly n d hn1) hPoly

end BstLean.Part84
