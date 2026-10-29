import BstLean.Part278Free
import BstLean.Part188R169Op

/-!
# Part 278: the odd root on `goodD` from `n ≥ 16 200`

`odd_root_good16200` is `odd_root_good` with the floor `16 200` instead of `16 384`. It uses the
re-based operator bound `Part188.Base169_R.opB_goodD` (`16 200 ≤ n`).
-/

namespace BstLean.Part278

open Real
open BstLean.Part130 (normSq normSq_nonneg mA)
open BstLean.Part157 (Ret qTilde Js)
open BstLean.Part169 (A1 A2 OpB Jz nodeS nodeL nodeH nodeD eR O1n O2n paperDesignP tauR qB
  bulk_of_window)
open BstLean.Part272 (statedDesign)

variable {n : ℕ}

theorem qB_nonneg16200 (hn : 16200 ≤ n) : 0 ≤ qB n := by
  unfold qB
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 6 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 771 / 1000 := by linarith
  nlinarith

/-- **The odd root on the good set and in the World window (`n ≥ 16 200`, through `Part188.Base169_R.opB_goodD`).** -/
theorem odd_root_good16200 (hn : 16200 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n) {EA : Set (Ret n)}
    (hgood : c ∈ BstLean.Part166.goodD n (paperDesignP n) EA) (hτ : 0 < tauR c)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c))
    (hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100)
    {χ : ℝ} (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ n) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  obtain ⟨h1, h2⟩ := BstLean.Part188.Base169_R.opB_goodD hn hgood
  obtain ⟨hLH, hs, -⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  have hq := qB_nonneg16200 hn
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  refine odd_root_lt (by omega) ho (Jz_pos (by omega)) t c
    (OpB_mono h2 O2n_nonneg (O2n_le (by omega))) (fun g hg => ?_) he hc hχ0 hχ
  obtain ⟨hL, hH⟩ := nodeS_mem (by omega) c hLH g hg
  have hs1 : (nodeS c g) ^ 2 ≤ 1 := by have := hs _ hL hH; linarith
  have hO1 := O1n_sq_le (n := n) (by omega)
  have hF := frob_le c h1
  calc ∑ i, aw c (nodeS c g) i ^ 2 ≤ ∑ i, 2 * ∑ j, A1 c i j ^ 2 :=
        Finset.sum_le_sum fun i _ => aw_sq_le (by omega) c _ hs1 i
    _ = 2 * ∑ i, ∑ j, A1 c i j ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (n * O1n n ^ 2) := by linarith
    _ ≤ 2 * (n * (8 * n)) := by
        have := mul_le_mul_of_nonneg_left hO1 (by linarith : (0:ℝ) ≤ n)
        linarith
    _ ≤ 16 * (n : ℝ) ^ 3 := by
        have : (n:ℝ) ^ 2 ≤ (n:ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
        nlinarith

end BstLean.Part278
