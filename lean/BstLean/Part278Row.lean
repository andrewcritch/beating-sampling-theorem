import BstLean.Part278Family
import BstLean.Part278StBase3
import BstLean.Part252MatrixEvent
import BstLean.Part252Centre

/-!
# Part 278 (O5): the odd root on the rows of the 12 225–12 349 family

Option (a) of the coordinator: the row good set already contains the needed events.
`sourceBase` contains `agentEv P (FirstMatrix n)` (the `A₁` operator event `Eop`), `Eop2 n`
(the `A₂` operator event) and `outputCentreEvent` (`|c_A|² ≤ γ_A|b|²χ⁺`). The row's
`RootInputs` give the World window and `e_b > 0`. So no event is added and no charge is paid.

* `odd_root_ops12000`: `odd_root_ops` from `n ≥ 12 000` (`qB ≥ 0` there).
* `odd_root_of_pass`: the odd root `≤ 10⁻²⁰` from the three events, the window and `e_b > 0`.
* `oddRoot_row`: `OddRoot R t` for a row whose base event contains the three events.
-/

namespace BstLean.Part278

open Real
open BstLean.Part130 (normSq normSq_nonneg mA)
open BstLean.Part157 (Ret qTilde Js)
open BstLean.Part169 (A1 A2 OpB Jz nodeS eR O1n O2n paperDesignP tauR bR passF passW
  measurable_passF measurable_passW bulk_of_window qB)
open BstLean.Part272 (statedDesign)

variable {n : ℕ}

theorem qB_nonneg12000 (hn : 12000 ≤ n) : 0 ≤ qB n := by
  unfold qB
  have hnR : (12000 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 7 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 777 / 1000 := by linarith
  nlinarith

/-- The odd root from the operator bounds directly (the body of `odd_root_good`). -/
theorem odd_root_ops12000 (hn : 12000 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (h1 : OpB (A1 c) (O1n n)) (h2 : OpB (A2 c) (O2n n)) (hτ : 0 < tauR c)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c))
    (hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100)
    {χ : ℝ} (he : 0 < eR c) (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ n) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  obtain ⟨hLH, hs, -⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  have hq := qB_nonneg12000 hn
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


/-- **The odd root from the row events.** -/
theorem odd_root_of_pass (hn : 12000 ≤ n) (ho : Odd n) (t : ℝ) (c : Ret n)
    (hF : c ∈ BstLean.Part160.agentEv (paperDesignP n) (BstLean.Part252.FirstMatrix n))
    (hE2 : c ∈ BstLean.Part164.Eop2 n)
    (hO : c ∈ BstLean.Part252.outputCentreEvent (BstLean.Part157.paperCentres n))
    (hw : BstLean.Part161.WINDOW (paperDesignP n) c) (he : 0 < eR c) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤ 1 / 10 ^ 20 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hτ : 0 < tauR c := hw.2.1
  have hS : 0 < normSq c.1.2 + (n : ℝ) * tauR c ^ 2 := by
    have := normSq_nonneg c.1.2; positivity
  have hθ : BstLean.Part150.thetaC c.1.2 (tauR c) =
      (n : ℝ) * tauR c ^ 2 / (normSq c.1.2 + (n : ℝ) * tauR c ^ 2) := by
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    rw [sq_sqrt hS.le]
  have hw1 : 46 / 100 * (normSq c.1.2 + n * tauR c ^ 2) ≤ n * tauR c ^ 2 := hw.2.2.1
  have hw2 : n * tauR c ^ 2 ≤ 54 / 100 * (normSq c.1.2 + n * tauR c ^ 2) := hw.2.2.2
  have hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c.1.2 (tauR c) := by
    rw [hθ, le_div_iff₀ hS]; linarith
  have hθ1 : BstLean.Part150.thetaC c.1.2 (tauR c) ≤ 55 / 100 := by
    rw [hθ, div_le_iff₀ hS]; linarith
  have hO1 : OpB (A1 c) (O1n n) := BstLean.Part169.opB_of_opN _ (hF hτ)
  have hO2 : OpB (A2 c) (O2n n) := BstLean.Part169.opB_of_opN _ hE2
  have hb1 : normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (bR c) * BstLean.Part164.chiUp n := hO
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at hb1
  have hcA : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * (BstLean.Part164.chiUp n / n) := by
    refine hb1.trans (le_of_eq ?_)
    unfold eR
    field_simp
  have hχ0 : 0 ≤ BstLean.Part164.chiUp n / n := by
    unfold BstLean.Part164.chiUp; positivity
  have hχ : BstLean.Part164.chiUp n / n ≤ n := by
    rw [div_le_iff₀ hnR]
    unfold BstLean.Part164.chiUp
    have hn12 : (12000:ℝ) ≤ n := by exact_mod_cast hn
    have hs : √((n:ℝ) * 12) ≤ (n:ℝ) * 12 := by
      calc √((n:ℝ) * 12) ≤ √(((n:ℝ) * 12) ^ 2) := sqrt_le_sqrt (by nlinarith)
        _ = (n:ℝ) * 12 := sqrt_sq (by linarith)
    nlinarith
  exact odd_root_ops12000 hn ho t c hO1 hO2 hτ hθ0 hθ1 he hcA hχ0 hχ

/-- **`OddRoot` for a row** whose base event contains the three events. -/
theorem oddRoot_row (R : BstLean.Part259.RowInputs n) (hn : 12000 ≤ n) (ho : Odd n) (t : ℝ)
    (hbase : ∀ c ∈ R.baseEvent,
      c ∈ BstLean.Part160.agentEv (paperDesignP n) (BstLean.Part252.FirstMatrix n) ∧
      c ∈ BstLean.Part164.Eop2 n ∧
      c ∈ BstLean.Part252.outputCentreEvent (BstLean.Part157.paperCentres n)) :
    OddRoot R t := by
  intro c hc
  obtain ⟨Ri⟩ := R.root t c hc
  obtain ⟨hF, hE2, hO⟩ := hbase c hc.2.1
  exact odd_root_of_pass hn ho t c hF hE2 hO Ri.window Ri.passes.he

end BstLean.Part278
