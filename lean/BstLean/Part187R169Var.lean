import BstLean.Part169Var
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R161Tail
import BstLean.Part187R161Red
import BstLean.Part187R161Fl
import BstLean.Part187R159Hat
import BstLean.Part187R159Win
import BstLean.Part187R159Frame
import BstLean.Part187R159Paper
import BstLean.Part187R159PaperF
import BstLean.Part187R159PaperW
import BstLean.Part187R159Uncond
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Ledger2Gen
import BstLean.Part187R160Lib
import BstLean.Part187R160Event
import BstLean.Part187R160Cov
import BstLean.Part187R160MFNum
import BstLean.Part187R160Cov8
import BstLean.Part187R160ScEv
import BstLean.Part187R160Theta
import BstLean.Part187R160Sc
import BstLean.Part187R160ScTab
import BstLean.Part187R160ScLo
import BstLean.Part187R165Ev
import BstLean.Part187R160MFB3
import BstLean.Part187R160MFB4
import BstLean.Part187R160MFBNum
import BstLean.Part187R160Comb
import BstLean.Part187R163Comb
import BstLean.Part187R164Bnd
import BstLean.Part187R164End
import BstLean.Part187R165End
import BstLean.Part187R169In
import BstLean.Part187R169Mom
import BstLean.Part187R169Op

/-! Part 187 (file `Part187R169Var`): copy of `Part169Var` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part169.R

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (latC Ix muI xLat lamX sigX)
open BstLean.Part162 (lbar psiA)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- `e_b ≤ 0.7315` on the good set (Part 160's `eb16_sharp`). -/
lemma eR_le (hn : 16250 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) : eR c ≤ 7315 / 10000 := by
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.R.window_goodA hn passF passW measurable_passF
    measurable_passW _ c hc
  have hup := BstLean.Part160.R.eb16_sharp hn hτ hθ0 hθ1
    (BstLean.Part164.R.goodC16_of_goodA hn passF passW measurable_passF measurable_passW hc)
    (hc.2.2.1.1.2 hτ)
  have hb := BstLean.Part160.paperDesign_agentCentre passF passW measurable_passF
    measurable_passW c
  rw [← hb] at hup
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at hup
  unfold eR
  have e : normSq (bR c) = normSq ((paperDesign n passF passW measurable_passF
    measurable_passW).bA c.1 c.2.1.1) := rfl
  rw [e, div_le_iff₀ hnR]
  have : 2 / (n : ℝ) ^ 2 * normSq ((paperDesign n passF passW measurable_passF
      measurable_passW).bA c.1 c.2.1.1) * ((n : ℝ) ^ 2 / 2) ≤
      2 / (n : ℝ) * (7315 / 10000) * ((n : ℝ) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hup (by positivity)
  have e1 : 2 / (n : ℝ) ^ 2 * normSq ((paperDesign n passF passW measurable_passF
      measurable_passW).bA c.1 c.2.1.1) * ((n : ℝ) ^ 2 / 2) = normSq ((paperDesign n passF passW
      measurable_passF measurable_passW).bA c.1 c.2.1.1) := by field_simp
  have e2 : 2 / (n : ℝ) * (7315 / 10000) * ((n : ℝ) ^ 2 / 2) = 7315 / 10000 * n := by
    field_simp
  linarith

/-- **`|f̄| ≤ H_f` on the good set.** -/
theorem fbR_le (hn : 16250 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) (a : Ix n) : |fbR c a| ≤ HfN n := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h1, h2⟩ := opB_goodD hn hc
  have hO1 := (O1n_pos (n := n) hn1).le
  have hO2 := (O2n_pos (n := n) hn1).le
  rw [fbR_eq]; unfold fbarS
  refine abs_int_le fun v => ?_
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  have h := fX_sub_le hn1 c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) 0
  have e : fX c 0 = 0 := by unfold fX; rw [hid2_zero']; simp
  rw [e, sub_zero, hid2_zero', sub_zero] at h
  exact h.trans (div_le_div_of_nonneg_right (sqrt_hid2_le hn1 c h1 h2 hO1 hO2 hs v)
    (Real.sqrt_nonneg _))

end BstLean.Part169.R
