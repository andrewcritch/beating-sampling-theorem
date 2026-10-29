import BstLean.Part169In
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

/-! Part 187 (file `Part187R169In`): copy of `Part169In` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part169.R

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (keptIx latC muI xLat Ix sA lamX sigX)
open BstLean.Part162 (sgA latC_sq_le normSq_xLat_le)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- **`|c_A|²` on the good set** (paper `t7:p08:inputs`): `e_b > 0` and
`|c_A|² ≤ γ_A e_b n χ_A⁺` with `χ_A⁺ = chiUp n / n = 1 + 2√(12/n) + 24/n`. -/
theorem cA_input (hn : 16250 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) :
    0 < eR c ∧ normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * (BstLean.Part164.chiUp n / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : c ∈ BstLean.Part164.EcA (paperCentres n) := hc.2.1.2.1.2
  have hpos := (BstLean.Part164.R.cA_of_good hn passF passW measurable_passF measurable_passW
    hc).1
  obtain ⟨h1, -⟩ := hE
  have hb : normSq ((paperCentres n).bA c.1 c.2.1.1) = normSq (bR c) := rfl
  rw [hb] at h1
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at h1
  have hup : 0 < BstLean.Part164.chiUp n := by unfold BstLean.Part164.chiUp; positivity
  constructor
  · unfold eR
    have : 0 < normSq (bR c) := by
      by_contra hneg
      have h0 : normSq (bR c) = 0 := le_antisymm (le_of_not_gt hneg) (normSq_nonneg _)
      rw [h0] at h1; simp at h1; linarith
    positivity
  · refine h1.trans (le_of_eq ?_)
    unfold eR
    field_simp

end BstLean.Part169.R
