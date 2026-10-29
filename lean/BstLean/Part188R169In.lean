import BstLean.Part187All
import BstLean.Part169In
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R161Tail
import BstLean.Part188R161Red
import BstLean.Part188R161Fl
import BstLean.Part188R159Hat
import BstLean.Part188R159Win
import BstLean.Part188R159Frame
import BstLean.Part188R159Paper
import BstLean.Part188R159PaperF
import BstLean.Part188R159PaperW
import BstLean.Part188R159Uncond
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154C16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R154Num16
import BstLean.Part188R160Ledger2Gen
import BstLean.Part188R160Lib
import BstLean.Part188R160Event
import BstLean.Part188R160Cov
import BstLean.Part188R160MFNum
import BstLean.Part188R160Cov8
import BstLean.Part188R160ScEv
import BstLean.Part188R160Theta
import BstLean.Part188R160Sc
import BstLean.Part188R160ScTab
import BstLean.Part188R160ScLo
import BstLean.Part188R165Ev
import BstLean.Part188R160MFB3
import BstLean.Part188R160MFB4
import BstLean.Part188R160MFBNum
import BstLean.Part188R160Comb
import BstLean.Part188R163Comb
import BstLean.Part188R164Bnd
import BstLean.Part188R164End
import BstLean.Part188R165End





namespace BstLean.Part188.Base169_R
open BstLean.Part169 BstLean.Part169.R

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
theorem cA_input (hn : 16200 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) :
    0 < eR c ∧ normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * (BstLean.Part164.chiUp n / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : c ∈ BstLean.Part164.EcA (paperCentres n) := hc.2.1.2.1.2
  have hpos := (BstLean.Part188.Base164_R.cA_of_good hn passF passW measurable_passF measurable_passW
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

end BstLean.Part188.Base169_R
