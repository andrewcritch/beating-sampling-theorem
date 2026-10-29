import BstLean.Part163Comb
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
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
import BstLean.Part187R160MFB3
import BstLean.Part187R160MFB4
import BstLean.Part187R160MFBNum
import BstLean.Part187R160Comb

/-! Part 187 (file `Part187R163Comb`): copy of `Part163Comb` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part163.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

/-- **`EVENTS_hyp` with the frame event**: `E₁` becomes `E₁ ∩ Eframe D` and `δ_extra` becomes
`δ_extra + 33515/10⁸` (`n ≥ 16 384`, `τ₀` a function of the World data). -/
theorem events_with_Eframe (hn : 16250 ≤ n) (D : Design n) (hτ : TauWorld D)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra) :
    EVENTS_hyp D.toCentres H (E₁ ∩ Eframe D) Hbar δhid vW (δextra + 33515 / 10 ^ 8) := by
  have hEv0 := BstLean.Part160.R.events_with_EA16 hn D hτ hEv
  have hEv1 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (BstLean.Part160.R.SXi_charge hn) hEv0
  have hEv2 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (BstLean.Part160.R.SXi4n_charge hn) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (BstLean.Part160.R.SXi8n_charge hn) hEv2
  have hEv4 := events_with_agent D hτ (measurableSet_SSc n) (by norm_num)
    (BstLean.Part160.R.SSc_charge_num hn) hEv3
  have hEv5 := events_with_agent D hτ (measurableSet_SScU n) (by norm_num)
    (BstLean.Part160.R.SScU_charge_num hn) hEv4
  have hEv6 := events_with_agent D hτ (measurableSet_SD' n) (by norm_num)
    (fun c τ _ => SD'_charge (by omega) c τ) hEv5
  rw [chain_eq] at hEv6
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hEv6
  exact ⟨h1, h2, h3, h4, h5, h6, by linarith⟩

end BstLean.Part163.R

