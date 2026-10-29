import BstLean.Part187All
import BstLean.Part163Comb
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
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
import BstLean.Part188R160MFB3
import BstLean.Part188R160MFB4
import BstLean.Part188R160MFBNum
import BstLean.Part188R160Comb





namespace BstLean.Part188.Base163_R
open BstLean.Part163 BstLean.Part163.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

/-- **`EVENTS_hyp` with the frame event**: `E₁` becomes `E₁ ∩ Eframe D` and `δ_extra` becomes
`δ_extra + 33515/10⁸` (`n ≥ 16 384`, `τ₀` a function of the World data). -/
theorem events_with_Eframe (hn : 16200 ≤ n) (D : Design n) (hτ : TauWorld D)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra) :
    EVENTS_hyp D.toCentres H (E₁ ∩ Eframe D) Hbar δhid vW (δextra + 33515 / 10 ^ 8) := by
  have hEv0 := BstLean.Part188.Base160_R.events_with_EA16 hn D hτ hEv
  have hEv1 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (BstLean.Part188.Base160_R.SXi_charge hn) hEv0
  have hEv2 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (BstLean.Part188.Base160_R.SXi4n_charge hn) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (BstLean.Part188.Base160_R.SXi8n_charge hn) hEv2
  have hEv4 := events_with_agent D hτ (measurableSet_SSc n) (by norm_num)
    (BstLean.Part188.Base160_R.SSc_charge_num hn) hEv3
  have hEv5 := events_with_agent D hτ (measurableSet_SScU n) (by norm_num)
    (BstLean.Part188.Base160_R.SScU_charge_num hn) hEv4
  have hEv6 := events_with_agent D hτ (measurableSet_SD' n) (by norm_num)
    (fun c τ _ => SD'_charge (by omega) c τ) hEv5
  rw [chain_eq] at hEv6
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hEv6
  exact ⟨h1, h2, h3, h4, h5, h6, by linarith⟩

end BstLean.Part188.Base163_R

