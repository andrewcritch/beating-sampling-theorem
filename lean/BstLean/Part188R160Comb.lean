import BstLean.Part187All
import BstLean.Part160Comb
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





namespace BstLean.Part188.Base160_R
open BstLean.Part160 BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156

variable {n : ℕ}

/-- **The window of Part 159 gives `WINDOW_hyp`** on every set inside
`HP n ∩ E_{θ−} ∩ E_{θ+}`, for the design of the paper. -/
theorem window_paper (hn : 16200 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {E : Set (Ret n)}
    (hE : E ⊆ BstLean.Part159.HP n ∩ (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n))) :
    WINDOW_hyp (paperDesign n fT wT hf hw) E := by
  intro c hc
  obtain ⟨hH, hm, hp⟩ := hE hc
  obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part188.Base159_R.theta_window_paper' hn
    (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hH
  have e := thetaIn_eq (paperDesign n fT wT hf hw) c
  refine ⟨hτ, ?_, ?_⟩
  · have := h1 hm; rw [e] at this; linarith
  · have := h2 hp; rw [e] at this; linarith

end BstLean.Part188.Base160_R

