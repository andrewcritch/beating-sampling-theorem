import BstLean.Part160Comb
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

/-! Part 187 (file `Part187R160Comb`): copy of `Part160Comb` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156

variable {n : ℕ}

/-- **The window of Part 159 gives `WINDOW_hyp`** on every set inside
`HP n ∩ E_{θ−} ∩ E_{θ+}`, for the design of the paper. -/
theorem window_paper (hn : 16250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {E : Set (Ret n)}
    (hE : E ⊆ BstLean.Part159.HP n ∩ (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n))) :
    WINDOW_hyp (paperDesign n fT wT hf hw) E := by
  intro c hc
  obtain ⟨hH, hm, hp⟩ := hE hc
  obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part159.R.theta_window_paper' hn
    (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hH
  have e := thetaIn_eq (paperDesign n fT wT hf hw) c
  refine ⟨hτ, ?_, ?_⟩
  · have := h1 hm; rw [e] at this; linarith
  · have := h2 hp; rw [e] at this; linarith

end BstLean.Part160.R

