import BstLean.Part187All
import BstLean.Part175Mass
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
import BstLean.Part188R169In
import BstLean.Part188R169Mom
import BstLean.Part188R169Op
import BstLean.Part188R169Var
import BstLean.Part188R170End





namespace BstLean.Part188.Base175_R
open BstLean.Part175 BstLean.Part175.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr nuA jS)
open BstLean.Part134 (res sig)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA hE8_of_good CAn E0 E0_nonneg roomB roomB_ge)

variable {n : ℕ}


/-- **The window of Part 159 on the good set `goodA`**: `τ₀ > 0` and `0.465 ≤ θ_in ≤ 0.528`. -/
theorem win528_goodA (hn : 16200 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (EA : Set (Ret n)) {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    0 < (paperDesign n fT wT hf hw).tau0 c ∧
      465 / 1000 ≤ thetaC c.1.2 ((paperDesign n fT wT hf hw).tau0 c) ∧
      thetaC c.1.2 ((paperDesign n fT wT hf hw).tau0 c) ≤ 528 / 1000 := by
  obtain ⟨hτ, -, -, -, h1, h2⟩ := BstLean.Part188.Base159_R.theta_window_paper' hn
    (paperDesign n fT wT hf hw) rfl (fun _ => rfl) hc.1.1
  have e := BstLean.Part160.thetaIn_eq (paperDesign n fT wT hf hw) c
  refine ⟨hτ, ?_, ?_⟩
  · have := h1 hc.2.1.1.1; rw [e] at this; exact this
  · have := h2 hc.2.1.1.2; rw [e] at this; exact this

end BstLean.Part188.Base175_R
