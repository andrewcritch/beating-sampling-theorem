import BstLean.Part164End
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
import BstLean.Part187R160MFB3
import BstLean.Part187R160MFB4
import BstLean.Part187R160MFBNum
import BstLean.Part187R160Comb
import BstLean.Part187R163Comb
import BstLean.Part187R164Bnd

/-! Part 187 (file `Part187R164End`): copy of `Part164End` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part164.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part163 (roomA roomA_ge Eframe)

variable {n : ℕ}

lemma window_goodA (hn : 16250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (EA : Set (Ret n)) :
    WINDOW_hyp (paperDesign n fT wT hf hw) (goodA n (paperDesign n fT wT hf hw) EA) :=
  BstLean.Part160.R.window_paper hn fT wT hf hw (fun _ hc => ⟨hc.1.1, hc.2.1.1.1, hc.2.1.1.2⟩)

lemma goodC16_of_goodA (hn : 16250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    (c.2.1.1.1, c.2.1.1.2) ∈ BstLean.Part154.GoodC16 n n c.1.2
      ((paperDesign n fT wT hf hw).tau0 c) :=
  hc.2.2.1.1.1.1.1.1 (window_goodA hn fT wT hf hw EA c hc).1

/-- **The eighth moment of `σ` on the good set**: `∫∫σ⁸ ≤ (E0 n)⁸`. -/
theorem hE8_of_good (hn : 16250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      E0 n ^ 8 :=
  sgA8_le (by omega) _ (eop_of_goodC16 (goodC16_of_goodA hn fT wT hf hw hc)) hc.2.1.2.2

/-- **The norm of `c_A` on the good set**: `0 < |c_A|² ≤ CAn n`. -/
theorem cA_of_good (hn : 16250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CAn n := by
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn fT wT hf hw EA c hc
  exact cA_bounds hn _ (paperDesign_agentCentre fT wT hf hw) hτ hθ0 hθ1
    (goodC16_of_goodA hn fT wT hf hw hc) (hc.2.2.1.1.2 hτ) hc.2.1.2.1.2

end BstLean.Part164.R
