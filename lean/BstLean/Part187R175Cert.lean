import BstLean.Part175Cert
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
import BstLean.Part187R169Var
import BstLean.Part187R170End
import BstLean.Part187R175Mass

/-! Part 187 (file `Part187R175Cert`): copy of `Part175Cert` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part175.N50.R

-- ===== from Part166Th.lean =====
section STh
open BstLean.Part166
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open scoped ENNReal
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part160 (WqN WqN_le exp_neg_13_le integrable_wqq)
open BstLean.Part161 (consV muI consV_map normSq_consV consV_add consV_smul measurable_consV
  stdGauss_normSq_zero)
open BstLean.Part157 (latitude)
end STh


section SCert
open BstLean.Part167
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157
  BstLean.Part160
open BstLean.Part161 (muI Ix BIAS_hyp lamX sigX)
open BstLean.Part162 (dPaper psiA)
open BstLean.Part153 (nuA)
open BstLean.Part166 (psiK psiK_nonneg fK sK winC certI Cf Scert measurableSet_Scert
  markov12 measurable_psiK_f measurable_psiK_s goodD measurable_certI measurable_thetaC_key pow64_le
  integral_le_of_lintegral psiA_lam_eq psiA_sig_eq)
open BstLean.Part165 (goodC roomC roomC_ge)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA)
variable {n : ℕ}

/-- **`Scert` on a good set that contains `Scert528`**: in the window `θ ≤ 0.528` of the good set,
the condition of `Scert` is the condition of `Scert528`. -/
theorem scert_of_good528 (hn : 16250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {E : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) E)
    (hS : c ∈ agentEv (paperDesign n fT wT hf hw) (Scert528 n)) :
    c ∈ agentEv (paperDesign n fT wT hf hw) (Scert n) := by
  intro hτ hw'
  obtain ⟨hτ', -, h528⟩ := BstLean.Part175.R.win528_goodA hn fT wT hf hw E hc
  exact hS hτ ⟨hw'.1, hw'.2.1, h528⟩

end SCert

end BstLean.Part175.N50.R
