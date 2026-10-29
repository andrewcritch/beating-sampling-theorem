import BstLean.Part187All
import BstLean.Part177Split
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
import BstLean.Part188R175Mass
import BstLean.Part188R175Cert





namespace BstLean.Part188.Base177_R
open BstLean.Part177 BstLean.Part177.R

section SRed
open MeasureTheory ProbabilityTheory Real
open BstLean.Part161
open BstLean.Part157

variable {n : ℕ}

/-- **`REPLA_mix_hyp` from the named hypotheses with a free split.** -/
theorem repla_of_hypsG (hn : 16200 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ d : SplitData n, FLUCT_hyp D t c d hfl ∧ BIAS_hyp D c d hb) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  intro c hc
  obtain ⟨d, hF, hB⟩ := hd c hc
  have hwc := hw c hc
  have h := repla_root_of_split (by omega) D t c hwc.1 hwc.2.1 d hF hB
    (BstLean.Part188.Base161_R.tail_of_window hn D c hwc)
  exact h.trans (repla_arithG hsum)

/-- **Part 161's `BstLean.Part188.Base161_R.repla_of_hyps_chi` with a free split.** -/
theorem repla_of_hyps_chiG (hn : 16200 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
      FLUCT_chi_hyp D c d ε₀ δ₀ slow hfl ∧ BIAS_hyp D c d hb) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  refine repla_of_hypsG hn D t hsum hw fun c hc => ?_
  obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hd c hc
  exact ⟨d, fluct_of_chi D t c d hF, hB⟩

end SRed

section SBias
open BstLean.Part163
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (FLUCT_chi_hyp BIAS_hyp SplitData muI lamX sigX)
open BstLean.Part162

variable {n : ℕ}

end SBias

end BstLean.Part188.Base177_R

namespace BstLean.Part188.Base177_N43_R
open BstLean.Part177 BstLean.Part177.N43 BstLean.Part177.N43.R

section SCA
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part164 (goodA CAn roomB)

variable {n : ℕ}

end SCA

end BstLean.Part188.Base177_N43_R
