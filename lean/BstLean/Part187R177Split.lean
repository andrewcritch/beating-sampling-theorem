import BstLean.Part177Split
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
import BstLean.Part187R175Cert

/-! Part 187 (file `Part187R177Split`): copy of `Part177Split` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part177.R

section SRed
open MeasureTheory ProbabilityTheory Real
open BstLean.Part161
open BstLean.Part157

variable {n : ℕ}

/-- **`REPLA_mix_hyp` from the named hypotheses with a free split.** -/
theorem repla_of_hypsG (hn : 16250 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ d : SplitData n, FLUCT_hyp D t c d hfl ∧ BIAS_hyp D c d hb) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  intro c hc
  obtain ⟨d, hF, hB⟩ := hd c hc
  have hwc := hw c hc
  have h := repla_root_of_split (by omega) D t c hwc.1 hwc.2.1 d hF hB
    (BstLean.Part161.R.tail_of_window hn D c hwc)
  exact h.trans (repla_arithG hsum)

/-- **Part 161's `BstLean.Part161.R.repla_of_hyps_chi` with a free split.** -/
theorem repla_of_hyps_chiG (hn : 16250 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
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

end BstLean.Part177.R

namespace BstLean.Part177.N43.R

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

end BstLean.Part177.N43.R
