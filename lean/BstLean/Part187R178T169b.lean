import BstLean.Part178T169b
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
import BstLean.Part187R177En
import BstLean.Part187R177Split
import BstLean.Part187R178TopJ34

/-! Part 187 (file `Part187R178T169b`): copy of `Part178T169b` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part178.N34.R

-- ===== the bias root `0.0029` (Part 169's `BIASP` has `0.004295`) =====
section SBiasR
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (hellG2 keptIx latC muI BIAS_hyp lamX sigX xLat measurable_latC Ix
  measurableSet_bulkIx measurableSet_keptSet)
open BstLean.Part162 (lbar measurable_lbar)
open BstLean.Part53 (unitF53 measurable_unitF)

open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- **`BIASR` on the good set** (a copy of Part 169's `BstLean.Part169.R.biasP_goodD` with root `0.0029`). -/
theorem biasR_goodD (hn : 16250 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hM : MomIn c ε vmax aw af Hf Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (379 / 10 ^ 5) ^ 2) :
    BIASR c := by
  obtain ⟨he, hcA⟩ := BstLean.Part169.R.cA_input hn hc
  exact biasR_of_inputs (by omega) c he dStar_ge hε1 hT haw haf hHf hCv
    (fun a ha => Sb_lower (by omega) c ha) hcA hM.hVm hM.iW2 hM.iW6 hM.iW8 hM.iF2 hM.iF4 hM.iF8
    hM.if4 hM.if24 hM.ifF2 hM.ifF6 hM.iV hM.hW8 hM.hF8 hM.hf4 hM.hf24 hM.hV hnum

end SBiasR

-- ===== from Part169End.lean =====
section SPart169End
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part166 (goodD)
variable {n : ℕ}
end SPart169End

-- ===== from Part169Mom.lean =====
section SPart169Mom
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (muI)
open BstLean.Part166 (goodD)
variable {n : ℕ}
end SPart169Mom

-- ===== from Part169Int.lean =====
section SPart169Int
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)
variable {n : ℕ}
end SPart169Int

-- ===== from Part169Op.lean =====
section SPart169Op
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI)
open BstLean.Part166 (goodD)
open BstLean.Part150 (c1F c2F rhoC)
variable {n : ℕ}
end SPart169Op

-- ===== from Part169Sig.lean =====
section SPart169Sig
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat hhMat uHat consV hh_normSq)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
variable {n : ℕ}
end SPart169Sig

-- ===== from Part169Var.lean =====
section SPart169Var
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (latC Ix muI xLat lamX sigX)
open BstLean.Part162 (lbar psiA)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 measurable_unitF)
variable {n : ℕ}
end SPart169Var

-- ===== from Part169Num.lean =====
section SPart169Num
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part150 (c1F c2F)
open BstLean.Part166 (goodD)
variable {n : ℕ}
end SPart169Num

end BstLean.Part178.N34.R
