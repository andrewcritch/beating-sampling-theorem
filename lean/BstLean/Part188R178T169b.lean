import BstLean.Part187All
import BstLean.Part178T169b
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
import BstLean.Part188R177En
import BstLean.Part188R177Split
import BstLean.Part188R178TopJ34





namespace BstLean.Part188.Base178_N34_R
open BstLean.Part178 BstLean.Part178.N34 BstLean.Part178.N34.R

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
/-- **`BIASR` on the good set** (a copy of Part 169's `BstLean.Part188.Base169_R.biasP_goodD` with root `0.0029`). -/
theorem biasR_goodD (hn : 16200 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / BstLean.Part178.N34.dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hM : BstLean.Part178.N34.MomIn c ε vmax aw af Hf Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) BstLean.Part178.N34.dStar ε vmax aw af Hf Cv ≤ (379 / 10 ^ 5) ^ 2) :
    BIASR c := by
  obtain ⟨he, hcA⟩ := BstLean.Part188.Base169_R.cA_input hn hc
  exact biasR_of_inputs (by omega) c he BstLean.Part178.N34.dStar_ge hε1 hT haw haf hHf hCv
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

end BstLean.Part188.Base178_N34_R
