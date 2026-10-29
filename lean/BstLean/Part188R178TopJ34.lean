import BstLean.Part187All
import BstLean.Part178TopJ34
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





namespace BstLean.Part188.Base178_N34_R
open BstLean.Part178 BstLean.Part178.N34 BstLean.Part178.N34.R

variable {n : ℕ}

lemma hmomN (hn : 16200 ≤ n) : BstLean.Part177.HMom n :=
  fun x hx q => BstLean.Part177.hid2_mom_unit (by omega) x hx q

section SJ
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
open BstLean.Part175.N50 (winC528 Scert528 measurableSet_Scert528 scert_of_good528 roomF roomF_ge)
variable {n : ℕ}


end SJ

end BstLean.Part188.Base178_N34_R
