import BstLean.Part177TopJ40
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

/-! Part 187 (file `Part187R177TopJ40`): copy of `Part177TopJ40` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part177.N40.R

variable {n : ℕ}

lemma hmomN (hn : 16250 ≤ n) : BstLean.Part177.HMom n :=
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

end BstLean.Part177.N40.R
