import BstLean.Part188Blocker
import BstLean.Part188CmbK
import BstLean.Part188FrK
import BstLean.Part188Frame
import BstLean.Part188Interfaces
import BstLean.Part188Kap
import BstLean.Part188Kap16
import BstLean.Part188Kap97
import BstLean.Part188LedK
import BstLean.Part188MSplit
import BstLean.Part188MStat
import BstLean.Part188MT167
import BstLean.Part188MT168
import BstLean.Part188MT169
import BstLean.Part188MTop
import BstLean.Part188MTopJ
import BstLean.Part188MW
import BstLean.Part188MW128
import BstLean.Part188Mass
import BstLean.Part188Network
import BstLean.Part188Parallel
import BstLean.Part188Poincare
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153Final
import BstLean.Part188R153PPs4
import BstLean.Part188R154C16
import BstLean.Part188R154Num16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R159Frame
import BstLean.Part188R159Hat
import BstLean.Part188R159Paper
import BstLean.Part188R159PaperF
import BstLean.Part188R159PaperW
import BstLean.Part188R159Uncond
import BstLean.Part188R159Win
import BstLean.Part188R160Comb
import BstLean.Part188R160Cov
import BstLean.Part188R160Cov8
import BstLean.Part188R160Event
import BstLean.Part188R160Ledger2Gen
import BstLean.Part188R160Lib
import BstLean.Part188R160MFB3
import BstLean.Part188R160MFB4
import BstLean.Part188R160MFBNum
import BstLean.Part188R160MFNum
import BstLean.Part188R160Sc
import BstLean.Part188R160ScEv
import BstLean.Part188R160ScLo
import BstLean.Part188R160ScTab
import BstLean.Part188R160Theta
import BstLean.Part188R161Fl
import BstLean.Part188R161Red
import BstLean.Part188R161Tail
import BstLean.Part188R163Comb
import BstLean.Part188R164Bnd
import BstLean.Part188R164End
import BstLean.Part188R165End
import BstLean.Part188R165Ev
import BstLean.Part188R169In
import BstLean.Part188R169Mom
import BstLean.Part188R169Op
import BstLean.Part188R169Var
import BstLean.Part188R170End
import BstLean.Part188R175Cert
import BstLean.Part188R175Mass
import BstLean.Part188R177En
import BstLean.Part188R177Split
import BstLean.Part188R177TopJ40
import BstLean.Part188R178T169b
import BstLean.Part188R178TopJ34
import BstLean.Part188RAll
import BstLean.Part188RW
import BstLean.Part188Rows
import BstLean.Part188Sc97
import BstLean.Part188Schur
import BstLean.Part188WF
import BstLean.Part188Weight

namespace BstLean.Part188
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_16250 {n : ℕ} (hn : 16250 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part187.classifier_paper_uncond_16250 hn t

theorem uncond_16250_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_16250 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

end BstLean.Part188

#print axioms BstLean.Part188.centreCoordinate_mean
#print axioms BstLean.Part188.parallelCentre_of_full
#print axioms BstLean.Part188.parallelCentre_GoodC16
#print axioms BstLean.Part188.weighted_frame_domination
#print axioms BstLean.Part188.WF_of_weighted_covariance
#print axioms BstLean.Part188.dependent_weight_schur
#print axioms BstLean.Part188.weighted_exceptional_moment
#print axioms BstLean.Part188.weighted_covariance_of_gradient
#print axioms BstLean.Part188.centreCoordinate_moment24
#print axioms BstLean.Part188.network_WF_mass
#print axioms BstLean.Part188.MASS_at_of_good_complement
#print axioms BstLean.Part188.reciprocal_weight_mean
#print axioms BstLean.Part188.dependent_row_bound
#print axioms BstLean.Part188.Sc.SSc97_ret_charge
#print axioms BstLean.Part188.eb97_46
#print axioms BstLean.Part188.eb97_54
#print axioms BstLean.Part188.classifier_paper_uncond_16250
#print axioms BstLean.Part188.uncond_16250_eq_172
#print axioms BstLean.Part188.Chain.M.rootFL_fixed22
#print axioms BstLean.Part188.Chain.M.PB_leE
#print axioms BstLean.Part188.Chain.stat_charge21
#print axioms BstLean.Part188.Chain.M.LJ_proved
#print axioms BstLean.Part188.sqrt_16200_old_bound_false
#print axioms BstLean.Part188.location_fluctuation_old_cap_false
