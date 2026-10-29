import BstLean.Part187All
import BstLean.Part164Bnd
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
import BstLean.Part188R160MFB3
import BstLean.Part188R160MFB4
import BstLean.Part188R160MFBNum
import BstLean.Part188R160Comb
import BstLean.Part188R163Comb





namespace BstLean.Part188.Base164_R
open BstLean.Part164 BstLean.Part164.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI latC xLat)
open BstLean.Part162 (sgA sgA_nonneg)

variable {n : ℕ}

/-- **`0 < |c_A|² ≤ C_A(n)` on the norm event** with `GoodC16`, `SSc` and the window
(`n ≥ 16 384`). -/
theorem cA_bounds (hn : 16200 ≤ n) (D : Design n) (hD : AgentCentre154 D) {c : Ret n}
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ BstLean.Part154.GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hc : c ∈ EcA D.toCentres) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CAn n := by
  obtain ⟨-, -, -, hpos, -, -, -⟩ := BstLean.Part188.Base160_R.centre16 hn hτ hθ0 hθ1 hG
  have hup := BstLean.Part188.Base160_R.eb16_sharp hn hτ hθ0 hθ1 hG hS
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
  rw [← hb] at hup hpos
  obtain ⟨h1, h2⟩ := hc
  have hm : (0 : ℝ) < (mA n : ℝ) := by
    have : 0 < mA n := by unfold mA; exact pow_pos (by omega) 2
    exact_mod_cast this
  have hlo := chiLo_pos (n := n) (by omega)
  have hup0 : 0 ≤ chiUp n := by unfold chiUp; positivity
  refine ⟨lt_of_lt_of_le ?_ h2, h1.trans ?_⟩
  · exact mul_pos (mul_pos (div_pos two_pos hm) hpos) hlo
  · unfold CAn
    exact mul_le_mul_of_nonneg_right hup hup0

end BstLean.Part188.Base164_R
