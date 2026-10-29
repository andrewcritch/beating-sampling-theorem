import BstLean.Part182Frame
import BstLean.Part182Cov

/-!
# Part 182 (file `FrameTI`): the Agent frame constant `1.82/n` at `n ≥ 22 000` on the covariance event

No proof is left open; no `native_decide` or `axiom` is used.

**`frameA_T_22000`**: Part 181's `frameA_22000` with the extra event `SCovT` (file `EvW`); the
covariance hypothesis of each piece is `cov_TI` (file `Cov`, the weighted Schur test). No
hypothesis `TI_hyp` enters this theorem: it enters only the CHARGE of `SCovT` (`SCovT_ret_charge`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181

variable {n : ℕ}

/-- **The Agent frame bound `(182/100)/n`, every `n ≥ 22 000`, on the covariance event**: seven
pieces of the window `0.46 ≤ θ_in ≤ 0.528`; on `EA16 D` and the five events `SXM22`, `SSc`,
`SScU`, `SD'`, `SCovT` (Part 181's four and the covariance event of this part). -/
theorem frameA_T_22000 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : ∀ c ∈ E, 0 < D.tau0 c ∧ 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) ∧
      thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXM22 n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n))
    (hE7 : E ⊆ agentEv D (SCovT n)) : FRAME_A_hyp D (182 / 100 / n) E := by
  intro c hc w
  obtain ⟨hτ, hlo46, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n := hE1 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hE4 hc hτ
  have hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hE5 hc hτ
  have hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n := hE6 hc hτ
  have hCv : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT n := hE7 hc hτ
  by_cases h46 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100
  · exact framePieceT_46 hn D hD c hτ hlo46 h46 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 47 / 100) (le_trans (by norm_num) hlo46) h46 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePieceT_47 hn D hD c hτ hlo47 h47 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 48 / 100) (le_trans (by norm_num) hlo47) h47 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePieceT_48 hn D hD c hτ hlo48 h48 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 49 / 100) (le_trans (by norm_num) hlo48) h48 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePieceT_49 hn D hD c hτ hlo49 h49 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 50 / 100) (le_trans (by norm_num) hlo49) h49 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePieceT_50 hn D hD c hτ hlo50 h50 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 51 / 100) (le_trans (by norm_num) hlo50) h50 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePieceT_51 hn D hD c hτ hlo51 h51 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 52 / 100) (le_trans (by norm_num) hlo51) h51 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  exact framePieceT_52 hn D hD c hτ hlo52 hθ1 hG hX hSS hSU hSD
      (cov_TI hn D c hτ (θh := 528 / 1000) (le_trans (by norm_num) hlo52) hθ1 (by norm_num) hX hCv
        (by norm_num)) w

end BstLean.Part182

open BstLean.Part182 in
#print axioms frameA_T_22000
