import BstLean.Part160Event
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16

/-! Part 187 (file `Part187R160Event`): copy of `Part160Event` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part150 (rhoC thetaC bT)
open BstLean.Part153 (nuA)

variable {n : ℕ}

lemma SC16_charge (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ BstLean.Part154.SC16 n} ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 :=
  BstLean.Part154.R.GoodC16_prob hn n c hτ

lemma charge16_le (hn : 16250 ≤ n) :
    rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 ≤ 15 / 100000 := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : rexp (-(n : ℝ) / 2) ≤ rexp (-12) := Real.exp_le_exp.mpr (by linarith)
  have h2 := exp_neg_twelve_le
  have h3 : 3445 / (n : ℝ) ^ 2 ≤ 3445 / (16250 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hnR 2)
  have h4 : (3445 : ℝ) / 16250 ^ 2 ≤ 1305 / 10 ^ 8 := by norm_num
  linarith

/-- **`EVENTS_hyp` with the Agent event of Part 154**: `E₁` becomes `E₁ ∩ EA16 D`, and
`δ_extra` becomes `δ_extra + 15/100000`. -/
theorem events_with_EA16 (hn : 16250 ≤ n) (D : Design n) (hτ : TauWorld D)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra) :
    EVENTS_hyp D.toCentres H (E₁ ∩ EA16 D) Hbar δhid vW (δextra + 15 / 100000) := by
  rw [EA16_eq]
  exact events_with_agent D hτ (BstLean.Part154.measurableSet_SC16 (by omega)) (by norm_num)
    (fun c τ h => (SC16_charge hn c τ h).trans (charge16_le hn)) hEv

end BstLean.Part160.R

