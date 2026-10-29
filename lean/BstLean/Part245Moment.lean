import BstLean.Part153PPs3
import BstLean.Part160Cov8

/-! Part 245: the fourth-moment coefficient on every M1/M2 cell. -/
namespace BstLean.Part245
open MeasureTheory Real BstLean.Part153
open BstLean.Part157 BstLean.Part160

/-- The same bound applies to every centre and every positive scale. No cell payment occurs. -/
theorem moment_M12 {n : ℕ} (hn : 11883 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | (13 / 10 : ℝ) * (2 / (n : ℝ)) / n < Xi4 a.1 a.2 c τ}
      ≤ 5 / 100000 := by
  haveI : IsProbabilityMeasure (nuA n) := by
    unfold nuA BstLean.Part130.gaussMat
    infer_instance
  refine (measureReal_mono (fun a ha => ?_) (measure_ne_top _ _)).trans
    (lemmaPP_numeric (by omega) c hτ)
  have hcoef : (127 / 100 : ℝ) * (2 / (n : ℝ)) / n ≤
      (13 / 10 : ℝ) * (2 / (n : ℝ)) / n := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (127 / 100 : ℝ) ≤ 13 / 10)
        (by positivity)) (Nat.cast_nonneg n)
  exact lt_of_le_of_lt hcoef ha

/-- One moment event for all theta and overlap cells. -/
def MomentM12 (n : ℕ) : Set (AgFam n) :=
  {k | Xi4 k.2.1 k.2.2 k.1.1 k.1.2 ≤ (13 / 10 : ℝ) * (2 / (n : ℝ)) / n}

theorem measurableSet_MomentM12 (n : ℕ) : MeasurableSet (MomentM12 n) := by
  have hm : Measurable (fun k : AgFam n => Xi4 k.2.1 k.2.2 k.1.1 k.1.2) := by
    simp_rw [Xi4_eq_XqN]
    exact (measurable_XqN_fam 2).sqrt.const_mul _
  exact measurableSet_le hm measurable_const

/-- Retained-data integration pays the moment charge once. -/
theorem moment_M12_ret {n : ℕ} (hn : 11883 ≤ n) (D : Design n) (hτ : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (MomentM12 n))ᶜ ≤ 5 / 100000 := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτ (measurableSet_MomentM12 n) (by norm_num)
  intro c τ hτ
  simpa only [MomentM12, Set.mem_setOf_eq, not_le] using moment_M12 hn c hτ

end BstLean.Part245
