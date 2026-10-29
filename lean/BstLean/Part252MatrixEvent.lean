import BstLean.Part252Variance
import BstLean.Part164Ev
import BstLean.Part160Event

/-! The ordinary operator events supply the pointwise variance guard. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169

def FirstMatrix (n : ℕ) : Set (AgFam n) := {k | k.2.1 ∈ Eop n}

theorem firstMatrix_measurable (n : ℕ) : MeasurableSet (FirstMatrix n) :=
  (measurableSet_Eop n).preimage (measurable_fst.comp measurable_snd)

theorem firstMatrix_charge {n : ℕ} (hn : 1 ≤ n) (D : Design n) (hτW : TauWorld D) :
    (retDist D.toCentres).real (agentEv D (FirstMatrix n))ᶜ ≤ exp (-(n : ℝ) / 2) := by
  rw [agentEv_compl]
  apply retDist_agent_charge D hτW (firstMatrix_measurable n) (exp_pos _).le
  intro c τ _
  change (nuA n).real {a | a.1 ∈ (Eop n)ᶜ} ≤ _
  rw [nuA, prod_real_fst]
  exact Eop_prob hn

theorem first_matrix_row (c : Ret 12225) (hc : A1 c ∈ Eop 12225) : OpB (A1 c) 160 := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (12225 : ℝ)) ≤ 1285 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12225 : ℝ) ≤ 111 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12225 : ℝ) + 2 * √12225 ≤ 12447 := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem second_matrix_row (c : Ret 12225) (hc : c ∈ BstLean.Part164.Eop2 12225) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12225 : ℝ)) ≤ 1157 / 10 ^ 7 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12225 + 5)).trans
    (by norm_num)

theorem variance_of_matrix_events (c : Ret 12225) (he : 0 < eR c)
    (hτ : 0 < (paperDesignP 12225).tau0 c)
    (h1 : c ∈ agentEv (paperDesignP 12225) (FirstMatrix 12225))
    (h2 : c ∈ BstLean.Part164.Eop2 12225) (a : BstLean.Part161.Ix 12225) :
    |VR c a| ≤ varianceMax := by
  have hb : normSq (bR c) ≠ 0 := by
    intro hh
    unfold eR at he
    rw [hh, zero_div] at he
    exact (lt_irrefl 0 he)
  exact variance_pointwise_row c hb (first_matrix_row c (h1 hτ)) (second_matrix_row c h2) a

end BstLean.Part252
