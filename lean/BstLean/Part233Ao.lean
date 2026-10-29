import BstLean.Part233ChiSquare
import BstLean.Part159PaperC

/-! Conditional goodAo concentration uses the complete second-layer distribution. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 BstLean.Part130 BstLean.Part136 BstLean.Part137
open BstLean.Part141 BstLean.Part157 BstLean.Part159

/-- The actual source norm has the conditional chi-square representation. -/
theorem goodAo_conditional_charge {n : ℕ} (hm : 1 ≤ mW n)
    (M₁ : Matrix (Fin (mW n)) (Fin (2 * n)) ℝ) {ε e : ℝ}
    (hε : 0 ≤ ε) (he : 0 < e)
    (hS : rowS M₁ / (mW n : ℝ) ≤ 2 * (1 + ε))
    (hcut : 8 * (1 + ε) * (1 + e) ≤ (10 : ℝ) ^ 8) :
    (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).real
      {M₂ | (M₁, M₂) ∉ goodAo n} ≤
      exp (-(mW n : ℝ) * (e - log (1 + e)) / 2) := by
  let ρ : Fin (mW n) → ℝ := fun j => √(normSq (rowOf j M₁))
  have hρ : normSq ρ = rowS M₁ := by
    unfold normSq ρ rowS
    apply Finset.sum_congr rfl
    intro j _
    exact Real.sq_sqrt (normSq_nonneg _)
  let B : Set (Fin (mW n) → ℝ) := {y | (10 : ℝ) ^ 8 < 2 / (mW n : ℝ) * normSq y}
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (measurable_normSq.const_mul _)
  have heq : {M₂ | (M₁, M₂) ∉ goodAo n} =
      (fun M₂ => M₂.mulVec ρ) ⁻¹' B := by
    ext M₂
    simp [goodAo, BstLean.Part141.aOf, B, ρ, not_le]
  rw [heq, ← map_measureReal_apply (measurable_mulVec_right ρ) hB,
    gaussMat_mulVec, map_measureReal_apply (measurable_const_smul _) hB]
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hsub : (fun ξ => (√(2 / (mW n : ℝ)) * √(normSq ρ)) • ξ) ⁻¹' B ⊆
      {ξ | (mW n : ℝ) * (1 + e) ≤ ∑ i, ξ i ^ 2} := by
    intro ξ hξ
    change (10 : ℝ) ^ 8 <
      2 / (mW n : ℝ) * normSq ((√(2 / (mW n : ℝ)) * √(normSq ρ)) • ξ) at hξ
    rw [normSq_smul, sq_scale (by positivity), hρ] at hξ
    have hc : 2 / (mW n : ℝ) * (2 / (mW n : ℝ) * rowS M₁) ≤
        8 * (1 + ε) / (mW n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 4 / (mW n : ℝ))
      convert h using 1 <;> ring
    have hb := mul_le_mul_of_nonneg_right hc (normSq_nonneg ξ)
    have hb' : 2 / (mW n : ℝ) *
        (2 / (mW n : ℝ) * rowS M₁ * normSq ξ) ≤
        8 * (1 + ε) / (mW n : ℝ) * normSq ξ := by
      convert hb using 1 <;> ring
    have hlt : (mW n : ℝ) * (1 + e) < normSq ξ := by
      have hεpos : 0 < 8 * (1 + ε) := by positivity
      have hh : 8 * (1 + ε) * (1 + e) <
          8 * (1 + ε) / (mW n : ℝ) * normSq ξ := lt_of_le_of_lt hcut (hξ.trans_le hb')
      have hh' : 1 + e < normSq ξ / (mW n : ℝ) := by
        by_contra hx
        have hx' := le_of_not_gt hx
        have hle := mul_le_mul_of_nonneg_left hx' hεpos.le
        have hlt : 8 * (1 + ε) * (1 + e) <
            8 * (1 + ε) * (normSq ξ / (mW n : ℝ)) := by
          convert hh using 1 <;> ring
        exact (not_lt_of_ge hle) hlt
      simpa only [mul_comm] using (lt_div_iff₀ hmpos).mp hh'
    exact hlt.le
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (by simpa using (chiSquare_chernoff (ι := Fin (mW n)) he))

end BstLean.Part233
#print axioms BstLean.Part233.goodAo_conditional_charge
