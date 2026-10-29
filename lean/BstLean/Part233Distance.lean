import BstLean.Part233Concentration

/-! Cancellation concentration for the exact source goodDist event. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part205
open BstLean.Part153 (nrm)

theorem conditional_distance_tail {n : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ mW n)
    (M₁ : Matrix (Fin (mW n)) (Fin (2 * n)) ℝ) {Xc M a : ℝ}
    (ha : 0 ≤ a) (hgap : M ≤ a)
    (hcut : a ^ 2 ≤ 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)))
    (hmean : ∫ Ξ, standardDistanceRoot M₁ Ξ ∂stdGauss (Fin (mW n) × Fin (mW n)) ≤ M) :
    (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).real
      {M₂ | (M₁, M₂) ∉ BstLean.Part140.goodDist n Xc} ≤
      exp (-(a - M) ^ 2 /
        (2 * ((√(firstQ M₁) + nrm (h1bar M₁)) / (mW n : ℝ)) ^ 2)) := by
  have hN : 1 ≤ 2 * n := by omega
  have hset : MeasurableSet {M₂ | (M₁, M₂) ∉ BstLean.Part140.goodDist n Xc} :=
    ((BstLean.Part140.goodDist_meas hn Xc).preimage
      (measurable_const.prodMk measurable_id)).compl
  rw [gaussMat, map_measureReal_apply (by fun_prop) hset]
  have hsub : (fun Ξ : Fin (mW n) × Fin (mW n) → ℝ =>
        Matrix.of fun i j => √(2 / (mW n : ℝ)) * Ξ (i, j)) ⁻¹'
        {M₂ | (M₁, M₂) ∉ BstLean.Part140.goodDist n Xc} ⊆
      {Ξ | a < standardDistanceRoot M₁ Ξ} := by
    intro Ξ hΞ
    have hh : 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) <
        standardDistanceRoot M₁ Ξ ^ 2 := by
      rw [standardDistanceRoot_sq hm]
      exact not_le.mp hΞ
    have hR : 0 ≤ standardDistanceRoot M₁ Ξ := by
      unfold standardDistanceRoot
      exact mul_nonneg (by positivity) (BstLean.Part153.nrm_nonneg _)
    change a < standardDistanceRoot M₁ Ξ
    nlinarith
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (standardDistanceRoot_tail hN M₁ hmean hgap)

/-- A positive variance certificate can enlarge the squared Lipschitz constant. -/
theorem conditional_distance_tail_of_variance {n : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ mW n)
    (M₁ : Matrix (Fin (mW n)) (Fin (2 * n)) ℝ) {Xc M a V : ℝ}
    (ha : 0 ≤ a) (hgap : M ≤ a) (hV : 0 < V)
    (hcut : a ^ 2 ≤ 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)))
    (hmean : ∫ Ξ, standardDistanceRoot M₁ Ξ ∂stdGauss (Fin (mW n) × Fin (mW n)) ≤ M)
    (hL0 : 0 < (√(firstQ M₁) + nrm (h1bar M₁)) / (mW n : ℝ))
    (hL : ((√(firstQ M₁) + nrm (h1bar M₁)) / (mW n : ℝ)) ^ 2 ≤ V) :
    (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).real
      {M₂ | (M₁, M₂) ∉ BstLean.Part140.goodDist n Xc} ≤
      exp (-(a - M) ^ 2 / (2 * V)) := by
  refine (conditional_distance_tail hn hm M₁ ha hgap hcut hmean).trans ?_
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left hL (by norm_num)))

end BstLean.Part233
#print axioms BstLean.Part233.conditional_distance_tail
#print axioms BstLean.Part233.conditional_distance_tail_of_variance
