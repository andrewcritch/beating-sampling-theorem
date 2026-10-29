import BstLean.Part137Smooth

/-! Two distinct auxiliary coordinates for the conditional distance kernel. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 BstLean.Part130 BstLean.Part137

/-- The first smoothing coordinate. -/
def smoothP {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) : Fin (m + 1 + 1) → ℝ :=
  Fin.cons σ (Fin.cons 0 h)

/-- The second, independent smoothing coordinate. -/
def smoothP' {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) : Fin (m + 1 + 1) → ℝ :=
  Fin.cons 0 (Fin.cons σ h)

lemma smoothP_normSq {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) :
    normSq (smoothP h σ) = normSq h + σ ^ 2 := by
  simp [smoothP, normSq_cons]; ring

lemma smoothP'_normSq {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) :
    normSq (smoothP' h σ) = normSq h + σ ^ 2 := by
  simp [smoothP', normSq_cons]; ring

lemma smoothing_dot {m : ℕ} (h : Fin m → ℝ) (σ : ℝ) :
    dotp (smoothP h σ) (smoothP' h σ) = normSq h := by
  unfold smoothP smoothP'
  rw [dotp_cons, dotp_cons]
  simp only [mul_zero, zero_mul, zero_add, dotp, normSq, pow_two]

lemma psiS_scale {c : ℝ} (hc : 0 ≤ c) (σ x : ℝ) :
    psiS (c * σ) (c * x) = c * psiS σ x := by
  unfold psiS
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    dsimp only
    rw [show c * x + c * σ * z = c * (x + σ * z) by ring,
      relu_mul_of_nonneg hc]

/-- Fourth powers of scaled row norms retain the factor `4/N²`. -/
lemma corrected_diagonal_factor {m k : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (ξ : Fin m → Fin k → ℝ) :
    (∑ i, normSq (√(2 / N) • ξ i) ^ 2) =
      4 / N ^ 2 * ∑ i, normSq (ξ i) ^ 2 := by
  have hscale : 0 ≤ 2 / N := div_nonneg (by norm_num) hN
  simp_rw [normSq_smul, Real.sq_sqrt hscale, mul_pow]
  rw [← Finset.mul_sum]
  congr 1
  ring

end BstLean.Part205

#print axioms BstLean.Part205.smoothP_normSq
#print axioms BstLean.Part205.smoothP'_normSq
#print axioms BstLean.Part205.smoothing_dot
#print axioms BstLean.Part205.corrected_diagonal_factor
#print axioms BstLean.Part205.psiS_scale
