import BstLean.Part209FirstMean
import BstLean.Part209Holder
import BstLean.Part209Scalar
import BstLean.Part200Network

/-! Deterministic comparison of the conditional mean with the composed-kernel derivative. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

variable {n m p : ℕ}

lemma pairCos_relu_mem (a b : Fin m → ℝ) : pairCos (reluV a) (reluV b) ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 ≤ dotp (reluV a) (reluV b) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (relu_nonneg _) (relu_nonneg _)
  have hp : 0 ≤ nrm (reluV a) * nrm (reluV b) := mul_nonneg (nrm_nonneg _) (nrm_nonneg _)
  refine ⟨div_nonneg hd hp, ?_⟩
  rcases hp.eq_or_lt with hp | hp
  · simp [pairCos, ← hp]
  · apply (div_le_one hp).mpr
    exact (le_abs_self _).trans (abs_dot_le _ _)

lemma unit_dot_mem {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    dotp x x' ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_dot_le x x'
  simp only [hx, hx', sqrt_one, one_mul] at h
  exact abs_le.mp h

lemma nrm_unit_projection {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    nrm (projT x *ᵥ x') = sqrt (1 - dotp x x' ^ 2) := by
  unfold nrm
  rw [projT_mulVec_sj, normSq_sub_smul, hx, hx', dotProduct_comm x' x]
  congr 1
  change 1 - 2 * dotp x x' * dotp x x' + dotp x x' ^ 2 * 1 = _
  ring

lemma projected_ideal_le {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    nrm (kernelSlope (dotp x x') • (projT x *ᵥ x')) ≤ 3 / 5 := by
  have hk : 0 ≤ kernelSlope (dotp x x') := (kappa_deriv_bounds _).1
  rw [nrm_smul, abs_of_nonneg hk, nrm_unit_projection hx hx']
  exact projected_kernelSlope_le (unit_dot_mem hx hx').1 (unit_dot_mem hx hx').2

lemma comparison_algebra (a b q : Fin n → ℝ) (k k₀ c : ℝ)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hc : 0 ≤ c) :
    nrm (k • a + c • b - k₀ • q) ≤ nrm (a - q) + |k - k₀| * nrm q + c * nrm b := by
  have he : k • a + c • b - k₀ • q = (k • (a - q) + (k - k₀) • q) + c • b := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  have h₁ := nrm_add_le (k • (a - q) + (k - k₀) • q) (c • b)
  have h₂ := nrm_add_le (k • (a - q)) ((k - k₀) • q)
  rw [nrm_smul, nrm_smul, abs_of_nonneg hk0] at h₂
  rw [nrm_smul, abs_of_nonneg hc] at h₁
  have h₃ := mul_le_mul_of_nonneg_right hk1 (nrm_nonneg (a - q))
  nlinarith

lemma pairMean_he_expansion (hp : 1 ≤ p) (A : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) (ha : reluV (A *ᵥ x) ≠ 0) :
    pairMean (p := p) (2 / (p : ℝ)) A x x' =
      kernelSlope (pairCos (reluV (A *ᵥ x)) (reluV (A *ᵥ x'))) • firstPair A x x' +
      (nrm (reluV (A *ᵥ x')) / nrm (reluV (A *ᵥ x)) *
        sqrt (1 - pairCos (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) ^ 2) / π) • firstPair A x x := by
  rw [pairMean_he_nonzero hp A x x' ha, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

/-- This pointwise bound supplies the three regular-set terms before moment integration. -/
theorem pairMean_comparison (hp : 1 ≤ p) (A : Matrix (Fin m) (Fin n) ℝ)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (ha : reluV (A *ᵥ x) ≠ 0) (α : ℝ) :
    nrm (α • pairMean (p := p) (2 / (p : ℝ)) A x x' - pairIdeal x x') ≤
      nrm (α • firstPair A x x' - kernelSlope (dotp x x') • (projT x *ᵥ x')) +
      3 / 10 * sqrt |pairCos (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) - kappa (dotp x x')| +
      (nrm (reluV (A *ᵥ x')) / nrm (reluV (A *ᵥ x)) / π) * nrm (α • firstPair A x x) := by
  let r := pairCos (reluV (A *ᵥ x)) (reluV (A *ᵥ x'))
  let r₀ := dotp x x'
  let c := nrm (reluV (A *ᵥ x')) / nrm (reluV (A *ᵥ x)) * sqrt (1 - r ^ 2) / π
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (div_nonneg (nrm_nonneg _) (nrm_nonneg _))
    (sqrt_nonneg _)) pi_pos.le
  have hk := kappa_deriv_bounds r
  have h := comparison_algebra (α • firstPair A x x') (α • firstPair A x x)
    (kernelSlope r₀ • (projT x *ᵥ x')) (kernelSlope r) (kernelSlope (kappa r₀)) c hk.1 hk.2 hc
  have he : α • pairMean (p := p) (2 / (p : ℝ)) A x x' - pairIdeal x x' =
      kernelSlope r • (α • firstPair A x x') + c • (α • firstPair A x x) -
        kernelSlope (kappa r₀) • (kernelSlope r₀ • (projT x *ᵥ x')) := by
    rw [pairMean_he_expansion hp A x x' ha, smul_add, smul_comm α, smul_comm α]
    simp only [pairIdeal, smul_smul]
    rfl
  rw [he]
  have hr := pairCos_relu_mem (A *ᵥ x) (A *ᵥ x')
  have hr₀ := unit_dot_mem hx hx'
  have hκ : kappa r₀ ∈ Icc (0 : ℝ) 1 := kappa_mem hr₀.1 hr₀.2
  have hh := kernelSlope_holder hr hκ
  have hq := projected_ideal_le hx hx'
  have hterm := mul_le_mul hh hq (nrm_nonneg _) (by positivity)
  have hs : sqrt (1 - r ^ 2) ≤ 1 := by
    apply sqrt_le_one.mpr
    nlinarith [sq_nonneg r]
  have hc' : c ≤ nrm (reluV (A *ᵥ x')) / nrm (reluV (A *ᵥ x)) / π := by
    have hh := mul_le_mul_of_nonneg_left hs
      (div_nonneg (nrm_nonneg (reluV (A *ᵥ x'))) (nrm_nonneg (reluV (A *ᵥ x))))
    exact div_le_div_of_nonneg_right (by simpa using hh) pi_pos.le
  have hlast := mul_le_mul_of_nonneg_right hc' (nrm_nonneg (α • firstPair A x x))
  dsimp only [r, r₀] at h hterm hlast ⊢
  nlinarith

end BstLean.Part209
