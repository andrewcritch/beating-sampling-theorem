import BstLean.Part162Gm
import BstLean.Part153Lp

/-! The paper rotation constant has a separate order-two branch. -/
namespace BstLean.Part195
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq gradSq_nonneg)
open BstLean.Part162 (gmom gmom_nonneg)

/-- The product is the odd double factorial at order `2q`. -/
noncomputable def oddMoment (q : ℕ) : ℝ :=
  ∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)

/-- The constant from the paper includes sharp Gaussian Poincare at order two. -/
noncomputable def rotationConstant (q : ℕ) : ℝ :=
  if q = 1 then 1 else π / 2 * oddMoment q ^ (((2 * q : ℕ) : ℝ)⁻¹)

lemma oddMoment_eq (q : ℕ) : oddMoment q = gmom (2 * q) :=
  (BstLean.Part162.gmom_even q).symm

lemma rotationConstant_one : rotationConstant 1 = 1 := by
  simp [rotationConstant]

lemma rotationConstant_nonneg (q : ℕ) : 0 ≤ rotationConstant q := by
  unfold rotationConstant
  split_ifs
  · norm_num
  · rw [oddMoment_eq]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (gmom_nonneg _) _)

lemma rotationConstant_pow {q : ℕ} (hq : 1 ≤ q) (hne : q ≠ 1) :
    rotationConstant q ^ (2 * q) = (π / 2) ^ (2 * q) * gmom (2 * q) := by
  rw [rotationConstant, if_neg hne, oddMoment_eq, mul_pow,
    Real.rpow_inv_natCast_pow (gmom_nonneg _) (by omega)]

/-- The even rotation inequality for every finite Gaussian dimension and Lipschitz function. -/
theorem rotation_even {ι : Type} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K) (hf : EuLip f K)
    {q : ℕ} (hq : 1 ≤ q) :
    ∫ x, |f x - ∫ y, f y ∂stdGauss ι| ^ (2 * q) ∂stdGauss ι ≤
      rotationConstant q ^ (2 * q) * ∫ x, gradSq f x ^ q ∂stdGauss ι := by
  by_cases he : q = 1
  · subst q
    simpa [rotationConstant_one, sq_abs, gradSq] using
      BstLean.Part151.poincare_lip hK hf
  · have h := BstLean.Part162.poincare_p hK hf (by omega : 1 ≤ 2 * q)
    simp only [pow_mul, Real.sq_sqrt (gradSq_nonneg _ _)] at h
    rw [rotationConstant_pow hq he]
    simpa only [mul_assoc, pow_mul] using h

/-- The norm form uses the existing absolute moment norm definition. -/
theorem rotation_even_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K) (hf : EuLip f K)
    {q : ℕ} (hq : 1 ≤ q) :
    BstLean.Part161.momN (stdGauss ι) (2 * q)
      (fun x => f x - ∫ y, f y ∂stdGauss ι) ≤
    rotationConstant q * BstLean.Part161.momN (stdGauss ι) (2 * q)
      (fun x => √(gradSq f x)) := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0)
    (mul_nonneg (rotationConstant_nonneg q) (BstLean.Part161.momN_nonneg _ _ _))
  rw [mul_pow, BstLean.Part161.momN_pow _ (by omega),
    BstLean.Part161.momN_pow _ (by omega)]
  simp only [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul,
    Real.sq_sqrt (gradSq_nonneg _ _)]
  simpa only [pow_mul] using rotation_even hK hf hq

end BstLean.Part195
#print axioms BstLean.Part195.rotationConstant_pow
#print axioms BstLean.Part195.rotation_even
#print axioms BstLean.Part195.rotation_even_norm
