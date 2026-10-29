import BstLean.Part56Defs

/-! Algebraic facts for the normalized rank-one Gaussian projection. -/

namespace BstLean.Part56

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part41 (Mono)

private def perpVec {n : ℕ} (v g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => g i - (∑ l, v l * g l) * v i

private lemma perpVec_orth {n : ℕ} (v g : Fin n → ℝ) (hv : UnitV v) :
    ∑ i, v i * perpVec v g i = 0 := by
  unfold perpVec
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have h : (∑ i, v i * ((∑ l, v l * g l) * v i)) =
      (∑ l, v l * g l) * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [h, hv, mul_one, sub_self]

/-- Normalization preserves orthogonality, including when the projection is zero. -/
theorem perpDir_orth56 {n : ℕ} (v g : Fin n → ℝ) (hv : UnitV v) :
    ∑ i, v i * perpDir v g i = 0 := by
  change (∑ i, v i * ((1 / Real.sqrt (∑ l, perpVec v g l ^ 2)) *
    perpVec v g i)) = 0
  have h : (∑ i, v i * ((1 / Real.sqrt (∑ l, perpVec v g l ^ 2)) *
      perpVec v g i)) =
      (1 / Real.sqrt (∑ l, perpVec v g l ^ 2)) * ∑ i, v i * perpVec v g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [h, perpVec_orth v g hv, mul_zero]

/-- The normalized projection has squared Euclidean norm at most one. -/
theorem perpDir_sq_le_one56 {n : ℕ} (v g : Fin n → ℝ) :
    ∑ i, perpDir v g i ^ 2 ≤ 1 := by
  let q : ℝ := ∑ i, perpVec v g i ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun i hi => sq_nonneg _
  have he : (∑ i, perpDir v g i ^ 2) = (1 / Real.sqrt q) ^ 2 * q := by
    change (∑ i, ((1 / Real.sqrt q) * perpVec v g i) ^ 2) = _
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  rw [he]
  by_cases hz : q = 0
  · simp [hz]
  · have hs : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hq (Ne.symm hz)))
    rw [div_pow, one_pow, Real.sq_sqrt hq, one_div_mul_cancel hz]

/-- Every normalized coordinate lies in the closed unit interval in absolute value. -/
theorem perpDir_abs_le_one56 {n : ℕ} (v g : Fin n → ℝ) (i : Fin n) :
    |perpDir v g i| ≤ 1 := by
  have hi : perpDir v g i ^ 2 ≤ ∑ l, perpDir v g l ^ 2 :=
    Finset.single_le_sum (fun l hl => sq_nonneg _) (Finset.mem_univ i)
  have h := hi.trans (perpDir_sq_le_one56 v g)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (perpDir v g i + 1),
    sq_nonneg (perpDir v g i - 1)]

/-- Subtracting the component along a unit vector subtracts its squared length. -/
theorem perpVec_sq56 {n : ℕ} (v g : Fin n → ℝ) (hv : UnitV v) :
    (∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2) =
      (∑ i, g i ^ 2) - (∑ l, v l * g l) ^ 2 := by
  let c := ∑ l, v l * g l
  have h : (∑ i, (g i - c * v i) ^ 2) =
      (∑ i, g i ^ 2) - 2 * c * (∑ i, v i * g i) + c ^ 2 * ∑ i, v i ^ 2 := by
    simp_rw [sub_sq, mul_pow]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h₁ : (∑ i, 2 * g i * (c * v i)) = 2 * c * ∑ i, v i * g i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h₁, ← Finset.mul_sum]
  change (∑ i, (g i - c * v i) ^ 2) = _
  rw [h, hv]
  dsimp [c]
  ring

/-- The normalization has squared norm one when its denominator is positive. -/
theorem perpDir_sq_eq_one56 {n : ℕ} (v g : Fin n → ℝ)
    (hg : 0 < ∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2) :
    ∑ i, perpDir v g i ^ 2 = 1 := by
  let q : ℝ := ∑ i, perpVec v g i ^ 2
  have hq : 0 < q := hg
  change (∑ i, ((1 / Real.sqrt q) * perpVec v g i) ^ 2) = 1
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  change (1 / Real.sqrt q) ^ 2 * q = 1
  rw [div_pow, one_pow, Real.sq_sqrt hq.le, one_div_mul_cancel hq.ne']

/-- The normalized projection is measurable at the zero denominator as well. -/
theorem measurable_perpDir56 {n : ℕ} (v : Fin n → ℝ) :
    Measurable (perpDir v) := by
  have hm (i : Fin n) : Measurable (fun g : Fin n → ℝ =>
      g i - (∑ l, v l * g l) * v i) := by
    exact (measurable_pi_apply i).sub
      ((Finset.measurable_sum Finset.univ fun l hl =>
        (measurable_const : Measurable (fun _ : Fin n → ℝ => v l)).mul
          (measurable_pi_apply l)).mul_const (v i))
  have hq : Measurable (fun g : Fin n → ℝ =>
      ∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2) :=
    Finset.measurable_sum _ fun i hi => (hm i).pow_const 2
  apply Measurable.of_eval
  intro i
  exact (measurable_const.div hq.sqrt).mul (hm i)

/-- Reversing the Gaussian input reverses the normalized projection. -/
theorem perpDir_neg56 {n : ℕ} (v g : Fin n → ℝ) :
    perpDir v (-g) = -perpDir v g := by
  have hs : (∑ l, v l * (-g) l) = -(∑ l, v l * g l) := by
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hq : (∑ i, ((-g) i - (∑ l, v l * (-g) l) * v i) ^ 2) =
      ∑ i, (g i - (∑ l, v l * g l) * v i) ^ 2 := by
    rw [hs]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.neg_apply]
    ring
  ext i
  simp only [perpDir, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  change (1 / Real.sqrt (∑ l, ((-g) l - (∑ j, v j * (-g) j) * v l) ^ 2)) *
      ((-g) i - (∑ j, v j * (-g) j) * v i) = _
  rw [hq, hs]
  simp only [Pi.neg_apply]
  ring

/-- Every coordinate of the normalized projection is integrable. -/
theorem integrable_perpDir56 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    Integrable (fun g => perpDir v g i) (stdGauss (Fin n)) := by
  apply Integrable.of_bound
    ((measurable_pi_apply i).comp (measurable_perpDir56 v)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun g => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using perpDir_abs_le_one56 v g i

/-- Gaussian sign symmetry gives zero mean without an exceptional-set argument. -/
theorem integral_perpDir56 {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (∫ g, perpDir v g i ∂stdGauss (Fin n)) = 0 := by
  classical
  have hi := integral_map (μ := stdGauss (Fin n))
    (measurable_neg : Measurable (fun g : Fin n → ℝ => -g)).aemeasurable
    ((measurable_pi_apply i).comp (measurable_perpDir56 v)).aestronglyMeasurable
  have hneg : (stdGauss (Fin n)).map (fun z => -z) = stdGauss (Fin n) := by
    unfold stdGauss
    change (Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)).map
      (fun z i => -z i) = _
    rw [Measure.pi_map_pi (fun _ => measurable_neg.aemeasurable)]
    simp only [ProbabilityTheory.gaussianReal_map_neg, neg_zero]
  rw [hneg] at hi
  simp only [Function.comp_def, perpDir_neg56, Pi.neg_apply, integral_neg] at hi
  linarith

/-- The coefficient definition is homogeneous in its normalized-projection argument. -/
theorem PhiJI_smul_right56 {n : ℕ} (d j i : ℕ) (a w : Fin n → ℝ) (c : ℝ)
    (p : Mono n d) :
    PhiJI d j i a (c • w) p = c ^ i * PhiJI d j i a w p := by
  classical
  unfold PhiJI
  split_ifs with hp
  · let Q : Polynomial ℝ :=
      ((p.2 : Multiset (Fin n)).map fun l =>
        Polynomial.C (a l) + Polynomial.X * Polynomial.C (w l)).prod
    have hQ : ((p.2 : Multiset (Fin n)).map fun l =>
        Polynomial.C (a l) + Polynomial.X * Polynomial.C ((c • w) l)).prod =
        Q.comp (Polynomial.C c * Polynomial.X) := by
      dsimp only [Q]
      rw [Polynomial.multiset_prod_comp, Multiset.map_map]
      congr 1
      apply Multiset.map_congr rfl
      intro l hl
      simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul, Polynomial.add_comp,
        Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_mul]
      ring
    rw [hQ, Polynomial.comp_C_mul_X_coeff, mul_comm]
  · simp

/-- The degree-zero case has no admissible positive homogeneous degree. -/
theorem keyLemma56_zero : ∃ CK : ℝ, 0 ≤ CK ∧ KeyLemma56 0 CK := by
  refine ⟨0, le_rfl, ?_⟩
  intro n hn v hv s s' hs hs' j i i' hj hi hij hi' hij'
  omega

end BstLean.Part56
