import BstLean.Part56PropD_Polar

/-! The perpendicular Gaussian direction in coordinates adapted to the anchor. -/
namespace BstLean.Part56

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53)

variable {k : ℕ}
variable (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))

noncomputable def tailReconstruct (z : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  basisReconstruct b (Fin.cons 0 z)

theorem tailReconstruct_smul (c : ℝ) (z : Fin k → ℝ) :
    tailReconstruct b (c • z) = c • tailReconstruct b z := by
  have h : Fin.cons (0 : ℝ) (c • z) = c • Fin.cons 0 z := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact (congrArg (basisReconstruct b) h).trans (basisReconstruct_smul b c _)

theorem tailReconstruct_sumsq (z : Fin k → ℝ) :
    (∑ i, tailReconstruct b z i ^ 2) = ∑ i, z i ^ 2 := by
  rw [tailReconstruct, basisReconstruct_sumsq, Fin.sum_univ_succ]
  simp

theorem basisReconstruct_cons (v : Fin (k + 1) → ℝ)
    (hb : b 0 = WithLp.toLp 2 v) (a : ℝ) (z : Fin k → ℝ) :
    basisReconstruct b (Fin.cons a z) = a • v + tailReconstruct b z := by
  classical
  have he : basisReconstruct b (Pi.single 0 1) = v := by
    change WithLp.ofLp (b.repr.symm (EuclideanSpace.single 0 (1 : ℝ))) = v
    rw [b.repr_symm_single, hb]
  have hz : Fin.cons a z = a • (Pi.single 0 1 : Fin (k + 1) → ℝ) + Fin.cons 0 z := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [hz, basisReconstruct_add, basisReconstruct_smul, he]
  rfl

theorem perpDir_basis_cons (v : Fin (k + 1) → ℝ)
    (hb : b 0 = WithLp.toLp 2 v) (a : ℝ) (z : Fin k → ℝ) :
    perpDir v (basisReconstruct b (Fin.cons a z)) = tailReconstruct b (unitF53 z) := by
  have ha : (∑ i, v i * basisReconstruct b (Fin.cons a z) i) = a := by
    simpa only [Fin.cons_zero] using basisReconstruct_axial b v hb (Fin.cons a z)
  have he : (fun i => basisReconstruct b (Fin.cons a z) i - a * v i) =
      tailReconstruct b z := by
    rw [basisReconstruct_cons b v hb]
    ext i
    simp
  unfold perpDir
  rw [ha]
  simp_rw [show ∀ i, basisReconstruct b (Fin.cons a z) i - a * v i =
    tailReconstruct b z i from fun i => congrFun he i]
  rw [tailReconstruct_sumsq]
  exact (tailReconstruct_smul b _ z).symm

theorem rad_smul_unit {ι : Type} [Fintype ι] (z : ι → ℝ) :
    radF53 z • unitF53 z = z := by
  classical
  by_cases hz : radF53 z = 0
  · have hs : (∑ i, z i ^ 2) = 0 := by
      exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hz
    have hzero : z = 0 := by
      ext i
      exact ((Finset.sum_sq_eq_zero_iff Finset.univ z).mp hs) i (Finset.mem_univ i)
    simp [radF53, unitF53, hzero]
  · unfold unitF53
    rw [smul_smul]
    change (radF53 z * (1 / radF53 z)) • z = z
    rw [one_div, mul_inv_cancel₀ hz, one_smul]

/-- A Gaussian radius can be kept while its direction is replaced by an independent copy. -/
theorem rad_direction_resample (H : ℝ → (Fin k → ℝ) → ℝ≥0∞)
    (hH : Measurable (Function.uncurry H)) :
    (∫⁻ z, H (radF53 z) (unitF53 z) ∂stdGauss (Fin k)) =
      ∫⁻ z, ∫⁻ z', H (radF53 z) (unitF53 z') ∂stdGauss (Fin k) ∂stdGauss (Fin k) := by
  have hp := BstLean.Part53.gauss_polar_gen (fun w r => H r w)
    (hH.comp measurable_swap)
  rw [hp]
  exact lintegral_lintegral_swap
    (hH.comp ((BstLean.Part53.measurable_radF.comp measurable_snd).prodMk
      (BstLean.Part53.measurable_unitF.comp measurable_fst))).aemeasurable

/-- The perpendicular direction has the law of a Gaussian direction in the remaining coordinates. -/
theorem perpDir_lintegral_tail (v : Fin (k + 1) → ℝ)
    (hb : b 0 = WithLp.toLp 2 v) (F : (Fin (k + 1) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ g, F (perpDir v g) ∂stdGauss (Fin (k + 1))) =
      ∫⁻ z, F (tailReconstruct b (unitF53 z)) ∂stdGauss (Fin k) := by
  have hm : Measurable (perpDir v) := by
    unfold perpDir
    fun_prop
  rw [basis_cons_lintegral b (fun g => F (perpDir v g)) (hF.comp hm)]
  simp_rw [← basisReconstruct_eq_symm, perpDir_basis_cons b v hb]
  rw [lintegral_const]
  simp

noncomputable def axialS (a r : ℝ) : ℝ := a / Real.sqrt (a ^ 2 + r ^ 2)
noncomputable def axialR (a r : ℝ) : ℝ := r / Real.sqrt (a ^ 2 + r ^ 2)
noncomputable def polarPoint (v w : Fin (k + 1) → ℝ) (a r : ℝ) : Fin (k + 1) → ℝ :=
  axialS a r • v + axialR a r • w

theorem normalized_basis_cons (v : Fin (k + 1) → ℝ)
    (hb : b 0 = WithLp.toLp 2 v) (a : ℝ) (z : Fin k → ℝ) :
    unitF53 (basisReconstruct b (Fin.cons a z)) =
      polarPoint v (tailReconstruct b (unitF53 z)) a (radF53 z) := by
  have hs : radF53 z ^ 2 = ∑ i, z i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have ht : tailReconstruct b z = radF53 z • tailReconstruct b (unitF53 z) := by
    rw [← tailReconstruct_smul, rad_smul_unit]
  unfold unitF53
  rw [basisReconstruct_sumsq, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [basisReconstruct_cons b v hb, ht]
  change (1 / Real.sqrt (a ^ 2 + ∑ i, z i ^ 2)) •
      (a • v + radF53 z • tailReconstruct b (unitF53 z)) = _
  unfold polarPoint axialS axialR
  rw [hs, smul_add, smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem axialS_abs_le_one (a r : ℝ) : |axialS a r| ≤ 1 := by
  have ht : 0 ≤ a ^ 2 + r ^ 2 := by positivity
  by_cases hz : Real.sqrt (a ^ 2 + r ^ 2) = 0
  · simp [axialS, hz]
  · have hp : 0 < Real.sqrt (a ^ 2 + r ^ 2) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    rw [axialS, abs_div, abs_of_pos hp, div_le_one hp]
    exact (Real.le_sqrt (abs_nonneg _) ht).2 (by rw [sq_abs]; nlinarith [sq_nonneg r])

theorem axialR_nonneg (a r : ℝ) (hr : 0 ≤ r) : 0 ≤ axialR a r :=
  div_nonneg hr (Real.sqrt_nonneg _)

theorem axialR_le_one (a r : ℝ) (hr : 0 ≤ r) : axialR a r ≤ 1 := by
  have ht : 0 ≤ a ^ 2 + r ^ 2 := by positivity
  by_cases hz : Real.sqrt (a ^ 2 + r ^ 2) = 0
  · simp [axialR, hz]
  · have hp : 0 < Real.sqrt (a ^ 2 + r ^ 2) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    rw [axialR, div_le_one hp]
    exact (Real.le_sqrt hr ht).2 (by nlinarith [sq_nonneg a])

theorem normalized_basis_axial (v : Fin (k + 1) → ℝ)
    (hb : b 0 = WithLp.toLp 2 v) (a : ℝ) (z : Fin k → ℝ) :
    (∑ i, v i * unitF53 (basisReconstruct b (Fin.cons a z)) i) =
      axialS a (radF53 z) := by
  have he : (∑ i, v i * unitF53 (basisReconstruct b (Fin.cons a z)) i) =
      (1 / radF53 (basisReconstruct b (Fin.cons a z))) *
        ∑ i, v i * basisReconstruct b (Fin.cons a z) i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [unitF53, radF53, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, basisReconstruct_axial b v hb]
  simp only [Fin.cons_zero]
  unfold radF53 axialS
  rw [basisReconstruct_sumsq, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  ring

end BstLean.Part56
