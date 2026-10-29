import BstLean.Part36Defs

/-!
# Part 36, wave 1: scaling `Z ↦ Z/‖Z‖` (light)

The analogues of `Part35Scale` on `CoefIdxD n d`. `floorYD` is homogeneous of degree 4 in the block.
Template: `Part35Scale.lean` (proved). Depends on `Part36Defs` only. Provers must not use `native_decide`.
-/

namespace BstLean.Part36

open BstLean.Part29 (qformι)

variable {n d : ℕ}

theorem nsqD_pos (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) : 0 < nsqD Z := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hZ
  have hi' : Z i ≠ 0 := hi
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi')
    (Finset.single_le_sum (fun j _ => sq_nonneg (Z j)) (Finset.mem_univ i))

theorem unitD_sq (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) : ∑ α, unitOfD Z α ^ 2 = 1 := by
  classical
  have hp := nsqD_pos Z hZ
  unfold nsqD at hp
  simp only [unitOfD, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [div_pow, one_pow, Real.sq_sqrt hp.le, div_mul_cancel₀ _ hp.ne']

theorem normalized_qformD (A : Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ) (Z : CoefIdxD n d → ℝ)
    (hZ : Z ≠ 0) :
    qformι A (unitOfD Z) - A.trace / DD n d = EFD A Z / nsqD Z := by
  classical
  have hp := nsqD_pos Z hZ
  have hs : Real.sqrt (∑ i, Z i ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hsub (a : ℝ) : qformι (A - a • 1) Z = qformι A Z - a * nsqD Z := by
    simp only [qformι, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib]
    change qformι A Z - (∑ i, ∑ j, a * (1 : Matrix (CoefIdxD n d) (CoefIdxD n d) ℝ) i j * Z i * Z j) = _
    simp only [mul_assoc, ← Finset.mul_sum]
    simp [Matrix.one_apply, nsqD, pow_two, qformι, mul_assoc]
  unfold EFD
  rw [hsub]
  have hscale : qformι A (unitOfD Z) = (1 / Real.sqrt (∑ i, Z i ^ 2)) ^ 2 * qformι A Z := by
    simp only [qformι, unitOfD, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hscale]
  unfold nsqD at *
  field_simp
  rw [Real.sq_sqrt hp.le]
  ring

theorem blkOf_smul (a : ℝ) (Z : CoefIdxD n d → ℝ) : blkOf (a • Z) = a • blkOf Z := by
  funext q
  rfl

theorem floorYD_smul (F : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (G : BlkD n d → ℝ) :
    floorYD F (a • G) = a ^ 4 * floorYD F G := by
  classical
  have hc (S : Finset (Fin n)) :
      coefCD F S (a • G) = a ^ 2 * coefCD F S G := by
    simp only [coefCD, qformι, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  simp only [floorYD, hc, mul_pow, ← Finset.mul_sum]
  ring

theorem floorYD_unit (F : Matrix (Fin n) (Fin n) ℝ) (Z : CoefIdxD n d → ℝ) (hZ : Z ≠ 0) :
    floorYD F (blkOf (unitOfD Z)) = floorYD F (blkOf Z) / nsqD Z ^ 2 := by
  have hp := nsqD_pos Z hZ
  change floorYD F (blkOf ((1 / Real.sqrt (nsqD Z)) • Z)) = _
  rw [blkOf_smul, floorYD_smul]
  have hs : (Real.sqrt (nsqD Z)) ^ 4 = nsqD Z ^ 2 := by
    calc
      (Real.sqrt (nsqD Z)) ^ 4 = ((Real.sqrt (nsqD Z)) ^ 2) ^ 2 := by ring
      _ = nsqD Z ^ 2 := by rw [Real.sq_sqrt hp.le]
  rw [div_pow, one_pow, hs]
  ring

end BstLean.Part36
