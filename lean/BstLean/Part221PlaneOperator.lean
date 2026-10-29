import BstLean.Part221PlaneEigen
import BstLean.Part153Op
import BstLean.Part153PPs

/-! The closed two-dimensional eigenvalue is bounded by the Gaussian matrix operator norm. -/
namespace BstLean.Part221
open MeasureTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153

lemma eigenTwo_characteristic (a b c : ℝ) :
    (eigenTwo a b c - a) * (eigenTwo a b c - c) = b ^ 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ (a - c) ^ 2 + 4 * b ^ 2 by positivity)
  unfold eigenTwo
  nlinarith only [hs]

theorem eigenTwo_le_of_quadratic (a b c B : ℝ)
    (hB : ∀ x y : ℝ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≤
      B * (x ^ 2 + y ^ 2)) : eigenTwo a b c ≤ B := by
  set e := eigenTwo a b c
  have hc : (e - a) * (e - c) = b ^ 2 := eigenTwo_characteristic a b c
  have hid : a * b ^ 2 + 2 * b * b * (e - a) + c * (e - a) ^ 2 =
      e * (b ^ 2 + (e - a) ^ 2) := by
    have hc' := congrArg (fun t : ℝ => (e - a) * t) hc
    nlinarith only [hc']
  by_cases hz : b ^ 2 + (e - a) ^ 2 = 0
  · have he : e = a := by nlinarith only [hz, sq_nonneg b, sq_nonneg (e-a)]
    have h := hB 1 0
    simp only [one_pow, zero_pow (by decide : 2 ≠ 0), mul_one, mul_zero,
      add_zero] at h
    exact he.trans_le h
  · have hp : 0 < b ^ 2 + (e - a) ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hz)
    have h := hB b (e - a)
    rw [hid] at h
    exact le_of_mul_le_mul_right h hp

noncomputable def matrixPlaneEigen {m : ℕ} (M : Matrix (Fin m) (Fin 2) ℝ) : ℝ :=
  eigenTwo (∑ i, M i 0 ^ 2) (∑ i, M i 0 * M i 1) (∑ i, M i 1 ^ 2)

theorem matrixPlaneEigen_le_opN {m : ℕ} (M : Matrix (Fin m) (Fin 2) ℝ) :
    matrixPlaneEigen M ≤ opN M ^ 2 := by
  apply eigenTwo_le_of_quadratic
  intro x y
  have h := normSq_mulVec_le M ![x, y]
  have he : normSq (M *ᵥ ![x,y]) =
      (∑ i, M i 0 ^ 2) * x ^ 2 + 2 * (∑ i, M i 0 * M i 1) * x * y +
        (∑ i, M i 1 ^ 2) * y ^ 2 := by
    calc
      _ = ∑ i, (M i 0 * x + M i 1 * y) ^ 2 := by
        simp [normSq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      _ = ∑ i, (M i 0 ^ 2 * x ^ 2 + 2 * (M i 0 * M i 1) * x * y +
          M i 1 ^ 2 * y ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [he] at h
  simpa [normSq, Fin.sum_univ_two] using h

lemma matrixPlaneEigen_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin 2) ℝ) :
    0 ≤ matrixPlaneEigen M := by
  unfold matrixPlaneEigen eigenTwo
  positivity

/-- The count-dependent Gaussian matrix estimate for each fixed gate array. -/
theorem selected_plane_moment {m P : ℕ} (hP : 1 ≤ P)
    (d : Fin m → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1) :
    (∫⁻ M : Matrix (Fin m) (Fin 2) ℝ,
      ENNReal.ofReal (matrixPlaneEigen (Matrix.diagonal d * M) ^ P)
      ∂gaussMat m 2 1) ≤
      ENNReal.ofReal ((√(∑ i, d i) + √2 + BstLean.Part152.gaussMomConst P) ^ (2 * P)) := by
  have h := opN_rowsel_moment d hd (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (by norm_num : (0 : ℝ) ≤ 1) hP
  simp only [Matrix.mul_one, Real.sqrt_one, one_mul, Nat.cast_ofNat] at h
  have hi : opN (1 : Matrix (Fin 2) (Fin 2) ℝ) ≤ 1 := by
    apply opN_le_of_forall _ zero_le_one
    intro v
    simp
  refine (lintegral_mono fun (M : Matrix (Fin m) (Fin 2) ℝ) => ENNReal.ofReal_le_ofReal
    (show matrixPlaneEigen (Matrix.diagonal d * M) ^ P ≤
      opN (Matrix.diagonal d * M) ^ (2 * P) by
      rw [pow_mul]
      exact pow_le_pow_left₀ (matrixPlaneEigen_nonneg _) (matrixPlaneEigen_le_opN _) P)).trans
    (h.trans (ENNReal.ofReal_le_ofReal ?_))
  apply pow_le_pow_left₀
  · exact mul_nonneg (opN_nonneg _) (add_nonneg
      (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (BstLean.Part152.gaussMomConst_nonneg _))
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (add_nonneg
      (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (BstLean.Part152.gaussMomConst_nonneg _))

end BstLean.Part221
