import BstLean.Part214Diagonal

/-! The diagonal Wishart statistic under the actual He-scaled first-layer distribution. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137

noncomputable def paperDiagonal (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  (N : ℝ) ^ 2 / 4 * diagonalSum N m M

lemma measurable_paperDiagonal (N m : ℕ) : Measurable (paperDiagonal N m) :=
  (measurable_diagonalSum N m).const_mul _

/-- Both exact diagonal formulas hold for the actual first-layer distribution. -/
theorem paperDiagonal_moments {N m : ℕ} (hN : 1 ≤ N) :
    Integrable (paperDiagonal N m) (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M, paperDiagonal N m M ∂gaussMat m N (2 / (N : ℝ))) = (m : ℝ) * N * (N + 2) ∧
    Integrable (fun M => (paperDiagonal N m M - (m : ℝ) * N * (N + 2)) ^ 2)
      (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M, (paperDiagonal N m M - (m : ℝ) * N * (N + 2)) ^ 2
      ∂gaussMat m N (2 / (N : ℝ))) = 8 * (m : ℝ) * N * (N + 2) * (N + 3) := by
  classical
  let v : ℝ := 2 / (N : ℝ)
  let f : (Fin N → ℝ) → ℝ := fun ξ => (N : ℝ) ^ 2 / 4 * normSq ξ ^ 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have mf : Measurable f := (measurable_normSq.pow_const 2).const_mul _
  have hs : ∀ ξ, f (√v • ξ) = normSq ξ ^ 2 := by
    intro ξ
    dsimp [f]
    rw [normSq_smul, Real.sq_sqrt (by dsimp [v]; positivity)]
    dsimp [v]
    field_simp
    ring
  have he : ∀ M, paperDiagonal N m M = ∑ i, f (rowOf i M) := by
    intro M
    unfold paperDiagonal diagonalSum
    exact Finset.mul_sum _ _ _
  have i1 : Integrable (fun ξ => f (√v • ξ)) (stdGauss (Fin N)) := by
    simp_rw [hs]
    exact gaussian_normSq_pow_integrable hN 2
  have i2 : Integrable (fun ξ => f (√v • ξ) ^ 2) (stdGauss (Fin N)) := by
    simp_rw [hs, ← pow_mul]
    exact gaussian_normSq_pow_integrable hN 4
  have em : (∫ ξ, f (√v • ξ) ∂stdGauss (Fin N)) = (N : ℝ) * (N + 2) := by
    simp_rw [hs]
    rw [gaussian_normSq_pow]
    simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  have ir : ∀ i : Fin m, Integrable (fun M => f (rowOf i M)) (gaussMat m N v) :=
    fun i => (row_integrable_iff v i mf).mpr i1
  have iS : Integrable (paperDiagonal N m) (gaussMat m N v) := by
    change Integrable (fun M => paperDiagonal N m M) (gaussMat m N v)
    simp_rw [he]
    exact integrable_finsetSum _ fun i _ => ir i
  have eS : (∫ M, paperDiagonal N m M ∂gaussMat m N v) = (m : ℝ) * N * (N + 2) := by
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => ir i)]
    simp_rw [row_integral v _ mf, em]
    simp
    ring
  obtain ⟨iv, ev⟩ := rows_variance_eq (m := m) v f mf i2
  have hecenter : (m : ℝ) * ((N : ℝ) * (N + 2)) = (m : ℝ) * N * (N + 2) := by ring
  simp_rw [← he, em, hecenter] at iv ev
  refine ⟨iS, eS, iv, ev.trans ?_⟩
  simp_rw [hs, ← pow_mul]
  rw [gaussian_normSq_pow]
  simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  ring

end BstLean.Part214
#print axioms BstLean.Part214.paperDiagonal_moments
