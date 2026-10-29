import BstLean.Part218OrderedBound
import BstLean.Part218Transfer

/-! Ordered statistics transfer exactly from standard rows to He-scaled rows. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130

noncomputable def offStatistic {N : ℕ} (φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∑ p : Fin m × Fin m, orderedRow φ p M

lemma offStatistic_measurable {N m : ℕ} {φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (mφ : Measurable φ) : Measurable (offStatistic φ m) := by
  classical
  apply Finset.measurable_sum
  intro p _
  unfold orderedRow
  split_ifs
  · exact measurable_const
  · exact mφ.comp ((measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2))

lemma offStatistic_memLp {N m : ℕ} {φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (iφ : MemLp φ 2 ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) :
    MemLp (offStatistic φ m) 2 (gaussMat m N 1) := by
  rw [gaussMat_one_pi]
  exact memLp_finsetSum _ (fun p _ => orderedRow_memLp _ iφ p)

lemma offStatistic_mean {N m : ℕ} {φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (mφ : Measurable φ) (iφ : MemLp φ 2 ((stdGauss (Fin N)).prod (stdGauss (Fin N)))) :
    (∫ M, offStatistic φ m M ∂gaussMat m N 1) =
      (m : ℝ) * ((m : ℝ) - 1) * ∫ p, φ p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)) := by
  rw [gaussMat_one_pi]
  exact iid_ordered_pair_mean _ mφ iφ

lemma offStatistic_smul {N m : ℕ} {φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (hφ : ∀ a : ℝ, 0 ≤ a → ∀ x y, φ (a • x, a • y) = a ^ 4 * φ (x, y))
    {a : ℝ} (ha : 0 ≤ a) (M : Matrix (Fin m) (Fin N) ℝ) :
    offStatistic φ m (a • M) = a ^ 4 * offStatistic φ m M := by
  classical
  unfold offStatistic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold orderedRow
  split_ifs with hp
  · ring
  · exact hφ a ha (M p.1) (M p.2)

theorem offStatistic_scaled_moments {N m : ℕ} {φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (mφ : Measurable φ) (iφ : MemLp φ 2 ((stdGauss (Fin N)).prod (stdGauss (Fin N))))
    (hφ : ∀ a : ℝ, 0 ≤ a → ∀ x y, φ (a • x, a • y) = a ^ 4 * φ (x, y))
    {v : ℝ} (hv : 0 ≤ v) :
    Integrable (offStatistic φ m) (gaussMat m N v) ∧
    (∫ M, offStatistic φ m M ∂gaussMat m N v) =
      v ^ 2 * ((m : ℝ) * ((m : ℝ) - 1) * ∫ p, φ p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) ∧
    Integrable (fun M => (offStatistic φ m M -
      v ^ 2 * ((m : ℝ) * ((m : ℝ) - 1) * ∫ p, φ p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)))) ^ 2)
      (gaussMat m N v) ∧
    (∫ M, (offStatistic φ m M -
      v ^ 2 * ((m : ℝ) * ((m : ℝ) - 1) * ∫ p, φ p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N)))) ^ 2
      ∂gaussMat m N v) = v ^ 4 * Var[offStatistic φ m; gaussMat m N 1] := by
  let c := (m : ℝ) * ((m : ℝ) - 1) * ∫ p, φ p ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))
  have mf := offStatistic_measurable (m := m) mφ
  have iS := offStatistic_memLp (m := m) iφ
  have he : ∀ M : Matrix (Fin m) (Fin N) ℝ,
      offStatistic φ m (√v • M) = v ^ 2 * offStatistic φ m M := by
    intro M
    rw [offStatistic_smul hφ (sqrt_nonneg _), show (4 : ℕ) = 2 * 2 from rfl,
      pow_mul, sq_sqrt hv]
  have ht := gaussMat_transfer v mf he
  have hsq : ∀ M : Matrix (Fin m) (Fin N) ℝ,
      (offStatistic φ m (√v • M) - v ^ 2 * c) ^ 2 = v ^ 4 * (offStatistic φ m M - c) ^ 2 := by
    intro M
    rw [he]
    ring
  have hs := gaussMat_transfer v ((mf.sub_const (v ^ 2 * c)).pow_const 2) hsq
  have ic : Integrable (fun M => (offStatistic φ m M - c) ^ 2) (gaussMat m N 1) :=
    (iS.sub (memLp_const c)).integrable_sq
  refine ⟨ht.1.mpr ((iS.integrable one_le_two).const_mul _), ?_,
    hs.1.mpr (ic.const_mul _), ?_⟩
  · rw [ht.2, integral_const_mul, offStatistic_mean mφ iφ]
  · rw [hs.2, integral_const_mul, variance_eq_integral mf.aemeasurable, offStatistic_mean mφ iφ]

end BstLean.Part218
#print axioms BstLean.Part218.offStatistic_scaled_moments
