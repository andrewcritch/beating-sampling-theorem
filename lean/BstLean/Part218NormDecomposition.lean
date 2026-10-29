import BstLean.Part218Decomposition
import BstLean.Part218Positive

/-! The actual input variance is its diagonal part plus the degenerate ordered kernel. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part105 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part214
open BstLean.Part205

lemma input_variance_kernel_sum {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin N) ℝ) :
    worldInputVariance M = ∑ i, ∑ j, normKernel N (rowOf i M, rowOf j M) := by
  have hp : ∀ u : Fin N → ℝ, normSq (reluV (M.mulVec u)) ^ 2 =
      ∑ i, ∑ j, relu (dotp (rowOf i M) u) ^ 2 * relu (dotp (rowOf j M) u) ^ 2 := by
    intro u
    unfold normSq reluV Matrix.mulVec dotProduct dotp rowOf
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hi : ∀ i j : Fin m, Integrable (fun u =>
      relu (dotp (rowOf i M) u) ^ 2 * relu (dotp (rowOf j M) u) ^ 2) (uniformSphere N) := by
    intro i j
    apply sphere_cont_integrable hN
    unfold dotp relu
    fun_prop
  rw [worldInputVariance_eq hN]
  simp_rw [hp]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  have heQ : firstQ M ^ 2 = (∑ i, normSq (rowOf i M)) ^ 2 / (4 * (N : ℝ) ^ 2) := by
    rw [firstQ_rows hN hm]
    unfold BstLean.Part141.rowS
    ring
  rw [heQ]
  have hs : (∑ i, ∑ j, normSq (rowOf i M) * normSq (rowOf j M)) =
      (∑ i, normSq (rowOf i M)) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  unfold normKernel
  simp only [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hi i j)
  · simp only [← Finset.sum_div]
    rw [hs]

theorem worldInputVariance_split {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin N) ℝ) :
    worldInputVariance M = normDiagonal N * diagonalSum N m M + offStatistic (normKernel N) m M := by
  rw [input_variance_kernel_sum hN hm, offStatistic_split]
  simp_rw [normKernel_diagonal hN]
  rw [← Finset.mul_sum]
  rfl

lemma normDiagonal_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ normDiagonal N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hn5 : 0 ≤ 5 * (N : ℝ) - 2 := by linarith
  have he : normDiagonal N = (5 * (N : ℝ) - 2) / (4 * (N : ℝ) ^ 2 * (N + 2)) := by
    unfold normDiagonal
    field_simp
    ring
  rw [he]
  positivity

lemma normDiagonal_mean {N m : ℕ} (hN : 1 ≤ N) :
    normDiagonal N * (4 / (N : ℝ) ^ 2) * ((m : ℝ) * N * (N + 2)) = inputVarianceMean N m := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold normDiagonal inputVarianceMean
  field_simp
  ring

end BstLean.Part218
#print axioms BstLean.Part218.worldInputVariance_split
