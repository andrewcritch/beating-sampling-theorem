import BstLean.Part218AngularMoments

/-! The angular mean bound and input variance mean are strictly positive. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part36 BstLean.Part130

lemma angularMoment_nonneg {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : 0 ≤ angularMoment N k := by
  rw [← sphere_coordinate_even hN ⟨0, hN⟩ k]
  apply integral_nonneg
  intro u
  change 0 ≤ u ⟨0, hN⟩ ^ (2 * k)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) k

lemma angularMoment_variance_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < angularMoment N 2 - angularMoment N 1 ^ 2 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have h1 : angularMoment N 1 = 1 / (N : ℝ) := by
    norm_num [angularMoment, gaussMom, rhoD, Finset.prod_range_succ]
  have h2 : angularMoment N 2 = 3 / ((N : ℝ) * (N + 2)) := by
    norm_num [angularMoment, gaussMom, rhoD, Finset.prod_range_succ, Nat.doubleFactorial]
  rw [h1, h2]
  have he : 3 / ((N : ℝ) * (N + 2)) - (1 / (N : ℝ)) ^ 2 =
      2 * ((N : ℝ) - 1) / ((N : ℝ) ^ 2 * (N + 2)) := by field_simp; ring
  rw [he]
  positivity

theorem angularJ2_pos {N : ℕ} (hN : 2 ≤ N) (e : ℝ) : 0 < angularJ2 N e := by
  have hn : 1 ≤ N := by omega
  have hn' : (0 : ℝ) < N := by exact_mod_cast hn
  have ha : 0 < angularA N := by unfold angularA; positivity
  have hb := angularB_nonneg N
  have h3 := angularMoment_nonneg hn 3
  have h4 := angularMoment_nonneg hn 4
  have he : angularJ2 N e = angularA N ^ 2 * (angularMoment N 2 - angularMoment N 1 ^ 2) +
      (angularA N * angularMoment N 1 + e) ^ 2 +
      2 * angularA N * angularB N * angularMoment N 3 + angularB N ^ 2 * angularMoment N 4 := by
    unfold angularJ2
    ring
  rw [he]
  have h0 := mul_pos (sq_pos_of_pos ha) (angularMoment_variance_pos hN)
  positivity

noncomputable def inputVarianceMean (N m : ℕ) : ℝ := 5 * m / (N : ℝ) ^ 2 - 2 * m / (N : ℝ) ^ 3

theorem inputVarianceMean_pos {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m) : 0 < inputVarianceMean N m := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < N := by linarith
  have hn5 : 0 < 5 * (N : ℝ) - 2 := by linarith
  have he : inputVarianceMean N m = (m : ℝ) * (5 * N - 2) / (N : ℝ) ^ 3 := by
    unfold inputVarianceMean
    field_simp
  rw [he]
  positivity

end BstLean.Part218
#print axioms BstLean.Part218.angularJ2_pos
