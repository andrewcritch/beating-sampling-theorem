import BstLean.Part218Covariance

/-! The covariance split gives the sharp Frobenius triangle bound. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part133 BstLean.Part137 BstLean.Part214

lemma sum_sq_add_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, (a i + b i) ^ 2) ≤ (√(∑ i, a i ^ 2) + √(∑ i, b i ^ 2)) ^ 2 := by
  have ha : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have he : (∑ i, (a i + b i) ^ 2) = (∑ i, a i ^ 2) + (∑ i, b i ^ 2) + 2 * ∑ i, a i * b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  nlinarith [sq_sqrt ha, sq_sqrt hb]

noncomputable def remainderFrobSq {N m : ℕ} (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, firstRemainderEntry M i j ^ 2

theorem worldFrob_triangle {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    worldFrobSq M ≤ (√(paperTrace N m M / (4 * (N : ℝ) ^ 4)) + √(remainderFrobSq M)) ^ 2 := by
  have h := sum_sq_add_le (fun p : Fin m × Fin m => firstLinearEntry M p.1 p.2)
    (fun p : Fin m × Fin m => firstRemainderEntry M p.1 p.2)
  have he : ∀ p : Fin m × Fin m,
      firstLinearEntry M p.1 p.2 + firstRemainderEntry M p.1 p.2 = firstCovEntry M p.1 p.2 := by
    intro p
    unfold firstRemainderEntry
    ring
  simp_rw [he, Fintype.sum_prod_type] at h
  rw [firstLinear_frob hN] at h
  exact h

theorem worldFrob_bound {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ)
    {S R : ℝ} (hS : paperTrace N m M ≤ S) (hR : remainderFrobSq M ≤ R) :
    worldFrobSq M ≤ (√(S / (4 * (N : ℝ) ^ 4)) + √R) ^ 2 := by
  apply (worldFrob_triangle hN M).trans
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add (sqrt_le_sqrt (div_le_div_of_nonneg_right hS (by positivity))) (sqrt_le_sqrt hR)

end BstLean.Part218
#print axioms BstLean.Part218.worldFrob_triangle
#print axioms BstLean.Part218.worldFrob_bound
