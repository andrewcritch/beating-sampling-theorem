import BstLean.Part160Split

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134 BstLean.Part160

noncomputable def weightSq (a d f : ℝ) : ℝ := (max (a - f ^ 2) d)⁻¹

noncomputable def weight (a d f : ℝ) : ℝ := √(weightSq a d f)

def goodInput (a d omega f : ℝ) : Prop := a ≤ omega ∧ f ^ 2 ≤ a - d

noncomputable instance (a d omega f : ℝ) : Decidable (goodInput a d omega f) :=
  Classical.propDecidable _

lemma weightSq_nonneg {a d f : ℝ} (hd : 0 < d) : 0 ≤ weightSq a d f := by
  unfold weightSq
  exact inv_nonneg.mpr ((le_max_right _ _).trans' hd.le)

lemma weight_sq {a d f : ℝ} (hd : 0 < d) : weight a d f ^ 2 = weightSq a d f :=
  Real.sq_sqrt (weightSq_nonneg hd)

lemma weightSq_le_inv {a d f : ℝ} (hd : 0 < d) : weightSq a d f ≤ 1 / d := by
  unfold weightSq
  rw [one_div]
  exact inv_anti₀ hd (le_max_right _ _)

lemma goodInput_residual {a d omega f : ℝ} (h : goodInput a d omega f) :
    d ≤ omega - f ^ 2 := by
  rcases h with ⟨h1, h2⟩
  linarith

lemma weightSq_on_good {a d omega f : ℝ} (hd : 0 < d)
    (h : goodInput a d omega f) :
    (omega - f ^ 2)⁻¹ ≤ weightSq a d f := by
  have hY : d ≤ a - f ^ 2 := by linarith [h.2]
  unfold weightSq
  rw [max_eq_left hY]
  exact inv_anti₀ (hd.trans_le hY) (by linarith [h.1])

/-- The good set is a subset of the residual-mass set. The sets need not be equal. -/
lemma goodInput_subset_residual {X : Type*} (a d : ℝ) (omega f : X → ℝ) :
    {x | goodInput a d (omega x) (f x)} ⊆ {x | d ≤ omega x - f x ^ 2} :=
  fun _ hx => goodInput_residual hx

/-- The scalar counterexample in the WF challenge. -/
lemma residual_set_not_good :
    (1 / 5 : ℝ) ≤ 9 / 10 - (1 / 10) ^ 2 ∧
      ¬ goodInput ((1 - 1 / 100) ^ 2) (1 / 5) (9 / 10) (1 / 10) := by
  norm_num [goodInput]

/-- A capped reciprocal has a second-order bound in its positive deficit. -/
theorem reciprocal_weight_bound {a d f m : ℝ} (hd : 0 < d)
    (hY : d < a - m ^ 2) :
    weightSq a d f ≤ 1 / (a - m ^ 2) + max (f ^ 2 - m ^ 2) 0 / (a - m ^ 2) ^ 2 +
      (max (f ^ 2 - m ^ 2) 0) ^ 2 / (d * (a - m ^ 2) ^ 2) := by
  set Y := a - m ^ 2
  set D := max (f ^ 2 - m ^ 2) 0
  have hY0 : 0 < Y := hd.trans hY
  have hD0 : 0 ≤ D := le_max_right _ _
  have hQ0 : 0 < max (a - f ^ 2) d := hd.trans_le (le_max_right _ _)
  by_cases hf : f ^ 2 ≤ m ^ 2
  · have hD : D = 0 := max_eq_right (by linarith)
    rw [hD]
    norm_num only [zero_div, zero_pow, add_zero]
    unfold weightSq
    rw [one_div]
    exact inv_anti₀ hY0 ((by dsimp [Y]; linarith : Y ≤ a - f ^ 2).trans (le_max_left _ _))
  · have hD : D = f ^ 2 - m ^ 2 := max_eq_left (by linarith)
    have he : a - f ^ 2 = Y - D := by rw [hD]; dsimp [Y]; ring
    unfold weightSq
    rw [he]
    by_cases hcap : d ≤ Y - D
    · rw [max_eq_left hcap]
      have hQ : 0 < Y - D := hd.trans_le hcap
      have hrec : 1 / (Y - D) = 1 / Y + D / Y ^ 2 + D ^ 2 / ((Y - D) * Y ^ 2) := by
        field_simp
        <;> ring
      rw [← one_div, hrec]
      have : d * Y ^ 2 ≤ (Y - D) * Y ^ 2 :=
        mul_le_mul_of_nonneg_right hcap (sq_nonneg _)
      exact add_le_add_right (div_le_div_of_nonneg_left (sq_nonneg D)
        (by positivity) this) _
    · rw [max_eq_right (by linarith)]
      have hDlarge : Y - d ≤ D := by linarith
      rw [← one_div, div_le_iff₀ hd]
      have heq : (1 / Y + D / Y ^ 2 + D ^ 2 / (d * Y ^ 2)) * d - 1 =
          (D - (Y - d)) * (D + Y) / Y ^ 2 := by
        field_simp
        <;> ring
      have hpos : 0 ≤ (D - (Y - d)) * (D + Y) / Y ^ 2 := by positivity
      linarith

end BstLean.Part188
