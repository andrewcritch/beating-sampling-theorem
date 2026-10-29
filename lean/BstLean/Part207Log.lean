import BstLean.Part151JF4
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The sharp logarithm remainder in the paper's HQ coefficient. -/
namespace BstLean.Part207
open Real Set

lemma log_sub_frac_sharp {x e : ℝ} (hx : |x| ≤ e) (he : e < 1) :
    |log (1 + x) - x / (1 + x)| ≤ x ^ 2 / (2 * (1 - e) ^ 2) := by
  have he0 : 0 ≤ e := (abs_nonneg x).trans hx
  have hd : 0 < 1 - e := by linarith
  have hxp : 0 < 1 + x := by have := (abs_le.mp hx).1; linarith
  have hlow : 0 ≤ log (1 + x) - x / (1 + x) := by
    have h := Real.one_sub_inv_le_log_of_pos hxp
    have hfrac : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [hfrac] at h
    linarith
  rw [abs_of_nonneg hlow]
  let G : ℝ → ℝ := fun y => y ^ 2 / (2 * (1 - e) ^ 2) - log (1 + y) + y / (1 + y)
  let G' : ℝ → ℝ := fun y => y * ((1 - e)⁻¹ ^ 2 - (1 + y)⁻¹ ^ 2)
  have hder : ∀ y, -e ≤ y → HasDerivAt G (G' y) y := by
    intro y hy
    have hp : 0 < 1 + y := by linarith
    have h1 := ((hasDerivAt_id y).pow 2).div_const (2 * (1 - e) ^ 2)
    have h2 := ((hasDerivAt_const y 1).add (hasDerivAt_id y)).log hp.ne'
    have h3 := (hasDerivAt_id y).div
      ((hasDerivAt_const y 1).add (hasDerivAt_id y)) hp.ne'
    convert (h1.sub h2).add h3 using 1
    · rfl
    · dsimp [G']
      field_simp
      ring
  have hdiff : ∀ y, -e ≤ y → 0 ≤ (1 - e)⁻¹ ^ 2 - (1 + y)⁻¹ ^ 2 := by
    intro y hy
    have hp : 0 < 1 + y := by linarith
    have hi : (1 + y)⁻¹ ≤ (1 - e)⁻¹ := inv_anti₀ hd (by linarith)
    have hi0 : 0 ≤ (1 + y)⁻¹ := inv_nonneg.mpr hp.le
    nlinarith [sq_nonneg ((1 - e)⁻¹ - (1 + y)⁻¹)]
  have hG0 : G 0 = 0 := by simp [G]
  have hxlo : -e ≤ x := (abs_le.mp hx).1
  by_cases hx0 : 0 ≤ x
  · have hc : ContinuousOn G (Icc 0 x) := by
      intro y hy
      exact (hder y (by linarith [hy.1])).continuousAt.continuousWithinAt
    have hm : MonotoneOn G (Icc 0 x) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hc
        (fun y hy => (hder y (by have := interior_subset hy; linarith [this.1])).hasDerivWithinAt)
        (fun y hy => by
          have hy' := interior_subset hy
          exact mul_nonneg hy'.1 (hdiff y (by linarith [hy'.1])))
    have h := hm ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
    rw [hG0] at h
    dsimp [G] at h
    linarith
  · have hx0' : x ≤ 0 := le_of_not_ge hx0
    have hc : ContinuousOn G (Icc x 0) := by
      intro y hy
      exact (hder y (hxlo.trans hy.1)).continuousAt.continuousWithinAt
    have hm : AntitoneOn G (Icc x 0) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 0) hc
        (fun y hy => (hder y (hxlo.trans (interior_subset hy).1)).hasDerivWithinAt)
        (fun y hy => mul_nonpos_of_nonpos_of_nonneg (interior_subset hy).2
          (hdiff y (hxlo.trans (interior_subset hy).1)))
    have h := hm ⟨le_rfl, hx0'⟩ ⟨hx0', le_rfl⟩ hx0'
    rw [hG0] at h
    dsimp [G] at h
    linarith

end BstLean.Part207
