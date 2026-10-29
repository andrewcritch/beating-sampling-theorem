import BstLean.Part217Rate
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The larger radial slope follows from the exact curvature polynomial. -/
namespace BstLean.Part221
open Real Set
open BstLean.Part217

noncomputable def radialSlope (d r : ℝ) : ℝ := r - d / r + 2 * r / (r ^ 2 - d + 1)
noncomputable def radialCurvature (d r : ℝ) : ℝ :=
  1 + d / r ^ 2 - 2 * (r ^ 2 + d - 1) / (r ^ 2 - d + 1) ^ 2

theorem correctedRate_derivative {d r : ℝ} (hr : 0 < r) (hden : 0 < r ^ 2 - d + 1) :
    HasDerivAt (correctedRadialRate d) (radialSlope d r) r := by
  have hsq := (hasDerivAt_id r).pow 2
  have hl := ((hsq.sub_const d).add_const 1).log hden.ne'
  have h := ((hsq.div_const 2).sub ((hasDerivAt_log hr.ne').const_mul d)).add hl
  convert h using 1
  · rfl
  · dsimp [radialSlope]; ring

theorem radialSlope_derivative {d r : ℝ} (hr : 0 < r) (hden : 0 < r ^ 2 - d + 1) :
    HasDerivAt (radialSlope d) (radialCurvature d r) r := by
  have h1 := (hasDerivAt_const r d).div (hasDerivAt_id r) hr.ne'
  have h2 := ((hasDerivAt_id r).const_mul 2).div
    ((((hasDerivAt_id r).pow 2).sub_const d).add_const 1) hden.ne'
  have h := ((hasDerivAt_id r).sub h1).add h2
  convert h using 1
  · rfl
  · dsimp [radialCurvature]
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, zero_mul, zero_sub]
    ring

theorem radialCurvature_identity {d r : ℝ} (hr : r ≠ 0) (hden : r ^ 2 - d + 1 ≠ 0) :
    radialCurvature d r - 1 =
      ((d - 2) * (r ^ 2) ^ 2 - 2 * (d ^ 2 - 1) * r ^ 2 + d * (d - 1) ^ 2) /
        (r ^ 2 * (r ^ 2 - d + 1) ^ 2) := by
  unfold radialCurvature
  field_simp
  <;> ring

theorem curvaturePolynomial_nonneg {d y : ℝ} (hd : 2 < d)
    (hy : (d - 1) * (d + 1 + sqrt (4 * d + 1)) / (d - 2) ≤ y) :
    0 ≤ (d - 2) * y ^ 2 - 2 * (d ^ 2 - 1) * y + d * (d - 1) ^ 2 := by
  have hd2 : 0 < d - 2 := by linarith
  have hs := sq_sqrt (by linarith : 0 ≤ 4 * d + 1)
  have hy' := (div_le_iff₀ hd2).mp hy
  have hl : (d - 1) * sqrt (4 * d + 1) ≤ (d - 2) * y - (d ^ 2 - 1) := by
    nlinarith
  have h0 : 0 ≤ (d - 1) * sqrt (4 * d + 1) := mul_nonneg (by linarith) (sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ h0 hl 2
  have he : ((d - 2) * y - (d ^ 2 - 1)) ^ 2 - ((d - 1) * sqrt (4 * d + 1)) ^ 2 =
      (d - 2) * ((d - 2) * y ^ 2 - 2 * (d ^ 2 - 1) * y + d * (d - 1) ^ 2) := by
    rw [mul_pow, hs]
    ring
  have hp : 0 ≤ (d - 2) * ((d - 2) * y ^ 2 - 2 * (d ^ 2 - 1) * y + d * (d - 1) ^ 2) := by
    rw [← he]; exact sub_nonneg.mpr hsq
  exact nonneg_of_mul_nonneg_right hp hd2

theorem radialCurvature_ge_one {d r : ℝ} (hd : 2 < d) (hr : 0 < r)
    (hden : 0 < r ^ 2 - d + 1)
    (hy : (d - 1) * (d + 1 + sqrt (4 * d + 1)) / (d - 2) ≤ r ^ 2) :
    1 ≤ radialCurvature d r := by
  have hp := curvaturePolynomial_nonneg hd hy
  have hi := radialCurvature_identity hr.ne' hden.ne'
  have hq : 0 ≤ ((d - 2) * (r ^ 2) ^ 2 - 2 * (d ^ 2 - 1) * r ^ 2 + d * (d - 1) ^ 2) /
      (r ^ 2 * (r ^ 2 - d + 1) ^ 2) := div_nonneg hp (by positivity)
  linarith

/-- A derivative lower bound on a half-line gives its quadratic rate increment. -/
theorem quadratic_increment {f g : ℝ → ℝ} {a c : ℝ}
    (hf : ∀ r ∈ Ici a, HasDerivAt f (g r) r)
    (hg : ∀ r ∈ Ici a, HasDerivAt g (deriv g r) r)
    (hc : ∀ r ∈ Ici a, c ≤ deriv g r) {v : ℝ} (hv : 0 ≤ v) :
    g a * v + c * v ^ 2 / 2 ≤ f (a + v) - f a := by
  have hmono : MonotoneOn (fun r => g r - c * r) (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    · intro r hr
      exact ((hg r hr).continuousAt.sub (continuousAt_const.mul continuousAt_id)).continuousWithinAt
    · intro r hr
      exact ((hg r (interior_subset hr)).sub ((hasDerivAt_id r).const_mul c)).hasDerivWithinAt
    · intro r hr
      simpa only [mul_one] using sub_nonneg.mpr (hc r (interior_subset hr))
  have hder (r : ℝ) (hr : r ∈ Ici a) :
      HasDerivAt (fun r => f r - g a * (r - a) - c * (r - a) ^ 2 / 2)
        (g r - g a - c * (r - a)) r := by
    have h := ((hf r hr).sub (((hasDerivAt_id r).sub_const a).const_mul (g a))).sub
      (((((hasDerivAt_id r).sub_const a).pow 2).const_mul c).div_const 2)
    exact h.congr_deriv (by dsimp; ring)
  have hm : MonotoneOn (fun r => f r - g a * (r - a) - c * (r - a) ^ 2 / 2) (Ici a) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    · intro r hr; exact (hder r hr).continuousAt.continuousWithinAt
    · intro r hr; exact (hder r (interior_subset hr)).hasDerivWithinAt
    · intro r hr
      have h := hmono (mem_Ici.mpr le_rfl) (interior_subset hr) (interior_subset hr)
      linarith
  have h := hm (a := a) (b := a + v) (mem_Ici.mpr le_rfl)
    (mem_Ici.mpr (by linarith)) (by linarith)
  dsimp at h
  nlinarith

theorem correctedRate_shift_large {d a v : ℝ} (hd : 2 < d) (ha : 0 < a)
    (hden : 0 < a ^ 2 - d + 1)
    (hy : (d - 1) * (d + 1 + sqrt (4 * d + 1)) / (d - 2) ≤ a ^ 2) (hv : 0 ≤ v) :
    radialSlope d a * v + v ^ 2 / 2 ≤ correctedRadialRate d (a + v) - correctedRadialRate d a := by
  have hdom (r : ℝ) (hr : r ∈ Ici a) : 0 < r ∧ 0 < r ^ 2 - d + 1 ∧
      (d - 1) * (d + 1 + sqrt (4 * d + 1)) / (d - 2) ≤ r ^ 2 := by
    have hr' : a ≤ r := hr
    have hsq := pow_le_pow_left₀ ha.le hr' 2
    exact ⟨by linarith, by linarith, hy.trans hsq⟩
  have h := quadratic_increment (a := a) (c := 1)
    (fun r hr => correctedRate_derivative (hdom r hr).1 (hdom r hr).2.1)
    (fun r hr => by
      have h := radialSlope_derivative (hdom r hr).1 (hdom r hr).2.1
      simpa only [h.deriv] using h)
    (fun r hr => by
      rw [(radialSlope_derivative (hdom r hr).1 (hdom r hr).2.1).deriv]
      exact radialCurvature_ge_one hd (hdom r hr).1 (hdom r hr).2.1 (hdom r hr).2.2) hv
  simpa only [one_mul] using h

end BstLean.Part221
