import BstLean.Part162LSs

/-! A degree-one extension of the square of a homogeneous Lipschitz function. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 unitF53)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq)
open BstLean.Part162

variable {ι : Type} [Fintype ι] {H : (ι → ℝ) → ℝ} {L : ℝ}

noncomputable def radialSquare (H : (ι → ℝ) → ℝ) (v : ι → ℝ) : ℝ :=
  H v ^ 2 / radF53 v

lemma radialSquare_hom
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v)
    (t : ℝ) (v : ι → ℝ) (ht : 0 < t) :
    radialSquare H (t • v) = t * radialSquare H v := by
  unfold radialSquare
  rw [hh t v ht, radF_smul ht]
  field_simp

lemma hom_radius_bound (hL : EuLip H L)
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v) (v : ι → ℝ) :
    |H v| ≤ L * radF53 v := by
  have h := hL v 0
  simpa [hom_zero hh, radF53] using h

lemma radialSquare_scalar {a b r s D L : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hs : 0 < s) (hsr : s ≤ r) (ha : |a| ≤ L * r) (hb : |b| ≤ L * s)
    (hab : |a - b| ≤ L * D) (hrs : |r - s| ≤ D) :
    |a ^ 2 / r - b ^ 2 / s| ≤ 3 * L ^ 2 * D := by
  have hr : 0 < r := hs.trans_le hsr
  have hsum : |a + b| ≤ 2 * L * r :=
    (abs_add_le a b).trans (by linarith [mul_le_mul_of_nonneg_left hsr hL])
  have hdiff : |a ^ 2 - b ^ 2| ≤ 2 * L ^ 2 * r * D := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul]
    have h := mul_le_mul hab hsum (abs_nonneg _) (by positivity : 0 ≤ L * D)
    convert h using 1 <;> ring
  have hb2 : b ^ 2 ≤ L ^ 2 * s * r := by
    have h := pow_le_pow_left₀ (abs_nonneg b) hb 2
    rw [sq_abs, mul_pow] at h
    nlinarith only [h,
      mul_nonneg (sq_nonneg L) (mul_nonneg hs.le (sub_nonneg.mpr hsr))]
  have he : a ^ 2 / r - b ^ 2 / s = (a ^ 2 - b ^ 2) / r - b ^ 2 * (r - s) / (r * s) := by
    field_simp
    <;> ring
  rw [he]
  calc
    _ ≤ |(a ^ 2 - b ^ 2) / r| + |b ^ 2 * (r - s) / (r * s)| := abs_sub _ _
    _ = |a ^ 2 - b ^ 2| / r + b ^ 2 * |r - s| / (r * s) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hr, abs_of_pos (mul_pos hr hs),
        abs_of_nonneg (sq_nonneg b)]
    _ ≤ (2 * L ^ 2 * r * D) / r + (L ^ 2 * s * r) * D / (r * s) := by
      gcongr
    _ = 3 * L ^ 2 * D := by field_simp; ring

/-- The extension is globally Lipschitz, including at the origin. -/
theorem radialSquare_lip (hL0 : 0 ≤ L) (hL : EuLip H L)
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v) :
    EuLip (radialSquare H) (3 * L ^ 2) := by
  have hbound := hom_radius_bound hL hh
  have hzero : ∀ v, |radialSquare H v - radialSquare H 0| ≤
      3 * L ^ 2 * radF53 v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp [radF53]
    have hr := radF_pos hv
    simp only [radialSquare, hom_zero hh, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_div, sub_zero]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hr.le), div_le_iff₀ hr]
    have hb := pow_le_pow_left₀ (abs_nonneg (H v)) (hbound v) 2
    rw [sq_abs, mul_pow] at hb
    nlinarith only [hb, mul_nonneg (sq_nonneg L) (sq_nonneg (radF53 v))]
  intro v w
  by_cases hv : v = 0
  · subst v
    rw [abs_sub_comm]
    simpa [radF53] using hzero w
  by_cases hw : w = 0
  · subst w
    simpa [radF53] using hzero v
  have hvp := radF_pos hv
  have hwp := radF_pos hw
  rcases le_total (radF53 w) (radF53 v) with h | h
  · exact radialSquare_scalar hL0 (sqrt_nonneg _) hwp h (hbound v) (hbound w)
      (hL v w) (radF_lip v w)
  · have H' := radialSquare_scalar hL0 (sqrt_nonneg _) hvp h (hbound w) (hbound v)
      (hL w v) (radF_lip w v)
    have he : (∑ i, (w i - v i) ^ 2) = ∑ i, (v i - w i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, abs_sub_comm] at H'
    exact H'

lemma radialSquare_unit
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v) (v : ι → ℝ) :
    radialSquare H (unitF53 v) = H (unitF53 v) ^ 2 := by
  by_cases hv : v = 0
  · subst v; simp [radialSquare, unitF53, hom_zero hh]
  · rw [radialSquare, radF_unitF hv, div_one]

/-- The tangential gradient of the extension has exactly the squared-function factor. -/
theorem radialSquare_tangent [DecidableEq ι]
    (hh : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H (t • v) = t * H v)
    {v : ι → ℝ} (hv : v ≠ 0) (hd : DifferentiableAt ℝ H v) :
    gradSq (radialSquare H) v - radialSquare H (unitF53 v) ^ 2 =
      4 * H (unitF53 v) ^ 2 * (gradSq H v - H (unitF53 v) ^ 2) := by
  have hr := radF_pos hv
  have hrd := (hasFDerivAt_radF hv).differentiableAt
  have hi := (hasDerivAt_inv hr.ne').comp_hasFDerivAt v hrd.hasFDerivAt
  have hder := (hd.hasFDerivAt.pow 2).mul hi
  dsimp only [Function.comp_def, Pi.mul_apply] at hder
  change HasFDerivAt (fun w => H w ^ 2 * (radF53 w)⁻¹) _ v at hder
  have hD : fderiv ℝ (radialSquare H) v =
      (radF53 v)⁻¹ • ((2 * H v) • fderiv ℝ H v) -
        (H v ^ 2 / radF53 v ^ 2) • fderiv ℝ radF53 v := by
    rw [show radialSquare H = (fun w => H w ^ 2 * (radF53 w)⁻¹) by
      funext w; exact div_eq_mul_inv _ _, hder.fderiv]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, nsmul_eq_mul]
    ext x
    simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]
    field_simp
    <;> ring
  have he : ∑ i, fderiv ℝ H v (Pi.single i 1) * v i =
      radF53 v * H (unitF53 v) := by
    rw [← hom_rad hh v, ← euler hh hd, clm_apply_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [radialSquare_unit hh]
  unfold gradSq
  rw [hD]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_radF_single hv]
  have hHv := hom_rad hh v
  have hs : ∑ i, v i ^ 2 = radF53 v ^ 2 := (radF_sq v).symm
  have ex : ∑ i, ((radF53 v)⁻¹ * (2 * H v * fderiv ℝ H v (Pi.single i 1)) -
        H v ^ 2 / radF53 v ^ 2 * (v i / radF53 v)) ^ 2 =
      4 * H (unitF53 v) ^ 2 * (∑ i, (fderiv ℝ H v (Pi.single i 1)) ^ 2) -
        (4 * H (unitF53 v) ^ 3 / radF53 v) *
          (∑ i, fderiv ℝ H v (Pi.single i 1) * v i) +
        (H (unitF53 v) ^ 4 / radF53 v ^ 2) * (∑ i, v i ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hHv]
    field_simp
    <;> ring
  rw [ex, he, hs]
  field_simp
  <;> ring

#print axioms radialSquare_lip
#print axioms radialSquare_tangent
end BstLean.Part223
