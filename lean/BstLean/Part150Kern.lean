import BstLean.Part150Gauss

/-!
# Part 150, item 2, tools: two kernels for `|y|` and `y|y|`

Role: `delegations/statements/p150-spec.md`, item 2 (the Fourier route, without the inversion
theorem). Paper source: `onW45-opus-prover.md` §2, Lemma B-F, Step 1.

* `ker1 t y = (1 − cos(ty))/t²` and `ker2 t y = (ty − sin(ty))/t³`.
* `ker1_integral`: `∫_0^∞ ker1 t y dt = |y|·K1`; `ker2_integral`: `∫_0^∞ ker2 t y dt = y|y|·K2`,
  with `K1 = ∫_0^∞ (1 − cos t)/t² dt`, `K2 = ∫_0^∞ (t − sin t)/t³ dt`.
* `prod_integrable_of_bounds`: the integrability on `γ × (0, ∞)` that the exchange of the two
  integrals needs.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

/-- A measurable function on `(0, ∞)` that is bounded on `(0, 1]` and at most `D/t²` on `(1, ∞)`
is integrable. -/
lemma integrableOn_Ioi_of_bounds {f : ℝ → ℝ} (hf : Measurable f) {C D : ℝ}
    (h1 : ∀ t, 0 < t → t ≤ 1 → |f t| ≤ C) (h2 : ∀ t, 1 < t → |f t| ≤ D / t ^ 2) :
    IntegrableOn f (Ioi 0) := by
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hu]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne
      hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact h1 t ht.1 ht.2
  · have hD : IntegrableOn (fun t : ℝ => D * t ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul D
    refine Integrable.mono' hD hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have e : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, e, ← div_eq_mul_inv]
    exact h2 t ht

/-- The integrability on the product that the exchange of the integrals needs. -/
lemma prod_integrable_of_bounds {k : ℝ → ℝ → ℝ} (hk : Measurable (fun p : ℝ × ℝ => k p.2 p.1))
    {B1 B2 : ℝ → ℝ} (h1 : Integrable B1 (gaussianReal 0 1)) (h2 : Integrable B2 (gaussianReal 0 1))
    (hb1 : ∀ t z, t ≤ 1 → |k t z| ≤ B1 z) (hb2 : ∀ t z, 1 < t → |k t z| ≤ B2 z / t ^ 2) :
    Integrable (fun p : ℝ × ℝ => k p.2 p.1)
      ((gaussianReal 0 1).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have i1 : Integrable ((Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ))) (volume.restrict (Ioi (0 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iic]
    exact ((measure_mono (fun x hx => (⟨hx.2, hx.1⟩ : x ∈ Ioc (0 : ℝ) 1))).trans_lt
      measure_Ioc_lt_top).ne
  have i2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).mono_measure
      Measure.restrict_le_self)
  have hG := (h1.mul_prod i1).add (h2.mul_prod i2)
  refine Integrable.mono' hG hk.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  show |k p.2 p.1| ≤ B1 p.1 * (Iic (1 : ℝ)).indicator (fun _ => (1 : ℝ)) p.2 +
    B2 p.1 * (Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ)) p.2
  rcases le_or_gt p.2 1 with h | h
  · rw [indicator_of_mem (show p.2 ∈ Iic (1 : ℝ) from h),
      indicator_of_notMem (show p.2 ∉ Ioi (1 : ℝ) from not_lt.mpr h)]
    simpa using hb1 p.2 p.1 h
  · rw [indicator_of_notMem (show p.2 ∉ Iic (1 : ℝ) from not_le.mpr h),
      indicator_of_mem (show p.2 ∈ Ioi (1 : ℝ) from h)]
    have ht0 : (0 : ℝ) < p.2 := lt_trans zero_lt_one h
    have e : p.2 ^ (-2 : ℝ) = (p.2 ^ 2)⁻¹ := by
      rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e, mul_zero, zero_add, ← div_eq_mul_inv]
    exact hb2 p.2 p.1 h

/-! ## The first kernel -/

/-- The kernel of `|y|`: `(1 − cos(ty))/t²`. -/
noncomputable def ker1 (t y : ℝ) : ℝ := (1 - Real.cos (t * y)) / t ^ 2

lemma ker1_nonneg (t y : ℝ) : 0 ≤ ker1 t y :=
  div_nonneg (sub_nonneg.2 (Real.cos_le_one _)) (sq_nonneg _)

lemma ker1_le_sq (t y : ℝ) : ker1 t y ≤ y ^ 2 / 2 := by
  unfold ker1
  rcases eq_or_ne t 0 with rfl | ht
  · simp; positivity
  · rw [div_le_iff₀ (by positivity)]
    have := Real.one_sub_sq_div_two_le_cos (x := t * y)
    nlinarith

lemma ker1_le_inv {t : ℝ} (ht : 0 < t) (y : ℝ) : ker1 t y ≤ 2 / t ^ 2 := by
  unfold ker1
  have := Real.neg_one_le_cos (t * y)
  gcongr
  linarith

lemma measurable_ker1 : Measurable (fun p : ℝ × ℝ => ker1 p.2 p.1) := by
  unfold ker1; fun_prop

lemma ker1_integrableOn (y : ℝ) : IntegrableOn (fun t => ker1 t y) (Ioi 0) := by
  have hm : Measurable (fun t => ker1 t y) := by unfold ker1; fun_prop
  refine integrableOn_Ioi_of_bounds (C := y ^ 2 / 2) (D := 2) hm ?_ ?_
  · intro t _ _; rw [abs_of_nonneg (ker1_nonneg t y)]; exact ker1_le_sq t y
  · intro t ht; rw [abs_of_nonneg (ker1_nonneg t y)]; exact ker1_le_inv (lt_trans zero_lt_one ht) y

/-- `K1 = ∫_0^∞ (1 − cos t)/t² dt` (its value is `π/2`: `K1_eq`). -/
noncomputable def K1 : ℝ := ∫ t in Ioi 0, ker1 t 1

/-- `∫_0^∞ (1 − cos(ty))/t² dt = |y|·K1`. -/
theorem ker1_integral (y : ℝ) : ∫ t in Ioi 0, ker1 t y = |y| * K1 := by
  have hpos : ∀ y : ℝ, 0 < y → ∫ t in Ioi 0, ker1 t y = y * K1 := by
    intro y hy
    have h := integral_comp_mul_left_Ioi (fun s => ker1 s 1) 0 hy
    have e : ∀ t : ℝ, ker1 t y = y ^ 2 * ker1 (y * t) 1 := by
      intro t
      unfold ker1
      rcases eq_or_ne t 0 with rfl | ht
      · simp
      · field_simp
    simp_rw [e]
    rw [integral_const_mul, h, mul_zero, smul_eq_mul]
    unfold K1
    field_simp
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have e : ∀ t : ℝ, ker1 t y = ker1 t (-y) := by
      intro t; unfold ker1; rw [mul_neg, Real.cos_neg]
    simp_rw [e]
    rw [hpos (-y) (neg_pos.mpr hy), abs_of_neg hy]
  · simp [ker1]
  · rw [hpos y hy, abs_of_pos hy]

/-! ## The second kernel -/

/-- The kernel of `y|y|`: `(ty − sin(ty))/t³`. -/
noncomputable def ker2 (t y : ℝ) : ℝ := (t * y - Real.sin (t * y)) / t ^ 3

lemma abs_sub_sin_le (w : ℝ) : |w - Real.sin w| ≤ |w| ^ 3 / 6 := by
  have hpos : ∀ w : ℝ, 0 < w → |w - Real.sin w| ≤ |w| ^ 3 / 6 := by
    intro w hw
    have h1 := Real.sin_le hw.le
    have h2 := Real.sin_gt_sub_cube hw
    rw [abs_of_nonneg (by linarith), abs_of_pos hw]
    linarith
  rcases lt_trichotomy w 0 with hw | rfl | hw
  · have := hpos (-w) (neg_pos.mpr hw)
    rw [Real.sin_neg, abs_neg] at this
    rwa [show -w - -Real.sin w = -(w - Real.sin w) by ring, abs_neg] at this
  · simp
  · exact hpos w hw

lemma ker2_abs_le_cube (t y : ℝ) : |ker2 t y| ≤ |y| ^ 3 / 6 := by
  unfold ker2
  rcases eq_or_ne t 0 with rfl | ht
  · simp; positivity
  · rw [abs_div, div_le_iff₀ (by positivity)]
    have := abs_sub_sin_le (t * y)
    rw [abs_mul] at this
    rw [abs_pow]
    calc |t * y - Real.sin (t * y)| ≤ (|t| * |y|) ^ 3 / 6 := this
      _ = |y| ^ 3 / 6 * |t| ^ 3 := by ring

lemma ker2_abs_le_inv {t : ℝ} (ht : 1 < t) (y : ℝ) : |ker2 t y| ≤ (|y| + 1) / t ^ 2 := by
  unfold ker2
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  rw [abs_div, abs_of_pos (pow_pos ht0 3), div_le_div_iff₀ (pow_pos ht0 3) (pow_pos ht0 2)]
  have h1 : |t * y - Real.sin (t * y)| ≤ t * |y| + 1 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos ht0]
    linarith [Real.abs_sin_le_one (t * y)]
  have h2 : t * |y| + 1 ≤ t * (|y| + 1) := by nlinarith
  calc |t * y - Real.sin (t * y)| * t ^ 2 ≤ (t * (|y| + 1)) * t ^ 2 :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
    _ = (|y| + 1) * t ^ 3 := by ring

lemma measurable_ker2 : Measurable (fun p : ℝ × ℝ => ker2 p.2 p.1) := by
  unfold ker2; fun_prop

lemma ker2_integrableOn (y : ℝ) : IntegrableOn (fun t => ker2 t y) (Ioi 0) := by
  have hm : Measurable (fun t => ker2 t y) := by unfold ker2; fun_prop
  exact integrableOn_Ioi_of_bounds (C := |y| ^ 3 / 6) (D := |y| + 1) hm
    (fun t _ _ => ker2_abs_le_cube t y) (fun _ ht => ker2_abs_le_inv ht y)

/-- `K2 = ∫_0^∞ (t − sin t)/t³ dt` (its value is `π/4`: `K2_eq`). -/
noncomputable def K2 : ℝ := ∫ t in Ioi 0, ker2 t 1

/-- `∫_0^∞ (ty − sin(ty))/t³ dt = y|y|·K2`. -/
theorem ker2_integral (y : ℝ) : ∫ t in Ioi 0, ker2 t y = y * |y| * K2 := by
  have hpos : ∀ y : ℝ, 0 < y → ∫ t in Ioi 0, ker2 t y = y ^ 2 * K2 := by
    intro y hy
    have h := integral_comp_mul_left_Ioi (fun s => ker2 s 1) 0 hy
    have e : ∀ t : ℝ, ker2 t y = y ^ 3 * ker2 (y * t) 1 := by
      intro t
      unfold ker2
      rcases eq_or_ne t 0 with rfl | ht
      · simp
      · field_simp
    simp_rw [e]
    rw [integral_const_mul, h, mul_zero, smul_eq_mul]
    unfold K2
    field_simp
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have e : ∀ t : ℝ, ker2 t y = -ker2 t (-y) := by
      intro t; unfold ker2; rw [mul_neg, Real.sin_neg]; ring
    simp_rw [e]
    rw [integral_neg, hpos (-y) (neg_pos.mpr hy), abs_of_neg hy]
    ring
  · simp [ker2]
  · rw [hpos y hy, abs_of_pos hy]; ring

end BstLean.Part150
