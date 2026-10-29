import BstLean.Part107Defs

/-!
# Part 107, (P4), preparation: geometry of `y ↦ y/|y|`, a scalar bound, Cauchy–Schwarz
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

section geom

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `v/‖v‖`. -/
noncomputable def uv (v : V) : V := (1 / ‖v‖) • v

lemma norm_uv_le (v : V) : ‖uv v‖ ≤ 1 := by
  unfold uv
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases h : ‖v‖ = 0
  · simp [h]
  · rw [one_div, inv_mul_cancel₀ h]

lemma uv_sub_le (v w : V) (hv : v ≠ 0) : ‖uv v - uv w‖ ≤ 2 * ‖v - w‖ / ‖v‖ := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  by_cases hw : w = 0
  · subst hw
    simp only [uv, norm_zero, smul_zero, sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : 1 / ‖v‖ * ‖v‖ = 1 := by field_simp
    have h2 : 2 * ‖v‖ / ‖v‖ = 2 := by field_simp
    rw [this, h2]
    norm_num
  · have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hc : (‖w‖ - ‖v‖) / (‖v‖ * ‖w‖) = 1 / ‖v‖ - 1 / ‖w‖ := by field_simp
    have e : uv v - uv w = (1 / ‖v‖) • (v - w) + ((‖w‖ - ‖v‖) / (‖v‖ * ‖w‖)) • w := by
      unfold uv
      rw [hc]
      module
    have h1 : |‖w‖ - ‖v‖| ≤ ‖v - w‖ := by
      rw [norm_sub_rev]; exact abs_norm_sub_norm_le w v
    have h3 : |‖w‖ - ‖v‖| / (‖v‖ * ‖w‖) * ‖w‖ = |‖w‖ - ‖v‖| / ‖v‖ := by field_simp
    calc ‖uv v - uv w‖ ≤ ‖(1 / ‖v‖) • (v - w)‖ + ‖((‖w‖ - ‖v‖) / (‖v‖ * ‖w‖)) • w‖ := by
          rw [e]; exact norm_add_le _ _
      _ = 1 / ‖v‖ * ‖v - w‖ + |‖w‖ - ‖v‖| / ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < 1 / ‖v‖), abs_div,
            abs_of_pos (by positivity : 0 < ‖v‖ * ‖w‖), h3]
      _ = (‖v - w‖ + |‖w‖ - ‖v‖|) / ‖v‖ := by ring
      _ ≤ 2 * ‖v - w‖ / ‖v‖ := div_le_div_of_nonneg_right (by linarith) hv'.le

end geom

section transfer

variable {n : ℕ}

lemma normSq_toLp (y : Fin n → ℝ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, y i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

lemma norm_toLp (y : Fin n → ℝ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ = Real.sqrt (∑ i, y i ^ 2) := by
  rw [← normSq_toLp, Real.sqrt_sq (norm_nonneg _)]

lemma sphProj_toLp (y : Fin n → ℝ) :
    (WithLp.toLp 2 (sphProj y) : EuclideanSpace ℝ (Fin n)) = uv (WithLp.toLp 2 y) := by
  unfold uv sphProj
  rw [norm_toLp]
  rfl

lemma dot_eq_inner (a b : Fin n → ℝ) :
    dot a b = inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 b) := by
  simp [dot, PiLp.inner_apply, mul_comm]

lemma cosA_abs_le (g v : Fin n → ℝ) : |cosA g v| ≤ 1 := by
  unfold cosA
  rw [dot_eq_inner, sphProj_toLp, sphProj_toLp]
  calc |inner ℝ (uv (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))) (uv (WithLp.toLp 2 v))|
      ≤ ‖uv (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin n))‖ * ‖uv (WithLp.toLp 2 v :
        EuclideanSpace ℝ (Fin n))‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_uv_le _) (norm_uv_le _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma cosA_diff_sq (g v w : Fin n → ℝ) (hv : v ≠ 0) :
    (cosA g v - cosA g w) ^ 2 ≤ 4 * (∑ i, (v i - w i) ^ 2) * (1 / ∑ i, v i ^ 2) := by
  set G : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 g
  set V' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v with hV
  set W' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 w with hW
  have hV0 : V' ≠ 0 := by
    intro h
    apply hv
    have := congrArg WithLp.ofLp h
    simpa [hV] using this
  have hVpos : 0 < ‖V'‖ := norm_pos_iff.mpr hV0
  have e : cosA g v - cosA g w = inner ℝ (uv G) (uv V' - uv W') := by
    unfold cosA
    rw [dot_eq_inner, dot_eq_inner, sphProj_toLp, sphProj_toLp, sphProj_toLp, inner_sub_right]
  have h1 : |cosA g v - cosA g w| ≤ 2 * ‖V' - W'‖ / ‖V'‖ := by
    rw [e]
    calc |inner ℝ (uv G) (uv V' - uv W')| ≤ ‖uv G‖ * ‖uv V' - uv W'‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * (2 * ‖V' - W'‖ / ‖V'‖) :=
          mul_le_mul (norm_uv_le _) (uv_sub_le _ _ hV0) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2 : (cosA g v - cosA g w) ^ 2 ≤ (2 * ‖V' - W'‖ / ‖V'‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : ‖V' - W'‖ ^ 2 = ∑ i, (v i - w i) ^ 2 := by
    have : V' - W' = WithLp.toLp 2 (v - w) := by rw [hV, hW]; rfl
    rw [this, normSq_toLp]
    rfl
  have h4 : ‖V'‖ ^ 2 = ∑ i, v i ^ 2 := normSq_toLp v
  rw [← h3, ← h4]
  calc (cosA g v - cosA g w) ^ 2 ≤ (2 * ‖V' - W'‖ / ‖V'‖) ^ 2 := h2
    _ = 4 * ‖V' - W'‖ ^ 2 * (1 / ‖V'‖ ^ 2) := by ring

end transfer

/-- (c): `(r₁−r₂)² + (s₁−s₂)² ≤ (r₁−r₂)²/(1−r₊²)`. -/
lemma sC_diff {r₁ r₂ rp : ℝ} (h1 : 0 ≤ r₁) (h1p : r₁ ≤ rp) (h2 : 0 ≤ r₂) (h2p : r₂ ≤ rp)
    (hp : rp < 1) :
    (r₁ - r₂) ^ 2 + (sC r₁ - sC r₂) ^ 2 ≤ (r₁ - r₂) ^ 2 / (1 - rp ^ 2) := by
  have hc : 0 < 1 - rp ^ 2 := by nlinarith
  have hs1 : sC r₁ ^ 2 = 1 - r₁ ^ 2 := sC_sq (by rw [abs_of_nonneg h1]; linarith)
  have hs2 : sC r₂ ^ 2 = 1 - r₂ ^ 2 := sC_sq (by rw [abs_of_nonneg h2]; linarith)
  have hσ : Real.sqrt (1 - rp ^ 2) ^ 2 = 1 - rp ^ 2 := Real.sq_sqrt hc.le
  have hσ0 : 0 ≤ Real.sqrt (1 - rp ^ 2) := Real.sqrt_nonneg _
  have g1 : Real.sqrt (1 - rp ^ 2) ≤ sC r₁ := Real.sqrt_le_sqrt (by nlinarith)
  have g2 : Real.sqrt (1 - rp ^ 2) ≤ sC r₂ := Real.sqrt_le_sqrt (by nlinarith)
  have hsum : 4 * (1 - rp ^ 2) ≤ (sC r₁ + sC r₂) ^ 2 := by
    rw [← hσ]
    nlinarith
  have hprod : (sC r₁ - sC r₂) ^ 2 * (sC r₁ + sC r₂) ^ 2 = (r₁ - r₂) ^ 2 * (r₁ + r₂) ^ 2 := by
    have : (sC r₁ - sC r₂) * (sC r₁ + sC r₂) = (r₂ - r₁) * (r₂ + r₁) := by
      linear_combination hs1 - hs2
    calc (sC r₁ - sC r₂) ^ 2 * (sC r₁ + sC r₂) ^ 2 = ((sC r₁ - sC r₂) * (sC r₁ + sC r₂)) ^ 2 := by
          ring
      _ = _ := by rw [this]; ring
  have hrr : (r₁ + r₂) ^ 2 ≤ 4 * rp ^ 2 := by nlinarith
  have key : (sC r₁ - sC r₂) ^ 2 * (1 - rp ^ 2) ≤ rp ^ 2 * (r₁ - r₂) ^ 2 := by
    have a1 : (sC r₁ - sC r₂) ^ 2 * (4 * (1 - rp ^ 2)) ≤
        (sC r₁ - sC r₂) ^ 2 * (sC r₁ + sC r₂) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    have a2 : (r₁ - r₂) ^ 2 * (r₁ + r₂) ^ 2 ≤ (r₁ - r₂) ^ 2 * (4 * rp ^ 2) :=
      mul_le_mul_of_nonneg_left hrr (sq_nonneg _)
    linarith
  rw [le_div_iff₀ hc]
  linarith

/-- Cauchy–Schwarz in the form `(E D)² ≤ E U · E V` when `D² ≤ U V`. -/
lemma cs_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (D U V : α → ℝ) (hD : Integrable D μ) (hU : Integrable U μ) (hV : Integrable V μ)
    (hUnn : ∀ x, 0 ≤ U x) (hVnn : ∀ x, 0 ≤ V x) (h : ∀ᵐ x ∂μ, D x ^ 2 ≤ U x * V x) :
    (∫ x, D x ∂μ) ^ 2 ≤ (∫ x, U x ∂μ) * ∫ x, V x ∂μ := by
  have hq : ∀ c : ℝ, 0 ≤ (∫ x, U x ∂μ) * (c * c) + (-2 * ∫ x, |D x| ∂μ) * c + ∫ x, V x ∂μ := by
    intro c
    have hi : Integrable (fun x => U x * (c * c) + (-2 * |D x|) * c + V x) μ :=
      ((hU.mul_const _).add ((hD.abs.const_mul _).mul_const _)).add hV
    have h0 : 0 ≤ ∫ x, (U x * (c * c) + (-2 * |D x|) * c + V x) ∂μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [h] with x hx
      have hnn : 0 ≤ U x * (c * c) + V x := by nlinarith [hUnn x, hVnn x, mul_self_nonneg c]
      have hsq : (2 * |D x| * c) ^ 2 ≤ (U x * (c * c) + V x) ^ 2 := by
        have e1 : (2 * |D x| * c) ^ 2 = 4 * (c * c) * D x ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
        have e2 : 4 * (c * c) * D x ^ 2 ≤ 4 * (c * c) * (U x * V x) :=
          mul_le_mul_of_nonneg_left hx (by nlinarith [mul_self_nonneg c])
        nlinarith [sq_nonneg (U x * (c * c) - V x)]
      have := abs_le_of_sq_le_sq' hsq hnn
      show (0 : ℝ) ≤ U x * (c * c) + (-2 * |D x|) * c + V x
      linarith [this.2]
    have e : ∫ x, (U x * (c * c) + (-2 * |D x|) * c + V x) ∂μ =
        (∫ x, U x ∂μ) * (c * c) + (-2 * ∫ x, |D x| ∂μ) * c + ∫ x, V x ∂μ := by
      have i1 : Integrable (fun x => U x * (c * c)) μ := hU.mul_const _
      have i2 : Integrable (fun x => -2 * |D x| * c) μ := (hD.abs.const_mul _).mul_const _
      have i12 : Integrable (fun x => U x * (c * c) + -2 * |D x| * c) μ := i1.add i2
      rw [integral_add i12 hV, integral_add i1 i2,
        integral_mul_const, integral_mul_const, integral_const_mul]
    rw [← e]
    exact h0
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have h1 : |∫ x, D x ∂μ| ≤ ∫ x, |D x| ∂μ := abs_integral_le_integral_abs
  have h2 : (∫ x, D x ∂μ) ^ 2 ≤ (∫ x, |D x| ∂μ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

end BstLean.Part107
