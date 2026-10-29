import BstLean.Part160Final

/-!
# Part 160 (file `Split2`): the frame split of second order

Do not use `sorry`, `native_decide` or `axiom`.

The frame split of the paper (Lemma `t7:p04:split`) uses `1/S ≤ 1/(γ_A d)` on `{S ≥ γ_A d}`,
with a cutoff `d` below the typical value `s²` of `S/γ_A`. This file keeps the typical value:
for `R ≥ a > 0` and `A > 0`, `1/R ≤ 1/A + (A − R)₊/(a·A)`. So

`∫⟨e, w⟩² ≤ (1/A)∫⟨r, w⟩² + (1/(aA))·(∫⟨r, w⟩⁴)^{1/2}·(∫(A − |r|²)₊²)^{1/2} + μ{|r|² < a}·|w|²`.

The first term has the typical value `A` in the place of the cutoff `a`; the second term is
of relative size `n^{-1/2}` for the networks; the cutoff `a` occurs only in the small terms.

* `frame_split2`: the split for a probability measure.
* `resid_fourth`: `∫ (t_A⟨r, w⟩²)² ≤ (κ₄ (γ_A/n) |w|²)²` (fourth moment of a linear functional of
  the hidden vector, `Part160Mass4`).
* `gap_sq`: `∫ (γ_A s² − S)₊² ≤ (2 γ_A (1 + N22) ρ)²`, `ρ² ≥ N/n`.
* `frameA_point2`: the frame bound at one retained value:
  `n·L_A ≤ (N + ξ)/s² + 2 κ₄ (1 + N22) ρ/(sd² s²) + (16.09 a)⁴/(n³ (s − sd)⁸)`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (lam res sig eDir eDir_unit_or_zero measurable_eDir measurable_res)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS Xi4 N2 sq2 hid2Mean_cr)

section general

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- `1/R ≤ 1/A + (A − R)₊/(a·A)` for `R ≥ a > 0`, `A > 0`. -/
lemma inv_split {R a A : ℝ} (ha : 0 < a) (hA : 0 < A) (hR : a ≤ R) :
    R⁻¹ ≤ 1 / A + max 0 (A - R) / (a * A) := by
  have hR0 : 0 < R := lt_of_lt_of_le ha hR
  by_cases h : A ≤ R
  · have h1 : R⁻¹ ≤ 1 / A := by rw [one_div]; exact inv_anti₀ hA h
    have h2 : 0 ≤ max 0 (A - R) / (a * A) := by positivity
    linarith
  · have hlt : R < A := not_le.mp h
    rw [max_eq_right (by linarith)]
    have e : R⁻¹ = 1 / A + (A - R) / (R * A) := by field_simp; ring
    rw [e]
    have : (A - R) / (R * A) ≤ (A - R) / (a * A) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_right hR hA.le)
    linarith

/-- The pointwise split of second order. -/
lemma eDir_sq_le2 (b h w : Fin m → ℝ) {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    (∑ j, eDir b h j * w j) ^ 2 ≤
      1 / A * (∑ j, res b h j * w j) ^ 2 +
        (∑ j, res b h j * w j) ^ 2 * max 0 (A - normSq (res b h)) / (a * A) +
        (if normSq (res b h) < a then ∑ j, w j ^ 2 else 0) := by
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : 0 ≤ 1 / A * (∑ j, res b h j * w j) ^ 2 := by positivity
  have h2 : 0 ≤ (∑ j, res b h j * w j) ^ 2 * max 0 (A - normSq (res b h)) / (a * A) := by
    positivity
  by_cases hlt : normSq (res b h) < a
  · simp only [hlt, ↓reduceIte]
    have cs := sum_mul_sq_le (eDir b h) w
    have he : normSq (eDir b h) ≤ 1 := by
      rcases eDir_unit_or_zero b h with h1 | h1
      · exact h1.le
      · rw [h1]; simp [normSq]
    have : normSq (eDir b h) * normSq w ≤ 1 * normSq w :=
      mul_le_mul_of_nonneg_right he (normSq_nonneg w)
    have e : normSq w = ∑ j, w j ^ 2 := rfl
    linarith
  · simp only [hlt, ↓reduceIte, add_zero]
    have hN : a ≤ normSq (res b h) := not_lt.mp hlt
    have hN0 : 0 < normSq (res b h) := lt_of_lt_of_le ha hN
    have e : ∑ j, eDir b h j * w j =
        (Real.sqrt (normSq (res b h)))⁻¹ * ∑ j, res b h j * w j := by
      unfold eDir
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]
    rw [e, mul_pow, inv_pow, Real.sq_sqrt hN0.le]
    have h3 := inv_split ha hA hN
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg (∑ j, res b h j * w j))
    calc (normSq (res b h))⁻¹ * (∑ j, res b h j * w j) ^ 2
        ≤ (1 / A + max 0 (A - normSq (res b h)) / (a * A)) * (∑ j, res b h j * w j) ^ 2 := h4
      _ = _ := by ring

/-- Cauchy–Schwarz in the form `∫ x·y ≤ P·Q` from `∫ x² ≤ P²`, `∫ y² ≤ Q²`, `P, Q > 0`. -/
lemma int_mul_le_of_sq (μ : Measure Ω) {x y : Ω → ℝ} {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (hx : Integrable (fun ω => x ω ^ 2) μ) (hy : Integrable (fun ω => y ω ^ 2) μ)
    (hxy : Integrable (fun ω => x ω * y ω) μ)
    (hPx : ∫ ω, x ω ^ 2 ∂μ ≤ P ^ 2) (hQy : ∫ ω, y ω ^ 2 ∂μ ≤ Q ^ 2) :
    ∫ ω, x ω * y ω ∂μ ≤ P * Q := by
  have hpt : ∀ ω, x ω * y ω ≤ Q / (2 * P) * x ω ^ 2 + P / (2 * Q) * y ω ^ 2 := by
    intro ω
    have h := sq_nonneg (Q * x ω - P * y ω)
    have e : Q / (2 * P) * x ω ^ 2 + P / (2 * Q) * y ω ^ 2 - x ω * y ω =
        (Q * x ω - P * y ω) ^ 2 / (2 * P * Q) := by
      field_simp; ring
    have : 0 ≤ (Q * x ω - P * y ω) ^ 2 / (2 * P * Q) := by positivity
    linarith
  have hsum : ∫ ω, (Q / (2 * P) * x ω ^ 2 + P / (2 * Q) * y ω ^ 2) ∂μ =
      Q / (2 * P) * ∫ ω, x ω ^ 2 ∂μ + P / (2 * Q) * ∫ ω, y ω ^ 2 ∂μ := by
    have h : ∫ ω, (Q / (2 * P) * x ω ^ 2 + P / (2 * Q) * y ω ^ 2) ∂μ =
        ∫ ω, Q / (2 * P) * x ω ^ 2 ∂μ + ∫ ω, P / (2 * Q) * y ω ^ 2 ∂μ :=
      integral_add (hx.const_mul (Q / (2 * P))) (hy.const_mul (P / (2 * Q)))
    rw [h, integral_const_mul, integral_const_mul]
  have h1 : ∫ ω, x ω * y ω ∂μ ≤ ∫ ω, (Q / (2 * P) * x ω ^ 2 + P / (2 * Q) * y ω ^ 2) ∂μ :=
    integral_mono hxy ((hx.const_mul _).add (hy.const_mul _)) hpt
  rw [hsum] at h1
  have h2 : Q / (2 * P) * ∫ ω, x ω ^ 2 ∂μ ≤ Q / (2 * P) * P ^ 2 :=
    mul_le_mul_of_nonneg_left hPx (by positivity)
  have h3 : P / (2 * Q) * ∫ ω, y ω ^ 2 ∂μ ≤ P / (2 * Q) * Q ^ 2 :=
    mul_le_mul_of_nonneg_left hQy (by positivity)
  have e : Q / (2 * P) * P ^ 2 + P / (2 * Q) * Q ^ 2 = P * Q := by field_simp; ring
  linarith

/-- **The frame split of second order.** For `a, A > 0`:
`∫⟨e, w⟩² ≤ (1/A)∫⟨r, w⟩² + P·Q/(a·A) + μ{|r|² < a}·|w|²` when `∫⟨r, w⟩⁴ ≤ P²` and
`∫(A − |r|²)₊² ≤ Q²`. -/
theorem frame_split2 (μ : Measure Ω) [IsProbabilityMeasure μ] {h : Ω → Fin m → ℝ}
    (hh : Measurable h) (b w : Fin m → ℝ) {a A P Q : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hP : 0 < P) (hQ : 0 < Q)
    (hint : Integrable (fun x => (∑ j, res b (h x) j * w j) ^ 2) μ)
    (hint4 : Integrable (fun x => ((∑ j, res b (h x) j * w j) ^ 2) ^ 2) μ)
    (hP4 : ∫ x, ((∑ j, res b (h x) j * w j) ^ 2) ^ 2 ∂μ ≤ P ^ 2)
    (hQ2 : ∫ x, (max 0 (A - normSq (res b (h x)))) ^ 2 ∂μ ≤ Q ^ 2) :
    ∫ x, (∑ j, eDir b (h x) j * w j) ^ 2 ∂μ ≤
      1 / A * ∫ x, (∑ j, res b (h x) j * w j) ^ 2 ∂μ + P * Q / (a * A) +
        μ.real {x | normSq (res b (h x)) < a} * ∑ j, w j ^ 2 := by
  have hmr : Measurable (fun x => normSq (res b (h x))) :=
    measurable_normSq.comp ((measurable_res b).comp hh)
  have hS : MeasurableSet {x | normSq (res b (h x)) < a} := measurableSet_lt hmr measurable_const
  have hW : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hmX : Measurable (fun x => (∑ j, res b (h x) j * w j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_res b).comp hh)).mul_const _).pow_const 2
  have hmG : Measurable (fun x => max 0 (A - normSq (res b (h x)))) :=
    measurable_const.max (measurable_const.sub hmr)
  have hG2 : Integrable (fun x => (max 0 (A - normSq (res b (h x)))) ^ 2) μ := by
    refine Integrable.of_bound (hmG.pow_const 2).aestronglyMeasurable (A ^ 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 : 0 ≤ max 0 (A - normSq (res b (h x))) := le_max_left _ _
    have h1 : max 0 (A - normSq (res b (h x))) ≤ A :=
      max_le hA.le (by linarith [normSq_nonneg (res b (h x))])
    exact pow_le_pow_left₀ h0 h1 2
  have hXG : Integrable (fun x => (∑ j, res b (h x) j * w j) ^ 2 *
      max 0 (A - normSq (res b (h x)))) μ := by
    refine Integrable.mono' (hint.const_mul A) (hmX.mul hmG).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ max 0 (A - normSq (res b (h x))) := le_max_left _ _
    have h1 : max 0 (A - normSq (res b (h x))) ≤ A :=
      max_le hA.le (by linarith [normSq_nonneg (res b (h x))])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h0), mul_comm A]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hCS := int_mul_le_of_sq μ hP hQ hint4 hG2 hXG hP4 hQ2
  have hmL : Measurable (fun x => (∑ j, eDir b (h x) j * w j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_eDir b).comp hh)).mul_const _).pow_const 2
  have hiL : Integrable (fun x => (∑ j, eDir b (h x) j * w j) ^ 2) μ := by
    refine Integrable.of_bound hmL.aestronglyMeasurable (∑ j, w j ^ 2)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have cs := sum_mul_sq_le (eDir b (h x)) w
    have he : normSq (eDir b (h x)) ≤ 1 := by
      rcases eDir_unit_or_zero b (h x) with h1 | h1
      · exact h1.le
      · rw [h1]; simp [normSq]
    have : normSq (eDir b (h x)) * normSq w ≤ 1 * normSq w :=
      mul_le_mul_of_nonneg_right he (normSq_nonneg w)
    have e : normSq w = ∑ j, w j ^ 2 := rfl
    linarith
  have hind : (fun x => if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) =
      Set.indicator {x | normSq (res b (h x)) < a} (fun _ => ∑ j, w j ^ 2) := by
    funext x
    simp [Set.indicator]
  have hiI : Integrable (fun x => if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) μ := by
    rw [hind]; exact (integrable_const _).indicator hS
  have hI : ∫ x, (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) ∂μ =
      μ.real {x | normSq (res b (h x)) < a} * ∑ j, w j ^ 2 := by
    rw [hind, integral_indicator_const _ hS, smul_eq_mul]
  have hi2 : Integrable (fun x => (∑ j, res b (h x) j * w j) ^ 2 *
      max 0 (A - normSq (res b (h x))) / (a * A)) μ := hXG.div_const _
  have hA1 : ∫ x, (1 / A * (∑ j, res b (h x) j * w j) ^ 2 +
      (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) / (a * A) +
      (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0)) ∂μ =
      1 / A * ∫ x, (∑ j, res b (h x) j * w j) ^ 2 ∂μ +
        (∫ x, (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) ∂μ) / (a * A) +
        μ.real {x | normSq (res b (h x)) < a} * ∑ j, w j ^ 2 := by
    have e1 : ∫ x, (1 / A * (∑ j, res b (h x) j * w j) ^ 2 +
        (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) / (a * A) +
        (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0)) ∂μ =
        ∫ x, (1 / A * (∑ j, res b (h x) j * w j) ^ 2 +
          (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) / (a * A)) ∂μ +
        ∫ x, (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0) ∂μ :=
      integral_add ((hint.const_mul _).add hi2) hiI
    have e2 : ∫ x, (1 / A * (∑ j, res b (h x) j * w j) ^ 2 +
          (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) / (a * A)) ∂μ =
        ∫ x, 1 / A * (∑ j, res b (h x) j * w j) ^ 2 ∂μ +
        ∫ x, (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) / (a * A) ∂μ :=
      integral_add (hint.const_mul _) hi2
    rw [e1, e2, integral_const_mul, integral_div, hI]
  have hmono : ∫ x, (∑ j, eDir b (h x) j * w j) ^ 2 ∂μ ≤
      ∫ x, (1 / A * (∑ j, res b (h x) j * w j) ^ 2 +
      (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) / (a * A) +
      (if normSq (res b (h x)) < a then ∑ j, w j ^ 2 else 0)) ∂μ :=
    integral_mono hiL (((hint.const_mul _).add hi2).add hiI)
      fun x => eDir_sq_le2 b (h x) w ha hA
  rw [hA1] at hmono
  have h5 : (∫ x, (∑ j, res b (h x) j * w j) ^ 2 * max 0 (A - normSq (res b (h x))) ∂μ) /
      (a * A) ≤ P * Q / (a * A) := div_le_div_of_nonneg_right hCS (by positivity)
  linarith

/-- `(x + y)² ≤ (1 + η)x² + (1 + 1/η)y²`, `η > 0`. -/
lemma sq_add_le_eta (x y : ℝ) {η : ℝ} (hη : 0 < η) :
    (x + y) ^ 2 ≤ (1 + η) * x ^ 2 + (1 + 1 / η) * y ^ 2 := by
  have e : (1 + η) * x ^ 2 + (1 + 1 / η) * y ^ 2 - (x + y) ^ 2 = (η * x - y) ^ 2 / η := by
    field_simp; ring
  have : 0 ≤ (η * x - y) ^ 2 / η := by positivity
  linarith

/-- `(x + y)⁴ ≤ (1 + η)³x⁴ + (1 + 1/η)³y⁴`, `η > 0`. -/
lemma pow4_add_le_eta (x y : ℝ) {η : ℝ} (hη : 0 < η) :
    (x + y) ^ 4 ≤ (1 + η) ^ 3 * x ^ 4 + (1 + 1 / η) ^ 3 * y ^ 4 := by
  have h1 := sq_add_le_eta x y hη
  have h0 : 0 ≤ (x + y) ^ 2 := sq_nonneg _
  have hη' : (0 : ℝ) < 1 / η := by positivity
  have h2 := sq_add_le_eta ((1 + η) * x ^ 2) ((1 + 1 / η) * y ^ 2) hη
  calc (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
    _ ≤ ((1 + η) * x ^ 2 + (1 + 1 / η) * y ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ (1 + η) * ((1 + η) * x ^ 2) ^ 2 + (1 + 1 / η) * ((1 + 1 / η) * y ^ 2) ^ 2 := h2
    _ = _ := by ring

end general

variable {n : ℕ}

/-- `v1D` as a scalar product: `v1D v ξ = (√t/|v|)·⟨v, h⟩`. -/
lemma v1D_dot (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) {v : Fin (mA n) → ℝ} (hv : 0 < normSq v) (ξ : Fin n → ℝ) :
    v1D A₁ A₂ c τ v ξ =
      √(2 / (mA n : ℝ)) / nrm v * (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))) := by
  have hnv : 0 < nrm v := Real.sqrt_pos.mpr hv
  have e2 : normSq v = nrm v ^ 2 := (BstLean.Part153.nrm_sq v).symm
  have e3 : ∑ j, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j * v j =
      v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := by
    unfold dotProduct
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  unfold v1D lam
  rw [e3, show √(normSq v) = nrm v from rfl, e2]
  field_simp

/-- **The fourth moment of the scaled residual in a direction `w`**:
`∫ (⟨r, w⟩²)² ≤ (κ₄·(γ_A/n)·|w|²/t_A)²` when `(1 + η)³(2a + r)² + (1 + 1/η)³ξ² ≤ κ₄²`,
`Ξ ≤ N γ_A/n`, `Ξ₄ ≤ a γ_A/n`, `4a² + N² ≤ r²`, `t_A|μ − b|² ≤ ξ γ_A/n`. -/
theorem resid_fourth (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (b w : Fin (mA n) → ℝ) {N a xi r η κ : ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 A₁ A₂ c τ ≤ a * (2 / (n : ℝ)) / n)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (ha0 : 0 ≤ a) (hr : 0 ≤ r) (hr2 : 4 * a ^ 2 + N ^ 2 ≤ r ^ 2) (hη : 0 < η) (hκ0 : 0 ≤ κ)
    (hκ : (1 + η) ^ 3 * (2 * a + r) ^ 2 + (1 + 1 / η) ^ 3 * xi ^ 2 ≤ κ ^ 2) :
    Integrable (fun ξ : Fin n → ℝ =>
      ((∑ j, res b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) j * w j) ^ 2) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, ((∑ j, res b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) j * w j) ^ 2) ^ 2 ∂stdGauss (Fin n) ≤
      (κ * (2 / (n : ℝ) / n) * (∑ j, w j ^ 2) / (2 / (mA n : ℝ))) ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  obtain ⟨v, hv⟩ : ∃ v : Fin (mA n) → ℝ, v = res b w := ⟨_, rfl⟩
  have hsym : ∀ ξ : Fin n → ℝ, ∑ j, res b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) j * w j =
      v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) := by
    intro ξ
    rw [res_symm, hv]
    unfold dotProduct
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hsym]
  have hvw : normSq v ≤ ∑ j, w j ^ 2 := by rw [hv]; exact normSq_res_le b w
  by_cases hv0 : normSq v = 0
  · have hz : v = 0 := BstLean.Part134.eq_zero_of_normSq hv0
    simp only [hz, zero_dotProduct]
    refine ⟨by simp, ?_⟩
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    positivity
  have hvp : 0 < normSq v := lt_of_le_of_ne (normSq_nonneg v) (Ne.symm hv0)
  have hnv : 0 < nrm v := Real.sqrt_pos.mpr hvp
  obtain ⟨st, hst⟩ : ∃ st : ℝ, st = √(2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hstp : 0 < st := by rw [hst]; exact Real.sqrt_pos.mpr ht0
  have hst2 : st ^ 2 = 2 / (mA n : ℝ) := by rw [hst]; exact Real.sq_sqrt ht0.le
  -- `⟨v, h⟩ = (|v|/√t)·v1D`
  have hdot : ∀ ξ : Fin n → ℝ, v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) =
      nrm v / st * v1D A₁ A₂ c τ v ξ := by
    intro ξ
    rw [v1D_dot A₁ A₂ c τ hvp, ← hst]
    field_simp
  obtain ⟨m1, hm1⟩ : ∃ m1 : ℝ, m1 = ∫ ζ, v1D A₁ A₂ c τ v ζ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have hF := eulip_phi1D hvp
  obtain ⟨hI4, -⟩ := lipD_fourth hn hF A₁ A₂ c hτ
  have hvar := lipD_var hn hF A₁ A₂ c hτ
  have h4 := lipD_fourth_sharp hn hF A₁ A₂ c hτ hXi4 (hvar.trans hXi)
  rw [← v1D_eq hvp] at hI4 h4
  rw [← hm1] at hI4 h4
  -- the mean
  have hm1e : m1 = st / nrm v * (v ⬝ᵥ (hid2Mean_cr A₁ A₂ c τ - b)) := by
    rw [hm1]
    simp_rw [v1D_dot A₁ A₂ c τ hvp]
    rw [integral_const_mul, BstLean.Part153.integral_dot_hid2_cr hn1, ← hst, dotProduct_sub]
    have hvb : v ⬝ᵥ b = 0 := by
      have h1 := res_symm b b w
      rw [res_self] at h1
      have h2 : ∑ j, b j * res b w j = 0 := by
        rw [← h1]; simp
      rw [hv]
      unfold dotProduct
      rw [← h2]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hvb, sub_zero]
  have hm1sq : m1 ^ 2 ≤ xi * (2 / (n : ℝ) / n) := by
    have h1 := BstLean.Part153.abs_dot_le_nrm v (hid2Mean_cr A₁ A₂ c τ - b)
    have h2 : |m1| ≤ st * nrm (hid2Mean_cr A₁ A₂ c τ - b) := by
      rw [hm1e, abs_mul, abs_of_pos (div_pos hstp hnv)]
      calc st / nrm v * |v ⬝ᵥ (hid2Mean_cr A₁ A₂ c τ - b)|
          ≤ st / nrm v * (nrm v * nrm (hid2Mean_cr A₁ A₂ c τ - b)) :=
            mul_le_mul_of_nonneg_left h1 (div_pos hstp hnv).le
        _ = _ := by field_simp
    have h3 := pow_le_pow_left₀ (abs_nonneg m1) h2 2
    rw [sq_abs, mul_pow, hst2, BstLean.Part153.nrm_sq] at h3
    calc m1 ^ 2 ≤ 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) := h3
      _ ≤ xi * (2 / (n : ℝ)) / n := hxi
      _ = _ := by ring
  have hxi0 : 0 ≤ xi * (2 / (n : ℝ) / n) := le_trans (sq_nonneg m1) hm1sq
  -- `∫ (v1D − m1)⁴ ≤ ((2a + r)·γ/n)²`
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = 2 / (n : ℝ) / n := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; positivity
  rw [← hg] at hm1sq hxi0 ⊢
  have h4' : ∫ ξ, (v1D A₁ A₂ c τ v ξ - m1) ^ 4 ∂stdGauss (Fin n) ≤ ((2 * a + r) * g) ^ 2 := by
    refine h4.trans ?_
    have e1 : 4 * (a * (2 / (n : ℝ)) / n) ^ 2 + (N * (2 / (n : ℝ)) / n) ^ 2 =
        g ^ 2 * (4 * a ^ 2 + N ^ 2) := by rw [hg]; ring
    have e2 : √(g ^ 2 * (4 * a ^ 2 + N ^ 2)) = g * √(4 * a ^ 2 + N ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hg0.le]
    have h5 : √(4 * a ^ 2 + N ^ 2) ≤ r := by
      rw [← Real.sqrt_sq hr]; exact Real.sqrt_le_sqrt hr2
    rw [e1, e2]
    have e3 : 2 * (a * (2 / (n : ℝ)) / n) + g * √(4 * a ^ 2 + N ^ 2) =
        (2 * a + √(4 * a ^ 2 + N ^ 2)) * g := by rw [hg]; ring
    rw [e3]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (by linarith) hg0.le) 2
  -- `∫ v1D⁴ ≤ (κ g)²`
  have hm := measurable_v1D hvp A₁ A₂ c τ
  have hpt : ∀ ξ, v1D A₁ A₂ c τ v ξ ^ 4 ≤
      (1 + η) ^ 3 * (v1D A₁ A₂ c τ v ξ - m1) ^ 4 + (1 + 1 / η) ^ 3 * m1 ^ 4 := by
    intro ξ
    have := pow4_add_le_eta (v1D A₁ A₂ c τ v ξ - m1) m1 hη
    rwa [sub_add_cancel] at this
  have hdom : Integrable (fun ξ => (1 + η) ^ 3 * (v1D A₁ A₂ c τ v ξ - m1) ^ 4 +
      (1 + 1 / η) ^ 3 * m1 ^ 4) (stdGauss (Fin n)) :=
    (hI4.const_mul _).add (integrable_const _)
  have hv4i : Integrable (fun ξ => v1D A₁ A₂ c τ v ξ ^ 4) (stdGauss (Fin n)) := by
    refine Integrable.mono' hdom (hm.pow_const 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt ξ
  have hv4 : ∫ ξ, v1D A₁ A₂ c τ v ξ ^ 4 ∂stdGauss (Fin n) ≤ (κ * g) ^ 2 := by
    have h1 := integral_mono hv4i hdom hpt
    rw [integral_add (hI4.const_mul _) (integrable_const _), integral_const_mul, integral_const,
      probReal_univ, one_smul] at h1
    have h2 : (1 + η) ^ 3 * ∫ ξ, (v1D A₁ A₂ c τ v ξ - m1) ^ 4 ∂stdGauss (Fin n) ≤
        (1 + η) ^ 3 * ((2 * a + r) * g) ^ 2 := mul_le_mul_of_nonneg_left h4' (by positivity)
    have h3 : m1 ^ 4 ≤ (xi * g) ^ 2 := by
      calc m1 ^ 4 = (m1 ^ 2) ^ 2 := by ring
        _ ≤ (xi * g) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hm1sq 2
    have h3' : (1 + 1 / η) ^ 3 * m1 ^ 4 ≤ (1 + 1 / η) ^ 3 * (xi * g) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h6 : (1 + η) ^ 3 * ((2 * a + r) * g) ^ 2 + (1 + 1 / η) ^ 3 * (xi * g) ^ 2 ≤
        (κ * g) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hκ (sq_nonneg g)
      calc _ = ((1 + η) ^ 3 * (2 * a + r) ^ 2 + (1 + 1 / η) ^ 3 * xi ^ 2) * g ^ 2 := by ring
        _ ≤ κ ^ 2 * g ^ 2 := this
        _ = _ := by ring
    linarith
  -- back to `⟨v, h⟩`
  have e4 : ∀ ξ : Fin n → ℝ, ((v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ 2 =
      (nrm v / st) ^ 4 * v1D A₁ A₂ c τ v ξ ^ 4 := by
    intro ξ
    rw [hdot]; ring
  simp_rw [e4]
  refine ⟨hv4i.const_mul _, ?_⟩
  rw [integral_const_mul]
  have h7 : (nrm v / st) ^ 4 = (normSq v / (2 / (mA n : ℝ))) ^ 2 := by
    rw [← hst2, ← BstLean.Part153.nrm_sq v]
    field_simp
  rw [h7]
  have hS0 : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc (normSq v / (2 / (mA n : ℝ))) ^ 2 * ∫ ξ, v1D A₁ A₂ c τ v ξ ^ 4 ∂stdGauss (Fin n)
      ≤ (normSq v / (2 / (mA n : ℝ))) ^ 2 * (κ * g) ^ 2 :=
        mul_le_mul_of_nonneg_left hv4 (sq_nonneg _)
    _ = (κ * g * normSq v / (2 / (mA n : ℝ))) ^ 2 := by ring
    _ ≤ (κ * g * (∑ j, w j ^ 2) / (2 / (mA n : ℝ))) ^ 2 := by
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvw (mul_nonneg hκ0 hg0.le)) ht0.le

/-- **The second moment of the positive part of the energy gap**:
`∫ (A − |r|²)₊² ≤ (2 γ_A (1 + N22) ρ/t_A)²` with `A = γ_A s²/t_A`, `ρ² ≥ N/n`, under the hypotheses
of `sigD_moments` (which give `γ_A s² ≤ (E σ)²`). -/
theorem gap_sq (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {N eb xi N22 e1 e2 s ρ : ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n)
    (hρ : N / n ≤ ρ ^ 2) :
    ∫ ξ, (max 0 (2 / (n : ℝ) * s ^ 2 / (2 / (mA n : ℝ)) -
        normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))))) ^ 2 ∂stdGauss (Fin n) ≤
      (2 * (2 / (n : ℝ)) * (1 + N22) * ρ / (2 / (mA n : ℝ))) ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  obtain ⟨hi1, hi2, hV, L, hL, hs'⟩ := sigD_moments hn A₁ A₂ c hτ hb hXi heb hxi hN22 he1 he1'
    he2 he2' hs2
  have hN2nn := BstLean.Part153.N2_nonneg 2 A₁ A₂ c τ
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN22
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 / (mA n : ℝ) := ⟨_, rfl⟩
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = 2 / (n : ℝ) := ⟨_, rfl⟩
  rw [← ht] at ht0 ⊢
  rw [← hγd] at hγ hV hs' ⊢
  have hγs : (√γ * s) ^ 2 = γ * s ^ 2 := by rw [mul_pow, Real.sq_sqrt hγ.le]
  rw [hγs] at hs'
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin n → ℝ) → ℝ, σ = sigD A₁ A₂ c τ b := ⟨_, rfl⟩
  rw [← hσ] at hi1 hV
  have hi2' : Integrable (fun ξ => σ ξ ^ 2) (stdGauss (Fin n)) := by rw [hσ]; exact hi2
  have hL' : L ≤ ∫ ξ, σ ξ ^ 2 ∂stdGauss (Fin n) := by rw [hσ]; exact hL
  have hσ0 : ∀ ξ, 0 ≤ σ ξ := fun ξ => by rw [hσ]; exact sigD_nonneg A₁ A₂ c τ b ξ
  have hσsq : ∀ ξ, σ ξ ^ 2 = t * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) := by
    intro ξ; rw [hσ, ht]; exact sigD_sq A₁ A₂ c τ b ξ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ y, σ y ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hM] at hV
  have hM0 : 0 ≤ M := by rw [hM]; exact integral_nonneg hσ0
  have i2 := hi1.const_mul (2 * M)
  have hcen : Integrable (fun x => (σ x - M) ^ 2) (stdGauss (Fin n)) := by
    have e : (fun x => (σ x - M) ^ 2) = fun x => σ x ^ 2 - 2 * M * σ x + M ^ 2 :=
      funext fun x => by ring
    rw [e]
    exact (hi2'.sub i2).add (integrable_const _)
  have hvar : ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) = ∫ x, σ x ^ 2 ∂stdGauss (Fin n) - M ^ 2 := by
    have hA : ∫ x, (σ x ^ 2 - 2 * M * σ x + M ^ 2) ∂stdGauss (Fin n) =
        ∫ x, (σ x ^ 2 - 2 * M * σ x) ∂stdGauss (Fin n) + ∫ _x, M ^ 2 ∂stdGauss (Fin n) :=
      integral_add (hi2'.sub i2) (integrable_const _)
    have hB : ∫ x, (σ x ^ 2 - 2 * M * σ x) ∂stdGauss (Fin n) =
        ∫ x, σ x ^ 2 ∂stdGauss (Fin n) - ∫ x, 2 * M * σ x ∂stdGauss (Fin n) :=
      integral_sub hi2' i2
    have e : (fun x => (σ x - M) ^ 2) = fun x => σ x ^ 2 - 2 * M * σ x + M ^ 2 :=
      funext fun x => by ring
    rw [e, hA, hB, integral_const_mul, ← hM, integral_const, probReal_univ, one_smul]
    ring
  have hvar0 : 0 ≤ ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) := integral_nonneg fun x => sq_nonneg _
  -- `γ s² ≤ M²`
  have hMlo : γ * s ^ 2 ≤ M ^ 2 := by linarith
  -- `M² ≤ γ (1 + N22)²`
  have hsq2m := BstLean.Part153.measurable_sq2 A₁ A₂ c τ
  have hsq2b : ∀ ξ, |sq2 A₁ A₂ c τ ξ| ≤ opN A₂ * opN A₁ / √(n : ℝ) := by
    intro ξ
    rw [BstLean.Part153.sq2_eq_hid2,
      abs_of_nonneg (div_nonneg (BstLean.Part153.nrm_nonneg _) (Real.sqrt_nonneg _))]
    exact div_le_div_of_nonneg_right (BstLean.Part153.nrm_hid2_sph_le_cr hn1 A₁ A₂ _)
      (Real.sqrt_nonneg _)
  have hs2i : Integrable (fun ξ => sq2 A₁ A₂ c τ ξ ^ 2) (stdGauss (Fin n)) :=
    Integrable.of_bound (hsq2m.pow_const 2).aestronglyMeasurable
      ((opN A₂ * opN A₁ / √(n : ℝ)) ^ 2) (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(abs_le.mp (hsq2b ξ)).1]) (abs_le.mp (hsq2b ξ)).2)
  have hMhi : M ^ 2 ≤ γ * (1 + N22) ^ 2 := by
    have h1 : ∫ x, σ x ^ 2 ∂stdGauss (Fin n) ≤ ∫ ξ, γ * sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) :=
      integral_mono hi2' (hs2i.const_mul _) fun ξ => by
        show σ ξ ^ 2 ≤ γ * sq2 A₁ A₂ c τ ξ ^ 2
        rw [hσsq, hγd, ← t_normSq_hid2 hn1, ← ht]
        exact mul_le_mul_of_nonneg_left (normSq_res_le b _) ht0.le
    rw [integral_const_mul] at h1
    have h2 := BstLean.Part153.int_sq2_sq_le hn1 A₁ A₂ c τ
    have h3 : (1 + N2 2 A₁ A₂ c τ) ^ 2 ≤ (1 + N22) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hγ.le
    linarith
  -- the pointwise bound
  have hpt : ∀ ξ, (max 0 (γ * s ^ 2 / t - normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))))) ^ 2 ≤
      4 * M ^ 2 / t ^ 2 * (σ ξ - M) ^ 2 := by
    intro ξ
    have hR : normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) = σ ξ ^ 2 / t := by
      rw [hσsq]; field_simp
    rw [hR]
    have e : γ * s ^ 2 / t - σ ξ ^ 2 / t = (γ * s ^ 2 - σ ξ ^ 2) / t := by ring
    rw [e]
    have hrhs : 0 ≤ 4 * M ^ 2 / t ^ 2 * (σ ξ - M) ^ 2 := by positivity
    by_cases hD : γ * s ^ 2 - σ ξ ^ 2 ≤ 0
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hD ht0.le)]
      simpa using hrhs
    · have hD' : 0 < γ * s ^ 2 - σ ξ ^ 2 := not_le.mp hD
      rw [max_eq_right (div_nonneg hD'.le ht0.le)]
      have hlt : σ ξ < M := by
        by_contra hge
        have hge' : M ≤ σ ξ := not_lt.mp hge
        have : M ^ 2 ≤ σ ξ ^ 2 := pow_le_pow_left₀ hM0 hge' 2
        linarith
      have h1 : γ * s ^ 2 - σ ξ ^ 2 ≤ 2 * M * (M - σ ξ) := by
        nlinarith [hσ0 ξ]
      have h2 : (γ * s ^ 2 - σ ξ ^ 2) ^ 2 ≤ (2 * M * (M - σ ξ)) ^ 2 :=
        pow_le_pow_left₀ hD'.le h1 2
      rw [div_pow]
      calc (γ * s ^ 2 - σ ξ ^ 2) ^ 2 / t ^ 2 ≤ (2 * M * (M - σ ξ)) ^ 2 / t ^ 2 :=
            div_le_div_of_nonneg_right h2 (sq_nonneg t)
        _ = _ := by ring
  have hmono := integral_mono_of_nonneg (μ := stdGauss (Fin n))
    (Filter.Eventually.of_forall fun ξ => sq_nonneg
      (max 0 (γ * s ^ 2 / t - normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))))))
    (hcen.const_mul (4 * M ^ 2 / t ^ 2)) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine hmono.trans ?_
  have hNn : N * γ / n = γ * (N / n) := by ring
  rw [hNn] at hV
  have h5 : 4 * M ^ 2 / t ^ 2 * ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) ≤
      4 * (γ * (1 + N22) ^ 2) / t ^ 2 * (γ * ρ ^ 2) := by
    have h6 : ∫ x, (σ x - M) ^ 2 ∂stdGauss (Fin n) ≤ γ * ρ ^ 2 :=
      hV.trans (mul_le_mul_of_nonneg_left hρ hγ.le)
    have h7 : 4 * M ^ 2 / t ^ 2 ≤ 4 * (γ * (1 + N22) ^ 2) / t ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
    exact mul_le_mul h7 h6 hvar0 (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The frame bound at one retained value by the split of second order, every number free.**
`n·L_A ≤ (N + ξ)/s² + 2κ(1 + N22)ρ/(sd²·s²) + (16.09·a)⁴/(n³(s − sd)⁸)`. -/
theorem frameA_point2 (hn : 10 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) {N a eb xi e1 e2 N22 q sd s r η κ ρ cf : ℝ} (hN0 : 0 ≤ N)
    (hb : 0 < normSq ((1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (hXi8 : Xi8 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤
        xi * (2 / (n : ℝ)) / n)
    (hN2 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / (n : ℝ) ≤ e2 ^ 2)
    (hq : 2 * N / n ≤ q)
    (hsd : 0 < sd) (hs : sd < s) (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - q)
    (ha0 : 0 ≤ a) (hr : 0 ≤ r) (hr2 : 4 * a ^ 2 + N ^ 2 ≤ r ^ 2) (hη : 0 < η) (hκ0 : 0 < κ)
    (hκ : (1 + η) ^ 3 * (2 * a + r) ^ 2 + (1 + 1 / η) ^ 3 * xi ^ 2 ≤ κ ^ 2)
    (hρ0 : 0 < ρ) (hρ : N / n ≤ ρ ^ 2)
    (hsum : (N + xi) / s ^ 2 + 2 * κ * (1 + N22) * ρ / (sd ^ 2 * s ^ 2) +
      (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) ≤ cf)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) < 2 / (mA n : ℝ) := by positivity
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs0 : 0 < s := lt_trans hsd hs
  have hgap : 0 < s - sd := by linarith
  have hN2nn := BstLean.Part153.N2_nonneg 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)
  have hN22nn : 0 ≤ N22 := hN2nn.trans hN2
  have hs2' : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n := by linarith
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ j, w j ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← hS]
  by_cases hSz : S = 0
  · have hw : w = 0 := BstLean.Part134.eq_zero_of_normSq (by rw [← hSz, hS]; rfl)
    simp [hw, hSz]
  have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hSz)
  have hcov := cov_at_of_XiS hn6 D c hτ hXi
  have hcen : CENTRE_at D c xi := by
    unfold CENTRE_at
    rw [hD c, muStand_eq]
    exact hxi
  have hT1 := Cr_at hn1 D c hN0 hcov hcen w
  rw [← hS] at hT1
  rw [← hD c] at hb heb hxi
  obtain ⟨b, hbd⟩ : ∃ b : Fin (mA n) → ℝ, b = D.bA c.1 c.2.1.1 := ⟨_, rfl⟩
  rw [← hbd] at hb heb hxi hT1 ⊢
  have hint : Integrable (fun ξ => (∑ j, res b (hStand D c ξ) j * w j) ^ 2) (stdGauss (Fin n)) := by
    simp_rw [res_symm b _ w]
    exact hStand_int2 hn1 D c (res b w)
  obtain ⟨hint4, hP4⟩ := resid_fourth hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ b w hXi hXi4 hxi ha0 hr
    hr2 hη hκ0.le hκ
  rw [← hS] at hP4
  have hQ2 := gap_sq hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi heb hxi hN2 he1 he1' he2 he2' hs2'
    hρ
  have hm8 := mass_bound8 hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb hXi hXi4 hXi8 heb hxi hN2 he1 he1'
    he2 he2' hsd.le hs hs2'
  -- the cutoffs
  obtain ⟨ac, hac⟩ : ∃ ac : ℝ, ac = 2 / (n : ℝ) * sd ^ 2 / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Ac, hAc⟩ : ∃ Ac : ℝ, Ac = 2 / (n : ℝ) * s ^ 2 / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hac0 : 0 < ac := by rw [hac]; positivity
  have hAc0 : 0 < Ac := by rw [hAc]; positivity
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = κ * (2 / (n : ℝ) / n) * S / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQd⟩ : ∃ Q : ℝ, Q = 2 * (2 / (n : ℝ)) * (1 + N22) * ρ / (2 / (mA n : ℝ)) := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hPd]; positivity
  have hQ0 : 0 < Q := by rw [hQd]; positivity
  rw [← hPd] at hP4
  rw [← hAc, ← hQd] at hQ2
  have h1 := frame_split2 (stdGauss (Fin n)) (measurable_hStand D c) b w hac0 hAc0 hP0 hQ0 hint
    hint4 hP4 hQ2
  rw [← hS] at h1
  have hset : {ξ : Fin n → ℝ | normSq (res b (hStand D c ξ)) < ac} =
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 c.2.1.1.1 c.2.1.1.2
        (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    change normSq (res b (hStand D c ξ)) < ac ↔
      2 / (mA n : ℝ) * normSq (res b (hStand D c ξ)) < 2 / (n : ℝ) * sd ^ 2
    rw [hac, lt_div_iff₀ (by positivity), mul_comm]
  rw [hset] at h1
  obtain ⟨Pm, hPm⟩ : ∃ Pm : ℝ, Pm = (stdGauss (Fin n)).real
      {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 c.2.1.1.1 c.2.1.1.2
        (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := ⟨_, rfl⟩
  rw [← hPm] at h1 hm8
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ ξ, (∑ j, res b (hStand D c ξ) j * w j) ^ 2
      ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hI] at h1 hT1
  obtain ⟨M8, hM8⟩ : ∃ M8 : ℝ, M8 = (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) :=
    ⟨_, rfl⟩
  rw [← hM8] at hm8 hsum
  -- the three terms
  have t1 : 1 / Ac * I ≤ (N + xi) / s ^ 2 / n * S := by
    have e : 1 / Ac * I = (2 / (mA n : ℝ) * I) / (2 / (n : ℝ) * s ^ 2) := by
      rw [hAc]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : (N + xi) / s ^ 2 / n * S * (2 / (n : ℝ) * s ^ 2) =
        (N + xi) * (2 / (n : ℝ)) / n * S := by field_simp
    rw [e2]; exact hT1
  have t2 : P * Q / (ac * Ac) = 2 * κ * (1 + N22) * ρ / (sd ^ 2 * s ^ 2) / n * S := by
    rw [hPd, hQd, hac, hAc]
    field_simp
  have t3 : Pm * S ≤ M8 / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0
    rw [le_div_iff₀ hnR]; linarith
  have t4 : ((N + xi) / s ^ 2 / n + 2 * κ * (1 + N22) * ρ / (sd ^ 2 * s ^ 2) / n + M8 / n) * S ≤
      cf / n * S := by
    refine mul_le_mul_of_nonneg_right ?_ hS0
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right hsum hnR.le
  rw [t2] at h1
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms frame_split2
open BstLean.Part160 in
#print axioms resid_fourth
open BstLean.Part160 in
#print axioms gap_sq
open BstLean.Part160 in
#print axioms frameA_point2
