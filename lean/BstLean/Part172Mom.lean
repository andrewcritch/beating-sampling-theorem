import BstLean.Part171All

/-!
# Part 172 (file `Mom`): moment algebra for the statistics of `wT = S²`

No proof is left open; no `native_decide` or `axiom` is used.

On a probability space, for a bounded measurable `S` with mean `μ₀` and `D = S − μ₀`:
* `mo_sq_int_le`: `(∫ f)² ≤ ∫ f²`; `mo_pow8_int_le`: `(∫ f)⁸ ≤ ∫ f⁸`.
* `mo_lyap`: `∫ f⁸ ≤ K⁸ ⇒ ∫ f⁴ ≤ K⁴, ∫ f² ≤ K², ∫ f ≤ K` for `f ≥ 0`.
* **`mo_var_sq`**: `∫ (S² − ∫ S²)² ≤ (x + 2|μ₀| y)²` if `∫ D⁴ ≤ x²`, `∫ D² ≤ y²`.
* **`mo_eight_sq`**: `∫ (S² − ∫ S²)⁸ ≤ (α + β + γ)⁸` if `∫ D¹⁶ ≤ α⁸`, `(2|μ₀|)⁸ ∫ D⁸ ≤ β⁸`,
  `∫ D² ≤ γ`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma mo_bdd_int {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

lemma mo_bdd_pow {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (k : ℕ) :
    Integrable (fun ω => f ω ^ k) μ :=
  mo_bdd_int (hf.pow_const k) (C := C ^ k) fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) k

lemma mo_quad {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (a b c : ℝ) :
    ∫ ω, (a * f ω ^ 2 + b * f ω + c) ∂μ = a * ∫ ω, f ω ^ 2 ∂μ + b * ∫ ω, f ω ∂μ + c := by
  have i1 := mo_bdd_int (μ := μ) hf hC
  have i2 := mo_bdd_pow (μ := μ) hf hC 2
  have ja : Integrable (fun ω => a * f ω ^ 2) μ := i2.const_mul a
  have jb : Integrable (fun ω => b * f ω) μ := i1.const_mul b
  have jab : Integrable (fun ω => a * f ω ^ 2 + b * f ω) μ := ja.add jb
  rw [integral_add jab (integrable_const c), integral_add ja jb, integral_const_mul,
    integral_const_mul]
  simp

/-- `(∫ f)² ≤ ∫ f²` for a bounded measurable `f`. -/
lemma mo_sq_int_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  have i1 := mo_bdd_int (μ := μ) hf hC
  have i2 := mo_bdd_pow (μ := μ) hf hC 2
  set m := ∫ ω, f ω ∂μ
  have h0 : 0 ≤ ∫ ω, (f ω - m) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have e : ∫ ω, (f ω - m) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - m ^ 2 := by
    have : (fun ω => (f ω - m) ^ 2) = fun ω => 1 * f ω ^ 2 + (-2 * m) * f ω + m ^ 2 := by
      funext ω; ring
    rw [this, mo_quad hf hC]
    ring
  linarith

/-- `(∫ f)⁸ ≤ ∫ f⁸`. -/
lemma mo_pow8_int_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    (∫ ω, f ω ∂μ) ^ 8 ≤ ∫ ω, f ω ^ 8 ∂μ := by
  have h1 := mo_sq_int_le (μ := μ) hf hC
  have h2 := mo_sq_int_le (μ := μ) (hf.pow_const 2) (C := C ^ 2) (fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2)
  have h4 := mo_sq_int_le (μ := μ) (hf.pow_const 4) (C := C ^ 4) (fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 4)
  have e2 : (fun ω => (f ω ^ 2) ^ 2) = fun ω => f ω ^ 4 := by funext ω; ring
  have e4 : (fun ω => (f ω ^ 4) ^ 2) = fun ω => f ω ^ 8 := by funext ω; ring
  rw [e2] at h2; rw [e4] at h4
  have p1 : (∫ ω, f ω ∂μ) ^ 8 ≤ (∫ ω, f ω ^ 2 ∂μ) ^ 4 := by
    calc (∫ ω, f ω ∂μ) ^ 8 = ((∫ ω, f ω ∂μ) ^ 2) ^ 4 := by ring
      _ ≤ (∫ ω, f ω ^ 2 ∂μ) ^ 4 := pow_le_pow_left₀ (sq_nonneg _) h1 4
  have p2 : (∫ ω, f ω ^ 2 ∂μ) ^ 4 ≤ (∫ ω, f ω ^ 4 ∂μ) ^ 2 := by
    calc (∫ ω, f ω ^ 2 ∂μ) ^ 4 = ((∫ ω, f ω ^ 2 ∂μ) ^ 2) ^ 2 := by ring
      _ ≤ (∫ ω, f ω ^ 4 ∂μ) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
  linarith

/-- AM–GM step: `∫ f^{2k} ≤ K^{2k} ⇒ ∫ f^k ≤ K^k` for `f ≥ 0`, `K > 0`. -/
lemma mo_half {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (k : ℕ) {K : ℝ}
    (hK : 0 < K) (h : ∫ ω, f ω ^ (2 * k) ∂μ ≤ K ^ (2 * k)) :
    ∫ ω, f ω ^ k ∂μ ≤ K ^ k := by
  have hKk : 0 < K ^ k := pow_pos hK k
  have hpt : ∀ ω, f ω ^ k ≤ (f ω ^ (2 * k) / K ^ k + K ^ k) / 2 := by
    intro ω
    have e : f ω ^ (2 * k) = (f ω ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have : (f ω ^ k) ^ 2 / K ^ k + K ^ k - 2 * f ω ^ k = (f ω ^ k - K ^ k) ^ 2 / K ^ k := by
      field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (f ω ^ k - K ^ k)) hKk.le]
  have i1 := mo_bdd_pow (μ := μ) hf hC k
  have i2 := mo_bdd_pow (μ := μ) hf hC (2 * k)
  calc ∫ ω, f ω ^ k ∂μ ≤ ∫ ω, (f ω ^ (2 * k) / K ^ k + K ^ k) / 2 ∂μ :=
        integral_mono i1 (((i2.div_const _).add (integrable_const _)).div_const _) hpt
    _ = ((∫ ω, f ω ^ (2 * k) ∂μ) / K ^ k + K ^ k) / 2 := by
        rw [integral_div, integral_add (i2.div_const _) (integrable_const _), integral_div]
        simp
    _ ≤ (K ^ (2 * k) / K ^ k + K ^ k) / 2 := by gcongr
    _ = K ^ k := by rw [pow_mul', sq]; field_simp; ring

/-- Lyapunov from the eighth moment. -/
lemma mo_lyap {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) {K : ℝ}
    (hK : 0 < K) (h : ∫ ω, f ω ^ 8 ∂μ ≤ K ^ 8) :
    ∫ ω, f ω ^ 4 ∂μ ≤ K ^ 4 ∧ ∫ ω, f ω ^ 2 ∂μ ≤ K ^ 2 ∧ ∫ ω, f ω ∂μ ≤ K := by
  have h4 := mo_half (μ := μ) hf hC 4 hK h
  have h2 := mo_half (μ := μ) hf hC 2 hK h4
  have h1 := mo_half (μ := μ) hf hC 1 hK (by simpa using h2)
  exact ⟨h4, h2, by simpa using h1⟩

/-- `∫ (f − ∫ f)² ≤ ∫ (f − c)²`. -/
lemma mo_var_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (c : ℝ) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂μ) ^ 2 ∂μ ≤ ∫ ω, (f ω - c) ^ 2 ∂μ := by
  have i1 := mo_bdd_int (μ := μ) hf hC
  have i2 := mo_bdd_pow (μ := μ) hf hC 2
  set m := ∫ ω, f ω ∂μ
  have ex : ∀ d : ℝ, ∫ ω, (f ω - d) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - 2 * d * m + d ^ 2 := by
    intro d
    have : (fun ω => (f ω - d) ^ 2) = fun ω => 1 * f ω ^ 2 + (-2 * d) * f ω + d ^ 2 := by
      funext ω; ring
    rw [this, mo_quad hf hC]
    ring
  rw [ex, ex]
  nlinarith [sq_nonneg (m - c)]

/-- **The variance of `S²`.** -/
theorem mo_var_sq {S : Ω → ℝ} (hS : Measurable S) {C : ℝ} (hC : ∀ ω, |S ω| ≤ C) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h4 : ∫ ω, (S ω - ∫ ω', S ω' ∂μ) ^ 4 ∂μ ≤ x ^ 2)
    (h2 : ∫ ω, (S ω - ∫ ω', S ω' ∂μ) ^ 2 ∂μ ≤ y ^ 2) :
    ∫ ω, (S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ) ^ 2 ∂μ ≤ (x + 2 * |∫ ω, S ω ∂μ| * y) ^ 2 := by
  set m := ∫ ω, S ω ∂μ with hm
  have hS2 : ∀ ω, |S ω ^ 2| ≤ C ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2
  have hv := mo_var_le (μ := μ) (hS.pow_const 2) hS2 (m ^ 2)
  refine hv.trans ?_
  set D : Ω → ℝ := fun ω => S ω - m with hD
  have hDm : Measurable D := hS.sub_const _
  have hDC : ∀ ω, |D ω| ≤ C + |m| := fun ω => (abs_sub _ _).trans (by linarith [hC ω])
  have e : (fun ω => (S ω ^ 2 - m ^ 2) ^ 2) =
      fun ω => D ω ^ 4 + 4 * m * (D ω ^ 2 * D ω) + 4 * m ^ 2 * D ω ^ 2 := by
    funext ω; simp only [hD]; ring
  rw [e]
  have i4 := mo_bdd_pow (μ := μ) hDm hDC 4
  have i2 := mo_bdd_pow (μ := μ) hDm hDC 2
  have i3 : Integrable (fun ω => D ω ^ 2 * D ω) μ := by
    have := mo_bdd_pow (μ := μ) hDm hDC 3
    refine this.congr (Filter.Eventually.of_forall fun ω => by ring)
  have eI : ∫ ω, (D ω ^ 4 + 4 * m * (D ω ^ 2 * D ω) + 4 * m ^ 2 * D ω ^ 2) ∂μ =
      ∫ ω, D ω ^ 4 ∂μ + 4 * m * ∫ ω, D ω ^ 2 * D ω ∂μ + 4 * m ^ 2 * ∫ ω, D ω ^ 2 ∂μ := by
    have j3 : Integrable (fun ω => 4 * m * (D ω ^ 2 * D ω)) μ := i3.const_mul _
    have j2 : Integrable (fun ω => 4 * m ^ 2 * D ω ^ 2) μ := i2.const_mul _
    have j43 : Integrable (fun ω => D ω ^ 4 + 4 * m * (D ω ^ 2 * D ω)) μ := i4.add j3
    rw [integral_add j43 j2, integral_add i4 j3, integral_const_mul, integral_const_mul]
  rw [eI]
  -- the cubic term
  have hcub : |∫ ω, D ω ^ 2 * D ω ∂μ| ≤ x * y := by
    refine (abs_integral_le_integral_abs).trans ?_
    rcases hx.lt_or_eq with hxp | hx0
    · rcases hy.lt_or_eq with hyp | hy0
      · -- AM–GM with t = y/x
        have hpt : ∀ ω, |D ω ^ 2 * D ω| ≤ (y / x * D ω ^ 4 + x / y * D ω ^ 2) / 2 := by
          intro ω
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          have ha := abs_nonneg (D ω)
          have e2 : D ω ^ 2 = |D ω| ^ 2 := (sq_abs _).symm
          have e4 : D ω ^ 4 = (|D ω| ^ 2) ^ 2 := by rw [← e2]; ring
          rw [e4, e2]
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
          have : y / x * (|D ω| ^ 2) ^ 2 + x / y * |D ω| ^ 2 - |D ω| ^ 2 * |D ω| * 2 =
              |D ω| ^ 2 * (y * |D ω| - x) ^ 2 / (x * y) := by
            field_simp; ring
          nlinarith [div_nonneg (mul_nonneg (sq_nonneg |D ω|) (sq_nonneg (y * |D ω| - x)))
            (mul_pos hxp hyp).le]
        calc ∫ ω, |D ω ^ 2 * D ω| ∂μ ≤ ∫ ω, (y / x * D ω ^ 4 + x / y * D ω ^ 2) / 2 ∂μ :=
              integral_mono i3.abs (((i4.const_mul _).add (i2.const_mul _)).div_const _) hpt
          _ = (y / x * ∫ ω, D ω ^ 4 ∂μ + x / y * ∫ ω, D ω ^ 2 ∂μ) / 2 := by
              rw [integral_div, integral_add (i4.const_mul _) (i2.const_mul _),
                integral_const_mul, integral_const_mul]
          _ ≤ (y / x * x ^ 2 + x / y * y ^ 2) / 2 := by gcongr
          _ = x * y := by field_simp; ring
      · -- y = 0: D = 0 a.e.
        have h0 : ∫ ω, D ω ^ 2 ∂μ = 0 := le_antisymm (by rw [← hy0] at h2; simpa using h2)
          (integral_nonneg fun _ => sq_nonneg _)
        have hae : (fun ω => D ω ^ 2) =ᵐ[μ] 0 :=
          (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) i2).mp h0
        have : ∫ ω, |D ω ^ 2 * D ω| ∂μ = 0 := by
          rw [integral_eq_zero_of_ae]
          filter_upwards [hae] with ω hω
          simp only [Pi.zero_apply] at hω ⊢
          rw [hω, zero_mul, abs_zero]
        rw [this, ← hy0, mul_zero]
    · have h0 : ∫ ω, D ω ^ 4 ∂μ = 0 := le_antisymm (by rw [← hx0] at h4; simpa using h4)
        (integral_nonneg fun _ => by positivity)
      have hae : (fun ω => D ω ^ 4) =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) i4).mp h0
      have : ∫ ω, |D ω ^ 2 * D ω| ∂μ = 0 := by
        rw [integral_eq_zero_of_ae]
        filter_upwards [hae] with ω hω
        simp only [Pi.zero_apply] at hω ⊢
        have : D ω = 0 := by
          have : D ω ^ 4 = 0 := hω
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        rw [this]; simp
      rw [this, ← hx0, zero_mul]
  have h4' : ∫ ω, D ω ^ 4 ∂μ ≤ x ^ 2 := h4
  have h2' : ∫ ω, D ω ^ 2 ∂μ ≤ y ^ 2 := h2
  have hc' : 4 * m * ∫ ω, D ω ^ 2 * D ω ∂μ ≤ 4 * |m| * (x * y) := by
    have := abs_le.mp hcub
    have hma := abs_nonneg m
    rcases le_total 0 m with hm0 | hm0
    · rw [abs_of_nonneg hm0]; nlinarith
    · rw [abs_of_nonpos hm0]; nlinarith
  have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  nlinarith [mul_le_mul_of_nonneg_left h2' (by positivity : (0:ℝ) ≤ 4 * m ^ 2)]

/-- **The eighth moment of `S² − E S²`.** -/
theorem mo_eight_sq {S : Ω → ℝ} (hS : Measurable S) {C : ℝ} (hC : ∀ ω, |S ω| ≤ C)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (h16 : ∫ ω, (S ω - ∫ ω', S ω' ∂μ) ^ 16 ∂μ ≤ α ^ 8)
    (h8 : (2 * |∫ ω, S ω ∂μ|) ^ 8 * ∫ ω, (S ω - ∫ ω', S ω' ∂μ) ^ 8 ∂μ ≤ β ^ 8)
    (h2 : ∫ ω, (S ω - ∫ ω', S ω' ∂μ) ^ 2 ∂μ ≤ γ) :
    ∫ ω, (S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ) ^ 8 ∂μ ≤ (α + β + γ) ^ 8 := by
  set m := ∫ ω, S ω ∂μ with hm
  set D : Ω → ℝ := fun ω => S ω - m with hD
  have hDm : Measurable D := hS.sub_const _
  have hDC : ∀ ω, |D ω| ≤ C + |m| := fun ω => (abs_sub _ _).trans (by linarith [hC ω])
  have i1 := mo_bdd_int (μ := μ) hS hC
  have i2S := mo_bdd_pow (μ := μ) hS hC 2
  set V := ∫ ω, D ω ^ 2 ∂μ with hV
  have hV0 : 0 ≤ V := integral_nonneg fun _ => sq_nonneg _
  -- E S² = m² + V
  have hES2 : ∫ ω, S ω ^ 2 ∂μ = m ^ 2 + V := by
    have i1' := mo_bdd_int (μ := μ) hS hC
    have : (fun ω => D ω ^ 2) = fun ω => 1 * S ω ^ 2 + (-2 * m) * S ω + m ^ 2 := by
      funext ω; simp only [hD]; ring
    rw [hV, this, mo_quad hS hC]
    ring
  have hpt : ∀ ω, |S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ| ≤ D ω ^ 2 + 2 * |m| * |D ω| + V := by
    intro ω
    rw [hES2]
    have e : S ω ^ 2 - (m ^ 2 + V) = D ω ^ 2 + 2 * m * D ω - V := by simp only [hD]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hV0]
    gcongr
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hpt8 : ∀ ω, (S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ) ^ 8 ≤
      (α + β + γ) ^ 7 * ((D ω ^ 2) ^ 8 / α ^ 7 + (2 * |m| * |D ω|) ^ 8 / β ^ 7 + V ^ 8 / γ ^ 7) := by
    intro ω
    have h := BstLean.Part171.pow8_three (sq_nonneg (D ω)) (by positivity : 0 ≤ 2 * |m| * |D ω|)
      hV0 hα hβ hγ
    calc (S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ) ^ 8 = |S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ| ^ 8 := by
          rw [Even.pow_abs (by decide)]
      _ ≤ (D ω ^ 2 + 2 * |m| * |D ω| + V) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) (hpt ω) 8
      _ ≤ _ := h
  have i16 := mo_bdd_pow (μ := μ) hDm hDC 16
  have i8 := mo_bdd_pow (μ := μ) hDm hDC 8
  have iL : Integrable (fun ω => (S ω ^ 2 - ∫ ω', S ω' ^ 2 ∂μ) ^ 8) μ :=
    mo_bdd_pow (μ := μ) ((hS.pow_const 2).sub_const _) (C := C ^ 2 + |∫ ω', S ω' ^ 2 ∂μ|)
      (fun ω => (abs_sub _ _).trans (by
        rw [abs_pow]; gcongr; exact hC ω)) 8
  have e1 : (fun ω => (D ω ^ 2) ^ 8 / α ^ 7) = fun ω => D ω ^ 16 / α ^ 7 := by
    funext ω; ring
  have e2 : (fun ω => (2 * |m| * |D ω|) ^ 8 / β ^ 7) =
      fun ω => (2 * |m|) ^ 8 / β ^ 7 * D ω ^ 8 := by
    funext ω; rw [mul_pow, Even.pow_abs (by decide)]; ring
  have iR : Integrable (fun ω => (α + β + γ) ^ 7 * ((D ω ^ 2) ^ 8 / α ^ 7 +
      (2 * |m| * |D ω|) ^ 8 / β ^ 7 + V ^ 8 / γ ^ 7)) μ := by
    refine Integrable.const_mul ?_ _
    refine (Integrable.add ?_ ?_).add (integrable_const _)
    · rw [e1]; exact i16.div_const _
    · rw [e2]; exact i8.const_mul _
  refine (integral_mono iL iR hpt8).trans ?_
  have j1 : Integrable (fun ω => (D ω ^ 2) ^ 8 / α ^ 7) μ := by rw [e1]; exact i16.div_const _
  have j2 : Integrable (fun ω => (2 * |m| * |D ω|) ^ 8 / β ^ 7) μ := by
    rw [e2]; exact i8.const_mul _
  have j12 : Integrable (fun ω => (D ω ^ 2) ^ 8 / α ^ 7 + (2 * |m| * |D ω|) ^ 8 / β ^ 7) μ :=
    j1.add j2
  have eI : ∫ ω, (α + β + γ) ^ 7 * ((D ω ^ 2) ^ 8 / α ^ 7 + (2 * |m| * |D ω|) ^ 8 / β ^ 7 +
      V ^ 8 / γ ^ 7) ∂μ = (α + β + γ) ^ 7 * ((∫ ω, D ω ^ 16 ∂μ) / α ^ 7 +
      (2 * |m|) ^ 8 / β ^ 7 * ∫ ω, D ω ^ 8 ∂μ + V ^ 8 / γ ^ 7) := by
    rw [integral_const_mul, integral_add j12 (integrable_const _), integral_add j1 j2, e1, e2,
      integral_div, integral_const_mul]
    simp
  rw [eI]
  have hb1 : (∫ ω, D ω ^ 16 ∂μ) / α ^ 7 ≤ α := by
    rw [div_le_iff₀ (by positivity)]; calc _ ≤ α ^ 8 := h16
      _ = α * α ^ 7 := by ring
  have hb2 : (2 * |m|) ^ 8 / β ^ 7 * ∫ ω, D ω ^ 8 ∂μ ≤ β := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; calc _ ≤ β ^ 8 := h8
      _ = β * β ^ 7 := by ring
  have hb3 : V ^ 8 / γ ^ 7 ≤ γ := by
    rw [div_le_iff₀ (by positivity)]
    calc V ^ 8 ≤ γ ^ 8 := pow_le_pow_left₀ hV0 h2 8
      _ = γ * γ ^ 7 := by ring
  calc (α + β + γ) ^ 7 * ((∫ ω, D ω ^ 16 ∂μ) / α ^ 7 + (2 * |m|) ^ 8 / β ^ 7 * ∫ ω, D ω ^ 8 ∂μ +
        V ^ 8 / γ ^ 7) ≤ (α + β + γ) ^ 7 * (α + β + γ) := by gcongr
    _ = (α + β + γ) ^ 8 := by ring

end BstLean.Part172
