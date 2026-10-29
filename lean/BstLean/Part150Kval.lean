import BstLean.Part150Kern

/-!
# Part 150, item 2, tools: the Gaussian side of the two kernels, and `K1 = π/2`, `K2 = π/4`

* `gauss_ker1`: `K1·E|x + Z| = ∫_0^∞ (1 − e^{−t²/2}cos(tx))/t² dt`, with integrability.
* `gauss_ker2`: `K2·E[(x + Z)|x + Z|] = ∫_0^∞ (tx − e^{−t²/2}sin(tx))/t³ dt`, with integrability.
* `integral_one_sub_exp`: `∫_0^∞ (1 − e^{−t²/2})/t² dt = √(π/2)`.
* `K1_eq : K1 = π/2` (from `gauss_ker1` at `x = 0` and `E|Z| = √(2/π)`);
  `K2_eq : K2 = π/4` (integration by parts).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part130 BstLean.Part137 BstLean.Part141

lemma integrable_shift_sq (x : ℝ) : Integrable (fun z : ℝ => (x + z) ^ 2) (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have h := ((integrable_const (x ^ 2)).add (h1.const_mul (2 * x))).add (integrable_pow_gauss 2)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]; ring

lemma integrable_shift_pow4 (x : ℝ) : Integrable (fun z : ℝ => (x + z) ^ 4) (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  have h := ((((integrable_const (x ^ 4)).add (h1.const_mul (4 * x ^ 3))).add
    ((integrable_pow_gauss 2).const_mul (6 * x ^ 2))).add
    ((integrable_pow_gauss 3).const_mul (4 * x))).add (integrable_pow_gauss 4)
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]; ring

lemma integrable_abs_shift (x : ℝ) : Integrable (fun z : ℝ => |x + z|) (gaussianReal 0 1) := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
  exact ((integrable_const x).add h1).abs

lemma integrable_shift_mul_abs (x : ℝ) :
    Integrable (fun z : ℝ => (x + z) * |x + z|) (gaussianReal 0 1) := by
  refine (integrable_shift_sq x).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, ← sq, sq_abs]

/-- The Gaussian side of the first kernel. -/
theorem gauss_ker1 (x : ℝ) :
    IntegrableOn (fun t : ℝ => (1 - rexp (-(t ^ 2 / 2)) * Real.cos (t * x)) / t ^ 2) (Ioi 0) ∧
    K1 * ∫ z, |x + z| ∂gaussianReal 0 1 =
      ∫ t in Ioi 0, (1 - rexp (-(t ^ 2 / 2)) * Real.cos (t * x)) / t ^ 2 := by
  have hk : Measurable (fun p : ℝ × ℝ => ker1 p.2 (x + p.1)) := by unfold ker1; fun_prop
  have hint := prod_integrable_of_bounds (k := fun t z => ker1 t (x + z)) hk
    (B1 := fun z => (x + z) ^ 2 / 2) (B2 := fun _ => 2) ((integrable_shift_sq x).div_const 2)
    (integrable_const _)
    (fun t z _ => by rw [abs_of_nonneg (ker1_nonneg _ _)]; exact ker1_le_sq _ _)
    (fun t z ht => by
      rw [abs_of_nonneg (ker1_nonneg _ _)]; exact ker1_le_inv (lt_trans zero_lt_one ht) _)
  have hsw := integral_integral_swap (f := fun z t => ker1 t (x + z)) hint
  have hinner : ∀ t : ℝ, ∫ z, ker1 t (x + z) ∂gaussianReal 0 1 =
      (1 - rexp (-(t ^ 2 / 2)) * Real.cos (t * x)) / t ^ 2 := by
    intro t
    unfold ker1
    have hc := integrable_cos_gauss t (t * x)
    have e : (fun z : ℝ => Real.cos (t * z + t * x)) = fun z => Real.cos (t * (x + z)) := by
      funext z; congr 1; ring
    rw [e] at hc
    rw [integral_div, integral_sub (integrable_const _) hc, gauss_cos_shift]
    simp
  constructor
  · have h := hint.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    exact hinner t
  · calc K1 * ∫ z, |x + z| ∂gaussianReal 0 1
        = ∫ z, |x + z| * K1 ∂gaussianReal 0 1 := by rw [integral_mul_const]; ring
      _ = ∫ z, (∫ t in Ioi 0, ker1 t (x + z)) ∂gaussianReal 0 1 := by simp_rw [ker1_integral]
      _ = ∫ t in Ioi 0, (∫ z, ker1 t (x + z) ∂gaussianReal 0 1) := hsw
      _ = _ := by simp_rw [hinner]

/-- The Gaussian side of the second kernel. -/
theorem gauss_ker2 (x : ℝ) :
    IntegrableOn (fun t : ℝ => (t * x - rexp (-(t ^ 2 / 2)) * Real.sin (t * x)) / t ^ 3) (Ioi 0) ∧
    K2 * ∫ z, (x + z) * |x + z| ∂gaussianReal 0 1 =
      ∫ t in Ioi 0, (t * x - rexp (-(t ^ 2 / 2)) * Real.sin (t * x)) / t ^ 3 := by
  have hk : Measurable (fun p : ℝ × ℝ => ker2 p.2 (x + p.1)) := by unfold ker2; fun_prop
  have hint := prod_integrable_of_bounds (k := fun t z => ker2 t (x + z)) hk
    (B1 := fun z => (1 + (x + z) ^ 4) / 6) (B2 := fun z => 2 + (x + z) ^ 2)
    (((integrable_const 1).add (integrable_shift_pow4 x)).div_const 6)
    ((integrable_const 2).add (integrable_shift_sq x))
    (fun t z _ => by
      refine (ker2_abs_le_cube _ _).trans ?_
      have h0 := abs_nonneg (x + z)
      have h4 : (x + z) ^ 4 = |x + z| ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      rw [h4]
      nlinarith [sq_nonneg (|x + z| ^ 2 - |x + z|), sq_nonneg (|x + z| - 1), sq_nonneg (|x + z|),
        mul_nonneg h0 (sq_nonneg (|x + z| - 1))])
    (fun t z ht => by
      refine (ker2_abs_le_inv ht _).trans ?_
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      exact div_le_div_of_nonneg_right
        (by nlinarith [sq_nonneg (|x + z| - 1), sq_abs (x + z)]) (by positivity))
  have hsw := integral_integral_swap (f := fun z t => ker2 t (x + z)) hint
  have hinner : ∀ t : ℝ, ∫ z, ker2 t (x + z) ∂gaussianReal 0 1 =
      (t * x - rexp (-(t ^ 2 / 2)) * Real.sin (t * x)) / t ^ 3 := by
    intro t
    unfold ker2
    have hs := integrable_sin_gauss t (t * x)
    have e : (fun z : ℝ => Real.sin (t * z + t * x)) = fun z => Real.sin (t * (x + z)) := by
      funext z; congr 1; ring
    rw [e] at hs
    have h1 : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := by simpa using integrable_pow_gauss 1
    have hl : Integrable (fun z : ℝ => t * (x + z)) (gaussianReal 0 1) :=
      ((integrable_const x).add h1).const_mul t
    have hlv : ∫ z, t * (x + z) ∂gaussianReal 0 1 = t * x := by
      rw [integral_const_mul, integral_add (integrable_const x) h1, integral_id_gaussianReal]
      simp
    rw [integral_div, integral_sub hl hs, gauss_sin_shift, hlv]
  constructor
  · have h := hint.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    exact hinner t
  · calc K2 * ∫ z, (x + z) * |x + z| ∂gaussianReal 0 1
        = ∫ z, (x + z) * |x + z| * K2 ∂gaussianReal 0 1 := by rw [integral_mul_const]; ring
      _ = ∫ z, (∫ t in Ioi 0, ker2 t (x + z)) ∂gaussianReal 0 1 := by simp_rw [ker2_integral]
      _ = ∫ t in Ioi 0, (∫ z, ker2 t (x + z) ∂gaussianReal 0 1) := hsw
      _ = _ := by simp_rw [hinner]

lemma one_sub_exp_bounds (t : ℝ) :
    0 ≤ 1 - rexp (-(t ^ 2 / 2)) ∧ 1 - rexp (-(t ^ 2 / 2)) ≤ t ^ 2 / 2 ∧
      1 - rexp (-(t ^ 2 / 2)) ≤ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have := Real.exp_le_one_iff.mpr (show -(t ^ 2 / 2) ≤ 0 by nlinarith [sq_nonneg t]); linarith
  · have := Real.add_one_le_exp (-(t ^ 2 / 2)); linarith
  · have := Real.exp_pos (-(t ^ 2 / 2)); linarith

/-- `∫_0^∞ (1 − e^{−t²/2})/t² dt = √(π/2)`. -/
theorem integral_one_sub_exp :
    ∫ t in Ioi (0 : ℝ), (1 - rexp (-(t ^ 2 / 2))) / t ^ 2 = √(π / 2) := by
  set F : ℝ → ℝ := fun t => -(1 - rexp (-(t ^ 2 / 2))) / t with hF
  set f' : ℝ → ℝ := fun t => (1 - rexp (-(t ^ 2 / 2))) / t ^ 2 - rexp (-(t ^ 2 / 2)) with hf'
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt F (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : HasDerivAt (fun t : ℝ => rexp (-(t ^ 2 / 2))) (-x * rexp (-(x ^ 2 / 2))) x := by
      have h0 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-x) x := by
        have := ((hasDerivAt_pow 2 x).div_const 2).neg
        convert this using 1; ring
      have := h0.exp
      convert this using 1; ring
    have h2 : HasDerivAt (fun t : ℝ => -(1 - rexp (-(t ^ 2 / 2)))) (-x * rexp (-(x ^ 2 / 2))) x := by
      have := ((hasDerivAt_const x (1 : ℝ)).sub h1).neg
      convert this using 1; ring
    have h3 := h2.div (hasDerivAt_id x) hx0
    have e : f' x = (-x * rexp (-(x ^ 2 / 2)) * id x - -(1 - rexp (-(x ^ 2 / 2))) * 1) / id x ^ 2 := by
      simp only [hf', id]; field_simp; ring
    rw [e]
    exact h3
  have hm1 : Measurable (fun t : ℝ => (1 - rexp (-(t ^ 2 / 2))) / t ^ 2) := by fun_prop
  have hi1 : IntegrableOn (fun t : ℝ => (1 - rexp (-(t ^ 2 / 2))) / t ^ 2) (Ioi 0) := by
    refine integrableOn_Ioi_of_bounds (C := 1 / 2) (D := 1) hm1 ?_ ?_
    · intro t ht _
      obtain ⟨h0, h1, _⟩ := one_sub_exp_bounds t
      rw [abs_of_nonneg (div_nonneg h0 (sq_nonneg t)), div_le_iff₀ (by positivity)]
      linarith
    · intro t ht
      obtain ⟨h0, _, h1⟩ := one_sub_exp_bounds t
      rw [abs_of_nonneg (div_nonneg h0 (sq_nonneg t))]
      gcongr
  have hi2 : IntegrableOn (fun t : ℝ => rexp (-(t ^ 2 / 2))) (Ioi 0) := by
    have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn (s := Ioi 0)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show rexp (-(1 / 2) * t ^ 2) = _
    congr 1; ring
  have hle : ∀ t : ℝ, |F t| ≤ |t| / 2 := by
    intro t
    obtain ⟨h0, h1, _⟩ := one_sub_exp_bounds t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [hF]
    · have hpos : 0 < |t| := abs_pos.mpr ht
      simp only [hF]
      rw [abs_div, abs_neg, abs_of_nonneg h0, div_le_iff₀ hpos]
      have : |t| / 2 * |t| = t ^ 2 / 2 := by rw [← sq_abs t]; ring
      linarith
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    have hF0 : F 0 = 0 := by simp [hF]
    have ht : Tendsto F (𝓝 0) (𝓝 0) := by
      refine squeeze_zero_norm (fun t => hle t) ?_
      have : Continuous (fun t : ℝ => |t| / 2) := by fun_prop
      simpa using this.tendsto 0
    have hc : ContinuousAt F 0 := by unfold ContinuousAt; rw [hF0]; exact ht
    exact hc.continuousWithinAt
  have hlim : Tendsto F atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
    obtain ⟨h0, _, h1⟩ := one_sub_exp_bounds t
    have ht0 : (0 : ℝ) < t := ht
    simp only [hF]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg h0, abs_of_pos ht0, inv_eq_one_div]
    gcongr
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv (hi1.sub hi2) hlim
  have hF0 : F 0 = 0 := by simp [hF]
  rw [hF0, sub_zero] at hmain
  have hsub : ∫ t in Ioi (0 : ℝ), f' t =
      (∫ t in Ioi (0 : ℝ), (1 - rexp (-(t ^ 2 / 2))) / t ^ 2) -
        ∫ t in Ioi (0 : ℝ), rexp (-(t ^ 2 / 2)) := integral_sub hi1 hi2
  have hg : ∫ t in Ioi (0 : ℝ), rexp (-(t ^ 2 / 2)) = √(π / 2) := by
    have h := integral_gaussian_Ioi (1 / 2)
    have e : (fun t : ℝ => rexp (-(1 / 2) * t ^ 2)) = fun t => rexp (-(t ^ 2 / 2)) := by
      funext t; congr 1; ring
    rw [e] at h
    have e2 : √(π / 2) = √(π / (1 / 2)) / 2 := by
      rw [show π / 2 = (π / (1 / 2)) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [h, e2]
  linarith

/-- **`K1 = π/2`.** -/
theorem K1_eq : K1 = π / 2 := by
  have h := (gauss_ker1 0).2
  simp only [zero_add, mul_zero, Real.cos_zero, mul_one] at h
  rw [gauss_abs, integral_one_sub_exp] at h
  have hp : (0 : ℝ) < π := Real.pi_pos
  have h1 : √(π / 2) = π / 2 * √(2 / π) := by
    rw [show π / 2 = (π / 2) ^ 2 * (2 / π) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    congr 2
    field_simp
  have h2 : (0 : ℝ) < √(2 / π) := Real.sqrt_pos.mpr (by positivity)
  rw [h1] at h
  exact mul_right_cancel₀ h2.ne' h

/-- **`K2 = π/4`** (integration by parts: `K2 = K1/2`). -/
theorem K2_eq : K2 = π / 4 := by
  set G : ℝ → ℝ := fun t => -(t - Real.sin t) / (2 * t ^ 2) with hG
  set g' : ℝ → ℝ := fun t => ker2 t 1 - ker1 t 1 / 2 with hg'
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt G (g' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have h1 : HasDerivAt (fun t : ℝ => -(t - Real.sin t)) (-(1 - Real.cos x)) x :=
      ((hasDerivAt_id x).sub (Real.hasDerivAt_sin x)).neg
    have h2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * x) x := by
      have := (hasDerivAt_pow 2 x).const_mul 2
      convert this using 1; ring
    have h3 := h1.div h2 (by positivity)
    have e : g' x = (-(1 - Real.cos x) * (2 * x ^ 2) - -(x - Real.sin x) * (4 * x)) /
        (2 * x ^ 2) ^ 2 := by
      simp only [hg', ker1, ker2, mul_one]; field_simp; ring
    rw [e]
    exact h3
  have hle : ∀ t : ℝ, |G t| ≤ |t| / 12 := by
    intro t
    have h := abs_sub_sin_le t
    rcases eq_or_ne t 0 with rfl | ht
    · simp [hG]
    · have hpos : 0 < |t| := abs_pos.mpr ht
      simp only [hG]
      rw [abs_div, abs_neg, abs_mul, abs_pow, abs_of_pos (show (0 : ℝ) < 2 by norm_num),
        div_le_iff₀ (by positivity)]
      calc |t - Real.sin t| ≤ |t| ^ 3 / 6 := h
        _ = |t| / 12 * (2 * |t| ^ 2) := by ring
  have hcont : ContinuousWithinAt G (Ici 0) 0 := by
    have hG0 : G 0 = 0 := by simp [hG]
    have ht : Tendsto G (𝓝 0) (𝓝 0) := by
      refine squeeze_zero_norm (fun t => hle t) ?_
      have : Continuous (fun t : ℝ => |t| / 12) := by fun_prop
      simpa using this.tendsto 0
    have hc : ContinuousAt G 0 := by unfold ContinuousAt; rw [hG0]; exact ht
    exact hc.continuousWithinAt
  have hlim : Tendsto G atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
    filter_upwards [Ioi_mem_atTop (1 : ℝ)] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    simp only [hG]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (show (0 : ℝ) < 2 * t ^ 2 by positivity),
      div_le_iff₀ (by positivity)]
    have h1 : |t - Real.sin t| ≤ t + 1 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_pos ht0]; linarith [Real.abs_sin_le_one t]
    have : t⁻¹ * (2 * t ^ 2) = 2 * t := by field_simp
    rw [this]; linarith
  have hi : IntegrableOn g' (Ioi 0) := (ker2_integrableOn 1).sub ((ker1_integrableOn 1).div_const 2)
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hi hlim
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero] at hmain
  have hsub : ∫ t in Ioi (0 : ℝ), g' t = K2 - K1 / 2 := by
    simp only [hg']
    rw [integral_sub (ker2_integrableOn 1) ((ker1_integrableOn 1).div_const 2), integral_div]
    rfl
  rw [hsub, K1_eq] at hmain
  linarith

end BstLean.Part150
