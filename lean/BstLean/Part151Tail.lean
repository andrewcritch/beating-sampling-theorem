import BstLean.Part131Tail

/-!
# Part 151, the upper tail of the standard Gaussian

Role: `delegations/statements/p151-spec.md`, item 2 (the bounds of the Gaussian tail that the
final Gaussian step uses). `Φ̄(a)` is written `(gaussianReal 0 1).real (Set.Ioi a)`; `φ(a)` is
`gaussianPDFReal 0 1 a`.

* `tail_le_exp`: `Φ̄(a) ≤ exp(−a²/2)/2` for `a ≥ 0`.
* `tail_le_mills1`: `Φ̄(a) ≤ φ(a)/a` for `a > 0`.
* `tail_le_mills3`: `Φ̄(a) ≤ φ(a)(1/a − 1/a³ + 3/a⁵)` for `a > 0` (the bound (G4) of the paper).
* `two_tail_three`: `2Φ̄(3) ≤ 3/1000`; `two_tail_four`: `2Φ̄(a) ≤ 7/100000` for `a ≥ 4`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open BstLean.Part131 (pdf_eq gauss_real_eq tail_neg)

/-! ## The density -/

lemma pdf_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => gaussianPDFReal 0 1 x) (gaussianPDFReal 0 1 x * (-x)) x := by
  have h2 : HasDerivAt (fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)))
      ((√(2 * Real.pi))⁻¹ * (Real.exp (-(x ^ 2 / 2)) * (-(2 * x ^ 1 * 1 / 2)))) x :=
    (((hasDerivAt_id x).pow 2).div_const 2).neg.exp.const_mul _
  have e : (fun x : ℝ => gaussianPDFReal 0 1 x) =
      fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := funext pdf_eq
  rw [e, pdf_eq]
  convert h2 using 1; ring

lemma pdf_tendsto : Tendsto (fun x : ℝ => gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  have e : (fun x : ℝ => gaussianPDFReal 0 1 x) =
      fun x : ℝ => (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := funext pdf_eq
  rw [e]
  have h1 : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  simpa using h2.const_mul (√(2 * Real.pi))⁻¹

/-! ## A general comparison -/

/-- If `x·q(x) − q′(x) ≥ 1` on `(a, ∞)` and `q` is bounded there, then `Φ̄(a) ≤ φ(a)·q(a)`. -/
lemma tail_le_of {a K : ℝ} {q q' : ℝ → ℝ} (hq : ∀ x ∈ Ici a, HasDerivAt q (q' x) x)
    (hlow : ∀ x ∈ Ioi a, 1 ≤ x * q x - q' x) (hK : ∀ x ∈ Ioi a, |q x| ≤ K) :
    (gaussianReal 0 1).real (Ioi a) ≤ gaussianPDFReal 0 1 a * q a := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [gauss_real_eq]
  let f : ℝ → ℝ := fun x => -(gaussianPDFReal 0 1 x * q x)
  let f' : ℝ → ℝ := fun x => gaussianPDFReal 0 1 x * (x * q x - q' x)
  have hderiv : ∀ x ∈ Ici a, HasDerivAt f (f' x) x := by
    intro x hx
    have h3 := ((pdf_hasDerivAt x).mul (hq x hx)).neg
    have e4 : f' x = -(gaussianPDFReal 0 1 x * -x * q x + gaussianPDFReal 0 1 x * q' x) := by
      simp only [f']; ring
    rw [e4]; exact h3
  have hpos : ∀ x ∈ Ioi a, 0 ≤ f' x := by
    intro x hx
    have := hlow x hx
    exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith)
  have htend : Tendsto f atTop (𝓝 0) := by
    have hb : ∀ᶠ x : ℝ in atTop, ‖f x‖ ≤ K * gaussianPDFReal 0 1 x := by
      filter_upwards [eventually_gt_atTop a] with x hx
      simp only [f, norm_neg, Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (gaussianPDFReal_nonneg _ _ _), mul_comm]
      exact mul_le_mul_of_nonneg_right (hK x hx) (gaussianPDFReal_nonneg _ _ _)
    have h0 : Tendsto (fun x : ℝ => K * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
      simpa using pdf_tendsto.const_mul K
    exact squeeze_zero_norm' hb h0
  have hf'int : IntegrableOn f' (Ioi a) := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hf'int htend
  have hle : ∫ x in Ioi a, gaussianPDFReal 0 1 x ≤ ∫ x in Ioi a, f' x := by
    refine setIntegral_mono_on hint.integrableOn hf'int measurableSet_Ioi ?_
    intro x hx
    have h1 := hlow x hx
    have hp := gaussianPDFReal_nonneg 0 1 x
    simp only [f']
    nlinarith
  rw [hI] at hle
  simpa [f] using hle

/-! ## The Mills bounds -/

/-- `Φ̄(a) ≤ φ(a)/a` for `a > 0`. -/
theorem tail_le_mills1 {a : ℝ} (ha : 0 < a) :
    (gaussianReal 0 1).real (Ioi a) ≤ gaussianPDFReal 0 1 a / a := by
  have h := tail_le_of (a := a) (K := a⁻¹) (q := fun x => x⁻¹) (q' := fun x => -(x ^ 2)⁻¹)
    (fun x _ => hasDerivAt_inv (by
      have hx : a ≤ x := ‹x ∈ Ici a›
      exact (lt_of_lt_of_le ha hx).ne'))
    (fun x hx => by
      have hx0 : 0 < x := lt_trans ha hx
      have : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0.ne'
      have h2 : 0 ≤ (x ^ 2)⁻¹ := by positivity
      linarith)
    (fun x hx => by
      have hx0 : 0 < x := lt_trans ha hx
      rw [abs_of_pos (inv_pos.mpr hx0)]
      exact inv_anti₀ ha (le_of_lt hx))
  rwa [← div_eq_mul_inv] at h

/-- **The bound (G4)**: `Φ̄(a) ≤ φ(a)(1/a − 1/a³ + 3/a⁵)` for `a > 0`. -/
theorem tail_le_mills3 {a : ℝ} (ha : 0 < a) :
    (gaussianReal 0 1).real (Ioi a) ≤
      gaussianPDFReal 0 1 a * (1 / a - 1 / a ^ 3 + 3 / a ^ 5) := by
  have h := tail_le_of (a := a) (K := 1 / a + 1 / a ^ 3 + 3 / a ^ 5)
    (q := fun x => x⁻¹ - x⁻¹ ^ 3 + 3 * x⁻¹ ^ 5)
    (q' := fun x => -(x ^ 2)⁻¹ - 3 * x⁻¹ ^ 2 * -(x ^ 2)⁻¹ + 3 * (5 * x⁻¹ ^ 4 * -(x ^ 2)⁻¹))
    (fun x hx => by
      have hx' : a ≤ x := hx
      have hx0 : x ≠ 0 := (lt_of_lt_of_le ha hx').ne'
      have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
      exact (h1.sub (h1.pow 3)).add ((h1.pow 5).const_mul 3))
    (fun x hx => by
      have hx0 : 0 < x := lt_trans ha hx
      have e : x * (x⁻¹ - x⁻¹ ^ 3 + 3 * x⁻¹ ^ 5) -
          (-(x ^ 2)⁻¹ - 3 * x⁻¹ ^ 2 * -(x ^ 2)⁻¹ + 3 * (5 * x⁻¹ ^ 4 * -(x ^ 2)⁻¹)) =
          1 + 15 / x ^ 6 := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ 15 / x ^ 6 := by positivity
      linarith)
    (fun x hx => by
      have hx0 : 0 < x := lt_trans ha hx
      have hxa : a ≤ x := le_of_lt hx
      have hi : x⁻¹ ≤ a⁻¹ := inv_anti₀ ha hxa
      have hi0 : 0 < x⁻¹ := inv_pos.mpr hx0
      have h3 : x⁻¹ ^ 3 ≤ a⁻¹ ^ 3 := pow_le_pow_left₀ hi0.le hi 3
      have h5 : x⁻¹ ^ 5 ≤ a⁻¹ ^ 5 := pow_le_pow_left₀ hi0.le hi 5
      have p3 : 0 ≤ x⁻¹ ^ 3 := by positivity
      have p5 : 0 ≤ x⁻¹ ^ 5 := by positivity
      have e : 1 / a + 1 / a ^ 3 + 3 / a ^ 5 = a⁻¹ + a⁻¹ ^ 3 + 3 * a⁻¹ ^ 5 := by
        field_simp
      rw [e, abs_le]
      constructor <;> linarith)
  have e : a⁻¹ - a⁻¹ ^ 3 + 3 * a⁻¹ ^ 5 = 1 / a - 1 / a ^ 3 + 3 / a ^ 5 := by
    field_simp
  simpa only [e] using h

/-! ## The bound with the exponential -/

lemma tail_zero : (gaussianReal 0 1).real (Ioi 0) = 1 / 2 := by
  have h1 := tail_neg 0
  rw [neg_zero] at h1
  have h2 : (gaussianReal 0 1).real (Iio 0) + (gaussianReal 0 1).real (Ici 0) = 1 := by
    have h := measureReal_add_measureReal_compl (μ := gaussianReal 0 1) (s := Iio (0 : ℝ))
      measurableSet_Iio
    rwa [compl_Iio, probReal_univ] at h
  have h3 : (gaussianReal 0 1).real (Ici 0) = (gaussianReal 0 1).real (Ioi 0) := by
    have hae : (Ioi (0 : ℝ)) =ᵐ[gaussianReal 0 1] Ici 0 := by
      have hac : gaussianReal 0 1 ≪ volume := gaussianReal_absolutelyContinuous 0 one_ne_zero
      exact hac.ae_eq Ioi_ae_eq_Ici
    exact (measureReal_congr hae).symm
  linarith

/-- `Φ̄(a) ≤ exp(−a²/2)/2` for `a ≥ 0`. -/
theorem tail_le_exp {a : ℝ} (ha : 0 ≤ a) :
    (gaussianReal 0 1).real (Ioi a) ≤ Real.exp (-(a ^ 2 / 2)) / 2 := by
  have hint := integrable_gaussianPDFReal 0 1
  have h0 := tail_zero
  rw [gauss_real_eq] at h0
  rw [gauss_real_eq]
  -- translate
  have e1 : ∫ x in Ioi a, gaussianPDFReal 0 1 x =
      ∫ x in Ioi (0 : ℝ), gaussianPDFReal 0 1 (x + a) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
      ← integral_add_right_eq_self _ a]
    congr 1
    funext x
    simp only [indicator, mem_Ioi]
    by_cases hx : 0 < x
    · have hx' : a < x + a := by linarith
      simp [hx, hx']
    · have hx' : ¬ a < x + a := by linarith
      simp [hx, hx']
  rw [e1]
  have hle : ∫ x in Ioi (0 : ℝ), gaussianPDFReal 0 1 (x + a) ≤
      ∫ x in Ioi (0 : ℝ), Real.exp (-(a ^ 2 / 2)) * gaussianPDFReal 0 1 x := by
    refine setIntegral_mono_on (hint.comp_add_right a).integrableOn
      (hint.const_mul _).integrableOn measurableSet_Ioi ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [pdf_eq, pdf_eq, mul_left_comm, ← Real.exp_add]
    have hc : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
    nlinarith [mul_nonneg hx0.le ha]
  rw [integral_const_mul, h0] at hle
  linarith

/-! ## Two numbers -/

lemma sqrt_two_pi_ge : (5 : ℝ) / 2 ≤ √(2 * Real.pi) := by
  rw [Real.le_sqrt' (by norm_num)]
  have := Real.pi_gt_d2
  nlinarith

lemma tail_anti {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Ioi b) ≤ (gaussianReal 0 1).real (Ioi a) :=
  measureReal_mono (Ioi_subset_Ioi hab)

/-- `2Φ̄(3) ≤ 3/1000`. -/
theorem two_tail_three : 2 * (gaussianReal 0 1).real (Ioi 3) ≤ 3 / 1000 := by
  have h := tail_le_mills3 (a := 3) (by norm_num)
  rw [pdf_eq] at h
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  -- `exp(9/2)² = exp 9 ≥ 2.718⁹`
  have h9 : Real.exp (9 / 2) ^ 2 = Real.exp 1 ^ 9 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have hp : (2.718 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he.le 9
  have hE : (89 : ℝ) ≤ Real.exp (9 / 2) := by
    have hpos := Real.exp_pos (9 / 2 : ℝ)
    by_contra hc
    rw [not_le] at hc
    have : Real.exp (9 / 2) ^ 2 < 89 ^ 2 := by nlinarith
    rw [h9] at this
    norm_num at hp this
    linarith
  have hx : Real.exp (-((3 : ℝ) ^ 2 / 2)) ≤ 1 / 89 := by
    rw [show -((3 : ℝ) ^ 2 / 2) = -(9 / 2) by norm_num, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hE
  have hs := sqrt_two_pi_ge
  have hsi : (√(2 * Real.pi))⁻¹ ≤ 2 / 5 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; convert hs using 1; norm_num
  have hprod : (√(2 * Real.pi))⁻¹ * Real.exp (-((3 : ℝ) ^ 2 / 2)) ≤ 2 / 5 * (1 / 89) :=
    mul_le_mul hsi hx (Real.exp_pos _).le (by norm_num)
  have hq : (0 : ℝ) ≤ 1 / 3 - 1 / 3 ^ 3 + 3 / 3 ^ 5 := by norm_num
  have := mul_le_mul_of_nonneg_right hprod hq
  norm_num at this h ⊢
  linarith

/-- `2Φ̄(a) ≤ 7/100000` for `a ≥ 4`. -/
theorem two_tail_four {a : ℝ} (ha : 4 ≤ a) :
    2 * (gaussianReal 0 1).real (Ioi a) ≤ 7 / 100000 := by
  have hmono := tail_anti ha
  have h := tail_le_mills3 (a := 4) (by norm_num)
  rw [pdf_eq] at h
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.718 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) he.le 8
  have hE : (2978 : ℝ) ≤ Real.exp 8 := by
    rw [h8]; norm_num at hp ⊢; linarith
  have hx : Real.exp (-((4 : ℝ) ^ 2 / 2)) ≤ 1 / 2978 := by
    rw [show -((4 : ℝ) ^ 2 / 2) = -8 by norm_num, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hE
  have hs := sqrt_two_pi_ge
  have hsi : (√(2 * Real.pi))⁻¹ ≤ 2 / 5 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; convert hs using 1; norm_num
  have hprod : (√(2 * Real.pi))⁻¹ * Real.exp (-((4 : ℝ) ^ 2 / 2)) ≤ 2 / 5 * (1 / 2978) :=
    mul_le_mul hsi hx (Real.exp_pos _).le (by norm_num)
  have hq : (0 : ℝ) ≤ 1 / 4 - 1 / 4 ^ 3 + 3 / 4 ^ 5 := by norm_num
  have := mul_le_mul_of_nonneg_right hprod hq
  norm_num at this h ⊢
  linarith

end BstLean.Part151
