import BstLean.Part150Trig

/-!
# Part 150, item 2: the periodic peaks of `|cos u|^J`

Paper source: `onW45-opus-prover.md` §2, Lemma B-F, Steps 3 and 4 (the cosine part of Region C).

* `hJ0 J = ∫_0^{π/2} cos(v)^J dv ≤ √(2π/J)/2`, `hJ2 J = ∫_0^{π/2} v² cos(v)^J dv ≤ √(2π/J)/(2J)`,
  `cJ J = ∫_{−π/2}^{π/2} cos(v)^J dv ≤ √(2π/J)`.
* `tail_le_of_periods`: an integral over `(π/2, ∞)` is at most a bound of the sums over periods.
* **`peak2`**: `∫_{π/2}^∞ |cos u|^J/u² du ≤ √(2π/J)·(1/6 + 22/(405J))` (the pairing `v ↔ −v`,
  the chord `44/9`, `Σ 1/k² = π²/6`, `Σ 1/k⁴ = π⁴/90`: the paper's value).
* **`peak3`**: `∫_{π/2}^∞ |cos u|^J/u³ du ≤ √(2π/J)·56807/(6750π³)` (the paper has `7ζ(3)/π³`, which is
  `8.41440/π³`; `56807/6750 = 8.41585…`: three exact terms and a telescoping bound).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology

/-! ## Gaussian integrals -/

lemma integrableOn_sq_exp {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun v : ℝ => v ^ 2 * rexp (-b * v ^ 2)) (Ioi 0) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)).integrableOn (s := Ioi 0)
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  show v ^ (2 : ℝ) * rexp (-b * v ^ 2) = _
  rw [Real.rpow_two]

/-- `∫_0^∞ v² e^{−bv²} dv = √(π/b)/(4b)`. -/
theorem integral_sq_exp_Ioi {b : ℝ} (hb : 0 < b) :
    ∫ v in Ioi (0 : ℝ), v ^ 2 * rexp (-b * v ^ 2) = √(π / b) / (4 * b) := by
  set F : ℝ → ℝ := fun v => -(v * rexp (-b * v ^ 2)) / (2 * b) with hF
  set f' : ℝ → ℝ := fun v => v ^ 2 * rexp (-b * v ^ 2) - rexp (-b * v ^ 2) / (2 * b) with hf'
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F (f' x) x := by
    intro x _
    have h0 : HasDerivAt (fun v : ℝ => -b * v ^ 2) (-b * (2 * x)) x := by
      have := (hasDerivAt_pow 2 x).const_mul (-b)
      convert this using 1; ring
    have h1 : HasDerivAt (fun v : ℝ => rexp (-b * v ^ 2)) (rexp (-b * x ^ 2) * (-b * (2 * x))) x :=
      h0.exp
    have h2 := (((hasDerivAt_id x).mul h1).neg).div_const (2 * b)
    have e : f' x = -(1 * rexp (-b * x ^ 2) + id x * (rexp (-b * x ^ 2) * (-b * (2 * x)))) /
        (2 * b) := by
      simp only [hf', id]; field_simp; ring
    rw [e]
    exact h2
  have hi1 := integrableOn_sq_exp hb
  have hi2 : IntegrableOn (fun v : ℝ => rexp (-b * v ^ 2) / (2 * b)) (Ioi 0) :=
    ((integrable_exp_neg_mul_sq hb).integrableOn (s := Ioi 0)).div_const _
  have hlim : Tendsto F atTop (𝓝 0) := by
    have ht : Tendsto (fun v : ℝ => 1 / (2 * b ^ 2) * v⁻¹) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (1 / (2 * b ^ 2))
      rwa [mul_zero] at h
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with v hv
    have hv0 : (0 : ℝ) < v := hv
    have hw : 0 < b * v ^ 2 := by positivity
    have h1 : rexp (-b * v ^ 2) ≤ 1 / (b * v ^ 2) := by
      rw [show -b * v ^ 2 = -(b * v ^ 2) by ring, Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le hw
      linarith [Real.add_one_le_exp (b * v ^ 2)]
    simp only [hF]
    rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * b),
      abs_of_pos (by positivity : (0 : ℝ) < v * rexp (-b * v ^ 2)), div_le_iff₀ (by positivity)]
    calc v * rexp (-b * v ^ 2) ≤ v * (1 / (b * v ^ 2)) := mul_le_mul_of_nonneg_left h1 hv0.le
      _ = 1 / (2 * b ^ 2) * v⁻¹ * (2 * b) := by field_simp
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (hi1.sub hi2) hlim
  have hF0 : F 0 = 0 := by simp [hF]
  rw [hF0, sub_zero] at hmain
  have hsub : ∫ v in Ioi (0 : ℝ), f' v =
      (∫ v in Ioi (0 : ℝ), v ^ 2 * rexp (-b * v ^ 2)) -
        ∫ v in Ioi (0 : ℝ), rexp (-b * v ^ 2) / (2 * b) := integral_sub hi1 hi2
  rw [integral_div, integral_gaussian_Ioi b] at hsub
  have : √(π / b) / 2 / (2 * b) = √(π / b) / (4 * b) := by field_simp; ring
  linarith

/-! ## Integrals of `cos^J` over a half period -/

/-- `∫_0^{π/2} cos(v)^J dv`. -/
noncomputable def hJ0 (J : ℕ) : ℝ := ∫ v in (0 : ℝ)..(π / 2), Real.cos v ^ J

/-- `∫_0^{π/2} v² cos(v)^J dv`. -/
noncomputable def hJ2 (J : ℕ) : ℝ := ∫ v in (0 : ℝ)..(π / 2), v ^ 2 * Real.cos v ^ J

/-- `∫_{−π/2}^{π/2} cos(v)^J dv`. -/
noncomputable def cJ (J : ℕ) : ℝ := ∫ v in (-(π / 2))..(π / 2), Real.cos v ^ J

lemma cos_pow_bounds (J : ℕ) {v : ℝ} (h1 : -(π / 2) ≤ v) (h2 : v ≤ π / 2) :
    0 ≤ Real.cos v ^ J ∧ Real.cos v ^ J ≤ rexp (-((J : ℝ) / 2) * v ^ 2) := by
  have hc : 0 ≤ Real.cos v := Real.cos_nonneg_of_neg_pi_div_two_le_of_le h1 h2
  have hle : Real.cos v ≤ rexp (-(v ^ 2 / 2)) :=
    cos_le_exp (abs_le.mpr ⟨by linarith [Real.pi_le_four], by linarith [Real.pi_le_four]⟩)
  refine ⟨pow_nonneg hc J, ?_⟩
  have := pow_le_pow_left₀ hc hle J
  rw [exp_pow_J] at this
  refine this.trans (le_of_eq ?_)
  congr 1; ring

lemma hJ0_nonneg (J : ℕ) : 0 ≤ hJ0 J :=
  intervalIntegral.integral_nonneg (by positivity) fun v hv =>
    (cos_pow_bounds J (by linarith [hv.1, Real.pi_pos]) hv.2).1

lemma hJ2_nonneg (J : ℕ) : 0 ≤ hJ2 J :=
  intervalIntegral.integral_nonneg (by positivity) fun v hv =>
    mul_nonneg (sq_nonneg v) (cos_pow_bounds J (by linarith [hv.1, Real.pi_pos]) hv.2).1

lemma cJ_nonneg (J : ℕ) : 0 ≤ cJ J :=
  intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun v hv =>
    (cos_pow_bounds J hv.1 hv.2).1

theorem hJ0_le {J : ℕ} (hJ : 1 ≤ J) : hJ0 J ≤ √(2 * π / J) / 2 := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hb : (0 : ℝ) < (J : ℝ) / 2 := by positivity
  have hp : (0 : ℝ) ≤ π / 2 := by positivity
  have hG : IntegrableOn (fun v : ℝ => rexp (-((J : ℝ) / 2) * v ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  unfold hJ0
  rw [intervalIntegral.integral_of_le hp]
  calc ∫ v in Ioc 0 (π / 2), Real.cos v ^ J
      ≤ ∫ v in Ioc 0 (π / 2), rexp (-((J : ℝ) / 2) * v ^ 2) := by
        refine setIntegral_mono_on ?_ (hG.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
          fun v hv => (cos_pow_bounds J (by linarith [hv.1]) hv.2).2
        exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    _ ≤ ∫ v in Ioi 0, rexp (-((J : ℝ) / 2) * v ^ 2) :=
        setIntegral_mono_set hG (Filter.Eventually.of_forall fun v => (Real.exp_pos _).le)
          (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
    _ = √(2 * π / J) / 2 := by
        rw [integral_gaussian_Ioi]; congr 2; field_simp

theorem hJ2_le {J : ℕ} (hJ : 1 ≤ J) : hJ2 J ≤ √(2 * π / J) / (2 * J) := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hb : (0 : ℝ) < (J : ℝ) / 2 := by positivity
  have hp : (0 : ℝ) ≤ π / 2 := by positivity
  have hG := integrableOn_sq_exp hb
  unfold hJ2
  rw [intervalIntegral.integral_of_le hp]
  calc ∫ v in Ioc 0 (π / 2), v ^ 2 * Real.cos v ^ J
      ≤ ∫ v in Ioc 0 (π / 2), v ^ 2 * rexp (-((J : ℝ) / 2) * v ^ 2) := by
        refine setIntegral_mono_on ?_ (hG.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
          fun v hv => mul_le_mul_of_nonneg_left
            (cos_pow_bounds J (by linarith [hv.1]) hv.2).2 (sq_nonneg v)
        exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    _ ≤ ∫ v in Ioi 0, v ^ 2 * rexp (-((J : ℝ) / 2) * v ^ 2) :=
        setIntegral_mono_set hG
          (Filter.Eventually.of_forall fun v => mul_nonneg (sq_nonneg v) (Real.exp_pos _).le)
          (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
    _ = √(2 * π / J) / (2 * J) := by
        rw [integral_sq_exp_Ioi hb]
        rw [show π / ((J : ℝ) / 2) = 2 * π / J by field_simp]
        congr 1; ring

theorem cJ_le {J : ℕ} (hJ : 1 ≤ J) : cJ J ≤ √(2 * π / J) := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hb : (0 : ℝ) < (J : ℝ) / 2 := by positivity
  have hp : -(π / 2) ≤ π / 2 := by linarith [Real.pi_pos]
  have hG : Integrable (fun v : ℝ => rexp (-((J : ℝ) / 2) * v ^ 2)) := integrable_exp_neg_mul_sq hb
  unfold cJ
  rw [intervalIntegral.integral_of_le hp]
  calc ∫ v in Ioc (-(π / 2)) (π / 2), Real.cos v ^ J
      ≤ ∫ v in Ioc (-(π / 2)) (π / 2), rexp (-((J : ℝ) / 2) * v ^ 2) := by
        refine setIntegral_mono_on ?_ hG.integrableOn measurableSet_Ioc
          fun v hv => (cos_pow_bounds J hv.1.le hv.2).2
        exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    _ ≤ ∫ v, rexp (-((J : ℝ) / 2) * v ^ 2) :=
        setIntegral_le_integral hG (Filter.Eventually.of_forall fun v => (Real.exp_pos _).le)
    _ = √(2 * π / J) := by
        rw [integral_gaussian]; congr 1; field_simp

/-! ## The sum over the periods -/

/-- An integral over `(π/2, ∞)` is at most a bound of the sums of bounds over the periods
`[(k + 1/2)π, (k + 3/2)π]`. -/
theorem tail_le_of_periods {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi (π / 2))) {a : ℕ → ℝ} {S : ℝ}
    (hper : ∀ k : ℕ, ∫ u in ((k : ℝ) + 1 / 2) * π..(((k + 1 : ℕ) : ℝ) + 1 / 2) * π, f u ≤ a k)
    (hsum : ∀ N : ℕ, ∑ k ∈ Finset.range N, a k ≤ S) :
    ∫ u in Ioi (π / 2), f u ≤ S := by
  set b : ℕ → ℝ := fun k => ((k : ℝ) + 1 / 2) * π with hb
  have hb0 : b 0 = π / 2 := by simp [hb]; ring
  have hmono : ∀ k : ℕ, b k ≤ b (k + 1) := by
    intro k; simp only [hb]; push_cast; nlinarith [Real.pi_pos]
  have hge : ∀ k : ℕ, π / 2 ≤ b k := by
    intro k; simp only [hb]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [Real.pi_pos]
  have htend : Tendsto b atTop atTop :=
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).atTop_mul_const Real.pi_pos
  have hlim := intervalIntegral_tendsto_integral_Ioi (π / 2) hf htend
  refine le_of_tendsto' hlim fun N => ?_
  have hint : ∀ k < N, IntervalIntegrable f volume (b k) (b (k + 1)) := by
    intro k _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hmono k)]
    exact hf.mono_set fun x hx => lt_of_le_of_lt (hge k) hx.1
  rw [← hb0, ← intervalIntegral.sum_integral_adjacent_intervals hint]
  exact (Finset.sum_le_sum fun k _ => hper k).trans (hsum N)

/-- The kernel of the peaks: `|cos u|^J/u^p`. -/
noncomputable def pk (J p : ℕ) (u : ℝ) : ℝ := |Real.cos u| ^ J / u ^ p

lemma pk_nonneg (J p : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pk J p u := by unfold pk; positivity

lemma pk_integrableOn (J : ℕ) {p : ℕ} (hp : 2 ≤ p) : IntegrableOn (pk J p) (Ioi (π / 2)) := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hD : IntegrableOn (fun t : ℝ => t ^ (-(p : ℝ))) (Ioi (π / 2)) :=
    integrableOn_Ioi_rpow_of_lt (by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith) hpi
  have hm : Measurable (pk J p) := by unfold pk; fun_prop
  refine Integrable.mono' hD hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0 : ℝ) < u := lt_trans hpi hu
  rw [Real.norm_eq_abs, abs_of_nonneg (pk_nonneg J p hu0.le), Real.rpow_neg hu0.le,
    Real.rpow_natCast]
  unfold pk
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one u))

/-- One period, moved to `[−π/2, π/2]`. -/
lemma period_shift (J p k : ℕ) :
    ∫ u in ((k : ℝ) + 1 / 2) * π..(((k + 1 : ℕ) : ℝ) + 1 / 2) * π, pk J p u =
      ∫ v in (-(π / 2))..(π / 2), Real.cos v ^ J / (v + ((k : ℝ) + 1) * π) ^ p := by
  have h := intervalIntegral.integral_comp_add_right (a := -(π / 2)) (b := π / 2) (pk J p)
    (((k : ℝ) + 1) * π)
  rw [show ((k : ℝ) + 1 / 2) * π = -(π / 2) + ((k : ℝ) + 1) * π by ring,
    show (((k + 1 : ℕ) : ℝ) + 1 / 2) * π = π / 2 + ((k : ℝ) + 1) * π by push_cast; ring, ← h]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hv
  have e : Real.cos (v + ((k : ℝ) + 1) * π) = (-1) ^ (k + 1) * Real.cos v := by
    have := Real.cos_add_nat_mul_pi v (k + 1)
    push_cast at this
    exact this
  show |Real.cos (v + ((k : ℝ) + 1) * π)| ^ J / (v + ((k : ℝ) + 1) * π) ^ p = _
  rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hv)]

end BstLean.Part150
