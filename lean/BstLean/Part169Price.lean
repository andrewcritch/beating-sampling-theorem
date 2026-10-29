import BstLean.Part161Gauss

/-!
# Part 169 (file `Price`): the deterministic bias price of Part 08

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, "The scale price and the corrected exceptional-mass step",
formula `t7:p08:price` (the Gaussian affinity, the location and scale price, and the
exceptional mass).

* `hell_price_pt`: for `S̄, S̃ > 0`, `|S̃/S̄ − 1| ≤ ε < 1`:
  `H²(N(m̄, S̄I), N(m̃, S̃I)) ≤ n(S̃/S̄ − 1)²/(8(1 − ε)) + |m̄ − m̃|²/(2S̄(2 − ε))`
  (the paper: `H² ≤ n(R − 1)²/(8R) + |c_A|²(λ̃ − λ̄)²/(2S̄(1 + R))`, `R = S̃/S̄`).
* `hell_price_loc`: with `|c_A|² ≤ γ e n χ`, `S̄ ≥ γ d`:
  `H² ≤ n Δ_S²/(8(1 − ε)) + nχ(√e(λ̄ − λ̃))²/(2(2 − ε)d)` (`Δ_f = √e(λ̄ − λ̃)`; at
  `ε = 0.02`: `8(1 − ε) = 7.84`, `χ/(2(2 − ε)d) = c_f`).
* **`bias_price`**: the integrated price over a measurable set `K` of any finite measure:
  `∫_K H² ≤ (c_f(ε)∫_K(nΔ_f)² + ∫_K(nΔ_S)²/(8(1 − ε)))/n + 2μ(K ∩ {|Δ_S| > ε})`.
* `sq_int_le_of_pow8`, `pow4_int_le_of_pow8`: on a set of mass at most one, an `L⁸` bound `a`
  gives the `L²` and `L⁴` bounds `a² `, `a⁴` (Jensen, here by the weighted AM–GM inequality).
* **`bias_price_L8`**: the paper's form `P_B = (c_f a_f² + B_S²/(8(1 − ε)))/n + 2μ_exc` from the
  `L⁸` bound `a_f` on `nΔ_f`, the `L²` bound `B_S` on `nΔ_S` and the exceptional mass `μ_exc`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part161 (hellG2 hellG2_le hellG2_le_two hellG2_nonneg)

/-- **The pointwise Gaussian price** (paper `t7:p08:price`, first display). -/
theorem hell_price_pt (n : ℕ) {Sb St d2 ε : ℝ} (hSb : 0 < Sb) (hSt : 0 < St) (hd : 0 ≤ d2)
    (hε : |St / Sb - 1| ≤ ε) (hε1 : ε < 1) :
    hellG2 n d2 Sb St ≤ n * (St / Sb - 1) ^ 2 / (8 * (1 - ε)) + d2 / (2 * Sb * (2 - ε)) := by
  refine (hellG2_le n hSb hSt hd).trans ?_
  set R := St / Sb with hR
  have hR0 : 0 < R := div_pos hSt hSb
  have hRl : 1 - ε ≤ R := by linarith [(abs_le.mp hε).1]
  have hRu : R ≤ 1 + ε := by linarith [(abs_le.mp hε).2]
  have hpos : 0 < 1 - ε := by linarith
  have e1 : Sb / St = R⁻¹ := by rw [hR, inv_div]
  have h1 : (n : ℝ) * (Sb / St - 1) ^ 2 / (8 * (Sb / St)) = n * (R - 1) ^ 2 / (8 * R) := by
    rw [e1]; field_simp; ring
  have a1 : (n : ℝ) * (R - 1) ^ 2 / (8 * R) ≤ n * (R - 1) ^ 2 / (8 * (1 - ε)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hsum : Sb * (2 - ε) ≤ Sb + St := by
    have : St = R * Sb := by rw [hR]; field_simp
    rw [this]; nlinarith
  have a2 : d2 / (2 * (Sb + St)) ≤ d2 / (2 * Sb * (2 - ε)) := by
    apply div_le_div_of_nonneg_left hd (by have : 0 < 2 - ε := by linarith
                                           positivity)
    linarith
  rw [h1]; linarith

/-- **The pointwise price with the location inputs** `|c_A|² ≤ γ e n χ`, `S̄ ≥ γ d`. -/
theorem hell_price_loc (n : ℕ) {Sb St lb lt cA2 γ e χ d ε : ℝ} (hSt : 0 < St)
    (hγ : 0 < γ) (he : 0 < e) (hdd : 0 < d) (hSbd : γ * d ≤ Sb) (hc0 : 0 ≤ cA2)
    (hc : cA2 ≤ γ * e * n * χ) (hε : |St / Sb - 1| ≤ ε) (hε1 : ε < 1) :
    hellG2 n ((lb - lt) ^ 2 * cA2) Sb St ≤
      n * (St / Sb - 1) ^ 2 / (8 * (1 - ε)) + n * χ * (√e * (lb - lt)) ^ 2 / (2 * (2 - ε) * d) := by
  have hSb : 0 < Sb := lt_of_lt_of_le (mul_pos hγ hdd) hSbd
  refine (hell_price_pt n hSb hSt (mul_nonneg (sq_nonneg _) hc0) hε hε1).trans ?_
  have h2e : 0 < 2 - ε := by linarith
  have hb : (lb - lt) ^ 2 * cA2 / (2 * Sb * (2 - ε)) ≤
      (lb - lt) ^ 2 * (γ * e * n * χ) / (2 * (γ * d) * (2 - ε)) := by
    apply div_le_div₀ (by
        have : 0 ≤ (lb - lt) ^ 2 * cA2 := mul_nonneg (sq_nonneg _) hc0
        exact this.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg _)))
      (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSbd (by norm_num)) h2e.le
  have he' : (√e * (lb - lt)) ^ 2 = e * (lb - lt) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt he.le]
  have hc' : (lb - lt) ^ 2 * (γ * e * n * χ) / (2 * (γ * d) * (2 - ε)) =
      n * χ * (√e * (lb - lt)) ^ 2 / (2 * (2 - ε) * d) := by
    rw [he']; field_simp
  linarith

/-- **The integrated bias price** (paper `t7:p08:price`): on a measurable set `K` of a finite
measure `μ` (the latitude measure, restricted to the kept bulk), with `Δ_f = √e(λ̄ − λ̃)` and
`Δ_S = S̃/S̄ − 1`,
`∫_K H²(N(λ̄c_A, S̄I), N(λ̃c_A, S̃I)) ≤ (c_f(ε)∫_K(nΔ_f)² + ∫_K(nΔ_S)²/(8(1 − ε)))/n
  + 2μ(K ∩ {|Δ_S| > ε})`, `c_f(ε) = χ/(2(2 − ε)d)`. -/
theorem bias_price {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (n : ℕ) (hn : 0 < n) {Sb St lb lt : α → ℝ}
    (mSb : Measurable Sb) (mSt : Measurable St)
    {cA2 γ e χ d ε : ℝ} (hγ : 0 < γ) (he : 0 < e) (hdd : 0 < d) (hc0 : 0 ≤ cA2)
    (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1)
    (hSbd : ∀ a ∈ K, γ * d ≤ Sb a) (hSt : ∀ a ∈ K, 0 < St a)
    (iF : IntegrableOn (fun a => ((n : ℝ) * (√e * (lb a - lt a))) ^ 2) K μ)
    (iS : IntegrableOn (fun a => ((n : ℝ) * (St a / Sb a - 1)) ^ 2) K μ) :
    ∫ a in K, hellG2 n ((lb a - lt a) ^ 2 * cA2) (Sb a) (St a) ∂μ ≤
      (χ / (2 * (2 - ε) * d) * ∫ a in K, ((n : ℝ) * (√e * (lb a - lt a))) ^ 2 ∂μ +
        1 / (8 * (1 - ε)) * ∫ a in K, ((n : ℝ) * (St a / Sb a - 1)) ^ 2 ∂μ) / n +
      2 * μ.real (K ∩ {a | ε < |St a / Sb a - 1|}) := by
  set X : Set α := {a | ε < |St a / Sb a - 1|} with hX
  have mX : MeasurableSet X :=
    measurableSet_lt measurable_const (((mSt.div mSb).sub_const 1).abs)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hχ : 0 ≤ χ := by
    by_contra h
    have : γ * e * n * χ < 0 := mul_neg_of_pos_of_neg (by positivity) (lt_of_not_ge h)
    linarith
  set g : α → ℝ := fun a =>
    (χ / (2 * (2 - ε) * d) * ((n : ℝ) * (√e * (lb a - lt a))) ^ 2 +
      1 / (8 * (1 - ε)) * ((n : ℝ) * (St a / Sb a - 1)) ^ 2) / n + X.indicator (fun _ => 2) a
    with hg
  have hgi : IntegrableOn g K μ := by
    refine (((iF.const_mul _).add (iS.const_mul _)).div_const _).add ?_
    exact (integrable_const (2 : ℝ)).indicator mX |>.integrableOn
  have hpt : ∀ a ∈ K, hellG2 n ((lb a - lt a) ^ 2 * cA2) (Sb a) (St a) ≤ g a := by
    intro a ha
    have hA : 0 ≤ (χ / (2 * (2 - ε) * d) * ((n : ℝ) * (√e * (lb a - lt a))) ^ 2 +
        1 / (8 * (1 - ε)) * ((n : ℝ) * (St a / Sb a - 1)) ^ 2) / n := by
      have : 0 < 1 - ε := by linarith
      have : 0 < 2 - ε := by linarith
      positivity
    by_cases hx : a ∈ X
    · simp only [hg, Set.indicator_of_mem hx]
      linarith [hellG2_le_two n ((lb a - lt a) ^ 2 * cA2) (Sb a) (St a)]
    · simp only [hg, Set.indicator_of_notMem hx, add_zero]
      have hle : |St a / Sb a - 1| ≤ ε := le_of_not_gt hx
      refine (hell_price_loc n (hSt a ha) hγ he hdd (hSbd a ha) hc0 hc hle hε1).trans
        (le_of_eq ?_)
      field_simp
      ring
  have hmono : ∫ a in K, hellG2 n ((lb a - lt a) ^ 2 * cA2) (Sb a) (St a) ∂μ ≤ ∫ a in K, g a ∂μ :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun a =>
        hellG2_nonneg n (mul_nonneg (sq_nonneg _) hc0) _ _) hgi
      ((ae_restrict_iff' hK).mpr (Filter.Eventually.of_forall hpt))
  refine hmono.trans (le_of_eq ?_)
  have i1 : IntegrableOn (fun a => (χ / (2 * (2 - ε) * d) * ((n : ℝ) * (√e * (lb a - lt a))) ^ 2 +
      1 / (8 * (1 - ε)) * ((n : ℝ) * (St a / Sb a - 1)) ^ 2) / n) K μ :=
    ((iF.const_mul _).add (iS.const_mul _)).div_const _
  have i2 : IntegrableOn (fun a => X.indicator (fun _ => (2 : ℝ)) a) K μ :=
    (integrable_const (2 : ℝ)).indicator mX |>.integrableOn
  simp only [hg]
  rw [integral_add i1 i2, integral_div, integral_add (iF.const_mul _) (iS.const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator mX]
  simp only [integral_const, smul_eq_mul]
  rw [Measure.restrict_restrict mX, Set.inter_comm, measureReal_restrict_apply_univ]
  ring

/-- **Jensen for an `L⁸` bound on a set of mass at most one**: `∫_K h⁸ ≤ a⁸` gives
`∫_K h² ≤ a²`. -/
theorem sq_int_le_of_pow8 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK1 : μ.real K ≤ 1) {h : α → ℝ} {a : ℝ} (ha : 0 < a)
    (i2 : IntegrableOn (fun x => h x ^ 2) K μ) (i8 : IntegrableOn (fun x => h x ^ 8) K μ)
    (h8 : ∫ x in K, h x ^ 8 ∂μ ≤ a ^ 8) :
    ∫ x in K, h x ^ 2 ∂μ ≤ a ^ 2 := by
  -- `y ≤ (3/4)a² + (1/4) y⁴/a⁶` for `y ≥ 0` (weighted AM–GM)
  have hpt : ∀ x, h x ^ 2 ≤ 3 / 4 * a ^ 2 + 1 / 4 * (h x ^ 8 / a ^ 6) := by
    intro x
    set y := h x ^ 2
    have hy : 0 ≤ y := sq_nonneg _
    have e : h x ^ 8 = y ^ 4 := by rw [show h x ^ 8 = (h x ^ 2) ^ 4 by ring]
    rw [e]
    have ha6 : 0 < a ^ 6 := by positivity
    rw [show 3 / 4 * a ^ 2 + 1 / 4 * (y ^ 4 / a ^ 6) = (3 * a ^ 8 + y ^ 4) / (4 * a ^ 6) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    -- `4 y a⁶ ≤ 3a⁸ + y⁴`: `3a⁸ + y⁴ − 4ya⁶ = (y − a²)²(y² + 2ya² + 3a⁴)`
    have hq : 0 ≤ y ^ 2 + 2 * y * a ^ 2 + 3 * (a ^ 2) ^ 2 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (y - a ^ 2)) hq]
  have i3 : IntegrableOn (fun x => 3 / 4 * a ^ 2 + 1 / 4 * (h x ^ 8 / a ^ 6)) K μ :=
    (integrable_const _).add ((i8.div_const _).const_mul _)
  refine (integral_mono i2 i3 hpt).trans ?_
  have e1 : ∫ x in K, (3 / 4 * a ^ 2 + 1 / 4 * (h x ^ 8 / a ^ 6)) ∂μ =
      μ.real K * (3 / 4 * a ^ 2) + 1 / 4 * ((∫ x in K, h x ^ 8 ∂μ) / a ^ 6) := by
    rw [integral_add (integrable_const _) ((i8.div_const _).const_mul _), integral_const,
      smul_eq_mul, measureReal_restrict_apply_univ, integral_const_mul, integral_div]
  rw [e1]
  have ha6 : 0 < a ^ 6 := by positivity
  have h1 : μ.real K * (3 / 4 * a ^ 2) ≤ 3 / 4 * a ^ 2 := by
    have := mul_le_mul_of_nonneg_right hK1 (by positivity : (0:ℝ) ≤ 3 / 4 * a ^ 2)
    linarith
  have h2 : 1 / 4 * ((∫ x in K, h x ^ 8 ∂μ) / a ^ 6) ≤ 1 / 4 * a ^ 2 := by
    have : (∫ x in K, h x ^ 8 ∂μ) / a ^ 6 ≤ a ^ 2 := by
      rw [div_le_iff₀ ha6]; nlinarith
    linarith
  linarith

/-- **Jensen, order four**: on a set of mass at most one, `∫_K h⁸ ≤ a⁸` gives `∫_K h⁴ ≤ a⁴`. -/
theorem pow4_int_le_of_pow8 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK1 : μ.real K ≤ 1) {h : α → ℝ} {a : ℝ} (ha : 0 < a)
    (i4 : IntegrableOn (fun x => h x ^ 4) K μ) (i8 : IntegrableOn (fun x => h x ^ 8) K μ)
    (h8 : ∫ x in K, h x ^ 8 ∂μ ≤ a ^ 8) :
    ∫ x in K, h x ^ 4 ∂μ ≤ a ^ 4 := by
  have ha4 : 0 < a ^ 4 := by positivity
  have hpt : ∀ x, h x ^ 4 ≤ 1 / 2 * a ^ 4 + 1 / 2 * (h x ^ 8 / a ^ 4) := by
    intro x
    have e : h x ^ 8 = (h x ^ 4) ^ 2 := by ring
    rw [e, show 1 / 2 * a ^ 4 + 1 / 2 * ((h x ^ 4) ^ 2 / a ^ 4) =
      ((a ^ 4) ^ 2 + (h x ^ 4) ^ 2) / (2 * a ^ 4) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (h x ^ 4 - a ^ 4)]
  have i3 : IntegrableOn (fun x => 1 / 2 * a ^ 4 + 1 / 2 * (h x ^ 8 / a ^ 4)) K μ :=
    (integrable_const _).add ((i8.div_const _).const_mul _)
  refine (integral_mono i4 i3 hpt).trans ?_
  have e1 : ∫ x in K, (1 / 2 * a ^ 4 + 1 / 2 * (h x ^ 8 / a ^ 4)) ∂μ =
      μ.real K * (1 / 2 * a ^ 4) + 1 / 2 * ((∫ x in K, h x ^ 8 ∂μ) / a ^ 4) := by
    rw [integral_add (integrable_const _) ((i8.div_const _).const_mul _), integral_const,
      smul_eq_mul, measureReal_restrict_apply_univ, integral_const_mul, integral_div]
  rw [e1]
  have h1 : μ.real K * (1 / 2 * a ^ 4) ≤ 1 / 2 * a ^ 4 := by
    have := mul_le_mul_of_nonneg_right hK1 (by positivity : (0:ℝ) ≤ 1 / 2 * a ^ 4)
    linarith
  have h2 : (∫ x in K, h x ^ 8 ∂μ) / a ^ 4 ≤ a ^ 4 := by
    rw [div_le_iff₀ ha4]; nlinarith
  linarith

/-- **The bias price in the paper's form** (`t7:p08:price`):
`E_s[H²; K] ≤ P_B = (c_f a_f² + B_S²/(8(1 − ε)))/n + 2μ_exc`, from `‖nΔ_f‖_{L⁸(K)} ≤ a_f`,
`‖nΔ_S‖_{L²(K)} ≤ B_S` and `μ(K ∩ {|Δ_S| > ε}) ≤ μ_exc`, on a set `K` of mass at most one. -/
theorem bias_price_L8 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (n : ℕ) (hn : 0 < n)
    {Sb St lb lt : α → ℝ} (mSb : Measurable Sb) (mSt : Measurable St)
    {cA2 γ e χ d ε af BS mex : ℝ} (hγ : 0 < γ) (he : 0 < e) (hdd : 0 < d) (hc0 : 0 ≤ cA2)
    (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1) (haf : 0 < af)
    (hSbd : ∀ a ∈ K, γ * d ≤ Sb a) (hSt : ∀ a ∈ K, 0 < St a)
    (iF : IntegrableOn (fun a => ((n : ℝ) * (√e * (lb a - lt a))) ^ 2) K μ)
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (√e * (lb a - lt a))) ^ 8) K μ)
    (iS : IntegrableOn (fun a => ((n : ℝ) * (St a / Sb a - 1)) ^ 2) K μ)
    (hF8 : ∫ a in K, ((n : ℝ) * (√e * (lb a - lt a))) ^ 8 ∂μ ≤ af ^ 8)
    (hS2 : ∫ a in K, ((n : ℝ) * (St a / Sb a - 1)) ^ 2 ∂μ ≤ BS ^ 2)
    (hmex : μ.real (K ∩ {a | ε < |St a / Sb a - 1|}) ≤ mex) :
    ∫ a in K, hellG2 n ((lb a - lt a) ^ 2 * cA2) (Sb a) (St a) ∂μ ≤
      (χ / (2 * (2 - ε) * d) * af ^ 2 + BS ^ 2 / (8 * (1 - ε))) / n + 2 * mex := by
  have hP := bias_price μ hK n hn mSb mSt hγ he hdd hc0 hc hε1 hSbd hSt iF iS
  have hF2 := sq_int_le_of_pow8 μ hK1 haf iF iF8 hF8
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hχ : 0 ≤ χ := by
    by_contra h
    have : γ * e * n * χ < 0 := mul_neg_of_pos_of_neg (by positivity) (lt_of_not_ge h)
    linarith
  have h2e : 0 < 2 - ε := by linarith
  have h1e : 0 < 1 - ε := by linarith
  have k1 : χ / (2 * (2 - ε) * d) * ∫ a in K, ((n : ℝ) * (√e * (lb a - lt a))) ^ 2 ∂μ ≤
      χ / (2 * (2 - ε) * d) * af ^ 2 := mul_le_mul_of_nonneg_left hF2 (by positivity)
  have k2 : 1 / (8 * (1 - ε)) * ∫ a in K, ((n : ℝ) * (St a / Sb a - 1)) ^ 2 ∂μ ≤
      BS ^ 2 / (8 * (1 - ε)) := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hS2 (by positivity)
  have k3 := div_le_div_of_nonneg_right (add_le_add k1 k2) hnR.le
  linarith

end BstLean.Part169
