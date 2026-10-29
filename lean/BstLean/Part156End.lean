import BstLean.Part156Comp

/-!
# Part 156 (item 2): the two endpoint tails from the ASSUMED bound (CP-R)

`(Ω, μ)` is a probability space and `p : Ω → [0, 1]` is measurable. The theorems `tail_plus` and
`tail_minus` ASSUME the bound `CPR μ p (c_W/n) (c_frame/n) h_W Q` of `Part156Comp` and conclude

* `μ {p > z_+(Q)} ≤ B_+ = exp (n E_+)`,
* `μ {p < z_-(Q)} ≤ B_- = exp (n E_-)` when `z_-(Q) > 1/1000`,

with the exponents `E_±` of the paper at the endpoints `z_+ = 1/100` and `z_- = 1/1000`. The
proofs include the endpoint reduction for every `Q` (`Hplus_scale`, `Hminus_scale`): the exponent
per unit of `z` is worst at the endpoint. The hypotheses `E_+ ≤ 0` and `E_- ≤ 0` are those of the
paper (the paper has `E_± < 0`).

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open MeasureTheory ProbabilityTheory Real

/-- `w_+ = (√(0.01/a) + h)²`. -/
noncomputable def wP (a h : ℝ) : ℝ := (√(1 / 100 / a) + h) ^ 2

/-- `w_- = (√(0.01/a) - h)²`. -/
noncomputable def wM (a h : ℝ) : ℝ := (√(1 / 100 / a) - h) ^ 2

/-- The upper endpoint exponent of the paper:
`E_+ = -(τ_+)(1/100) + T_+ β_+ + (w_+/c_frame)(exp (c_frame T_+ α_+) - 1)`, with
`T_+ = (exp (c_W τ_+) - 1)/c_W`, `α_+ = 1 + h_W/√w_+`, `β_+ = h_W √w_+ + h_W²`. -/
noncomputable def Eplus (a h hW cW cf τ : ℝ) : ℝ :=
  -τ * (1 / 100) +
    cprRhs (Tfun cW τ) (alphaP hW (wP a h)) (betaP hW (wP a h)) (wP a h) cf

/-- The lower endpoint exponent of the paper:
`E_- = -(τ_-)(1/1000) + T_- β_- + (w_- / c_frame)(exp (c_frame T_- α_-) - 1)`, with
`T_- = (exp (c_W τ_-) - 1)/c_W`, `α_- = 1 - h_W/√w_-`, `β_- = -h_W √w_-`. -/
noncomputable def Eminus (a h hW cW cf τ : ℝ) : ℝ :=
  -τ * (1 / 1000) +
    cprRhs (Tfun cW τ) (alphaM hW (wM a h)) (betaM hW (wM a h)) (wM a h) cf

/-- The upper tail bound `B_+ = exp (n E_+)`. -/
noncomputable def Bplus (n a h hW cW cf τ : ℝ) : ℝ := exp (n * Eplus a h hW cW cf τ)

/-- The lower tail bound `B_- = exp (n E_-)`. -/
noncomputable def Bminus (n a h hW cW cf τ : ℝ) : ℝ := exp (n * Eminus a h hW cW cf τ)

/-- Endpoint reduction, upper tail (real numbers). `x0 = √(z0/a)`, `x = t x0` with `t ≥ 1`
(so `z = t² z0`), `r = x + h`. The exponent at `z` is at most `t²` times the exponent at `z0`. -/
lemma Hplus_scale {τ T hW cf h x0 t z0 : ℝ} (hT : 0 ≤ T) (hcf : 0 < cf) (hhW : 0 ≤ hW)
    (hh : 0 ≤ h) (hx0 : 0 < x0) (ht : 1 ≤ t) :
    -τ * (t ^ 2 * z0) + (T * (hW * (t * x0 + h) + hW ^ 2) +
        (t * x0 + h) ^ 2 / cf * (exp (cf * T * (1 + hW / (t * x0 + h))) - 1))
      ≤ t ^ 2 * (-τ * z0 + (T * (hW * (x0 + h) + hW ^ 2) +
        (x0 + h) ^ 2 / cf * (exp (cf * T * (1 + hW / (x0 + h))) - 1))) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have h1t2 : 1 ≤ t ^ 2 := by nlinarith
  have hr0 : 0 < x0 + h := by linarith
  have hr : x0 + h ≤ t * x0 + h := by nlinarith
  have hrpos : 0 < t * x0 + h := lt_of_lt_of_le hr0 hr
  -- (a)
  have ha : hW * (t * x0 + h) + hW ^ 2 ≤ t ^ 2 * (hW * (x0 + h) + hW ^ 2) := by
    have h1 : t * x0 + h ≤ t ^ 2 * (x0 + h) := by nlinarith
    have h2 : hW * (t * x0 + h) ≤ hW * (t ^ 2 * (x0 + h)) := mul_le_mul_of_nonneg_left h1 hhW
    nlinarith [sq_nonneg hW]
  -- (b)
  have hb : (t * x0 + h) ^ 2 ≤ t ^ 2 * (x0 + h) ^ 2 := by
    have h1 : t * x0 + h ≤ t * (x0 + h) := by nlinarith
    calc (t * x0 + h) ^ 2 ≤ (t * (x0 + h)) ^ 2 := pow_le_pow_left₀ hrpos.le h1 2
      _ = _ := by ring
  -- (c)
  have hc : hW / (t * x0 + h) ≤ hW / (x0 + h) := div_le_div_of_nonneg_left hhW hr0 hr
  have harg : cf * T * (1 + hW / (t * x0 + h)) ≤ cf * T * (1 + hW / (x0 + h)) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hcf.le hT)
  have hbr : exp (cf * T * (1 + hW / (t * x0 + h))) - 1 ≤
      exp (cf * T * (1 + hW / (x0 + h))) - 1 := by
    have := exp_le_exp.2 harg
    linarith
  have hbr0 : 0 ≤ exp (cf * T * (1 + hW / (t * x0 + h))) - 1 := by
    have : 0 ≤ cf * T * (1 + hW / (t * x0 + h)) :=
      mul_nonneg (mul_nonneg hcf.le hT) (by have := div_nonneg hhW hrpos.le; linarith)
    have := Real.one_le_exp this
    linarith
  have h3 : (t * x0 + h) ^ 2 / cf * (exp (cf * T * (1 + hW / (t * x0 + h))) - 1) ≤
      t ^ 2 * ((x0 + h) ^ 2 / cf * (exp (cf * T * (1 + hW / (x0 + h))) - 1)) := by
    calc (t * x0 + h) ^ 2 / cf * (exp (cf * T * (1 + hW / (t * x0 + h))) - 1)
        ≤ (t ^ 2 * (x0 + h) ^ 2) / cf * (exp (cf * T * (1 + hW / (t * x0 + h))) - 1) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hcf.le) hbr0
      _ ≤ (t ^ 2 * (x0 + h) ^ 2) / cf * (exp (cf * T * (1 + hW / (x0 + h))) - 1) :=
          mul_le_mul_of_nonneg_left hbr (div_nonneg (by positivity) hcf.le)
      _ = _ := by ring
  have h4 : T * (hW * (t * x0 + h) + hW ^ 2) ≤ T * (t ^ 2 * (hW * (x0 + h) + hW ^ 2)) :=
    mul_le_mul_of_nonneg_left ha hT
  linarith

/-- Endpoint reduction, lower tail (real numbers). `y0 = √(10 z0/a)`, `y = t y0` with `t ≥ 1`
(so `z = t² z0`), `r = y - h`. The side conditions are `y0 ≥ 2h` and `y0 - h > h_W`. The exponent
at `z` is at most `t²` times the exponent at `z0`. -/
lemma Hminus_scale {τ T hW cf h y0 t z0 : ℝ} (hT : T ≤ 0) (hcf : 0 < cf) (hhW : 0 ≤ hW)
    (hh : 0 ≤ h) (hy0 : 2 * h ≤ y0) (hy0W : hW < y0 - h) (ht : 1 ≤ t) :
    -τ * (t ^ 2 * z0) + (T * (-(hW * (t * y0 - h))) +
        (t * y0 - h) ^ 2 / cf * (exp (cf * T * (1 - hW / (t * y0 - h))) - 1))
      ≤ t ^ 2 * (-τ * z0 + (T * (-(hW * (y0 - h))) +
        (y0 - h) ^ 2 / cf * (exp (cf * T * (1 - hW / (y0 - h))) - 1))) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hr0 : 0 < y0 - h := lt_of_le_of_lt hhW hy0W
  have hy0pos : 0 < y0 := by linarith
  have hr : y0 - h ≤ t * y0 - h := by nlinarith
  have hrpos : 0 < t * y0 - h := lt_of_lt_of_le hr0 hr
  -- (a)
  have ha : t * y0 - h ≤ t ^ 2 * (y0 - h) := by
    have h1 : 0 ≤ (t - 1) * (t * y0 - (t + 1) * h) := by
      refine mul_nonneg (by linarith) ?_
      nlinarith
    nlinarith
  have ha' : T * (-(hW * (t * y0 - h))) ≤ t ^ 2 * (T * (-(hW * (y0 - h)))) := by
    have h1 : hW * (t * y0 - h) ≤ hW * (t ^ 2 * (y0 - h)) := mul_le_mul_of_nonneg_left ha hhW
    nlinarith
  -- (b)
  have hb : t ^ 2 * (y0 - h) ^ 2 ≤ (t * y0 - h) ^ 2 := by
    have h1 : t * (y0 - h) ≤ t * y0 - h := by nlinarith
    calc t ^ 2 * (y0 - h) ^ 2 = (t * (y0 - h)) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg ht0.le hr0.le) h1 2
  -- (c)
  have hc : hW / (t * y0 - h) ≤ hW / (y0 - h) := div_le_div_of_nonneg_left hhW hr0 hr
  have hα0 : 0 ≤ 1 - hW / (y0 - h) := by
    have := (div_lt_one hr0).2 hy0W
    linarith
  have harg : cf * T * (1 - hW / (t * y0 - h)) ≤ cf * T * (1 - hW / (y0 - h)) :=
    mul_le_mul_of_nonpos_left (by linarith) (mul_nonpos_of_nonneg_of_nonpos hcf.le hT)
  have hbr : exp (cf * T * (1 - hW / (t * y0 - h))) - 1 ≤
      exp (cf * T * (1 - hW / (y0 - h))) - 1 := by
    have := exp_le_exp.2 harg
    linarith
  have hbr0 : exp (cf * T * (1 - hW / (t * y0 - h))) - 1 ≤ 0 := by
    have h1 : cf * T * (1 - hW / (y0 - h)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hcf.le hT) hα0
    have := exp_le_exp.2 (harg.trans h1)
    rw [exp_zero] at this
    linarith
  have h3 : (t * y0 - h) ^ 2 / cf * (exp (cf * T * (1 - hW / (t * y0 - h))) - 1) ≤
      t ^ 2 * ((y0 - h) ^ 2 / cf * (exp (cf * T * (1 - hW / (y0 - h))) - 1)) := by
    calc (t * y0 - h) ^ 2 / cf * (exp (cf * T * (1 - hW / (t * y0 - h))) - 1)
        ≤ (t ^ 2 * (y0 - h) ^ 2) / cf * (exp (cf * T * (1 - hW / (t * y0 - h))) - 1) :=
          mul_le_mul_of_nonpos_right (div_le_div_of_nonneg_right hb hcf.le) hbr0
      _ ≤ (t ^ 2 * (y0 - h) ^ 2) / cf * (exp (cf * T * (1 - hW / (y0 - h))) - 1) :=
          mul_le_mul_of_nonneg_left hbr (div_nonneg (by positivity) hcf.le)
      _ = _ := by ring
  linarith

lemma Tfun_scale {n cW τ : ℝ} (hn : 0 < n) : Tfun (cW / n) (n * τ) = n * Tfun cW τ := by
  unfold Tfun
  have : n * τ * (cW / n) = τ * cW := by field_simp
  rw [this]
  by_cases hc : cW = 0
  · simp [hc]
  · field_simp

lemma cprRhs_scale {n T α β Q cf : ℝ} (hn : 0 < n) :
    cprRhs (n * T) α β Q (cf / n) = n * cprRhs T α β Q cf := by
  unfold cprRhs
  have : cf / n * (n * T) * α = cf * T * α := by field_simp
  rw [this]
  by_cases hc : cf = 0
  · simp [hc]; ring
  · field_simp

section tails

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The upper endpoint tail, conditional on (CP-R).** If `CPR μ p (c_W/n) (c_frame/n) h_W Q`
holds, `Q ≥ 0`, `a > 0`, `h ≥ 0`, `h_W ≥ 0`, `τ_+ > 0` and `E_+ ≤ 0`, then
`μ {p > z_+(Q)} ≤ exp (n E_+)`. -/
theorem tail_plus (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ} (hpm : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
    {n cW cf hW Q a h τ : ℝ} (hn : 0 < n) (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 ≤ hW)
    (hQ : 0 ≤ Q) (ha : 0 < a) (hh : 0 ≤ h) (hτ : 0 < τ)
    (hE : Eplus a h hW cW cf τ ≤ 0)
    (hCPR : CPR μ p (cW / n) (cf / n) hW Q) :
    μ.real {ω | zplus a h Q < p ω} ≤ Bplus n a h hW cW cf τ := by
  set z := zplus a h Q with hz
  have hz0 : (1 : ℝ) / 100 ≤ z := zplus_ge a h Q
  have hzpos : 0 < z := by linarith
  set x0 := √(1 / 100 / a) with hx0
  have hx0pos : 0 < x0 := Real.sqrt_pos.2 (by positivity)
  set x := √(z / a) with hx
  have hxx0 : x0 ≤ x := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hz0 ha.le)
  have hxpos : 0 < x := lt_of_lt_of_le hx0pos hxx0
  set t := x / x0 with ht
  have ht1 : 1 ≤ t := (one_le_div hx0pos).2 hxx0
  have hxt : x = t * x0 := by rw [ht]; field_simp
  have hzt : z = t ^ 2 * (1 / 100) := by
    have h1 : x ^ 2 = z / a := Real.sq_sqrt (by positivity)
    have h2 : x0 ^ 2 = 1 / 100 / a := Real.sq_sqrt (by positivity)
    have h3 : t ^ 2 = x ^ 2 / x0 ^ 2 := by rw [ht]; ring
    rw [h3, h1, h2]
    field_simp
  set w := wplus a h z with hw
  have hwpos : 0 < w := by
    rw [hw]; unfold wplus
    have : 0 < x + h := by linarith
    positivity
  have hsw : √w = x + h := by
    rw [hw]; unfold wplus
    exact Real.sqrt_sq (by linarith)
  have hQw : Q ≤ w := le_wplus_zplus hQ ha
  have hT : 0 < Tfun cW τ := Tfun_pos hcW hτ
  -- Chernoff
  have hint : Integrable (fun ω => exp (n * τ * p ω)) μ := integrable_exp_mul μ hpm hp0 hp1 _
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := p) z (mul_pos hn hτ).le hint
  have hsub : μ.real {ω | z < p ω} ≤ μ.real {ω | z ≤ p ω} :=
    measureReal_mono (fun ω hω => le_of_lt (show z < p ω from hω))
  have hmgf := hCPR.1 (n * τ) (mul_pos hn hτ) w hwpos
  rw [Tfun_scale hn, cprRhs_scale hn] at hmgf
  have hmgf' : mgf p μ (n * τ) ≤
      exp (n * cprRhs (Tfun cW τ) (alphaP hW w) (betaP hW w) Q cf) := hmgf
  -- the bracket is nonnegative, so `Q` can be replaced by `w`
  have hα : 0 ≤ alphaP hW w := by
    unfold alphaP
    have := div_nonneg hhW (Real.sqrt_nonneg w)
    linarith
  have hbr : 0 ≤ exp (cf * Tfun cW τ * alphaP hW w) - 1 := by
    have := Real.one_le_exp (mul_nonneg (mul_nonneg hcf.le hT.le) hα)
    linarith
  have hQw' : cprRhs (Tfun cW τ) (alphaP hW w) (betaP hW w) Q cf ≤
      cprRhs (Tfun cW τ) (alphaP hW w) (betaP hW w) w cf := by
    unfold cprRhs
    have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hQw hcf.le) hbr
    linarith
  -- the endpoint reduction
  have hscale := Hplus_scale (τ := τ) (z0 := 1 / 100) hT.le hcf hhW hh hx0pos ht1
  have hsw0 : √(wP a h) = x0 + h := by
    unfold wP
    exact Real.sqrt_sq (by linarith)
  have hE' : -τ * z + cprRhs (Tfun cW τ) (alphaP hW w) (betaP hW w) w cf ≤
      t ^ 2 * Eplus a h hW cW cf τ := by
    unfold Eplus cprRhs alphaP betaP
    rw [hsw, hsw0, hzt, hxt]
    have e1 : w = (t * x0 + h) ^ 2 := by rw [← hxt, ← hsw, Real.sq_sqrt hwpos.le]
    have e2 : wP a h = (x0 + h) ^ 2 := rfl
    rw [e1, e2]
    exact hscale
  have hE'' : t ^ 2 * Eplus a h hW cW cf τ ≤ Eplus a h hW cW cf τ := by
    have : 1 ≤ t ^ 2 := by nlinarith
    nlinarith
  calc μ.real {ω | z < p ω} ≤ exp (-(n * τ) * z) * mgf p μ (n * τ) := hsub.trans hch
    _ ≤ exp (-(n * τ) * z) * exp (n * cprRhs (Tfun cW τ) (alphaP hW w) (betaP hW w) Q cf) :=
        mul_le_mul_of_nonneg_left hmgf' (exp_pos _).le
    _ = exp (n * (-τ * z + cprRhs (Tfun cW τ) (alphaP hW w) (betaP hW w) Q cf)) := by
        rw [← exp_add]; congr 1; ring
    _ ≤ exp (n * Eplus a h hW cW cf τ) := by
        refine exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hn.le)
        linarith
    _ = Bplus n a h hW cW cf τ := rfl

/-- **The lower endpoint tail, conditional on (CP-R).** If `CPR μ p (c_W/n) (c_frame/n) h_W Q`
holds, `Q ≥ 0`, `a > 0`, `h ≥ 0`, `h_W ≥ 0`, `τ_- < 0`, `E_- ≤ 0`, the side conditions
`√(0.01/a) > h + h_W` and `√(0.01/a) ≥ 2h` hold, and `z_-(Q) > 1/1000`, then
`μ {p < z_-(Q)} ≤ exp (n E_-)`. -/
theorem tail_minus (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ} (hpm : Measurable p)
    (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
    {n cW cf hW Q a h τ : ℝ} (hn : 0 < n) (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 ≤ hW)
    (hQ : 0 ≤ Q) (ha : 0 < a) (hh : 0 ≤ h) (hτ : τ < 0)
    (hside1 : h + hW < √(1 / 100 / a)) (hside2 : 2 * h ≤ √(1 / 100 / a))
    (hE : Eminus a h hW cW cf τ ≤ 0)
    (hCPR : CPR μ p (cW / n) (cf / n) hW Q)
    (hzQ : 1 / 1000 < zminus a h Q) :
    μ.real {ω | p ω < zminus a h Q} ≤ Bminus n a h hW cW cf τ := by
  set z := zminus a h Q with hz
  set y0 := √(1 / 100 / a) with hy0
  have hy0pos : 0 < y0 := Real.sqrt_pos.2 (by positivity)
  have hy : √(10 * z / a) = √Q + h := sqrt_ten_zminus ha hh
  set y := √Q + h with hydef
  have hyy0 : y0 ≤ y := by
    rw [← hy, hy0]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff_of_pos_right ha]
    linarith
  set t := y / y0 with ht
  have ht1 : 1 ≤ t := (one_le_div hy0pos).2 hyy0
  have hyt : y = t * y0 := by rw [ht]; field_simp
  have hzt : z = t ^ 2 * (1 / 1000) := by
    have h1 : y ^ 2 = 10 * z / a := by rw [← hy]; exact Real.sq_sqrt (by positivity)
    have h2 : y0 ^ 2 = 1 / 100 / a := Real.sq_sqrt (by positivity)
    have h3 : t ^ 2 = y ^ 2 / y0 ^ 2 := by rw [ht]; ring
    rw [h3, h1, h2]
    field_simp
    ring
  have hsQ : √Q = t * y0 - h := by rw [← hyt, hydef]; ring
  have hWQ : hW < √Q := by
    rw [hsQ, ← hyt]; linarith
  have hT : Tfun cW τ < 0 := Tfun_neg hcW hτ
  -- Chernoff
  have hint : Integrable (fun ω => exp (n * τ * p ω)) μ := integrable_exp_mul μ hpm hp0 hp1 _
  have hch := measure_le_le_exp_mul_mgf (μ := μ) (X := p) z (mul_neg_of_pos_of_neg hn hτ).le hint
  have hsub : μ.real {ω | p ω < z} ≤ μ.real {ω | p ω ≤ z} :=
    measureReal_mono (fun ω hω => le_of_lt (show p ω < z from hω))
  have hmgf := hCPR.2 (n * τ) (mul_neg_of_pos_of_neg hn hτ) Q hWQ
  rw [Tfun_scale hn, cprRhs_scale hn] at hmgf
  have hmgf' : mgf p μ (n * τ) ≤
      exp (n * cprRhs (Tfun cW τ) (alphaM hW Q) (betaM hW Q) Q cf) := hmgf
  -- the endpoint reduction
  have hscale := Hminus_scale (τ := τ) (z0 := 1 / 1000) hT.le hcf hhW hh hside2
    (by linarith) ht1
  have hsw0 : √(wM a h) = y0 - h := by
    unfold wM
    exact Real.sqrt_sq (by linarith)
  have hE' : -τ * z + cprRhs (Tfun cW τ) (alphaM hW Q) (betaM hW Q) Q cf ≤
      t ^ 2 * Eminus a h hW cW cf τ := by
    unfold Eminus cprRhs alphaM betaM
    rw [hsQ, hsw0, hzt]
    have e1 : Q = (t * y0 - h) ^ 2 := by rw [← hsQ, Real.sq_sqrt hQ]
    have e2 : wM a h = (y0 - h) ^ 2 := rfl
    rw [e2]
    rw [e1]
    exact hscale
  have hE'' : t ^ 2 * Eminus a h hW cW cf τ ≤ Eminus a h hW cW cf τ := by
    have : 1 ≤ t ^ 2 := by nlinarith
    nlinarith
  calc μ.real {ω | p ω < z} ≤ exp (-(n * τ) * z) * mgf p μ (n * τ) := hsub.trans hch
    _ ≤ exp (-(n * τ) * z) * exp (n * cprRhs (Tfun cW τ) (alphaM hW Q) (betaM hW Q) Q cf) :=
        mul_le_mul_of_nonneg_left hmgf' (exp_pos _).le
    _ = exp (n * (-τ * z + cprRhs (Tfun cW τ) (alphaM hW Q) (betaM hW Q) Q cf)) := by
        rw [← exp_add]; congr 1; ring
    _ ≤ exp (n * Eminus a h hW cW cf τ) := by
        refine exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hn.le)
        linarith
    _ = Bminus n a h hW cW cf τ := rfl

end tails

end BstLean.Part156
