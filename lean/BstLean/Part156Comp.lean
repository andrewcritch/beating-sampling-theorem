import BstLean.Part156Out

/-!
# Part 156 (item 3): the two-stage composition bound (CP-R) from two ASSUMED one-stage bounds

The space is a product `Ω_W × Ω_A` of two probability spaces. `p : Ω_W × Ω_A → [0, 1]` is the
target. `P : Ω_A → [0, 1]` is the stand-in. The theorem `cpr_of_stages` ASSUMES

* (GP-W) for every `ω_A` and every real `s`:
  `E_{ω_W} exp (s p) ≤ exp (T_W(s) · v(ω_A))`, `v(ω_A) = E_{ω_W} p`,
  `T_W(s) = (exp (s L_W) - 1)/L_W`;
* (GP-A) for every real `u`: `E_{ω_A} exp (u P) ≤ exp (((exp (u L_A) - 1)/L_A) · Q)`, `Q = E P`;
* (REPL) `|√(v ω_A) - √(P ω_A)| ≤ h_W` for every `ω_A`;

and concludes the bound (CP-R) of the paper (`CPR`), for every `s > 0` with every anchor `w > 0`,
and for every `s < 0` with every anchor `w` such that `√w > h_W`.

The hypotheses (GP-W) and (GP-A) are consequences, in the paper, of the geometric Brascamp–Lieb
inequality for the Gaussian measure. That inequality is NOT proved in Lean. The lemma
`gp_of_primitive` only derives the form used here from the primitive form
`E exp (s p / L) ≤ (1 - q + q e^s)^(1/L)`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open MeasureTheory Real

/-- `T(s) = (exp (s L) - 1)/L`. -/
noncomputable def Tfun (L s : ℝ) : ℝ := (exp (s * L) - 1) / L

/-- `α_+(w) = 1 + h_W/√w`. -/
noncomputable def alphaP (hW w : ℝ) : ℝ := 1 + hW / √w

/-- `β_+(w) = h_W √w + h_W²`. -/
noncomputable def betaP (hW w : ℝ) : ℝ := hW * √w + hW ^ 2

/-- `α_-(w) = 1 - h_W/√w`. -/
noncomputable def alphaM (hW w : ℝ) : ℝ := 1 - hW / √w

/-- `β_-(w) = -h_W √w`. -/
noncomputable def betaM (hW w : ℝ) : ℝ := -(hW * √w)

/-- The right side of (CP-R): `T β + (Q/L_A)(exp (L_A T α) - 1)`. -/
noncomputable def cprRhs (T α β Q LA : ℝ) : ℝ := T * β + Q / LA * (exp (LA * T * α) - 1)

/-- The bound (CP-R) as a statement on the moment generating function of `p` under `μ`:
for `s > 0` and every anchor `w > 0`,
`E exp (s p) ≤ exp (T(s) β_+(w) + (Q/L_A)(exp (L_A T(s) α_+(w)) - 1))`;
for `s < 0` and every anchor `w` with `√w > h_W`, the same with `α_-`, `β_-`.
Here `T(s) = (exp (s L_W) - 1)/L_W`. -/
def CPR {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : Ω → ℝ) (LW LA hW Q : ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → ∀ w : ℝ, 0 < w →
      ∫ ω, exp (s * p ω) ∂μ ≤ exp (cprRhs (Tfun LW s) (alphaP hW w) (betaP hW w) Q LA)) ∧
  (∀ s : ℝ, s < 0 → ∀ w : ℝ, hW < √w →
      ∫ ω, exp (s * p ω) ∂μ ≤ exp (cprRhs (Tfun LW s) (alphaM hW w) (betaM hW w) Q LA))

lemma Tfun_pos {L s : ℝ} (hL : 0 < L) (hs : 0 < s) : 0 < Tfun L s := by
  unfold Tfun
  have : 1 < exp (s * L) := Real.one_lt_exp_iff.2 (mul_pos hs hL)
  exact div_pos (by linarith) hL

lemma Tfun_neg {L s : ℝ} (hL : 0 < L) (hs : s < 0) : Tfun L s < 0 := by
  unfold Tfun
  have : exp (s * L) < 1 := by
    have := Real.exp_lt_exp.2 (mul_neg_of_neg_of_pos hs hL)
    rwa [Real.exp_zero] at this
  exact div_neg_of_neg_of_pos (by linarith) hL

/-- A bounded measurable function has an integrable exponential. -/
lemma integrable_exp_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ ω, 0 ≤ f ω) (h1 : ∀ ω, f ω ≤ 1) (s : ℝ) :
    Integrable (fun ω => exp (s * f ω)) μ := by
  refine Integrable.mono' (integrable_const (exp |s|))
    (Real.measurable_exp.comp (hf.const_mul s)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  refine exp_le_exp.2 ?_
  calc s * f ω ≤ |s * f ω| := le_abs_self _
    _ = |s| * f ω := by rw [abs_mul, abs_of_nonneg (h0 ω)]
    _ ≤ |s| * 1 := mul_le_mul_of_nonneg_left (h1 ω) (abs_nonneg _)
    _ = |s| := mul_one _

/-- The upper affine comparison: if `0 ≤ v`, `0 ≤ P`, `√v ≤ √P + h_W`, `h_W ≥ 0`, `w > 0`, then
`v ≤ α_+(w) P + β_+(w)`. -/
lemma v_le_affine {v P hW w : ℝ} (hv : 0 ≤ v) (hP : 0 ≤ P) (hhW : 0 ≤ hW) (hw : 0 < w)
    (h : √v ≤ √P + hW) : v ≤ alphaP hW w * P + betaP hW w := by
  have hu : 0 < √w := Real.sqrt_pos.2 hw
  have h1 : v ≤ (√P + hW) ^ 2 := by
    calc v = (√v) ^ 2 := (Real.sq_sqrt hv).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hPs : (√P) ^ 2 = P := Real.sq_sqrt hP
  have h2 : 2 * √P ≤ P / √w + √w := by
    have : P / √w + √w - 2 * √P = (√P - √w) ^ 2 / √w := by
      field_simp
      nlinarith [hPs]
    have h3 : 0 ≤ (√P - √w) ^ 2 / √w := div_nonneg (sq_nonneg _) hu.le
    linarith
  unfold alphaP betaP
  have h4 : hW * (2 * √P) ≤ hW * (P / √w + √w) := mul_le_mul_of_nonneg_left h2 hhW
  have h5 : (1 + hW / √w) * P + (hW * √w + hW ^ 2) = P + hW * (P / √w + √w) + hW ^ 2 := by
    field_simp
    ring
  nlinarith [h1, h4, h5, hPs]

/-- The lower affine comparison: if `0 ≤ v`, `0 ≤ P`, `√v ≥ √P - h_W`, `h_W ≥ 0`, `√w > h_W`,
then `v ≥ α_-(w) P + β_-(w)`. -/
lemma affine_le_v {v P hW w : ℝ} (hv : 0 ≤ v) (hP : 0 ≤ P) (hhW : 0 ≤ hW) (hw : hW < √w)
    (h : √P - hW ≤ √v) : alphaM hW w * P + betaM hW w ≤ v := by
  have hu : 0 < √w := lt_of_le_of_lt hhW hw
  have hPs : (√P) ^ 2 = P := Real.sq_sqrt hP
  have hvs : (√v) ^ 2 = v := Real.sq_sqrt hv
  have hr : hW / √w < 1 := (div_lt_one hu).2 hw
  have hr0 : 0 ≤ hW / √w := div_nonneg hhW hu.le
  unfold alphaM betaM
  by_cases hc : hW ≤ √P
  · have h1 : (√P - hW) ^ 2 ≤ v := by
      calc (√P - hW) ^ 2 ≤ (√v) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
        _ = v := hvs
    have h2 : 2 * √P ≤ P / √w + √w := by
      have : P / √w + √w - 2 * √P = (√P - √w) ^ 2 / √w := by
        field_simp
        nlinarith [hPs]
      have h3 : 0 ≤ (√P - √w) ^ 2 / √w := div_nonneg (sq_nonneg _) hu.le
      linarith
    have h4 : hW * (2 * √P) ≤ hW * (P / √w + √w) := mul_le_mul_of_nonneg_left h2 hhW
    have h5 : (1 - hW / √w) * P + -(hW * √w) = P - hW * (P / √w + √w) := by
      field_simp
      ring
    nlinarith [h1, h4, h5, hPs]
  · have hc' : √P < hW := not_le.1 hc
    have hP2 : P ≤ hW ^ 2 := by
      calc P = (√P) ^ 2 := hPs.symm
        _ ≤ hW ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hc'.le 2
    have h6 : (1 - hW / √w) * P ≤ 1 * hW ^ 2 := by
      apply mul_le_mul (by linarith) hP2 hP (by norm_num)
    have h7 : hW * hW ≤ hW * √w := mul_le_mul_of_nonneg_left hw.le hhW
    nlinarith [h6, h7]

/-- The bound (CP-R) in the logarithmic form of the paper:
`log E exp (s p) ≤ T β + (Q/L_A)(exp (L_A T α) - 1)`. -/
theorem CPR.log_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : Ω → ℝ} {LW LA hW Q : ℝ} (h : CPR μ p LW LA hW Q)
    (hpm : Measurable p) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1) :
    (∀ s : ℝ, 0 < s → ∀ w : ℝ, 0 < w →
      log (∫ ω, exp (s * p ω) ∂μ) ≤ cprRhs (Tfun LW s) (alphaP hW w) (betaP hW w) Q LA) ∧
    (∀ s : ℝ, s < 0 → ∀ w : ℝ, hW < √w →
      log (∫ ω, exp (s * p ω) ∂μ) ≤ cprRhs (Tfun LW s) (alphaM hW w) (betaM hW w) Q LA) := by
  have hpos : ∀ s : ℝ, 0 < ∫ ω, exp (s * p ω) ∂μ := fun s =>
    integral_exp_pos (integrable_exp_mul μ hpm hp0 hp1 s)
  constructor
  · intro s hs w hw
    have := Real.log_le_log (hpos s) (h.1 s hs w hw)
    rwa [Real.log_exp] at this
  · intro s hs w hw
    have := Real.log_le_log (hpos s) (h.2 s hs w hw)
    rwa [Real.log_exp] at this

section composition

variable {ΩW ΩA : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩA]

/-- **Composition with root replacement (CP-R), conditional on (GP-W), (GP-A), (REPL).**
See the header of this file. `μW`, `μA` are probability measures; `p` and `P` are measurable with
values in `[0, 1]`. The conclusion is `CPR` for the product measure, with `Q = E P`. -/
theorem cpr_of_stages (μW : Measure ΩW) (μA : Measure ΩA) [IsProbabilityMeasure μW]
    [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hpm : Measurable p) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    {P : ΩA → ℝ} (hPm : Measurable P) (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {LW LA hW : ℝ} (hLW : 0 < LW) (hhW : 0 ≤ hW)
    (GPW : ∀ (ωA : ΩA) (s : ℝ),
      ∫ ωW, exp (s * p (ωW, ωA)) ∂μW ≤ exp (Tfun LW s * ∫ ωW, p (ωW, ωA) ∂μW))
    (GPA : ∀ u : ℝ, ∫ ωA, exp (u * P ωA) ∂μA ≤ exp (Tfun LA u * ∫ ωA, P ωA ∂μA))
    (REPL : ∀ ωA : ΩA, |√(∫ ωW, p (ωW, ωA) ∂μW) - √(P ωA)| ≤ hW) :
    CPR (μW.prod μA) p LW LA hW (∫ ωA, P ωA ∂μA) := by
  have hv0 : ∀ ωA, 0 ≤ ∫ ωW, p (ωW, ωA) ∂μW := fun ωA => integral_nonneg (fun _ => hp0 _)
  -- the common step
  have key : ∀ (s α β : ℝ),
      (∀ ωA, Tfun LW s * (∫ ωW, p (ωW, ωA) ∂μW) ≤ Tfun LW s * (α * P ωA + β)) →
      ∫ ω, exp (s * p ω) ∂(μW.prod μA) ≤ exp (cprRhs (Tfun LW s) α β (∫ ωA, P ωA ∂μA) LA) := by
    intro s α β hcmp
    have hint : Integrable (fun ω => exp (s * p ω)) (μW.prod μA) :=
      integrable_exp_mul _ hpm hp0 hp1 s
    rw [integral_prod_symm _ hint]
    have hint2 : Integrable (fun ωA => exp (Tfun LW s * β) * exp (Tfun LW s * α * P ωA)) μA :=
      (integrable_exp_mul μA hPm hP0 hP1 (Tfun LW s * α)).const_mul _
    calc ∫ ωA, ∫ ωW, exp (s * p (ωW, ωA)) ∂μW ∂μA
        ≤ ∫ ωA, exp (Tfun LW s * β) * exp (Tfun LW s * α * P ωA) ∂μA := by
          refine integral_mono hint.integral_prod_right hint2 (fun ωA => ?_)
          refine (GPW ωA s).trans ?_
          rw [← exp_add]
          refine exp_le_exp.2 ((hcmp ωA).trans (le_of_eq ?_))
          ring
      _ = exp (Tfun LW s * β) * ∫ ωA, exp (Tfun LW s * α * P ωA) ∂μA := integral_const_mul _ _
      _ ≤ exp (Tfun LW s * β) * exp (Tfun LA (Tfun LW s * α) * ∫ ωA, P ωA ∂μA) :=
          mul_le_mul_of_nonneg_left (GPA _) (exp_pos _).le
      _ = exp (cprRhs (Tfun LW s) α β (∫ ωA, P ωA ∂μA) LA) := by
          rw [← exp_add]
          congr 1
          unfold cprRhs
          simp only [Tfun]
          ring_nf
  constructor
  · intro s hs w hw
    refine key s _ _ (fun ωA => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Tfun_pos hLW hs).le
    refine v_le_affine (hv0 ωA) (hP0 ωA) hhW hw ?_
    have := (abs_le.1 (REPL ωA)).2
    linarith
  · intro s hs w hw
    refine key s _ _ (fun ωA => ?_)
    refine mul_le_mul_of_nonpos_left ?_ (Tfun_neg hLW hs).le
    refine affine_le_v (hv0 ωA) (hP0 ωA) hhW hw ?_
    have := (abs_le.1 (REPL ωA)).1
    linarith

end composition

/-- The form of (GP-W) and (GP-A) used here follows from the primitive form of the paper,
`E exp (s p / L) ≤ (1 - q + q e^s)^(1/L)` for every real `s`, with `L > 0` and `q ∈ [0, 1]`:
the inequality `log (1 + q (e^s - 1)) ≤ q (e^s - 1)`. -/
theorem gp_of_primitive {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : Ω → ℝ} {L q : ℝ}
    (hL : 0 < L) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ s : ℝ, ∫ ω, exp (s * p ω / L) ∂μ ≤ (1 - q + q * exp s) ^ (1 / L)) (s : ℝ) :
    ∫ ω, exp (s * p ω) ∂μ ≤ exp (Tfun L s * q) := by
  have h1 := h (s * L)
  have h2 : (fun ω => exp (s * L * p ω / L)) = fun ω => exp (s * p ω) := by
    funext ω
    congr 1
    field_simp
  rw [h2] at h1
  refine h1.trans ?_
  have hbase : 0 ≤ 1 - q + q * exp (s * L) := by
    have := (exp_pos (s * L)).le
    nlinarith
  have hle : 1 - q + q * exp (s * L) ≤ exp (q * (exp (s * L) - 1)) := by
    have := Real.add_one_le_exp (q * (exp (s * L) - 1))
    linarith
  calc (1 - q + q * exp (s * L)) ^ (1 / L)
      ≤ (exp (q * (exp (s * L) - 1))) ^ (1 / L) :=
        Real.rpow_le_rpow hbase hle (by positivity)
    _ = exp (Tfun L s * q) := by
        rw [← Real.exp_mul]
        congr 1
        unfold Tfun
        ring

end BstLean.Part156
