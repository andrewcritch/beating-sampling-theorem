import BstLean.Part162Int

/-!
# Part 162, item 3 (scalar part): one latitude, the good set of Proposition FL

Role: `delegations/statements/p162-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, proof of Proposition
`t7:p07:FL` (the good set `𝒳_s = {|f − f̄| ≤ d_w, |z − z̄| ≤ d_w, z² ≥ d_low}`, the window
`ε₀`, `L`, the variance factor, the mean shift `t7:p07:mean-shift`, the three contributions of
`ι_k`). Abstract setting: a probability space `(V, ν)` (one latitude), a good set `G`, the scale
`ψ` (`σ`, or `z` up to the factor `√γ_A`) and the location `φ` (`λ`, or `f` up to `√e_b`).

* `nrm ν G`: the normalized restriction `ν(·|G)`.
* `mean_shift`: `(E(f|G) − Ef)² ≤ ((1 − m)/m) Var f`; `shift_le`: `≤ √(η/(1−η))·sd`.
* `idx_scale`, `idx_eps_window`: the window `|ψ²/S₀ − 1| ≤ (1 + 2w_s/σ_l)² − 1`.
* `idx_phi_window`: `|φ − E(φ|G)| ≤ 2w_l` on `G`.
* `idx_eps_sq`: `E(ε² | G) ≤ 4(1 + w_s/σ_l)²/σ_l² · E((ψ − Eψ)² | G)`.
* `idx_eps_pt`, `idx_eps_mom`: pointwise and `p`-th moment bounds of `ε` (three contributions).
* `idx_del_sq`, `idx_del_mom`: the same for `a_c δ` (two contributions).
* `pow3_le`, `pow2_le`: weighted power means.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

section nrm

variable {V : Type*} [MeasurableSpace V] (ν : Measure V) [IsProbabilityMeasure ν] {G : Set V}

/-- The normalized restriction `ν(·|G) = ν(G)^{−1}·ν|_G`. -/
noncomputable def nrm (ν : Measure V) (G : Set V) : Measure V :=
  (ENNReal.ofReal (ν.real G))⁻¹ • ν.restrict G

lemma nrm_prob (hG : MeasurableSet G) (hm : 0 < ν.real G) : IsProbabilityMeasure (nrm ν G) := by
  constructor
  have hνs : ν G = ENNReal.ofReal (ν.real G) := by rw [ofReal_measureReal (measure_ne_top _ _)]
  rw [nrm, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hνs,
    smul_eq_mul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hm).ne' ENNReal.ofReal_ne_top]

lemma integral_nrm (hG : MeasurableSet G) (hm : 0 < ν.real G) (f : V → ℝ) :
    ∫ v, f v ∂nrm ν G = (ν.real G)⁻¹ * ∫ v, G.indicator f v ∂ν := by
  rw [nrm, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hm.le,
    integral_indicator hG, smul_eq_mul]

lemma nrm_ae_mem (hG : MeasurableSet G) : ∀ᵐ v ∂nrm ν G, v ∈ G := by
  rw [nrm]
  exact Measure.ae_smul_measure (ae_restrict_mem hG) _


variable {ν}

lemma integral_nrm_le (hG : MeasurableSet G) (hm : 0 < ν.real G) {g : V → ℝ}
    (hg0 : ∀ v, 0 ≤ g v) (hgi : Integrable g ν) :
    ∫ v, g v ∂nrm ν G ≤ (ν.real G)⁻¹ * ∫ v, g v ∂ν := by
  rw [integral_nrm ν hG hm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hm.le)
  exact integral_mono (hgi.indicator hG) hgi fun v => by
    by_cases hv : v ∈ G
    · simp [Set.indicator_of_mem hv]
    · simp only [Set.indicator_of_notMem hv]; exact hg0 v

/-- Bounded functions are integrable for a probability measure (local copy). -/
lemma intB {μ : Measure V} [IsProbabilityMeasure μ] {f : V → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ v, |f v| ≤ M) : Integrable f μ := int_bdd μ hf hM

lemma nrm_mean_mem (hG : MeasurableSet G) (hm : 0 < ν.real G) {f : V → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, |f v| ≤ M) {lo hi : ℝ} (hlh : ∀ v ∈ G, lo ≤ f v ∧ f v ≤ hi) :
    lo ≤ ∫ v, f v ∂nrm ν G ∧ ∫ v, f v ∂nrm ν G ≤ hi := by
  have hP := nrm_prob ν hG hm
  have hi' := intB (μ := nrm ν G) hf hM
  have hae := nrm_ae_mem ν hG
  constructor
  · have := integral_mono_ae (integrable_const lo) hi' (hae.mono fun v hv => (hlh v hv).1)
    simpa using this
  · have := integral_mono_ae hi' (integrable_const hi) (hae.mono fun v hv => (hlh v hv).2)
    simpa using this

lemma int_quad {μ : Measure V} [IsProbabilityMeasure μ] {f : V → ℝ} (hi : Integrable f μ)
    (hi2 : Integrable (fun v => f v ^ 2) μ) (a b c : ℝ) :
    ∫ v, (a * f v ^ 2 + b * f v + c) ∂μ = a * ∫ v, f v ^ 2 ∂μ + b * ∫ v, f v ∂μ + c := by
  rw [integral_add (f := fun v => a * f v ^ 2 + b * f v) (g := fun _ => c)
    ((hi2.const_mul a).add (hi.const_mul b)) (integrable_const c),
    integral_add (f := fun v => a * f v ^ 2) (g := fun v => b * f v) (hi2.const_mul a)
      (hi.const_mul b), integral_const_mul, integral_const_mul, integral_const]
  simp

/-- `∫ (f − E f)² ≤ ∫ (f − C)²` for a probability measure. -/
lemma var_le_sq_sub {μ : Measure V} [IsProbabilityMeasure μ] {f : V → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, |f v| ≤ M) (C : ℝ) :
    ∫ v, (f v - ∫ w, f w ∂μ) ^ 2 ∂μ ≤ ∫ v, (f v - C) ^ 2 ∂μ := by
  have hi := intB (μ := μ) hf hM
  have hi2 : Integrable (fun v => f v ^ 2) μ := intB (hf.pow_const 2) (M := M ^ 2) fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_abs (f v)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hM v) 2
  set m := ∫ w, f w ∂μ
  have e : ∀ C : ℝ, ∫ v, (f v - C) ^ 2 ∂μ = ∫ v, f v ^ 2 ∂μ - 2 * C * m + C ^ 2 := fun C => by
    have : ∀ v, (f v - C) ^ 2 = 1 * f v ^ 2 + (-2 * C) * f v + C ^ 2 := fun v => by ring
    simp_rw [this]
    rw [int_quad hi hi2]
    ring
  rw [e, e]
  nlinarith [sq_nonneg (m - C)]

/-- Jensen: `(E f)² ≤ E f²`. -/
lemma mean_sq_le {μ : Measure V} [IsProbabilityMeasure μ] {f : V → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, |f v| ≤ M) : (∫ v, f v ∂μ) ^ 2 ≤ ∫ v, f v ^ 2 ∂μ := by
  have h := var_le_sq_sub hf hM (μ := μ) 0
  have hi := intB (μ := μ) hf hM
  have hi2 : Integrable (fun v => f v ^ 2) μ := intB (hf.pow_const 2) (M := M ^ 2) fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_abs (f v)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hM v) 2
  have h0 : 0 ≤ ∫ v, (f v - ∫ w, f w ∂μ) ^ 2 ∂μ := integral_nonneg fun v => sq_nonneg _
  have e : ∫ v, (f v - ∫ w, f w ∂μ) ^ 2 ∂μ = ∫ v, f v ^ 2 ∂μ - (∫ w, f w ∂μ) ^ 2 := by
    have : ∀ v, (f v - ∫ w, f w ∂μ) ^ 2 =
        1 * f v ^ 2 + (-2 * ∫ w, f w ∂μ) * f v + (∫ w, f w ∂μ) ^ 2 := fun v => by ring
    simp_rw [this]
    rw [int_quad hi hi2]
    ring
  linarith

/-- **Mean shift** (formula `t7:p07:mean-shift`): `(E(f | G) − E f)² ≤ ((1 − m)/m)·Var f`,
`m = ν(G)`. -/
lemma mean_shift (hG : MeasurableSet G) (hm : 0 < ν.real G) {f : V → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, |f v| ≤ M) :
    (∫ v, f v ∂nrm ν G - ∫ v, f v ∂ν) ^ 2 ≤
      (1 - ν.real G) / ν.real G * ∫ v, (f v - ∫ w, f w ∂ν) ^ 2 ∂ν := by
  set m := ν.real G with hmd
  set μf := ∫ w, f w ∂ν
  have hi := intB (μ := ν) hf hM
  -- E(f|G) − E f = m⁻¹ E[(f − μf)(1_G − m)]
  set X : V → ℝ := fun v => f v - μf
  set Y : V → ℝ := fun v => G.indicator 1 v - m
  have mX : Measurable X := hf.sub_const _
  have mY : Measurable Y := (measurable_one.indicator hG).sub_const _
  have bX : ∀ v, |X v| ≤ M + |μf| := fun v => (abs_sub _ _).trans (by linarith [hM v])
  have bY : ∀ v, |Y v| ≤ 1 + |m| := fun v => by
    refine (abs_sub _ _).trans ?_
    have : |G.indicator (1 : V → ℝ) v| ≤ 1 := by
      by_cases hv : v ∈ G <;> simp [hv]
    linarith
  have iX := intB (μ := ν) mX bX
  have key : ∫ v, f v ∂nrm ν G - μf = m⁻¹ * ∫ v, X v * Y v ∂ν := by
    rw [integral_nrm ν hG hm]
    have e1 : ∫ v, X v * Y v ∂ν = ∫ v, G.indicator f v ∂ν - m * μf := by
      have : ∀ v, X v * Y v = G.indicator f v - μf * G.indicator 1 v - m * f v + m * μf := fun v => by
        simp only [X, Y]
        by_cases hv : v ∈ G <;> simp [hv] <;> ring
      simp_rw [this]
      have i1 : Integrable (G.indicator f) ν := hi.indicator hG
      have i2 : Integrable (fun v => μf * G.indicator (1 : V → ℝ) v) ν :=
        ((integrable_const (1 : ℝ)).indicator hG).const_mul _
      rw [integral_add (f := fun v => G.indicator f v - μf * G.indicator 1 v - m * f v)
          (g := fun _ => m * μf) ((i1.sub i2).sub (hi.const_mul m)) (integrable_const _),
        integral_sub (f := fun v => G.indicator f v - μf * G.indicator 1 v) (g := fun v => m * f v)
          (i1.sub i2) (hi.const_mul m),
        integral_sub (f := fun v => G.indicator f v) (g := fun v => μf * G.indicator 1 v) i1 i2,
        integral_const_mul, integral_const_mul, integral_indicator_one hG, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul, hmd]
      ring
    rw [e1, mul_sub, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
  have cs := BstLean.Part138.cs_sq ν (f := X) (g := Y)
    (intB (mX.pow_const 2) (M := (M + |μf|) ^ 2) fun v => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_abs (X v)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (bX v) 2)
    (intB (mY.pow_const 2) (M := (1 + |m|) ^ 2) fun v => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_abs (Y v)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (bY v) 2)
    (intB (mX.mul mY) (M := (M + |μf|) * (1 + |m|)) fun v => by
      rw [abs_mul]
      exact mul_le_mul (bX v) (bY v) (abs_nonneg _) ((abs_nonneg _).trans (bX v)))
  have hY2 : ∫ v, Y v ^ 2 ∂ν = m * (1 - m) := by
    have : ∀ v, Y v ^ 2 = (1 - 2 * m) * G.indicator 1 v + m ^ 2 := fun v => by
      simp only [Y]; by_cases hv : v ∈ G <;> simp [hv] <;> ring
    simp_rw [this]
    rw [integral_add (f := fun v => (1 - 2 * m) * G.indicator 1 v) (g := fun _ => m ^ 2)
      (((integrable_const (1 : ℝ)).indicator hG).const_mul _) (integrable_const _),
      integral_const_mul, integral_indicator_one hG, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, hmd]
    ring
  rw [key, mul_pow]
  rw [hY2] at cs
  have hm1 : m ≤ 1 := by rw [hmd]; exact measureReal_le_one
  have h3 : (m⁻¹) ^ 2 * (∫ v, X v * Y v ∂ν) ^ 2 ≤ (m⁻¹) ^ 2 * ((∫ v, X v ^ 2 ∂ν) * (m * (1 - m))) :=
    mul_le_mul_of_nonneg_left cs (sq_nonneg _)
  refine h3.trans (le_of_eq ?_)
  field_simp
  ring

end nrm

/-- The weighted power mean for three terms. -/
lemma pow3_le (k : ℕ) {x1 x2 x3 c1 c2 c3 : ℝ} (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (p1 : 0 < c1) (p2 : 0 < c2) (p3 : 0 < c3) :
    (x1 + x2 + x3) ^ k ≤ (c1 + c2 + c3) ^ k *
      (c1 / (c1 + c2 + c3) * (x1 / c1) ^ k + c2 / (c1 + c2 + c3) * (x2 / c2) ^ k +
        c3 / (c1 + c2 + c3) * (x3 / c3) ^ k) := by
  set C := c1 + c2 + c3 with hC
  have hC0 : 0 < C := by positivity
  have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin 3))
    ![c1 / C, c2 / C, c3 / C] ![x1 * C / c1, x2 * C / c2, x3 * C / c3]
    (fun i _ => by fin_cases i <;> simp <;> positivity)
    (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← add_div, ← add_div, ← hC, div_self hC0.ne'])
    (fun i _ => by fin_cases i <;> simp <;> positivity) k
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h
  have e1 : c1 / C * (x1 * C / c1) + c2 / C * (x2 * C / c2) + c3 / C * (x3 * C / c3) =
      x1 + x2 + x3 := by field_simp
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  have e2 : ∀ (x c : ℝ), 0 < c → c / C * (x * C / c) ^ k = C ^ k * (c / C * (x / c) ^ k) := by
    intro x c hc
    rw [show x * C / c = C * (x / c) by field_simp, mul_pow]; ring
  rw [e2 x1 c1 p1, e2 x2 c2 p2, e2 x3 c3 p3]
  ring

/-- The weighted power mean for two terms. -/
lemma pow2_le (k : ℕ) {x1 x2 c1 c2 : ℝ} (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (p1 : 0 < c1) (p2 : 0 < c2) :
    (x1 + x2) ^ k ≤ (c1 + c2) ^ k *
      (c1 / (c1 + c2) * (x1 / c1) ^ k + c2 / (c1 + c2) * (x2 / c2) ^ k) := by
  set C := c1 + c2 with hC
  have hC0 : 0 < C := by positivity
  have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin 2))
    ![c1 / C, c2 / C] ![x1 * C / c1, x2 * C / c2]
    (fun i _ => by fin_cases i <;> simp <;> positivity)
    (by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [← add_div, ← hC, div_self hC0.ne'])
    (fun i _ => by fin_cases i <;> simp <;> positivity) k
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  have e1 : c1 / C * (x1 * C / c1) + c2 / C * (x2 * C / c2) = x1 + x2 := by field_simp
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  have e2 : ∀ (x c : ℝ), 0 < c → c / C * (x * C / c) ^ k = C ^ k * (c / C * (x / c) ^ k) := by
    intro x c hc
    rw [show x * C / c = C * (x / c) by field_simp, mul_pow]; ring
  rw [e2 x1 c1 p1, e2 x2 c2 p2]
  ring

section idx

variable {V : Type*} [MeasurableSpace V] {ν : Measure V} [IsProbabilityMeasure ν] {G : Set V}

lemma sq_bound_of_abs {f : V → ℝ} {M : ℝ} (hM : ∀ v, |f v| ≤ M) : ∀ v, |f v ^ 2| ≤ M ^ 2 :=
  fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_abs (f v)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hM v) 2

/-- **The scale window on a good set** (proof of Prop. `t7:p07:FL`): if on `G`
`|ψ − Eψ| ≤ w_s` and `ψ ≥ σ_l > 0`, then `S₀ = E(ψ² | G) ≥ σ_l²` and on `G`
`|ψ²/S₀ − 1| ≤ (1 + 2w_s/σ_l)² − 1`. Also the lower and upper ends `lo ≤ ψ, √S₀ ≤ hi` with
`hi ≤ lo + 2w_s`, `lo ≥ σ_l`. -/
lemma idx_scale (hG : MeasurableSet G) (hm : 0 < ν.real G) {ψ : V → ℝ} (mψ : Measurable ψ)
    {Mψ : ℝ} (bψ : ∀ v, |ψ v| ≤ Mψ) {ws σl : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl)
    (hGψ : ∀ v ∈ G, |ψ v - ∫ w, ψ w ∂ν| ≤ ws ∧ σl ≤ ψ v) :
    ∃ lo hi : ℝ, σl ≤ lo ∧ hi ≤ lo + 2 * ws ∧ (∀ v ∈ G, lo ≤ ψ v ∧ ψ v ≤ hi) ∧
      lo ^ 2 ≤ ∫ v, ψ v ^ 2 ∂nrm ν G ∧ ∫ v, ψ v ^ 2 ∂nrm ν G ≤ hi ^ 2 ∧
      lo ≤ ∫ v, ψ v ∂nrm ν G ∧ ∫ v, ψ v ∂nrm ν G ≤ hi := by
  set ψb := ∫ w, ψ w ∂ν
  refine ⟨max σl (ψb - ws), ψb + ws, le_max_left _ _, ?_, ?_, ?_⟩
  · have := le_max_right σl (ψb - ws); linarith
  · intro v hv
    obtain ⟨h1, h2⟩ := hGψ v hv
    refine ⟨max_le h2 (by linarith [(abs_le.mp h1).1]), by linarith [(abs_le.mp h1).2]⟩
  have hlo0 : 0 < max σl (ψb - ws) := lt_of_lt_of_le hσl (le_max_left _ _)
  have hG2 : ∀ v ∈ G, max σl (ψb - ws) ^ 2 ≤ ψ v ^ 2 ∧ ψ v ^ 2 ≤ (ψb + ws) ^ 2 := fun v hv => by
    obtain ⟨h1, h2⟩ := hGψ v hv
    have a1 : max σl (ψb - ws) ≤ ψ v := max_le h2 (by linarith [(abs_le.mp h1).1])
    have a2 : ψ v ≤ ψb + ws := by linarith [(abs_le.mp h1).2]
    exact ⟨pow_le_pow_left₀ hlo0.le a1 2, pow_le_pow_left₀ (hlo0.le.trans a1) a2 2⟩
  obtain ⟨s1, s2⟩ := nrm_mean_mem hG hm (mψ.pow_const 2) (sq_bound_of_abs bψ) hG2
  obtain ⟨t1, t2⟩ := nrm_mean_mem hG hm mψ bψ (lo := max σl (ψb - ws)) (hi := ψb + ws) fun v hv => by
    obtain ⟨h1, h2⟩ := hGψ v hv
    exact ⟨max_le h2 (by linarith [(abs_le.mp h1).1]), by linarith [(abs_le.mp h1).2]⟩
  exact ⟨s1, s2, t1, t2⟩

/-- The relative window `|ψ²/S₀ − 1| ≤ (1 + 2w_s/σ_l)² − 1` on `G`. -/
lemma idx_eps_window {lo hi S ws σl x : ℝ} (hσl : 0 < σl) (hws : 0 ≤ ws) (hlo : σl ≤ lo)
    (hhi : hi ≤ lo + 2 * ws) (hS1 : lo ^ 2 ≤ S) (hS2 : S ≤ hi ^ 2) (hx1 : lo ≤ x) (hx2 : x ≤ hi) :
    |x ^ 2 / S - 1| ≤ (1 + 2 * ws / σl) ^ 2 - 1 := by
  have hlo0 : 0 < lo := lt_of_lt_of_le hσl hlo
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS1
  set r := 1 + 2 * ws / σl with hr
  have hr1 : 1 ≤ r := by
    have : 0 ≤ 2 * ws / σl := by positivity
    rw [hr]; linarith
  have hhr : hi ≤ lo * r := by
    rw [hr, mul_add, mul_one]
    have : 2 * ws ≤ lo * (2 * ws / σl) := by
      rw [mul_div_assoc', le_div_iff₀ hσl]; nlinarith
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le hlo0 hx1
  -- upper: x²/S ≤ r²
  have u : x ^ 2 / S ≤ r ^ 2 := by
    rw [div_le_iff₀ hS0]
    have h1 : x ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hx0.le hx2 2
    have h2 : hi ^ 2 ≤ (lo * r) ^ 2 := pow_le_pow_left₀ (hx0.le.trans hx2) hhr 2
    have h3 : (lo * r) ^ 2 = r ^ 2 * lo ^ 2 := by ring
    have h4 : r ^ 2 * lo ^ 2 ≤ r ^ 2 * S := mul_le_mul_of_nonneg_left hS1 (sq_nonneg r)
    linarith
  -- lower: x²/S ≥ 1/r²
  have l : 1 / r ^ 2 ≤ x ^ 2 / S := by
    rw [div_le_div_iff₀ (by positivity) hS0, one_mul]
    have h1 : lo ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hlo0.le hx1 2
    have h2 : S ≤ (lo * r) ^ 2 := hS2.trans (pow_le_pow_left₀ (hx0.le.trans hx2) hhr 2)
    have h3 : (lo * r) ^ 2 = lo ^ 2 * r ^ 2 := by ring
    nlinarith [sq_nonneg r]
  have hq : 1 - 1 / r ^ 2 ≤ r ^ 2 - 1 := by
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    have h0 : 0 < r ^ 2 := by positivity
    have h1 : 1 / r ^ 2 ≤ 1 := by rw [div_le_one h0]; exact hr2
    have h2 : 0 ≤ 1 / r ^ 2 := by positivity
    have h3 : r ^ 2 * (1 / r ^ 2) = 1 := by field_simp
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- `E(ψ²/S₀ − 1)² ≤ 4(1 + w_s/σ_l)²/σ_l² · E(ψ − Eψ)²` for the normalized good-set measure
(the variance factor of Prop. `t7:p07:FL`). -/
lemma idx_eps_sq (hG : MeasurableSet G) (hm : 0 < ν.real G) {ψ : V → ℝ} (mψ : Measurable ψ)
    {Mψ : ℝ} (bψ : ∀ v, |ψ v| ≤ Mψ) {ws σl : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl)
    (hGψ : ∀ v ∈ G, |ψ v - ∫ w, ψ w ∂ν| ≤ ws ∧ σl ≤ ψ v) :
    ∫ v, (ψ v ^ 2 / ∫ w, ψ w ^ 2 ∂nrm ν G - 1) ^ 2 ∂nrm ν G ≤
      4 * (1 + ws / σl) ^ 2 / σl ^ 2 * ∫ v, (ψ v - ∫ w, ψ w ∂ν) ^ 2 ∂nrm ν G := by
  have hP := nrm_prob ν hG hm
  obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, t1, t2⟩ := idx_scale hG hm mψ bψ hws hσl hGψ
  set P := nrm ν G
  set S0 := ∫ w, ψ w ^ 2 ∂P
  set ψg := ∫ w, ψ w ∂P
  set ψb := ∫ w, ψ w ∂ν
  have hg0 : σl ≤ ψg := hlo.trans t1
  have hgp : 0 < ψg := lt_of_lt_of_le hσl hg0
  have hSg : ψg ^ 2 ≤ S0 := mean_sq_le mψ bψ
  have hS0 : 0 < S0 := lt_of_lt_of_le (by positivity) hSg
  have b2 := sq_bound_of_abs bψ
  -- step 1: E ε² = E(ψ² − S0)²/S0²
  have e1 : ∫ v, (ψ v ^ 2 / S0 - 1) ^ 2 ∂P = (∫ v, (ψ v ^ 2 - S0) ^ 2 ∂P) / S0 ^ 2 := by
    rw [← integral_div]
    congr 1; funext v; field_simp
  -- step 2: variance ≤ second moment about ψg²
  have h2 : ∫ v, (ψ v ^ 2 - S0) ^ 2 ∂P ≤ ∫ v, (ψ v ^ 2 - ψg ^ 2) ^ 2 ∂P :=
    var_le_sq_sub (mψ.pow_const 2) b2 (ψg ^ 2)
  -- step 3: pointwise on G
  have bψd : ∀ v, |ψ v - ψg| ≤ Mψ + |ψg| := fun v => (abs_sub _ _).trans (by linarith [bψ v])
  have bψb : ∀ v, |ψ v - ψb| ≤ Mψ + |ψb| := fun v => (abs_sub _ _).trans (by linarith [bψ v])
  have i3 : Integrable (fun v => (2 * ψg + 2 * ws) ^ 2 * (ψ v - ψg) ^ 2) P :=
    (intB ((mψ.sub_const _).pow_const 2) (sq_bound_of_abs bψd)).const_mul _
  have i4 : Integrable (fun v => (ψ v ^ 2 - ψg ^ 2) ^ 2) P :=
    intB (((mψ.pow_const 2).sub_const _).pow_const 2) (sq_bound_of_abs (M := Mψ ^ 2 + |ψg ^ 2|)
      fun v => (abs_sub _ _).trans (by linarith [b2 v]))
  have h3 : ∫ v, (ψ v ^ 2 - ψg ^ 2) ^ 2 ∂P ≤ ∫ v, (2 * ψg + 2 * ws) ^ 2 * (ψ v - ψg) ^ 2 ∂P := by
    refine integral_mono_ae i4 i3 ((nrm_ae_mem ν hG).mono fun v hv => ?_)
    obtain ⟨a1, a2⟩ := hG' v hv
    have hψ0 : 0 ≤ ψ v := (lt_of_lt_of_le hσl (hlo.trans a1)).le
    have k1 : 0 ≤ ψ v + ψg := by linarith
    have k2 : ψ v + ψg ≤ 2 * ψg + 2 * ws := by linarith
    have e : (ψ v ^ 2 - ψg ^ 2) ^ 2 = (ψ v + ψg) ^ 2 * (ψ v - ψg) ^ 2 := by ring
    beta_reduce
    rw [e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ k1 k2 2) (sq_nonneg _)
  have h4 : ∫ v, (ψ v - ψg) ^ 2 ∂P ≤ ∫ v, (ψ v - ψb) ^ 2 ∂P := var_le_sq_sub mψ bψ ψb
  rw [integral_const_mul] at h3
  -- step 4: constants
  have W0 : 0 ≤ ∫ v, (ψ v - ψb) ^ 2 ∂P := integral_nonneg fun v => sq_nonneg _
  have kc : (2 * ψg + 2 * ws) ^ 2 / S0 ^ 2 ≤ 4 * (1 + ws / σl) ^ 2 / σl ^ 2 := by
    have q1 : (2 * ψg + 2 * ws) ^ 2 / S0 ^ 2 ≤ (2 * ψg + 2 * ws) ^ 2 / (ψg ^ 2) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ (by positivity) hSg 2)
    have q2 : (2 * ψg + 2 * ws) ^ 2 / (ψg ^ 2) ^ 2 = 4 * ((ψg + ws) / ψg ^ 2) ^ 2 := by
      field_simp; ring
    have q3 : (ψg + ws) / ψg ^ 2 ≤ (σl + ws) / σl ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : σl ^ 2 * (ψg + ws) ≤ ψg ^ 2 * (σl + ws) := by
        have hd : 0 ≤ ψg - σl := by linarith
        nlinarith [mul_nonneg hd hσl.le, mul_nonneg hd hws, mul_nonneg (mul_nonneg hd hσl.le) hgp.le,
          mul_nonneg (mul_nonneg hd hws) (add_nonneg hgp.le hσl.le)]
      linarith
    have q4 : 4 * ((σl + ws) / σl ^ 2) ^ 2 = 4 * (1 + ws / σl) ^ 2 / σl ^ 2 := by
      field_simp
    calc (2 * ψg + 2 * ws) ^ 2 / S0 ^ 2 ≤ (2 * ψg + 2 * ws) ^ 2 / (ψg ^ 2) ^ 2 := q1
      _ = 4 * ((ψg + ws) / ψg ^ 2) ^ 2 := q2
      _ ≤ 4 * ((σl + ws) / σl ^ 2) ^ 2 := by
          gcongr
      _ = _ := q4
  rw [e1, div_le_iff₀ (by positivity)]
  calc ∫ v, (ψ v ^ 2 - S0) ^ 2 ∂P ≤ (2 * ψg + 2 * ws) ^ 2 * ∫ v, (ψ v - ψb) ^ 2 ∂P := by
        have := mul_le_mul_of_nonneg_left h4 (sq_nonneg (2 * ψg + 2 * ws))
        linarith
    _ = (2 * ψg + 2 * ws) ^ 2 / S0 ^ 2 * (∫ v, (ψ v - ψb) ^ 2 ∂P) * S0 ^ 2 := by
        field_simp
    _ ≤ 4 * (1 + ws / σl) ^ 2 / σl ^ 2 * (∫ v, (ψ v - ψb) ^ 2 ∂P) * S0 ^ 2 := by
        gcongr

lemma dec_frac {t ws σl : ℝ} (hσl : 0 < σl) (hws : 0 ≤ ws) (ht : σl ≤ t) :
    (t + ws) / t ^ 2 ≤ (σl + ws) / σl ^ 2 := by
  have htp : 0 < t := lt_of_lt_of_le hσl ht
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hd : 0 ≤ t - σl := by linarith
  nlinarith [mul_nonneg hd hσl.le, mul_nonneg hd hws, mul_nonneg (mul_nonneg hd hσl.le) htp.le,
    mul_nonneg (mul_nonneg hd hws) (add_nonneg htp.le hσl.le)]

lemma var_eq {μ : Measure V} [IsProbabilityMeasure μ] {f : V → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, |f v| ≤ M) :
    ∫ v, (f v - ∫ w, f w ∂μ) ^ 2 ∂μ = ∫ v, f v ^ 2 ∂μ - (∫ w, f w ∂μ) ^ 2 := by
  have hi := intB (μ := μ) hf hM
  have hi2 : Integrable (fun v => f v ^ 2) μ := intB (hf.pow_const 2) (sq_bound_of_abs hM)
  have : ∀ v, (f v - ∫ w, f w ∂μ) ^ 2 =
      1 * f v ^ 2 + (-2 * ∫ w, f w ∂μ) * f v + (∫ w, f w ∂μ) ^ 2 := fun v => by ring
  simp_rw [this]
  rw [int_quad hi hi2]
  ring

/-- **Pointwise bound of `ε` on the good set** (the three contributions of `ι_k` in Prop.
`t7:p07:FL`): with `ψ₀ = √S₀`, `ψ_g = E(ψ | G)`, `W = E((ψ − Eψ)² | G)`, on `G`:
`|ψ²/S₀ − 1| ≤ (2(σ_l + w_s)/σ_l²)·(|ψ − Eψ| + |Eψ − ψ_g| + W/(2σ_l))`. -/
lemma idx_eps_pt (hG : MeasurableSet G) (hm : 0 < ν.real G) {ψ : V → ℝ} (mψ : Measurable ψ)
    {Mψ : ℝ} (bψ : ∀ v, |ψ v| ≤ Mψ) {ws σl : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl)
    (hGψ : ∀ v ∈ G, |ψ v - ∫ w, ψ w ∂ν| ≤ ws ∧ σl ≤ ψ v) :
    ∀ v ∈ G, |ψ v ^ 2 / ∫ w, ψ w ^ 2 ∂nrm ν G - 1| ≤ 2 * (σl + ws) / σl ^ 2 *
      (|ψ v - ∫ w, ψ w ∂ν| + |∫ w, ψ w ∂ν - ∫ w, ψ w ∂nrm ν G| +
        (∫ w, (ψ w - ∫ u, ψ u ∂ν) ^ 2 ∂nrm ν G) / (2 * σl)) := by
  have hP := nrm_prob ν hG hm
  obtain ⟨lo, hi, hlo, hhi, hG', s1, s2, t1, t2⟩ := idx_scale hG hm mψ bψ hws hσl hGψ
  set P := nrm ν G
  set S0 := ∫ w, ψ w ^ 2 ∂P
  set ψg := ∫ w, ψ w ∂P
  set ψb := ∫ w, ψ w ∂ν
  set W := ∫ w, (ψ w - ψb) ^ 2 ∂P
  have hlo0 : 0 < lo := lt_of_lt_of_le hσl hlo
  have hg0 : σl ≤ ψg := hlo.trans t1
  have hgp : 0 < ψg := lt_of_lt_of_le hσl hg0
  have hSg : ψg ^ 2 ≤ S0 := mean_sq_le mψ bψ
  have hS0 : 0 < S0 := lt_of_lt_of_le (by positivity) hSg
  set ψ0 := √S0 with hψ0
  have hψ0sq : ψ0 ^ 2 = S0 := Real.sq_sqrt hS0.le
  have hψ0lo : lo ≤ ψ0 := by
    rw [hψ0, show lo = √(lo ^ 2) from (Real.sqrt_sq hlo0.le).symm]; exact Real.sqrt_le_sqrt s1
  have hψ0hi : ψ0 ≤ hi := by
    have hhi0 : 0 ≤ hi := hlo0.le.trans (t1.trans t2)
    rw [hψ0, show hi = √(hi ^ 2) from (Real.sqrt_sq hhi0).symm]; exact Real.sqrt_le_sqrt s2
  have hψ0g : ψg ≤ ψ0 := by
    rw [hψ0, show ψg = √(ψg ^ 2) from (Real.sqrt_sq hgp.le).symm]; exact Real.sqrt_le_sqrt hSg
  have hψ0p : 0 < ψ0 := lt_of_lt_of_le hgp hψ0g
  -- `S0 − ψg² ≤ W`
  have hvar : S0 - ψg ^ 2 ≤ W := by
    have := var_eq (μ := P) mψ bψ
    have h2 := var_le_sq_sub (μ := P) mψ bψ ψb
    linarith
  have hgap : ψ0 - ψg ≤ W / (2 * σl) := by
    have e : ψ0 - ψg = (S0 - ψg ^ 2) / (ψ0 + ψg) := by
      rw [← hψ0sq]; field_simp; ring
    rw [e, div_le_div_iff₀ (by linarith) (by positivity)]
    have hW0 : 0 ≤ S0 - ψg ^ 2 := by linarith
    have : 2 * σl ≤ ψ0 + ψg := by linarith
    nlinarith
  intro v hv
  obtain ⟨a1, a2⟩ := hG' v hv
  have hψp : 0 < ψ v := lt_of_lt_of_le hlo0 a1
  have k1 : |ψ v ^ 2 / S0 - 1| = |ψ v - ψ0| * (ψ v + ψ0) / ψ0 ^ 2 := by
    rw [← hψ0sq, show ψ v ^ 2 / ψ0 ^ 2 - 1 = (ψ v - ψ0) * (ψ v + ψ0) / ψ0 ^ 2 by
      field_simp; ring, abs_div, abs_mul, abs_of_pos (by linarith : 0 < ψ v + ψ0),
      abs_of_pos (by positivity : 0 < ψ0 ^ 2)]
  have k2 : ψ v + ψ0 ≤ 2 * (ψ0 + ws) := by linarith
  have k3 : (ψ0 + ws) / ψ0 ^ 2 ≤ (σl + ws) / σl ^ 2 := dec_frac hσl hws (hlo.trans hψ0lo)
  have k4 : |ψ v - ψ0| ≤ |ψ v - ψb| + |ψb - ψg| + W / (2 * σl) := by
    have : |ψg - ψ0| ≤ W / (2 * σl) := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact hgap
    calc |ψ v - ψ0| = |(ψ v - ψb) + (ψb - ψg) + (ψg - ψ0)| := by ring_nf
      _ ≤ |ψ v - ψb| + |ψb - ψg| + |ψg - ψ0| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  rw [k1]
  have k5 : |ψ v - ψ0| * (ψ v + ψ0) / ψ0 ^ 2 ≤ |ψ v - ψ0| * (2 * ((ψ0 + ws) / ψ0 ^ 2)) := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [show 2 * ((ψ0 + ws) / ψ0 ^ 2) = 2 * (ψ0 + ws) / ψ0 ^ 2 by ring]
    exact div_le_div_of_nonneg_right k2 (by positivity)
  refine k5.trans ?_
  have hR0 : 0 ≤ |ψ v - ψb| + |ψb - ψg| + W / (2 * σl) := by
    have : 0 ≤ W := integral_nonneg fun w => sq_nonneg _
    positivity
  calc |ψ v - ψ0| * (2 * ((ψ0 + ws) / ψ0 ^ 2)) ≤
        (|ψ v - ψb| + |ψb - ψg| + W / (2 * σl)) * (2 * ((σl + ws) / σl ^ 2)) :=
        mul_le_mul k4 (by linarith) (by positivity) hR0
    _ = _ := by ring

lemma shift_le (hG : MeasurableSet G) (hm : 0 < ν.real G) {f : V → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, |f v| ≤ M) {η : ℝ} (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) :
    |∫ v, f v ∂ν - ∫ v, f v ∂nrm ν G| ≤
      √(η / (1 - η)) * √(∫ v, (f v - ∫ w, f w ∂ν) ^ 2 ∂ν) := by
  have h := mean_shift hG hm hf hM
  have hV : 0 ≤ ∫ v, (f v - ∫ w, f w ∂ν) ^ 2 ∂ν := integral_nonneg fun v => sq_nonneg _
  have hq : (1 - ν.real G) / ν.real G ≤ η / (1 - η) := by
    rw [div_le_div_iff₀ hm (by linarith)]; nlinarith
  have hm1 : ν.real G ≤ 1 := measureReal_le_one
  have hη0 : 0 ≤ η := by linarith
  rw [← Real.sqrt_mul (div_nonneg hη0 (by linarith)), abs_sub_comm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (h.trans (mul_le_mul_of_nonneg_right hq hV))

lemma W_le (hG : MeasurableSet G) (hm : 0 < ν.real G) {ψ : V → ℝ} (mψ : Measurable ψ)
    {Mψ : ℝ} (bψ : ∀ v, |ψ v| ≤ Mψ) {ws : ℝ} (hws : 0 ≤ ws)
    (hGψ : ∀ v ∈ G, |ψ v - ∫ w, ψ w ∂ν| ≤ ws) {η : ℝ} (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) :
    ∫ v, (ψ v - ∫ w, ψ w ∂ν) ^ 2 ∂nrm ν G ≤
      ws / √(1 - η) * √(∫ v, (ψ v - ∫ w, ψ w ∂ν) ^ 2 ∂ν) := by
  have hP := nrm_prob ν hG hm
  set ψb := ∫ w, ψ w ∂ν
  set W := ∫ v, (ψ v - ψb) ^ 2 ∂nrm ν G
  set Var := ∫ v, (ψ v - ψb) ^ 2 ∂ν
  have bd : ∀ v, |ψ v - ψb| ≤ Mψ + |ψb| := fun v => (abs_sub _ _).trans (by linarith [bψ v])
  have iW : Integrable (fun v => (ψ v - ψb) ^ 2) (nrm ν G) :=
    intB ((mψ.sub_const _).pow_const 2) (sq_bound_of_abs bd)
  have iV : Integrable (fun v => (ψ v - ψb) ^ 2) ν :=
    intB ((mψ.sub_const _).pow_const 2) (sq_bound_of_abs bd)
  have hW0 : 0 ≤ W := integral_nonneg fun v => sq_nonneg _
  have hV0 : 0 ≤ Var := integral_nonneg fun v => sq_nonneg _
  have hWw : W ≤ ws ^ 2 := by
    have := integral_mono_ae iW (integrable_const (ws ^ 2)) ((nrm_ae_mem ν hG).mono fun v hv => by
      show (ψ v - ψb) ^ 2 ≤ ws ^ 2
      have := hGψ v hv
      exact (sq_abs (ψ v - ψb)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) this 2)
    simpa using this
  have hWV : W ≤ (ν.real G)⁻¹ * Var := integral_nrm_le hG hm (fun v => sq_nonneg _) iV
  have hm1 : (ν.real G)⁻¹ ≤ (1 - η)⁻¹ := inv_anti₀ (by linarith) hη
  have hsW : √W ≤ ws := by
    rw [show ws = √(ws ^ 2) from (Real.sqrt_sq hws).symm]; exact Real.sqrt_le_sqrt hWw
  have hsW2 : √W ≤ √Var / √(1 - η) := by
    rw [← Real.sqrt_div' _ (by linarith : (0:ℝ) ≤ 1 - η)]
    refine Real.sqrt_le_sqrt (hWV.trans ?_)
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hm1 hV0
  calc W = √W * √W := (Real.mul_self_sqrt hW0).symm
    _ ≤ ws * (√Var / √(1 - η)) := mul_le_mul hsW hsW2 (Real.sqrt_nonneg _) hws
    _ = ws / √(1 - η) * √Var := by ring

lemma abs_pow_bound {f : V → ℝ} {M : ℝ} (hM : ∀ v, |f v| ≤ M) (p : ℕ) :
    ∀ v, |(|f v| ^ p)| ≤ M ^ p := fun v => by
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hM v) p

/-- **Moments of `ε` on the good set** (the bound `e_k` of Prop. `t7:p07:FL`, one latitude):
for weights `b₁, b₂, b₃ > 0`, `B = b₁ + b₂ + b₃`, `c_E = 2(σ_l + w_s)/σ_l²`,
`E(|ψ²/S₀ − 1|^p | G) ≤ c_E^p B^p [(b₁/B)(1 − η)^{−1}E|ψ − Eψ|^p/b₁^p +
(b₂/B)(√(η/(1−η))·sd/b₂)^p + (b₃/B)(w_s/(2σ_l√(1−η))·sd/b₃)^p]`. -/
lemma idx_eps_mom (hG : MeasurableSet G) (hm : 0 < ν.real G) {ψ : V → ℝ} (mψ : Measurable ψ)
    {Mψ : ℝ} (bψ : ∀ v, |ψ v| ≤ Mψ) {ws σl : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl)
    (hGψ : ∀ v ∈ G, |ψ v - ∫ w, ψ w ∂ν| ≤ ws ∧ σl ≤ ψ v) {η : ℝ} (hη : 1 - η ≤ ν.real G)
    (hη1 : η < 1) (p : ℕ) {b1 b2 b3 : ℝ} (p1 : 0 < b1) (p2 : 0 < b2) (p3 : 0 < b3) :
    ∫ v, |ψ v ^ 2 / ∫ w, ψ w ^ 2 ∂nrm ν G - 1| ^ p ∂nrm ν G ≤
      (2 * (σl + ws) / σl ^ 2) ^ p * (b1 + b2 + b3) ^ p *
        (b1 / (b1 + b2 + b3) * ((1 - η)⁻¹ * (∫ v, |ψ v - ∫ w, ψ w ∂ν| ^ p ∂ν) / b1 ^ p) +
          b2 / (b1 + b2 + b3) *
            (√(η / (1 - η)) * √(∫ v, (ψ v - ∫ w, ψ w ∂ν) ^ 2 ∂ν) / b2) ^ p +
          b3 / (b1 + b2 + b3) *
            (ws / (2 * σl * √(1 - η)) * √(∫ v, (ψ v - ∫ w, ψ w ∂ν) ^ 2 ∂ν) / b3) ^ p) := by
  have hP := nrm_prob ν hG hm
  set P := nrm ν G
  set S0 := ∫ w, ψ w ^ 2 ∂P
  set ψb := ∫ w, ψ w ∂ν
  set sd := √(∫ v, (ψ v - ψb) ^ 2 ∂ν)
  set cE := 2 * (σl + ws) / σl ^ 2
  set B := b1 + b2 + b3
  set y2 := √(η / (1 - η)) * sd
  set y3 := ws / (2 * σl * √(1 - η)) * sd
  have hcE : 0 ≤ cE := by positivity
  have hy2 : 0 ≤ y2 := by positivity
  have hy3 : 0 ≤ y3 := by
    have : 0 ≤ ws / (2 * σl * √(1 - η)) := by positivity
    positivity
  have hpt := idx_eps_pt hG hm mψ bψ hws hσl hGψ
  have hsh := shift_le hG hm mψ bψ hη hη1
  have hW := W_le hG hm mψ bψ hws (fun v hv => (hGψ v hv).1) hη hη1
  have hW' : (∫ w, (ψ w - ψb) ^ 2 ∂P) / (2 * σl) ≤ y3 := by
    rw [div_le_iff₀ (by positivity)]
    have e : y3 * (2 * σl) = ws / √(1 - η) * sd := by
      simp only [y3]
      have : √(1 - η) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      field_simp
    rw [e]; exact hW
  have bd : ∀ v, |ψ v - ψb| ≤ Mψ + |ψb| := fun v => (abs_sub _ _).trans (by linarith [bψ v])
  -- pointwise
  have hae : ∀ᵐ v ∂P, |ψ v ^ 2 / S0 - 1| ^ p ≤ cE ^ p * (B ^ p *
      (b1 / B * (|ψ v - ψb| / b1) ^ p + b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p)) := by
    filter_upwards [nrm_ae_mem ν hG] with v hv
    have h1 := hpt v hv
    have h2 : |ψ v ^ 2 / S0 - 1| ≤ cE * (|ψ v - ψb| + y2 + y3) := by
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hcE)
      linarith
    have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 p
    rw [mul_pow] at h3
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hcE p))
    exact pow3_le p (abs_nonneg _) hy2 hy3 p1 p2 p3
  -- integrate
  have iL : Integrable (fun v => |ψ v - ψb| ^ p) ν :=
    intB ((mψ.sub_const _).abs.pow_const p) (abs_pow_bound bd p)
  have iLP : Integrable (fun v => |ψ v - ψb| ^ p) P :=
    intB ((mψ.sub_const _).abs.pow_const p) (abs_pow_bound bd p)
  have hS0 : 0 < S0 := by
    obtain ⟨lo, hi, hlo, -, -, s1, -⟩ := idx_scale hG hm mψ bψ hws hσl hGψ
    exact lt_of_lt_of_le (by have := lt_of_lt_of_le hσl hlo; positivity) s1
  have bε : ∀ v, |ψ v ^ 2 / S0 - 1| ≤ Mψ ^ 2 / S0 + 1 := fun v => by
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_pos hS0, abs_one]
    have := sq_bound_of_abs bψ v
    gcongr
  have iε : Integrable (fun v => |ψ v ^ 2 / S0 - 1| ^ p) P :=
    intB ((((mψ.pow_const 2).div_const _).sub_const 1).abs.pow_const p) (abs_pow_bound bε p)
  have iR : Integrable (fun v => cE ^ p * (B ^ p *
      (b1 / B * (|ψ v - ψb| / b1) ^ p + b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p))) P := by
    have : (fun v => cE ^ p * (B ^ p *
        (b1 / B * (|ψ v - ψb| / b1) ^ p + b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p))) =
        fun v => (cE ^ p * B ^ p * (b1 / B) / b1 ^ p) * |ψ v - ψb| ^ p +
          cE ^ p * B ^ p * (b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p) := by
      funext v; rw [div_pow]; ring
    rw [this]
    exact (iLP.const_mul _).add (integrable_const _)
  refine (integral_mono_ae iε iR hae).trans ?_
  have e : ∫ v, cE ^ p * (B ^ p *
      (b1 / B * (|ψ v - ψb| / b1) ^ p + b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p)) ∂P =
      cE ^ p * B ^ p * (b1 / B * ((∫ v, |ψ v - ψb| ^ p ∂P) / b1 ^ p) +
        b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p) := by
    have : (fun v => cE ^ p * (B ^ p *
        (b1 / B * (|ψ v - ψb| / b1) ^ p + b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p))) =
        fun v => (cE ^ p * B ^ p * (b1 / B) / b1 ^ p) * |ψ v - ψb| ^ p +
          cE ^ p * B ^ p * (b2 / B * (y2 / b2) ^ p + b3 / B * (y3 / b3) ^ p) := by
      funext v; rw [div_pow]; ring
    rw [this, integral_add (iLP.const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp only [probReal_univ, one_smul]
    ring
  rw [e]
  have hL : ∫ v, |ψ v - ψb| ^ p ∂P ≤ (1 - η)⁻¹ * ∫ v, |ψ v - ψb| ^ p ∂ν :=
    (integral_nrm_le hG hm (fun v => pow_nonneg (abs_nonneg _) _) iL).trans
      (mul_le_mul_of_nonneg_right (inv_anti₀ (by linarith) hη)
        (integral_nonneg fun v => pow_nonneg (abs_nonneg _) _))
  have hB : 0 < B := by positivity
  gcongr

/-- The location window: on `G`, `|φ − E(φ | G)| ≤ 2w_l` if `|φ − Eφ| ≤ w_l` on `G`. -/
lemma idx_phi_window (hG : MeasurableSet G) (hm : 0 < ν.real G) {φ : V → ℝ} (mφ : Measurable φ)
    {Mφ : ℝ} (bφ : ∀ v, |φ v| ≤ Mφ) {wl : ℝ} (hGφ : ∀ v ∈ G, |φ v - ∫ w, φ w ∂ν| ≤ wl) :
    ∀ v ∈ G, |φ v - ∫ w, φ w ∂nrm ν G| ≤ 2 * wl := by
  obtain ⟨t1, t2⟩ := nrm_mean_mem hG hm mφ bφ (lo := ∫ w, φ w ∂ν - wl) (hi := ∫ w, φ w ∂ν + wl)
    fun v hv => ⟨by linarith [(abs_le.mp (hGφ v hv)).1], by linarith [(abs_le.mp (hGφ v hv)).2]⟩
  intro v hv
  have := abs_le.mp (hGφ v hv)
  rw [abs_le]; constructor <;> linarith

/-- `E((√(C/S₀)(φ − E(φ|G)))² | G) ≤ (C/σ_l²)(1 − η)^{−1} Var φ` (the price `D`, one latitude). -/
lemma idx_del_sq (hG : MeasurableSet G) (hm : 0 < ν.real G) {φ : V → ℝ} (mφ : Measurable φ)
    {Mφ : ℝ} (bφ : ∀ v, |φ v| ≤ Mφ) {S0 C σl η : ℝ} (hσl : 0 < σl) (hS0 : σl ^ 2 ≤ S0)
    (hC : 0 ≤ C) (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) :
    ∫ v, (√(C / S0) * (φ v - ∫ w, φ w ∂nrm ν G)) ^ 2 ∂nrm ν G ≤
      C / σl ^ 2 * ((1 - η)⁻¹ * ∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν) := by
  have hP := nrm_prob ν hG hm
  have hS0p : 0 < S0 := lt_of_lt_of_le (by positivity) hS0
  have e : ∀ v, (√(C / S0) * (φ v - ∫ w, φ w ∂nrm ν G)) ^ 2 =
      C / S0 * (φ v - ∫ w, φ w ∂nrm ν G) ^ 2 := fun v => by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hC hS0p.le)]
  simp_rw [e]
  rw [integral_const_mul]
  have bd : ∀ v, |φ v - ∫ w, φ w ∂ν| ≤ Mφ + |∫ w, φ w ∂ν| :=
    fun v => (abs_sub _ _).trans (by linarith [bφ v])
  have h1 := var_le_sq_sub (μ := nrm ν G) mφ bφ (∫ w, φ w ∂ν)
  have h2 := integral_nrm_le hG hm (g := fun v => (φ v - ∫ w, φ w ∂ν) ^ 2) (fun v => sq_nonneg _)
    (intB ((mφ.sub_const _).pow_const 2) (sq_bound_of_abs bd))
  have h3 : (ν.real G)⁻¹ ≤ (1 - η)⁻¹ := inv_anti₀ (by linarith) hη
  have hV : 0 ≤ ∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν := integral_nonneg fun v => sq_nonneg _
  have h4 : C / S0 ≤ C / σl ^ 2 := div_le_div_of_nonneg_left hC (by positivity) hS0
  have h5 : 0 ≤ ∫ v, (φ v - ∫ w, φ w ∂nrm ν G) ^ 2 ∂nrm ν G := integral_nonneg fun v => sq_nonneg _
  calc C / S0 * ∫ v, (φ v - ∫ w, φ w ∂nrm ν G) ^ 2 ∂nrm ν G ≤
      C / σl ^ 2 * ∫ v, (φ v - ∫ w, φ w ∂nrm ν G) ^ 2 ∂nrm ν G :=
        mul_le_mul_of_nonneg_right h4 h5
    _ ≤ C / σl ^ 2 * ((1 - η)⁻¹ * ∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right h3 hV))

/-- **Moments of `a_c δ` on the good set** (the bound `d_k`, one latitude). -/
lemma idx_del_mom (hG : MeasurableSet G) (hm : 0 < ν.real G) {φ : V → ℝ} (mφ : Measurable φ)
    {Mφ : ℝ} (bφ : ∀ v, |φ v| ≤ Mφ) {S0 C σl η : ℝ} (hσl : 0 < σl) (hS0 : σl ^ 2 ≤ S0)
    (hC : 0 ≤ C) (hη : 1 - η ≤ ν.real G) (hη1 : η < 1) (p : ℕ) {b1 b2 : ℝ} (p1 : 0 < b1)
    (p2 : 0 < b2) :
    ∫ v, |√(C / S0) * (φ v - ∫ w, φ w ∂nrm ν G)| ^ p ∂nrm ν G ≤
      (√C / σl) ^ p * (b1 + b2) ^ p *
        (b1 / (b1 + b2) * ((1 - η)⁻¹ * (∫ v, |φ v - ∫ w, φ w ∂ν| ^ p ∂ν) / b1 ^ p) +
          b2 / (b1 + b2) * (√(η / (1 - η)) * √(∫ v, (φ v - ∫ w, φ w ∂ν) ^ 2 ∂ν) / b2) ^ p) := by
  have hP := nrm_prob ν hG hm
  set P := nrm ν G
  set φb := ∫ w, φ w ∂ν
  set φg := ∫ w, φ w ∂P
  set y2 := √(η / (1 - η)) * √(∫ v, (φ v - φb) ^ 2 ∂ν)
  set B := b1 + b2
  have hS0p : 0 < S0 := lt_of_lt_of_le (by positivity) hS0
  have hy2 : 0 ≤ y2 := by positivity
  have hsh : |φb - φg| ≤ y2 := shift_le hG hm mφ bφ hη hη1
  have ha : √(C / S0) ≤ √C / σl := by
    rw [Real.sqrt_div' _ hS0p.le]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hσl
      (by rw [show σl = √(σl ^ 2) from (Real.sqrt_sq hσl.le).symm]; exact Real.sqrt_le_sqrt hS0)
  have hc0 : 0 ≤ √C / σl := by positivity
  have bd : ∀ v, |φ v - φb| ≤ Mφ + |φb| := fun v => (abs_sub _ _).trans (by linarith [bφ v])
  have bdg : ∀ v, |√(C / S0) * (φ v - φg)| ≤ √(C / S0) * (Mφ + |φg|) := fun v => by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [bφ v])) (Real.sqrt_nonneg _)
  have hpt : ∀ v, |√(C / S0) * (φ v - φg)| ^ p ≤ (√C / σl) ^ p * (B ^ p *
      (b1 / B * (|φ v - φb| / b1) ^ p + b2 / B * (y2 / b2) ^ p)) := fun v => by
    have h1 : |√(C / S0) * (φ v - φg)| ≤ √C / σl * (|φ v - φb| + y2) := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have : |φ v - φg| ≤ |φ v - φb| + y2 := by
        calc |φ v - φg| = |(φ v - φb) + (φb - φg)| := by ring_nf
          _ ≤ |φ v - φb| + |φb - φg| := abs_add_le _ _
          _ ≤ _ := by linarith
      exact mul_le_mul ha this (abs_nonneg _) hc0
    have h3 := pow_le_pow_left₀ (abs_nonneg _) h1 p
    rw [mul_pow] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (pow2_le p (abs_nonneg _) hy2 p1 p2)
      (pow_nonneg hc0 p))
  have iL : Integrable (fun v => |φ v - φb| ^ p) ν :=
    intB ((mφ.sub_const _).abs.pow_const p) (abs_pow_bound bd p)
  have iLP : Integrable (fun v => |φ v - φb| ^ p) P :=
    intB ((mφ.sub_const _).abs.pow_const p) (abs_pow_bound bd p)
  have iε : Integrable (fun v => |√(C / S0) * (φ v - φg)| ^ p) P :=
    intB ((measurable_const.mul (mφ.sub_const _)).abs.pow_const p) (abs_pow_bound bdg p)
  have eR : (fun v => (√C / σl) ^ p * (B ^ p *
      (b1 / B * (|φ v - φb| / b1) ^ p + b2 / B * (y2 / b2) ^ p))) =
      fun v => ((√C / σl) ^ p * B ^ p * (b1 / B) / b1 ^ p) * |φ v - φb| ^ p +
        (√C / σl) ^ p * B ^ p * (b2 / B * (y2 / b2) ^ p) := by
    funext v; rw [div_pow]; ring
  have iR : Integrable (fun v => (√C / σl) ^ p * (B ^ p *
      (b1 / B * (|φ v - φb| / b1) ^ p + b2 / B * (y2 / b2) ^ p))) P := by
    rw [eR]; exact (iLP.const_mul _).add (integrable_const _)
  refine (integral_mono iε iR hpt).trans ?_
  rw [eR, integral_add (iLP.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  have hL : ∫ v, |φ v - φb| ^ p ∂P ≤ (1 - η)⁻¹ * ∫ v, |φ v - φb| ^ p ∂ν :=
    (integral_nrm_le hG hm (fun v => pow_nonneg (abs_nonneg _) _) iL).trans
      (mul_le_mul_of_nonneg_right (inv_anti₀ (by linarith) hη)
        (integral_nonneg fun v => pow_nonneg (abs_nonneg _) _))
  have hB : 0 < B := by positivity
  have e2 : (√C / σl) ^ p * B ^ p * (b1 / B) / b1 ^ p * ∫ v, |φ v - φb| ^ p ∂P +
      (√C / σl) ^ p * B ^ p * (b2 / B * (y2 / b2) ^ p) =
      (√C / σl) ^ p * B ^ p * (b1 / B * ((∫ v, |φ v - φb| ^ p ∂P) / b1 ^ p) +
        b2 / B * (y2 / b2) ^ p) := by ring
  rw [e2]
  gcongr

end idx

end BstLean.Part162

open BstLean.Part162 in
#print axioms idx_eps_mom
open BstLean.Part162 in
#print axioms idx_del_mom
