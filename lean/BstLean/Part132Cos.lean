import BstLean.Part132Layer

/-!
# Part 132, item 3 (tools): the cosine after the last matrix of `W` and the normalization

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3 ("W_3 and
normalization": `E cos ≥ τ − 16/n`); `onW4-opus-prover.md` T4(7).

* `lin_sq_var`: `Var |Mw|² = 2m·(v|w|²)²`; `lin_dot_var0` (polarization):
  `Var ⟨Mh, Mh′⟩ ≤ m·v²·(|h|² + |h′|²)²`.
* `cos_arith`: the pointwise second-order lower bound of a cosine.
* **`lin_cos_lower`**: for a Gaussian matrix `M` with `n` rows and inputs `h, h′` with
  `⟨h, h′⟩ ≥ 0`: `E ⟨x, x′⟩ ≥ cos(h, h′) − 17/n − 1{h = 0} − 1{h′ = 0}`, with `x = Mh/|Mh|`,
  `x′ = Mh′/|Mh′|` (the fixed point `e0` at `0`). The paper has `16/n`; the proof here uses
  Cauchy–Schwarz in the place of the count of index patterns.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part105 (sphProj)
open BstLean.Part130

/-! ## Linear combinations of integrals -/

lemma integral_lin4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f1 f2 f3 f4 : Ω → ℝ} (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ) (b c1 c2 c3 c4 : ℝ) :
    Integrable (fun ω => c1 * f1 ω + b - c2 * f2 ω - c3 * f3 ω - c4 * f4 ω) μ ∧
    ∫ ω, (c1 * f1 ω + b - c2 * f2 ω - c3 * f3 ω - c4 * f4 ω) ∂μ =
      c1 * ∫ ω, f1 ω ∂μ + b - c2 * ∫ ω, f2 ω ∂μ - c3 * ∫ ω, f3 ω ∂μ - c4 * ∫ ω, f4 ω ∂μ := by
  have g1 : Integrable (fun ω => c1 * f1 ω + b) μ := (h1.const_mul c1).add (integrable_const b)
  have g2 : Integrable (fun ω => c1 * f1 ω + b - c2 * f2 ω) μ := g1.sub (h2.const_mul c2)
  have g3 : Integrable (fun ω => c1 * f1 ω + b - c2 * f2 ω - c3 * f3 ω) μ :=
    g2.sub (h3.const_mul c3)
  refine ⟨g3.sub (h4.const_mul c4), ?_⟩
  have a1 := integral_sub g3 (h4.const_mul c4)
  have a2 := integral_sub g2 (h3.const_mul c3)
  have a3 := integral_sub g1 (h2.const_mul c2)
  have a4 := integral_add (h1.const_mul c1) (integrable_const b)
  have e1 : ∫ ω, c1 * f1 ω ∂μ = c1 * ∫ ω, f1 ω ∂μ := integral_const_mul _ _
  have e2 : ∫ ω, c2 * f2 ω ∂μ = c2 * ∫ ω, f2 ω ∂μ := integral_const_mul _ _
  have e3 : ∫ ω, c3 * f3 ω ∂μ = c3 * ∫ ω, f3 ω ∂μ := integral_const_mul _ _
  have e4 : ∫ ω, c4 * f4 ω ∂μ = c4 * ∫ ω, f4 ω ∂μ := integral_const_mul _ _
  have e5 : ∫ _ω : Ω, b ∂μ = b := by simp
  beta_reduce at a1 a2 a3 a4
  rw [a1, a2, a3, a4, e1, e2, e3, e4, e5]

/-! ## Vectors -/

section vec

variable {ι : Type*} [Fintype ι]

lemma polar (a b : ι → ℝ) : dotp a b = (normSq (a + b) - normSq (a - b)) / 4 := by
  unfold dotp normSq
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma parallelogram (a b : ι → ℝ) :
    normSq (a + b) + normSq (a - b) = 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma dotp_smul_smul (a b : ℝ) (y y' : ι → ℝ) : dotp (a • y) (b • y') = a * b * dotp y y' := by
  unfold dotp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma nrm_pos_of_ne {y : ι → ℝ} (hy : normSq y ≠ 0) : 0 < nrm y :=
  Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy))

lemma measurable_dotp_comp {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ι → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun ω => dotp (f ω) (g ω)) :=
  Measurable.comp (g := fun p : (ι → ℝ) × (ι → ℝ) => dotp p.1 p.2) (f := fun ω => (f ω, g ω))
    continuous_dotp.measurable (hf.prodMk hg)

end vec

variable {m k n : ℕ}

/-! ## Variances of one linear layer -/

/-- `Var |Mw|² = 2m·(v|w|²)²`. -/
theorem lin_sq_var {v : ℝ} (hv : 0 ≤ v) (w : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (normSq (M.mulVec w) - (m : ℝ) * (v * normSq w)) ^ 2
      ∂gaussMat m k v = 2 * (m : ℝ) * (v * normSq w) ^ 2 := by
  obtain ⟨i2, e2⟩ := layer_lin_sq (m := m) hv w
  obtain ⟨i4, e4⟩ := layer_lin_four (m := m) hv w
  set c := (m : ℝ) * (v * normSq w) with hc
  have e : (fun M : Matrix (Fin m) (Fin k) ℝ => (normSq (M.mulVec w) - c) ^ 2) =
      fun M => 1 * normSq (M.mulVec w) ^ 2 + c ^ 2 - 2 * c * normSq (M.mulVec w) -
        0 * normSq (M.mulVec w) - 0 * normSq (M.mulVec w) := by
    funext M; ring
  obtain ⟨hi, he⟩ := integral_lin4 (μ := gaussMat m k v) i4 i2 i2 i2 (c ^ 2) 1 (2 * c) 0 0
  rw [e]
  refine ⟨hi, ?_⟩
  rw [he, e2, e4, hc]
  ring

/-- Polarization: `Var ⟨Mh, Mh′⟩ ≤ m·v²·(|h|² + |h′|²)²`. -/
theorem lin_dot_var0 {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h')) ^ 2) (gaussMat m k v) ∧
    ∫ M : Matrix (Fin m) (Fin k) ℝ, (dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h')) ^ 2
      ∂gaussMat m k v ≤ (m : ℝ) * v ^ 2 * (normSq h + normSq h') ^ 2 := by
  obtain ⟨ip, ep⟩ := lin_sq_var (m := m) hv (h + h')
  obtain ⟨im, em⟩ := lin_sq_var (m := m) hv (h - h')
  have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      (dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h')) ^ 2 ≤
      ((normSq (M.mulVec (h + h')) - (m : ℝ) * (v * normSq (h + h'))) ^ 2 +
        (normSq (M.mulVec (h - h')) - (m : ℝ) * (v * normSq (h - h'))) ^ 2) / 8 := by
    intro M
    rw [polar (M.mulVec h) (M.mulVec h'), polar h h', ← Matrix.mulVec_add, ← Matrix.mulVec_sub]
    nlinarith [sq_nonneg ((normSq (M.mulVec (h + h')) - (m : ℝ) * (v * normSq (h + h'))) +
      (normSq (M.mulVec (h - h')) - (m : ℝ) * (v * normSq (h - h'))))]
  have hmeas : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h')) ^ 2) :=
    ((measurable_dotp_comp (measurable_mulVec_right h) (measurable_mulVec_right h')).sub
      measurable_const).pow_const 2
  have hb : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      ((normSq (M.mulVec (h + h')) - (m : ℝ) * (v * normSq (h + h'))) ^ 2 +
        (normSq (M.mulVec (h - h')) - (m : ℝ) * (v * normSq (h - h'))) ^ 2) / 8)
      (gaussMat m k v) := (ip.add im).div_const 8
  have hint : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') - (m : ℝ) * (v * dotp h h')) ^ 2) (gaussMat m k v) := by
    refine Integrable.mono' hb hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt M
  refine ⟨hint, ?_⟩
  have h1 := integral_mono hint hb hpt
  have a1 := integral_add ip im
  beta_reduce at a1
  rw [integral_div, a1, ep, em] at h1
  refine h1.trans ?_
  have hpar := parallelogram h h'
  have hp := normSq_nonneg (h + h')
  have hq := normSq_nonneg (h - h')
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have key : normSq (h + h') ^ 2 + normSq (h - h') ^ 2 ≤ 4 * (normSq h + normSq h') ^ 2 := by
    nlinarith
  have hmv : 0 ≤ (m : ℝ) * v ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hmv]

/-! ## The normalization -/

lemma sphPt_smul {c : ℝ} (hc : 0 < c) (y : Fin n → ℝ) : sphPt (c • y) = sphPt y := by
  unfold sphPt
  rw [normSq_smul]
  by_cases h : normSq y = 0
  · simp [h]
  · have hc2 : c ^ 2 * normSq y ≠ 0 := mul_ne_zero (by positivity) h
    simp only [h, hc2, ↓reduceIte]
    have hpos : 0 < normSq y := lt_of_le_of_ne (normSq_nonneg y) (Ne.symm h)
    have e : sphProj (c • y) = (1 / Real.sqrt (normSq (c • y))) • (c • y) := rfl
    have e' : sphProj y = (1 / Real.sqrt (normSq y)) • y := rfl
    rw [e, e', normSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le, smul_smul]
    congr 1
    have : Real.sqrt (normSq y) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp

lemma dotp_sphPt (y y' : Fin n → ℝ) (hy : normSq y ≠ 0) (hy' : normSq y' ≠ 0) :
    dotp (sphPt y) (sphPt y') = dotp y y' / (nrm y * nrm y') := by
  rw [sphPt_of_ne y hy, sphPt_of_ne y' hy']
  have e : sphProj y = (1 / nrm y) • y := rfl
  have e' : sphProj y' = (1 / nrm y') • y' := rfl
  rw [e, e', dotp_smul_smul]
  have := (nrm_pos_of_ne hy).ne'
  have := (nrm_pos_of_ne hy').ne'
  field_simp

lemma dotp_sphPt_ge (hn : 1 ≤ n) (y y' : Fin n → ℝ) : -1 ≤ dotp (sphPt y) (sphPt y') := by
  have h := abs_dotp_le_nrm (sphPt y) (sphPt y')
  rw [nrm_of_normSq_one (normSq_sphPt hn y), nrm_of_normSq_one (normSq_sphPt hn y')] at h
  have := (abs_le.mp h).1
  linarith

lemma dotp_sphPt_le (hn : 1 ≤ n) (y y' : Fin n → ℝ) : dotp (sphPt y) (sphPt y') ≤ 1 := by
  have h := abs_dotp_le_nrm (sphPt y) (sphPt y')
  rw [nrm_of_normSq_one (normSq_sphPt hn y), nrm_of_normSq_one (normSq_sphPt hn y')] at h
  have := (abs_le.mp h).2
  linarith

/-- The pointwise second-order lower bound of a cosine `T = C/P` against the reference
`(s, s·τ)`. -/
lemma cos_arith {s τ C P T : ℝ} (hs : 0 < s) (hP0 : 0 ≤ P) (hCP : |C| ≤ P) (hT1 : -1 ≤ T)
    (hTeq : 0 < P → T = C / P) :
    1 / s * C + τ - τ / s * P - 1 / (2 * s ^ 2) * (C - s * τ) ^ 2 -
      3 / (2 * s ^ 2) * (P - s) ^ 2 ≤ T := by
  rcases eq_or_lt_of_le hP0 with h | h
  · have hC : C = 0 := by rw [← h] at hCP; exact abs_nonpos_iff.mp hCP
    rw [← h, hC]
    have e : 1 / s * 0 + τ - τ / s * 0 - 1 / (2 * s ^ 2) * (0 - s * τ) ^ 2 -
        3 / (2 * s ^ 2) * (0 - s) ^ 2 = τ - τ ^ 2 / 2 - 3 / 2 := by field_simp; ring
    rw [e]
    nlinarith [sq_nonneg (τ - 1)]
  · have hT := hTeq h
    have hC : C = T * P := by rw [hT]; field_simp
    have e : 1 / s * C + τ - τ / s * P - 1 / (2 * s ^ 2) * (C - s * τ) ^ 2 -
        3 / (2 * s ^ 2) * (P - s) ^ 2 =
        T * (P / s) + τ - τ * (P / s) - (T * (P / s) - τ) ^ 2 / 2 - 3 * (P / s - 1) ^ 2 / 2 := by
      rw [hC]; field_simp
    rw [e]
    set p := P / s
    nlinarith [mul_nonneg (sq_nonneg (1 - p)) (by linarith : (0 : ℝ) ≤ T + 1),
      sq_nonneg (T * p - τ + 1 - p)]

lemma measurable_dotp_sphPt (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))) :=
  measurable_dotp_comp (measurable_sphPt.comp (measurable_mulVec_right h))
    (measurable_sphPt.comp (measurable_mulVec_right h'))

lemma integrable_dotp_sphPt (hn : 1 ≤ n) (v : ℝ) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))) (gaussMat n k v) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_dotp_sphPt h h').aestronglyMeasurable (Filter.Eventually.of_forall fun M => ?_)
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩

/-- The case of unit inputs. -/
theorem lin_cos_unit {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ} (hh : normSq h = 1)
    (hh' : normSq h' = 1) (hd : 0 ≤ dotp h h') :
    dotp h h' - 17 / (n : ℝ) ≤
      ∫ M : Matrix (Fin n) (Fin k) ℝ, dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))
        ∂gaussMat n k v := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := (n : ℝ) * v with hs
  have hs0 : 0 < s := by positivity
  set τ := dotp h h' with hτ
  obtain ⟨iC, eC⟩ := layer_dot_lin (m := n) hv.le h h'
  obtain ⟨iP, uP, -, iPv, uPv⟩ := lin_layer_pair (m := n) hv.le hn h h'
  obtain ⟨iCv, uCv⟩ := lin_dot_var0 (m := n) hv.le h h'
  rw [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one, mul_one] at uP iPv uPv
  rw [hh, hh'] at uCv
  have e0 : (n : ℝ) * (v * dotp h h') = s * τ := by rw [hs, hτ]; ring
  rw [e0] at iCv uCv eC
  obtain ⟨iR, eR⟩ := integral_lin4 (μ := gaussMat n k v) iC iP iCv iPv τ (1 / s) (τ / s)
    (1 / (2 * s ^ 2)) (3 / (2 * s ^ 2))
  have hpt : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      1 / s * dotp (M.mulVec h) (M.mulVec h') + τ - τ / s * (nrm (M.mulVec h) * nrm (M.mulVec h')) -
        1 / (2 * s ^ 2) * (dotp (M.mulVec h) (M.mulVec h') - s * τ) ^ 2 -
        3 / (2 * s ^ 2) * (nrm (M.mulVec h) * nrm (M.mulVec h') - s) ^ 2 ≤
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) := by
    intro M
    refine cos_arith hs0 (nrm_mul_nonneg _ _) (abs_dotp_le_nrm _ _) (dotp_sphPt_ge hn _ _) ?_
    intro hpos
    have h1 : nrm (M.mulVec h) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hpos; exact lt_irrefl _ hpos
    have h2 : nrm (M.mulVec h') ≠ 0 := fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
    have h1' : normSq (M.mulVec h) ≠ 0 := fun h0 => h1 (by unfold nrm; rw [h0, Real.sqrt_zero])
    have h2' : normSq (M.mulVec h') ≠ 0 := fun h0 => h2 (by unfold nrm; rw [h0, Real.sqrt_zero])
    exact dotp_sphPt _ _ h1' h2'
  have hmono := integral_mono iR (integrable_dotp_sphPt hn v h h') hpt
  rw [eR, eC] at hmono
  refine le_trans ?_ hmono
  -- the four terms
  have t1 : 1 / s * (s * τ) = τ := by field_simp
  have t2 : τ / s * ∫ M : Matrix (Fin n) (Fin k) ℝ, nrm (M.mulVec h) * nrm (M.mulVec h')
      ∂gaussMat n k v ≤ τ := by
    have := mul_le_mul_of_nonneg_left uP (by positivity : (0 : ℝ) ≤ τ / s)
    have e : τ / s * ((n : ℝ) * v) = τ := by rw [← hs]; field_simp
    linarith
  have t3 : 1 / (2 * s ^ 2) * ∫ M : Matrix (Fin n) (Fin k) ℝ,
      (dotp (M.mulVec h) (M.mulVec h') - s * τ) ^ 2 ∂gaussMat n k v ≤ 2 / (n : ℝ) := by
    have := mul_le_mul_of_nonneg_left uCv (by positivity : (0 : ℝ) ≤ 1 / (2 * s ^ 2))
    have e : 1 / (2 * s ^ 2) * ((n : ℝ) * v ^ 2 * (1 + 1) ^ 2) = 2 / (n : ℝ) := by
      rw [hs]; field_simp; ring
    linarith
  have t4 : 3 / (2 * s ^ 2) * ∫ M : Matrix (Fin n) (Fin k) ℝ,
      (nrm (M.mulVec h) * nrm (M.mulVec h') - s) ^ 2 ∂gaussMat n k v ≤ 15 / (n : ℝ) := by
    have := mul_le_mul_of_nonneg_left uPv (by positivity : (0 : ℝ) ≤ 3 / (2 * s ^ 2))
    have e : 3 / (2 * s ^ 2) * (10 / (n : ℝ) * ((n : ℝ) * v) ^ 2) = 15 / (n : ℝ) := by
      rw [hs]; field_simp; ring
    rw [← hs] at this
    linarith
  have e17 : (17 : ℝ) / n = 2 / n + 15 / n := by ring
  rw [t1, e17]
  linarith

/-- **The cosine after the last matrix and the normalization.** `M` a Gaussian matrix with `n`
rows and variance `v > 0`; `h, h′` with `⟨h, h′⟩ ≥ 0`. Then
`E ⟨sphPt(Mh), sphPt(Mh′)⟩ ≥ cos(h, h′) − 17/n − 1{h = 0} − 1{h′ = 0}`. -/
theorem lin_cos_lower {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (h h' : Fin k → ℝ)
    (hd : 0 ≤ dotp h h') :
    cosv h h' - 17 / (n : ℝ) - (if normSq h = 0 then 1 else 0) -
        (if normSq h' = 0 then 1 else 0) ≤
      ∫ M : Matrix (Fin n) (Fin k) ℝ, dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))
        ∂gaussMat n k v := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h17 : (0 : ℝ) ≤ 17 / (n : ℝ) := by positivity
  have hlow : (-1 : ℝ) ≤ ∫ M : Matrix (Fin n) (Fin k) ℝ,
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) ∂gaussMat n k v := by
    have := integral_mono (integrable_const (-1 : ℝ)) (integrable_dotp_sphPt hn v h h')
      (fun M => dotp_sphPt_ge hn _ _)
    simpa using this
  have hc1 := (cosv_mem h h').2
  by_cases h0 : normSq h = 0
  · have hz : nrm h = 0 := by unfold nrm; rw [h0, Real.sqrt_zero]
    have hc : cosv h h' = 0 := by unfold cosv; rw [hz]; simp
    rw [hc]; simp only [h0, ↓reduceIte]
    split_ifs <;> linarith
  by_cases h0' : normSq h' = 0
  · have hz : nrm h' = 0 := by unfold nrm; rw [h0', Real.sqrt_zero]
    have hc : cosv h h' = 0 := by unfold cosv; rw [hz]; simp
    rw [hc]; simp only [h0, h0', ↓reduceIte]
    linarith
  simp only [h0, h0', ↓reduceIte, sub_zero]
  have hp := nrm_pos_of_ne h0
  have hp' := nrm_pos_of_ne h0'
  have hu : normSq ((1 / nrm h) • h) = 1 := by
    rw [normSq_smul, ← nrm_sq]; field_simp
  have hu' : normSq ((1 / nrm h') • h') = 1 := by
    rw [normSq_smul, ← nrm_sq]; field_simp
  have hdu : dotp ((1 / nrm h) • h) ((1 / nrm h') • h') = cosv h h' := by
    rw [dotp_smul_smul]; unfold cosv; field_simp
  have key := lin_cos_unit (n := n) hv hn hu hu' (by rw [hdu]; exact div_nonneg hd (by positivity))
  rw [hdu] at key
  have e : ∀ M : Matrix (Fin n) (Fin k) ℝ,
      dotp (sphPt (M.mulVec ((1 / nrm h) • h))) (sphPt (M.mulVec ((1 / nrm h') • h'))) =
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) := by
    intro M
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, sphPt_smul (by positivity),
      sphPt_smul (by positivity)]
  simp_rw [e] at key
  exact key

end BstLean.Part132

open BstLean.Part132 in
#print axioms lin_cos_lower
