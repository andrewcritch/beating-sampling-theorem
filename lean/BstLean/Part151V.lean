import BstLean.Part151R

/-!
# Part 151: Lemma V (the coupling cost), Steps 2 to 4, in an abstract form

Paper source: `proofs/option-n/theorem5-10-transport.tex`, Lemma V, Steps 2, 3, 4 of the proof.

The setting has no network. `(Ξ, μ)` is a probability space and `v₁, v₂ : Ξ → ℝ` are the two
coordinates of the vector `v(x) = (⟨q(x), b̂⟩, |Π_b q(x)|)` of the document (`v₂ ≥ 0`,
`|v|² = |q|² ≤ H`). `ρ = |v|` (`rhoV`), `u = ρ/√γ − 1 = √ω₂ − 1` (`uV`), `Θ = arccos(v₁/ρ)`
(`thetaV`), `r = √γ(1 − ϑ)` (`rV`), `φ = Θ·min(1, ρ/r)` (`phiV`), and
`ℓ² = 1/ρ²` where `ρ > r`, `ℓ² = 6.61/r²` where `ρ ≤ r` (`ellSqV`: the square of the bound of
the pointwise Lipschitz constant of `φ`). The Poincaré steps of the document enter as
hypotheses with a function `X ≥ 0`, `E X² ≤ (M_P γ/n)²` (the document: `Ξ₄ ≤ M_P γ_A/n`):
`Var v₁ ≤ E X`, `Var v₂ ≤ E X`, `Var φ ≤ E[X·ℓ²]`.

* `stepV_2a`: `Var φ ≤ κ_ϑ·M_P/n`.
* `stepV_2b`: `tr Cov v ≤ γ·(𝔯_ϑ + √(Var-bound of φ))²`.
* `stepV_3`: `(E v₂ − σ_p)² ≤ γ·𝔡`, `σ_p = √(γ(1 − e_b))`.
* **`lemmaV_abs`**: `E|v − v_p|² ≤ γ·[(√(κ_ϑ M_P/n) + 𝔯_ϑ)² + ξ_∥/n + 𝔡]`,
  `v_p = (√(γ e_b), σ_p)`.
* `lemmaV_abs_n`: for `γ = 2/n`: `n²·E|v − v_p|² ≤ 2[(√(κ_ϑ M_P) + √n·𝔯_ϑ)² + ξ_∥ + n·𝔡]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set

/-! ## Tools -/

lemma le_of_sqV {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (abs_le_of_sq_le_sq' h hy).2

lemma sq_le_of_absV {x C : ℝ} (h : |x| ≤ C) : x ^ 2 ≤ C ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) h 2

lemma sq2_add_le {x₁ x₂ y₁ y₂ a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x₁ ^ 2 + x₂ ^ 2 ≤ a ^ 2)
    (hy : y₁ ^ 2 + y₂ ^ 2 ≤ b ^ 2) : (x₁ + y₁) ^ 2 + (x₂ + y₂) ^ 2 ≤ (a + b) ^ 2 := by
  have h1 : (x₁ * y₁ + x₂ * y₂) ^ 2 ≤ (a * b) ^ 2 := by
    have h2 : (x₁ * y₁ + x₂ * y₂) ^ 2 ≤ (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) := by
      nlinarith [sq_nonneg (x₁ * y₂ - x₂ * y₁)]
    have h3 : (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) ≤ a ^ 2 * b ^ 2 :=
      mul_le_mul hx hy (by positivity) (by positivity)
    rw [mul_pow]; exact h2.trans h3
  have h4 := le_of_sqV (mul_nonneg ha hb) h1
  nlinarith

/-- `(m − σ)² ≤ γ·e²/(s(2 − e/s)²)` from `|m² − σ²| ≤ γe`, `σ² ≥ γs`, `e/s < 1`. -/
lemma mean_dispV {m σ γ e s : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ) (hγ : 0 < γ) (hs : 0 < s)
    (hσ2 : γ * s ≤ σ ^ 2) (he0 : 0 ≤ e) (hw : e / s < 1) (h : |m ^ 2 - σ ^ 2| ≤ γ * e) :
    (m - σ) ^ 2 ≤ γ * (e ^ 2 / (s * (2 - e / s) ^ 2)) := by
  set w : ℝ := e / s with hwd
  have hw0 : 0 ≤ w := by rw [hwd]; positivity
  have he : e = w * s := by rw [hwd]; field_simp
  have h1 : γ * e ≤ w * σ ^ 2 := by
    rw [he]
    have := mul_le_mul_of_nonneg_left hσ2 hw0
    linarith
  have habs : |m ^ 2 - σ ^ 2| = |m - σ| * (m + σ) := by
    have e1 : m ^ 2 - σ ^ 2 = (m - σ) * (m + σ) := by ring
    rw [e1, abs_mul, abs_of_pos (by linarith : 0 < m + σ)]
  rw [habs] at h
  have ha0 : 0 ≤ |m - σ| := abs_nonneg _
  have h2 : |m - σ| * σ ≤ w * σ ^ 2 := by
    have : |m - σ| * σ ≤ |m - σ| * (m + σ) := mul_le_mul_of_nonneg_left (by linarith) ha0
    linarith
  have h3 : |m - σ| ≤ w * σ := by
    have h4 : |m - σ| * σ ≤ (w * σ) * σ := by rw [show w * σ * σ = w * σ ^ 2 by ring]; exact h2
    exact le_of_mul_le_mul_right h4 hσ
  have h5 : σ - w * σ ≤ m := by
    have := (abs_le.mp h3).1
    linarith
  have h2w : 0 < 2 - w := by linarith
  have h6 : |m - σ| * ((2 - w) * σ) ≤ γ * e := by
    have : |m - σ| * ((2 - w) * σ) ≤ |m - σ| * (m + σ) :=
      mul_le_mul_of_nonneg_left (by nlinarith) ha0
    linarith
  have h7 : (m - σ) ^ 2 * ((2 - w) * σ) ^ 2 ≤ (γ * e) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h6 2
    rwa [mul_pow, sq_abs] at this
  have h8 : (m - σ) ^ 2 * ((2 - w) ^ 2 * (γ * s)) ≤ (m - σ) ^ 2 * ((2 - w) * σ) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hσ2 (sq_nonneg _)
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  have h9 : γ * ((m - σ) ^ 2 * (s * (2 - w) ^ 2)) ≤ γ * (γ * e ^ 2) := by
    have e1 : γ * ((m - σ) ^ 2 * (s * (2 - w) ^ 2)) = (m - σ) ^ 2 * ((2 - w) ^ 2 * (γ * s)) := by
      ring
    have e2 : γ * (γ * e ^ 2) = (γ * e) ^ 2 := by ring
    rw [e1, e2]
    exact h8.trans h7
  exact le_of_mul_le_mul_left h9 hγ

section tools

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]

lemma int_bddV {f : Ξ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ξ, |f ξ| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hC ξ)

/-- `E(f − c)² = Var f + (E f − c)²` for a bounded measurable `f`. -/
lemma var_decompV {f : Ξ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ξ, |f ξ| ≤ C) (c : ℝ) :
    ∫ ξ, (f ξ - c) ^ 2 ∂μ = ∫ ξ, (f ξ - ∫ ζ, f ζ ∂μ) ^ 2 ∂μ + (∫ ζ, f ζ ∂μ - c) ^ 2 := by
  have hi : Integrable f μ := int_bddV hf hC
  set m : ℝ := ∫ ζ, f ζ ∂μ with hm
  have h2 : Integrable (fun ξ => (f ξ - m) ^ 2) μ := by
    refine int_bddV ((hf.sub_const m).pow_const 2) (C := (C + |m|) ^ 2) fun ξ => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    refine sq_le_of_absV ?_
    have := abs_sub (f ξ) m
    have := hC ξ
    linarith
  have h3 : Integrable (fun ξ => 2 * (m - c) * (f ξ - m)) μ :=
    (hi.sub (integrable_const m)).const_mul _
  have e : ∀ ξ, (f ξ - c) ^ 2 = (f ξ - m) ^ 2 + (2 * (m - c) * (f ξ - m) + (m - c) ^ 2) := by
    intro ξ; ring
  simp_rw [e]
  have h3c : Integrable (fun ξ => 2 * (m - c) * (f ξ - m) + (m - c) ^ 2) μ :=
    h3.add (integrable_const _)
  rw [integral_add h2 h3c, integral_add h3 (integrable_const _),
    integral_const_mul, integral_sub hi (integrable_const m), integral_const, integral_const]
  simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
  rw [← hm]
  ring

lemma var_le_V {f : Ξ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ξ, |f ξ| ≤ C) (c : ℝ) :
    ∫ ξ, (f ξ - ∫ ζ, f ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, (f ξ - c) ^ 2 ∂μ := by
  rw [var_decompV hf hC c]
  have := sq_nonneg (∫ ζ, f ζ ∂μ - c)
  linarith

/-- `E(a + b)² ≤ (A + B)²` if `E a² ≤ A²`, `E b² ≤ B²` (bounded measurable `a`, `b`). -/
lemma int_sq_add_le {a b : Ξ → ℝ} (ha : Measurable a) (hb : Measurable b) {Ca Cb : ℝ}
    (hCa : ∀ ξ, |a ξ| ≤ Ca) (hCb : ∀ ξ, |b ξ| ≤ Cb) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∫ ξ, a ξ ^ 2 ∂μ ≤ A ^ 2) (hB : ∫ ξ, b ξ ^ 2 ∂μ ≤ B ^ 2) :
    ∫ ξ, (a ξ + b ξ) ^ 2 ∂μ ≤ (A + B) ^ 2 := by
  have ia : Integrable (fun ξ => a ξ ^ 2) μ :=
    int_bddV (ha.pow_const 2) (C := Ca ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (hCa ξ)
  have ib : Integrable (fun ξ => b ξ ^ 2) μ :=
    int_bddV (hb.pow_const 2) (C := Cb ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (hCb ξ)
  have iab : Integrable (fun ξ => a ξ * b ξ) μ :=
    int_bddV (ha.mul hb) (C := Ca * Cb) fun ξ => by
      rw [abs_mul]
      exact mul_le_mul (hCa ξ) (hCb ξ) (abs_nonneg _) ((abs_nonneg _).trans (hCa ξ))
  have hcs := wcs iab ia ib (fun ξ => sq_nonneg _) (fun ξ => sq_nonneg _)
    (fun ξ => le_of_eq (by ring))
  have ia0 : 0 ≤ ∫ ξ, a ξ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  have ib0 : 0 ≤ ∫ ξ, b ξ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  have h1 : (∫ ξ, a ξ * b ξ ∂μ) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul hA hB ib0 (sq_nonneg _))
  have h2 := le_of_sqV (mul_nonneg hA0 hB0) h1
  have e : ∀ ξ, (a ξ + b ξ) ^ 2 = a ξ ^ 2 + (2 * (a ξ * b ξ) + b ξ ^ 2) := by intro ξ; ring
  simp_rw [e]
  have j : Integrable (fun ξ => 2 * (a ξ * b ξ) + b ξ ^ 2) μ := (iab.const_mul 2).add ib
  rw [integral_add ia j, integral_add (iab.const_mul 2) ib, integral_const_mul]
  nlinarith

/-- `E(1 + w)⁴ ≤ (1 + m)⁴` if `E w⁴ ≤ m⁴` (`w ≥ 0` bounded measurable). -/
lemma int_one_add_pow4 {w : Ξ → ℝ} (hw : Measurable w) (hw0 : ∀ ξ, 0 ≤ w ξ) {C : ℝ}
    (hC : ∀ ξ, w ξ ≤ C) {m : ℝ} (hm : 0 ≤ m) (h4 : ∫ ξ, w ξ ^ 4 ∂μ ≤ m ^ 4) :
    ∫ ξ, (1 + w ξ) ^ 4 ∂μ ≤ (1 + m) ^ 4 := by
  have ipow : ∀ j : ℕ, Integrable (fun ξ => w ξ ^ j) μ := fun j =>
    int_bddV (hw.pow_const j) (C := C ^ j) fun ξ => by
      rw [abs_of_nonneg (pow_nonneg (hw0 ξ) j)]
      exact pow_le_pow_left₀ (hw0 ξ) (hC ξ) j
  have i1 : Integrable w μ := by simpa using ipow 1
  have i2 := ipow 2
  have i3 := ipow 3
  have i4 := ipow 4
  have i40 : 0 ≤ ∫ ξ, w ξ ^ 4 ∂μ := integral_nonneg fun ξ => pow_nonneg (hw0 ξ) 4
  have i20 : 0 ≤ ∫ ξ, w ξ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  have c2 := wcs (P := μ) i2 (integrable_const (1 : ℝ)) i4 (fun _ => zero_le_one)
    (fun ξ => pow_nonneg (hw0 ξ) 4) (fun ξ => le_of_eq (by ring))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at c2
  have h2 : ∫ ξ, w ξ ^ 2 ∂μ ≤ m ^ 2 := by
    refine le_of_sqV (by positivity) ?_
    calc (∫ ξ, w ξ ^ 2 ∂μ) ^ 2 ≤ ∫ ξ, w ξ ^ 4 ∂μ := c2
      _ ≤ m ^ 4 := h4
      _ = (m ^ 2) ^ 2 := by ring
  have c1 := wcs (P := μ) i1 (integrable_const (1 : ℝ)) i2 (fun _ => zero_le_one)
    (fun ξ => sq_nonneg _) (fun ξ => le_of_eq (by ring))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at c1
  have h1 : ∫ ξ, w ξ ∂μ ≤ m := le_of_sqV hm (c1.trans h2)
  have c3 := wcs (P := μ) i3 i2 i4 (fun ξ => sq_nonneg _) (fun ξ => pow_nonneg (hw0 ξ) 4)
    (fun ξ => le_of_eq (by ring))
  have h3 : ∫ ξ, w ξ ^ 3 ∂μ ≤ m ^ 3 := by
    refine le_of_sqV (by positivity) ?_
    calc (∫ ξ, w ξ ^ 3 ∂μ) ^ 2 ≤ (∫ ξ, w ξ ^ 2 ∂μ) * ∫ ξ, w ξ ^ 4 ∂μ := c3
      _ ≤ m ^ 2 * m ^ 4 := mul_le_mul h2 h4 i40 (by positivity)
      _ = (m ^ 3) ^ 2 := by ring
  have e : ∀ ξ, (1 + w ξ) ^ 4 = 1 + (4 * w ξ + (6 * w ξ ^ 2 + (4 * w ξ ^ 3 + w ξ ^ 4))) := by
    intro ξ; ring
  simp_rw [e]
  have j3 : Integrable (fun ξ => 4 * w ξ ^ 3 + w ξ ^ 4) μ := (i3.const_mul 4).add i4
  have j2 : Integrable (fun ξ => 6 * w ξ ^ 2 + (4 * w ξ ^ 3 + w ξ ^ 4)) μ :=
    (i2.const_mul 6).add j3
  have j1 : Integrable (fun ξ => 4 * w ξ + (6 * w ξ ^ 2 + (4 * w ξ ^ 3 + w ξ ^ 4))) μ :=
    (i1.const_mul 4).add j2
  rw [integral_add (integrable_const 1) j1, integral_add (i1.const_mul 4) j2,
    integral_add (i2.const_mul 6) j3, integral_add (i3.const_mul 4) i4, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  nlinarith [h1, h2, h3, h4]

end tools

/-! ## Definitions -/

section V

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- `ρ = |v| = |q|`. -/
noncomputable def rhoV (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : ℝ := √(v₁ ξ ^ 2 + v₂ ξ ^ 2)

/-- `u = ρ/√γ − 1` (the document: `√ω₂ − 1`). -/
noncomputable def uV (γ : ℝ) (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : ℝ := rhoV v₁ v₂ ξ / √γ - 1

/-- The angle `Θ = arccos(v₁/ρ)`. -/
noncomputable def thetaV (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : ℝ := Real.arccos (v₁ ξ / rhoV v₁ v₂ ξ)

/-- `r_ϑ = √γ·(1 − ϑ)`. -/
noncomputable def rV (γ ϑ : ℝ) : ℝ := √γ * (1 - ϑ)

/-- The truncated angle `φ = Θ·min(1, ρ/r_ϑ)`. -/
noncomputable def phiV (γ ϑ : ℝ) (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : ℝ :=
  thetaV v₁ v₂ ξ * min 1 (rhoV v₁ v₂ ξ / rV γ ϑ)

/-- The square of the bound of the pointwise Lipschitz constant of `φ`: `1/ρ²` where `ρ > r_ϑ`,
`6.61/r_ϑ²` where `ρ ≤ r_ϑ`. -/
noncomputable def ellSqV (γ ϑ : ℝ) (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : ℝ :=
  if rV γ ϑ < rhoV v₁ v₂ ξ then 1 / rhoV v₁ v₂ ξ ^ 2 else 661 / 100 / rV γ ϑ ^ 2

/-- `κ_ϑ`. -/
noncomputable def kappaV (ϑ N24 : ℝ) : ℝ :=
  (1 + N24 / (1 - ϑ)) ^ 2 + 661 / 100 * N24 ^ 2 / ((1 - ϑ) ^ 2 * ϑ ^ 2)

/-- `𝔯_ϑ`. -/
noncomputable def rthV (ϑ N22 N24 : ℝ) : ℝ := N22 + 2 * N24 ^ 2 / ϑ ^ 2

/-- `e_Δ`. -/
noncomputable def eDeltaV (n sstar MP xi N22 : ℝ) : ℝ :=
  N22 * (2 + N22) + (2 * MP + xi) / n + 2 * √((1 - sstar) * xi / n)

/-- `𝔡 = e_Δ²/(s_*(2 − ϖ)²)`, `ϖ = e_Δ/s_*`. -/
noncomputable def dfrakV (n sstar MP xi N22 : ℝ) : ℝ :=
  eDeltaV n sstar MP xi N22 ^ 2 /
    (sstar * (2 - eDeltaV n sstar MP xi N22 / sstar) ^ 2)

variable {v₁ v₂ : Ξ → ℝ}

lemma rhoV_nonneg (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : 0 ≤ rhoV v₁ v₂ ξ := Real.sqrt_nonneg _

lemma rhoV_sq (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) : rhoV v₁ v₂ ξ ^ 2 = v₁ ξ ^ 2 + v₂ ξ ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma measurable_rhoV (hv1 : Measurable v₁) (hv2 : Measurable v₂) : Measurable (rhoV v₁ v₂) :=
  ((hv1.pow_const 2).add (hv2.pow_const 2)).sqrt

lemma measurable_uV (γ : ℝ) (hv1 : Measurable v₁) (hv2 : Measurable v₂) :
    Measurable (uV γ v₁ v₂) :=
  ((measurable_rhoV hv1 hv2).div_const _).sub_const _

lemma measurable_phiV (γ ϑ : ℝ) (hv1 : Measurable v₁) (hv2 : Measurable v₂) :
    Measurable (phiV γ ϑ v₁ v₂) :=
  (Real.continuous_arccos.measurable.comp (hv1.div (measurable_rhoV hv1 hv2))).mul
    (measurable_const.min ((measurable_rhoV hv1 hv2).div_const _))

lemma rhoV_le {H : ℝ} (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H) (ξ : Ξ) : rhoV v₁ v₂ ξ ≤ √H :=
  Real.sqrt_le_sqrt (hH ξ)

lemma rhoV_eq {γ : ℝ} (hγ : 0 < γ) (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) :
    rhoV v₁ v₂ ξ = √γ * (1 + uV γ v₁ v₂ ξ) := by
  have : 0 < √γ := Real.sqrt_pos.mpr hγ
  unfold uV; field_simp; ring

lemma uV_abs_le {γ H : ℝ} (hγ : 0 < γ) (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H) (ξ : Ξ) :
    |uV γ v₁ v₂ ξ| ≤ √H / √γ + 1 := by
  have hs : 0 < √γ := Real.sqrt_pos.mpr hγ
  have h0 : 0 ≤ rhoV v₁ v₂ ξ / √γ := div_nonneg (rhoV_nonneg _ _ _) hs.le
  have h1 : rhoV v₁ v₂ ξ / √γ ≤ √H / √γ := div_le_div_of_nonneg_right (rhoV_le hH ξ) hs.le
  unfold uV
  rw [abs_le]
  constructor <;> linarith

lemma phiV_abs_le {γ ϑ : ℝ} (hγ : 0 < γ) (hϑ1 : ϑ < 1) (v₁ v₂ : Ξ → ℝ) (ξ : Ξ) :
    |phiV γ ϑ v₁ v₂ ξ| ≤ Real.pi := by
  have hr : 0 < rV γ ϑ := mul_pos (Real.sqrt_pos.mpr hγ) (by linarith)
  have h1 : 0 ≤ min 1 (rhoV v₁ v₂ ξ / rV γ ϑ) :=
    le_min zero_le_one (div_nonneg (rhoV_nonneg _ _ _) hr.le)
  have h2 : min 1 (rhoV v₁ v₂ ξ / rV γ ϑ) ≤ 1 := min_le_left _ _
  have h3 := Real.arccos_nonneg (v₁ ξ / rhoV v₁ v₂ ξ)
  have h4 := Real.arccos_le_pi (v₁ ξ / rhoV v₁ v₂ ξ)
  unfold phiV thetaV
  rw [abs_of_nonneg (mul_nonneg h3 h1)]
  calc _ ≤ Real.pi * 1 := mul_le_mul h4 h2 h1 Real.pi_pos.le
    _ = Real.pi := mul_one _

/-- Where `ρ > 0` and `v₂ ≥ 0`: `v = ρ(cos Θ, sin Θ)`. -/
lemma trigV (hv20 : ∀ ξ, 0 ≤ v₂ ξ) {ξ : Ξ} (hρ : 0 < rhoV v₁ v₂ ξ) :
    Real.cos (thetaV v₁ v₂ ξ) = v₁ ξ / rhoV v₁ v₂ ξ ∧
      Real.sin (thetaV v₁ v₂ ξ) = v₂ ξ / rhoV v₁ v₂ ξ := by
  have hsq := rhoV_sq v₁ v₂ ξ
  set ρ := rhoV v₁ v₂ ξ
  have hx2 : (v₁ ξ / ρ) ^ 2 ≤ 1 ^ 2 := by
    rw [div_pow, one_pow, div_le_one (by positivity)]
    nlinarith [sq_nonneg (v₂ ξ)]
  have hx := abs_le_of_sq_le_sq' hx2 zero_le_one
  unfold thetaV
  refine ⟨Real.cos_arccos hx.1 hx.2, ?_⟩
  rw [Real.sin_arccos]
  have e : 1 - (v₁ ξ / ρ) ^ 2 = (v₂ ξ / ρ) ^ 2 := by
    rw [div_pow, div_pow]
    field_simp
    linarith
  rw [e, Real.sqrt_sq (div_nonneg (hv20 ξ) hρ.le)]

/-! ## Step 2a: the variance of the truncated angle -/

/-- **Lemma V, Step 2a**: `Var φ ≤ κ_ϑ·M_P/n`. -/
theorem stepV_2a (μ : Measure Ξ) [IsProbabilityMeasure μ] {X : Ξ → ℝ} (hv1 : Measurable v₁)
    (hv2 : Measurable v₂) {H : ℝ} (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H) {γ ϑ n MP N24 : ℝ}
    (hγ : 0 < γ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hn : 0 < n) (hMP : 0 ≤ MP) (hN24 : 0 ≤ N24)
    (hXm : Measurable X) (hX0 : ∀ ξ, 0 ≤ X ξ) (hX2i : Integrable (fun ξ => X ξ ^ 2) μ)
    (hX2 : ∫ ξ, X ξ ^ 2 ∂μ ≤ (MP * γ / n) ^ 2)
    (h4 : ∫ ξ, uV γ v₁ v₂ ξ ^ 4 ∂μ ≤ N24 ^ 4)
    (hP : ∫ ξ, (phiV γ ϑ v₁ v₂ ξ - ∫ ζ, phiV γ ϑ v₁ v₂ ζ ∂μ) ^ 2 ∂μ ≤
      ∫ ξ, X ξ * ellSqV γ ϑ v₁ v₂ ξ ∂μ) :
    ∫ ξ, (phiV γ ϑ v₁ v₂ ξ - ∫ ζ, phiV γ ϑ v₁ v₂ ζ ∂μ) ^ 2 ∂μ ≤ kappaV ϑ N24 * MP / n := by
  have hsγ : 0 < √γ := Real.sqrt_pos.mpr hγ
  have hsγ2 : √γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have h1ϑ : 0 < 1 - ϑ := by linarith
  set r : ℝ := rV γ ϑ with hr
  have hr0 : 0 < r := mul_pos hsγ h1ϑ
  have hr2 : r ^ 2 = γ * (1 - ϑ) ^ 2 := by rw [hr, rV, mul_pow, hsγ2]
  have hρm := measurable_rhoV hv1 hv2
  have hum := measurable_uV γ hv1 hv2
  set ρ := rhoV v₁ v₂ with hρ
  set u := uV γ v₁ v₂ with hu
  have hρu : ∀ ξ, ρ ξ = √γ * (1 + u ξ) := fun ξ => rhoV_eq hγ v₁ v₂ ξ
  have hCu : ∀ ξ, |u ξ| ≤ √H / √γ + 1 := fun ξ => uV_abs_le hγ hH ξ
  -- the two parts of `ℓ²`
  set A : Ξ → ℝ := fun ξ => if r < ρ ξ then 1 / ρ ξ ^ 2 else 0 with hA
  set B : Ξ → ℝ := fun ξ => if r < ρ ξ then 0 else 661 / 100 / r ^ 2 with hB
  have mS : MeasurableSet {ξ | r < ρ ξ} := measurableSet_lt measurable_const hρm
  have mA : Measurable A := Measurable.ite mS (measurable_const.div (hρm.pow_const 2))
    measurable_const
  have mB : Measurable B := Measurable.ite mS measurable_const measurable_const
  have hell : ∀ ξ, ellSqV γ ϑ v₁ v₂ ξ = A ξ + B ξ := by
    intro ξ
    show (if r < ρ ξ then 1 / ρ ξ ^ 2 else 661 / 100 / r ^ 2) = A ξ + B ξ
    simp only [hA, hB]
    split_ifs <;> simp
  have hA0 : ∀ ξ, 0 ≤ A ξ := by
    intro ξ; simp only [hA]; split_ifs <;> positivity
  have hB0 : ∀ ξ, 0 ≤ B ξ := by
    intro ξ; simp only [hB]; split_ifs <;> positivity
  have hAle : ∀ ξ, A ξ ≤ 1 / r ^ 2 := by
    intro ξ
    simp only [hA]
    split_ifs with h
    · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hr0.le h.le 2)
    · positivity
  have hBle : ∀ ξ, B ξ ≤ 661 / 100 / r ^ 2 := by
    intro ξ
    simp only [hB]
    split_ifs
    · positivity
    · exact le_rfl
  -- pointwise bounds
  set w : Ξ → ℝ := fun ξ => |u ξ| / (1 - ϑ) with hw
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => div_nonneg (abs_nonneg _) h1ϑ.le
  have mw : Measurable w := hum.abs.div_const _
  have hwC : ∀ ξ, w ξ ≤ (√H / √γ + 1) / (1 - ϑ) := fun ξ =>
    div_le_div_of_nonneg_right (hCu ξ) h1ϑ.le
  have hAw : ∀ ξ, A ξ ≤ (1 + w ξ) ^ 2 / γ := by
    intro ξ
    simp only [hA]
    split_ifs with h
    · have hρ0 : 0 < ρ ξ := lt_trans hr0 h
      set t : ℝ := 1 + u ξ with ht
      have hρt : ρ ξ = √γ * t := hρu ξ
      have htϑ : 1 - ϑ < t := by
        have : √γ * (1 - ϑ) < √γ * t := by rw [← hρt]; exact h
        exact lt_of_mul_lt_mul_left this hsγ.le
      have ht0 : 0 < t := lt_trans h1ϑ htϑ
      have hR : 1 ≤ t * (1 + w ξ) := by
        simp only [hw]
        rcases le_total 1 t with h1 | h1
        · have : 0 ≤ |u ξ| / (1 - ϑ) := div_nonneg (abs_nonneg _) h1ϑ.le
          nlinarith
        · have hu' : |u ξ| = 1 - t := by
            rw [abs_of_nonpos (by linarith : u ξ ≤ 0)]; linarith
          rw [hu']
          have e : t * (1 + (1 - t) / (1 - ϑ)) = (t * (1 - ϑ) + t * (1 - t)) / (1 - ϑ) := by
            field_simp
          rw [e, le_div_iff₀ h1ϑ]
          nlinarith
      rw [div_le_div_iff₀ (by positivity) hγ, hρt, mul_pow, hsγ2]
      have hR2 : 1 ≤ (t * (1 + w ξ)) ^ 2 := by
        have := pow_le_pow_left₀ zero_le_one hR 2
        simpa using this
      nlinarith
    · have : 0 ≤ (1 + w ξ) ^ 2 / γ := by positivity
      exact this
  have hBu : ∀ ξ, B ξ ^ 2 ≤ (661 / 100 / r ^ 2) ^ 2 * (u ξ ^ 4 / ϑ ^ 4) := by
    intro ξ
    simp only [hB]
    split_ifs with h
    · have : 0 ≤ (661 / 100 / r ^ 2) ^ 2 * (u ξ ^ 4 / ϑ ^ 4) := by positivity
      simpa using this
    · have hle : ρ ξ ≤ r := not_lt.mp h
      have hu' : u ξ ≤ -ϑ := by
        have h1 : √γ * (1 + u ξ) ≤ √γ * (1 - ϑ) := by rw [← hρu ξ]; exact hle
        have := le_of_mul_le_mul_left h1 hsγ
        linarith
      have h2 : ϑ ^ 2 ≤ u ξ ^ 2 := by nlinarith
      have h4' : ϑ ^ 4 ≤ u ξ ^ 4 := by
        have := pow_le_pow_left₀ (by positivity) h2 2
        calc ϑ ^ 4 = (ϑ ^ 2) ^ 2 := by ring
          _ ≤ (u ξ ^ 2) ^ 2 := this
          _ = u ξ ^ 4 := by ring
      have h5 : 1 ≤ u ξ ^ 4 / ϑ ^ 4 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h6 : 0 ≤ (661 / 100 / r ^ 2) ^ 2 := sq_nonneg _
      nlinarith
  -- integrability
  have hXi : Integrable X μ := by
    refine ((integrable_const (1 : ℝ)).add hX2i).mono' hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ξ)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X ξ - 1)]
  have iXA : Integrable (fun ξ => X ξ * A ξ) μ := by
    refine (hXi.mul_const (1 / r ^ 2)).mono' (hXm.mul mA).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hX0 ξ) (hA0 ξ))]
    exact mul_le_mul_of_nonneg_left (hAle ξ) (hX0 ξ)
  have iXB : Integrable (fun ξ => X ξ * B ξ) μ := by
    refine (hXi.mul_const (661 / 100 / r ^ 2)).mono' (hXm.mul mB).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hX0 ξ) (hB0 ξ))]
    exact mul_le_mul_of_nonneg_left (hBle ξ) (hX0 ξ)
  have iA2 : Integrable (fun ξ => A ξ ^ 2) μ :=
    int_bddV (mA.pow_const 2) (C := (1 / r ^ 2) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hA0 ξ) (hAle ξ) 2
  have iB2 : Integrable (fun ξ => B ξ ^ 2) μ :=
    int_bddV (mB.pow_const 2) (C := (661 / 100 / r ^ 2) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hB0 ξ) (hBle ξ) 2
  have iu4 : Integrable (fun ξ => u ξ ^ 4) μ :=
    int_bddV (hum.pow_const 4) (C := (√H / √γ + 1) ^ 4) fun ξ => by
      rw [abs_of_nonneg (by positivity)]
      calc u ξ ^ 4 = |u ξ| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hCu ξ) 4
  have iX20 : 0 ≤ ∫ ξ, X ξ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  -- the integral of `A²`
  set m : ℝ := N24 / (1 - ϑ) with hm
  have hm0 : 0 ≤ m := div_nonneg hN24 h1ϑ.le
  have hw4 : ∫ ξ, w ξ ^ 4 ∂μ ≤ m ^ 4 := by
    have e : ∀ ξ, w ξ ^ 4 = u ξ ^ 4 * (1 / (1 - ϑ) ^ 4) := by
      intro ξ
      simp only [hw]
      rw [div_pow, ← abs_pow, abs_of_nonneg (by positivity)]
      ring
    simp_rw [e]
    rw [integral_mul_const, hm, div_pow]
    have : (∫ ξ, u ξ ^ 4 ∂μ) * (1 / (1 - ϑ) ^ 4) ≤ N24 ^ 4 * (1 / (1 - ϑ) ^ 4) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    refine this.trans (le_of_eq ?_)
    ring
  have h1w := int_one_add_pow4 (μ := μ) mw hw0 hwC hm0 hw4
  have i1w : Integrable (fun ξ => (1 + w ξ) ^ 4 / γ ^ 2) μ :=
    int_bddV (((measurable_const.add mw).pow_const 4).div_const _)
      (C := (1 + (√H / √γ + 1) / (1 - ϑ)) ^ 4 / γ ^ 2) fun ξ => by
        rw [abs_of_nonneg (by have := hw0 ξ; positivity)]
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (by have := hw0 ξ; positivity) (by have := hwC ξ; linarith) 4)
          (by positivity)
  have hA2 : ∫ ξ, A ξ ^ 2 ∂μ ≤ (1 + m) ^ 4 / γ ^ 2 := by
    calc ∫ ξ, A ξ ^ 2 ∂μ ≤ ∫ ξ, (1 + w ξ) ^ 4 / γ ^ 2 ∂μ := by
          refine integral_mono iA2 i1w fun ξ => ?_
          have := pow_le_pow_left₀ (hA0 ξ) (hAw ξ) 2
          refine this.trans (le_of_eq ?_)
          rw [div_pow]; ring
      _ = (∫ ξ, (1 + w ξ) ^ 4 ∂μ) / γ ^ 2 := integral_div _ _
      _ ≤ (1 + m) ^ 4 / γ ^ 2 := div_le_div_of_nonneg_right h1w (by positivity)
  have hB2 : ∫ ξ, B ξ ^ 2 ∂μ ≤ (661 / 100 / r ^ 2) ^ 2 * (N24 ^ 4 / ϑ ^ 4) := by
    calc ∫ ξ, B ξ ^ 2 ∂μ ≤ ∫ ξ, (661 / 100 / r ^ 2) ^ 2 * (u ξ ^ 4 / ϑ ^ 4) ∂μ :=
          integral_mono iB2 ((iu4.div_const _).const_mul _) hBu
      _ = (661 / 100 / r ^ 2) ^ 2 * ((∫ ξ, u ξ ^ 4 ∂μ) / ϑ ^ 4) := by
          rw [integral_const_mul, integral_div]
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h4 (by positivity))
          (sq_nonneg _)
  -- Cauchy–Schwarz
  have cA := wcs iXA hX2i iA2 (fun ξ => sq_nonneg _) (fun ξ => sq_nonneg _)
    (fun ξ => le_of_eq (by ring))
  have cB := wcs iXB hX2i iB2 (fun ξ => sq_nonneg _) (fun ξ => sq_nonneg _)
    (fun ξ => le_of_eq (by ring))
  have iA20 : 0 ≤ ∫ ξ, A ξ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  have iB20 : 0 ≤ ∫ ξ, B ξ ^ 2 ∂μ := integral_nonneg fun ξ => sq_nonneg _
  have hXA : ∫ ξ, X ξ * A ξ ∂μ ≤ MP / n * (1 + m) ^ 2 := by
    refine le_of_sqV (by positivity) ?_
    calc (∫ ξ, X ξ * A ξ ∂μ) ^ 2 ≤ (∫ ξ, X ξ ^ 2 ∂μ) * ∫ ξ, A ξ ^ 2 ∂μ := cA
      _ ≤ (MP * γ / n) ^ 2 * ((1 + m) ^ 4 / γ ^ 2) := mul_le_mul hX2 hA2 iA20 (sq_nonneg _)
      _ = (MP / n * (1 + m) ^ 2) ^ 2 := by field_simp
  have hXB : ∫ ξ, X ξ * B ξ ∂μ ≤ MP / n * (661 / 100 * N24 ^ 2 / ((1 - ϑ) ^ 2 * ϑ ^ 2)) := by
    refine le_of_sqV (by positivity) ?_
    calc (∫ ξ, X ξ * B ξ ∂μ) ^ 2 ≤ (∫ ξ, X ξ ^ 2 ∂μ) * ∫ ξ, B ξ ^ 2 ∂μ := cB
      _ ≤ (MP * γ / n) ^ 2 * ((661 / 100 / r ^ 2) ^ 2 * (N24 ^ 4 / ϑ ^ 4)) :=
          mul_le_mul hX2 hB2 iB20 (sq_nonneg _)
      _ = (MP / n * (661 / 100 * N24 ^ 2 / ((1 - ϑ) ^ 2 * ϑ ^ 2))) ^ 2 := by
          rw [hr2]; field_simp
  refine hP.trans ?_
  have e : ∀ ξ, X ξ * ellSqV γ ϑ v₁ v₂ ξ = X ξ * A ξ + X ξ * B ξ := by
    intro ξ; rw [hell ξ]; ring
  simp_rw [e]
  rw [integral_add iXA iXB]
  have ek : kappaV ϑ N24 * MP / n =
      MP / n * (1 + m) ^ 2 + MP / n * (661 / 100 * N24 ^ 2 / ((1 - ϑ) ^ 2 * ϑ ^ 2)) := by
    rw [kappaV, hm]; ring
  rw [ek]
  linarith

/-! ## Step 2b: the covariance of `v` -/

/-- **Lemma V, Step 2b**: `tr Cov v ≤ γ·(𝔯_ϑ + √Vφ)²` if `Var φ ≤ Vφ`. -/
theorem stepV_2b (μ : Measure Ξ) [IsProbabilityMeasure μ] (hv1 : Measurable v₁)
    (hv2 : Measurable v₂) (hv20 : ∀ ξ, 0 ≤ v₂ ξ) {H : ℝ} (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H)
    {γ ϑ Vφ N22 N24 : ℝ} (hγ : 0 < γ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hVφ0 : 0 ≤ Vφ)
    (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24)
    (hVφ : ∫ ξ, (phiV γ ϑ v₁ v₂ ξ - ∫ ζ, phiV γ ϑ v₁ v₂ ζ ∂μ) ^ 2 ∂μ ≤ Vφ)
    (h2 : ∫ ξ, uV γ v₁ v₂ ξ ^ 2 ∂μ ≤ N22 ^ 2) (h4 : ∫ ξ, uV γ v₁ v₂ ξ ^ 4 ∂μ ≤ N24 ^ 4) :
    ∫ ξ, (v₁ ξ - ∫ ζ, v₁ ζ ∂μ) ^ 2 ∂μ + ∫ ξ, (v₂ ξ - ∫ ζ, v₂ ζ ∂μ) ^ 2 ∂μ ≤
      γ * (rthV ϑ N22 N24 + √Vφ) ^ 2 := by
  have hsγ : 0 < √γ := Real.sqrt_pos.mpr hγ
  have hsγ2 : √γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have h1ϑ : 0 < 1 - ϑ := by linarith
  set r : ℝ := rV γ ϑ with hr
  have hr0 : 0 < r := mul_pos hsγ h1ϑ
  have hrγ : r ≤ √γ := by rw [hr, rV]; nlinarith
  have hρm := measurable_rhoV hv1 hv2
  have hum := measurable_uV γ hv1 hv2
  have hφm := measurable_phiV γ ϑ hv1 hv2
  set ρ := rhoV v₁ v₂ with hρ
  set u := uV γ v₁ v₂ with hu
  set φ := phiV γ ϑ v₁ v₂ with hφ
  have hρu : ∀ ξ, ρ ξ = √γ * (1 + u ξ) := fun ξ => rhoV_eq hγ v₁ v₂ ξ
  have hCu : ∀ ξ, |u ξ| ≤ √H / √γ + 1 := fun ξ => uV_abs_le hγ hH ξ
  have hCφ : ∀ ξ, |φ ξ| ≤ Real.pi := fun ξ => phiV_abs_le hγ hϑ1 v₁ v₂ ξ
  set φb : ℝ := ∫ ζ, φ ζ ∂μ with hφb
  set c₁ : ℝ := √γ * Real.cos φb with hc₁
  set c₂ : ℝ := √γ * Real.sin φb with hc₂
  -- bounds of `v₁`, `v₂`
  have hC1 : ∀ ξ, |v₁ ξ| ≤ √H := fun ξ => by
    apply Real.abs_le_sqrt
    nlinarith [hH ξ, sq_nonneg (v₂ ξ)]
  have hC2 : ∀ ξ, |v₂ ξ| ≤ √H := fun ξ => by
    apply Real.abs_le_sqrt
    nlinarith [hH ξ, sq_nonneg (v₁ ξ)]
  have hle1 := var_le_V (μ := μ) hv1 hC1 c₁
  have hle2 := var_le_V (μ := μ) hv2 hC2 c₂
  -- the two functions
  set aF : Ξ → ℝ := fun ξ => √γ * (if r ≤ ρ ξ then |u ξ| else 2) with haF
  set bF : Ξ → ℝ := fun ξ => √γ * |φ ξ - φb| with hbF
  have mS : MeasurableSet {ξ | r ≤ ρ ξ} := measurableSet_le measurable_const hρm
  have maF : Measurable aF := measurable_const.mul (Measurable.ite mS hum.abs measurable_const)
  have mbF : Measurable bF := measurable_const.mul (hφm.sub_const _).abs
  have haF0 : ∀ ξ, 0 ≤ aF ξ := by
    intro ξ; simp only [haF]; split_ifs <;> positivity
  have hbF0 : ∀ ξ, 0 ≤ bF ξ := fun ξ => by simp only [hbF]; positivity
  have haFC : ∀ ξ, |aF ξ| ≤ √γ * (√H / √γ + 1 + 2) := by
    intro ξ
    rw [abs_of_nonneg (haF0 ξ)]
    simp only [haF]
    refine mul_le_mul_of_nonneg_left ?_ hsγ.le
    have := hCu ξ
    have := abs_nonneg (u ξ)
    split_ifs <;> linarith
  have hφbC : |φb| ≤ Real.pi := by
    have h1 := abs_integral_le_integral_abs (f := φ) (μ := μ)
    have h2 : ∫ ξ, |φ ξ| ∂μ ≤ ∫ _ξ, Real.pi ∂μ :=
      integral_mono (int_bddV hφm.abs (C := Real.pi) fun ξ => by rw [abs_abs]; exact hCφ ξ)
        (integrable_const _) hCφ
    simp only [integral_const, probReal_univ, one_smul] at h2
    exact h1.trans h2
  have hbFC : ∀ ξ, |bF ξ| ≤ √γ * (Real.pi + Real.pi) := by
    intro ξ
    rw [abs_of_nonneg (hbF0 ξ)]
    simp only [hbF]
    refine mul_le_mul_of_nonneg_left ?_ hsγ.le
    have := abs_sub (φ ξ) φb
    have := hCφ ξ
    linarith
  -- pointwise
  have hpt : ∀ ξ, (v₁ ξ - c₁) ^ 2 + (v₂ ξ - c₂) ^ 2 ≤ (aF ξ + bF ξ) ^ 2 := by
    intro ξ
    have e1 : v₁ ξ - c₁ = (v₁ ξ - √γ * Real.cos (φ ξ)) + (√γ * Real.cos (φ ξ) - c₁) := by ring
    have e2 : v₂ ξ - c₂ = (v₂ ξ - √γ * Real.sin (φ ξ)) + (√γ * Real.sin (φ ξ) - c₂) := by ring
    rw [e1, e2]
    refine sq2_add_le (haF0 ξ) (hbF0 ξ) ?_ ?_
    · -- `|v − ṽ|² ≤ aF²`
      have hcs := Real.cos_sq_add_sin_sq (φ ξ)
      have hsq := rhoV_sq v₁ v₂ ξ
      simp only [haF]
      split_ifs with h
      · have hρ0 : 0 < ρ ξ := lt_of_lt_of_le hr0 h
        obtain ⟨hc, hs⟩ := trigV (v₁ := v₁) hv20 hρ0
        have hmin : min 1 (ρ ξ / r) = 1 := min_eq_left (by rw [le_div_iff₀ hr0]; linarith)
        have hφξ : φ ξ = thetaV v₁ v₂ ξ := by
          show thetaV v₁ v₂ ξ * min 1 (ρ ξ / r) = thetaV v₁ v₂ ξ
          rw [hmin, mul_one]
        rw [hφξ] at hcs ⊢
        rw [hc, hs] at hcs ⊢
        have hx1 : v₁ ξ - √γ * (v₁ ξ / ρ ξ) = v₁ ξ / ρ ξ * (ρ ξ - √γ) := by field_simp
        have hx2 : v₂ ξ - √γ * (v₂ ξ / ρ ξ) = v₂ ξ / ρ ξ * (ρ ξ - √γ) := by field_simp
        have hu1 : ρ ξ - √γ = √γ * u ξ := by rw [hρu ξ]; ring
        refine le_of_eq ?_
        calc (v₁ ξ - √γ * (v₁ ξ / ρ ξ)) ^ 2 + (v₂ ξ - √γ * (v₂ ξ / ρ ξ)) ^ 2
            = ((v₁ ξ / ρ ξ) ^ 2 + (v₂ ξ / ρ ξ) ^ 2) * (ρ ξ - √γ) ^ 2 := by
              rw [hx1, hx2]; ring
          _ = (√γ * |u ξ|) ^ 2 := by
              rw [hcs, one_mul, hu1, mul_pow, mul_pow, sq_abs]
      · have hlt : ρ ξ < r := not_le.mp h
        have hρ0 : 0 ≤ ρ ξ := rhoV_nonneg _ _ _
        have hcross : (v₁ ξ * Real.cos (φ ξ) + v₂ ξ * Real.sin (φ ξ)) ^ 2 ≤ ρ ξ ^ 2 := by
          rw [hρ, hsq]
          nlinarith [sq_nonneg (v₁ ξ * Real.sin (φ ξ) - v₂ ξ * Real.cos (φ ξ))]
        have hc2 := abs_le_of_sq_le_sq' hcross hρ0
        have e : (v₁ ξ - √γ * Real.cos (φ ξ)) ^ 2 + (v₂ ξ - √γ * Real.sin (φ ξ)) ^ 2 =
            (v₁ ξ ^ 2 + v₂ ξ ^ 2) - 2 * √γ * (v₁ ξ * Real.cos (φ ξ) + v₂ ξ * Real.sin (φ ξ)) +
              γ * (Real.cos (φ ξ) ^ 2 + Real.sin (φ ξ) ^ 2) := by
          linear_combination (Real.cos (φ ξ) ^ 2 + Real.sin (φ ξ) ^ 2) * hsγ2
        have h1 : ρ ξ ≤ √γ := hlt.le.trans hrγ
        have h3 : ρ ξ ^ 2 ≤ √γ ^ 2 := pow_le_pow_left₀ hρ0 h1 2
        have h4' : √γ * ρ ξ ≤ √γ * √γ := mul_le_mul_of_nonneg_left h1 hsγ.le
        have h5 : √γ * √γ = γ := Real.mul_self_sqrt hγ.le
        have h6 : √γ * (v₁ ξ * Real.cos (φ ξ) + v₂ ξ * Real.sin (φ ξ)) ≥ -(√γ * ρ ξ) := by
          have := mul_le_mul_of_nonneg_left hc2.1 hsγ.le
          linarith
        have h7 : (√γ * 2) ^ 2 = 4 * γ := by rw [mul_pow, hsγ2]; ring
        rw [e, hcs, ← hsq, h7]
        have h8 : rhoV v₁ v₂ ξ ^ 2 = ρ ξ ^ 2 := rfl
        rw [h8]
        linarith
    · -- `|ṽ − c|² ≤ bF²`
      show (√γ * Real.cos (φ ξ) - √γ * Real.cos φb) ^ 2 +
          (√γ * Real.sin (φ ξ) - √γ * Real.sin φb) ^ 2 ≤ (√γ * |φ ξ - φb|) ^ 2
      have hcos := Real.one_sub_sq_div_two_le_cos (x := φ ξ - φb)
      rw [Real.cos_sub] at hcos
      have h1 := Real.cos_sq_add_sin_sq (φ ξ)
      have h2' := Real.cos_sq_add_sin_sq φb
      have e : (√γ * Real.cos (φ ξ) - √γ * Real.cos φb) ^ 2 +
          (√γ * Real.sin (φ ξ) - √γ * Real.sin φb) ^ 2 =
          γ * ((Real.cos (φ ξ) ^ 2 + Real.sin (φ ξ) ^ 2) + (Real.cos φb ^ 2 + Real.sin φb ^ 2) -
            2 * (Real.cos (φ ξ) * Real.cos φb + Real.sin (φ ξ) * Real.sin φb)) := by
        linear_combination ((Real.cos (φ ξ) ^ 2 + Real.sin (φ ξ) ^ 2) +
          (Real.cos φb ^ 2 + Real.sin φb ^ 2) -
            2 * (Real.cos (φ ξ) * Real.cos φb + Real.sin (φ ξ) * Real.sin φb)) * hsγ2
      have e2 : (√γ * |φ ξ - φb|) ^ 2 = γ * (φ ξ - φb) ^ 2 := by
        rw [mul_pow, hsγ2, sq_abs]
      rw [e, h1, h2', e2]
      refine mul_le_mul_of_nonneg_left ?_ hγ.le
      linarith
  -- the integrals of `aF²`, `bF²`
  have iu2 : Integrable (fun ξ => u ξ ^ 2) μ :=
    int_bddV (hum.pow_const 2) (C := (√H / √γ + 1) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (hCu ξ)
  have iu4 : Integrable (fun ξ => u ξ ^ 4) μ :=
    int_bddV (hum.pow_const 4) (C := (√H / √γ + 1) ^ 4) fun ξ => by
      rw [abs_of_nonneg (by positivity)]
      calc u ξ ^ 4 = |u ξ| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hCu ξ) 4
  have iaF : Integrable (fun ξ => aF ξ ^ 2) μ :=
    int_bddV (maF.pow_const 2) (C := (√γ * (√H / √γ + 1 + 2)) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (haFC ξ)
  have haFpt : ∀ ξ, aF ξ ^ 2 ≤ γ * (u ξ ^ 2 + 4 * (u ξ ^ 4 / ϑ ^ 4)) := by
    intro ξ
    simp only [haF]
    rw [mul_pow, hsγ2]
    refine mul_le_mul_of_nonneg_left ?_ hγ.le
    split_ifs with h
    · rw [sq_abs]
      have : 0 ≤ 4 * (u ξ ^ 4 / ϑ ^ 4) := by positivity
      linarith
    · have hlt : ρ ξ < r := not_le.mp h
      have hu' : u ξ ≤ -ϑ := by
        have h1 : √γ * (1 + u ξ) ≤ √γ * (1 - ϑ) := by rw [← hρu ξ]; exact hlt.le
        have := le_of_mul_le_mul_left h1 hsγ
        linarith
      have h2' : ϑ ^ 2 ≤ u ξ ^ 2 := by nlinarith
      have h4' : ϑ ^ 4 ≤ u ξ ^ 4 := by
        have := pow_le_pow_left₀ (by positivity) h2' 2
        calc ϑ ^ 4 = (ϑ ^ 2) ^ 2 := by ring
          _ ≤ (u ξ ^ 2) ^ 2 := this
          _ = u ξ ^ 4 := by ring
      have h5 : 1 ≤ u ξ ^ 4 / ϑ ^ 4 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith [sq_nonneg (u ξ)]
  have hA : ∫ ξ, aF ξ ^ 2 ∂μ ≤ (√γ * rthV ϑ N22 N24) ^ 2 := by
    calc ∫ ξ, aF ξ ^ 2 ∂μ ≤ ∫ ξ, γ * (u ξ ^ 2 + 4 * (u ξ ^ 4 / ϑ ^ 4)) ∂μ :=
          integral_mono iaF ((iu2.add ((iu4.div_const _).const_mul 4)).const_mul γ) haFpt
      _ = γ * ((∫ ξ, u ξ ^ 2 ∂μ) + 4 * ((∫ ξ, u ξ ^ 4 ∂μ) / ϑ ^ 4)) := by
          rw [integral_const_mul, integral_add iu2 ((iu4.div_const _).const_mul 4),
            integral_const_mul, integral_div]
      _ ≤ γ * (N22 ^ 2 + 4 * (N24 ^ 4 / ϑ ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ hγ.le
          have := div_le_div_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ ϑ ^ 4)
          linarith
      _ ≤ (√γ * rthV ϑ N22 N24) ^ 2 := by
          rw [mul_pow, hsγ2, rthV]
          refine mul_le_mul_of_nonneg_left ?_ hγ.le
          have e : (N22 + 2 * N24 ^ 2 / ϑ ^ 2) ^ 2 =
              N22 ^ 2 + 4 * (N24 ^ 4 / ϑ ^ 4) + 4 * N22 * (N24 ^ 2 / ϑ ^ 2) := by
            field_simp; ring
          rw [e]
          have : 0 ≤ 4 * N22 * (N24 ^ 2 / ϑ ^ 2) := by positivity
          linarith
  have hB : ∫ ξ, bF ξ ^ 2 ∂μ ≤ (√γ * √Vφ) ^ 2 := by
    have e : ∀ ξ, bF ξ ^ 2 = γ * (φ ξ - φb) ^ 2 := by
      intro ξ; simp only [hbF]; rw [mul_pow, hsγ2, sq_abs]
    simp_rw [e]
    rw [integral_const_mul, mul_pow, hsγ2, Real.sq_sqrt hVφ0]
    exact mul_le_mul_of_nonneg_left hVφ hγ.le
  have hrth0 : 0 ≤ rthV ϑ N22 N24 := by rw [rthV]; positivity
  have hmk := int_sq_add_le (μ := μ) maF mbF haFC hbFC (mul_nonneg hsγ.le hrth0)
    (mul_nonneg hsγ.le (Real.sqrt_nonneg _)) hA hB
  -- assemble
  have i1 : Integrable (fun ξ => (v₁ ξ - c₁) ^ 2) μ :=
    int_bddV ((hv1.sub_const _).pow_const 2) (C := (√H + |c₁|) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      refine sq_le_of_absV ?_
      have := abs_sub (v₁ ξ) c₁
      have := hC1 ξ
      linarith
  have i2 : Integrable (fun ξ => (v₂ ξ - c₂) ^ 2) μ :=
    int_bddV ((hv2.sub_const _).pow_const 2) (C := (√H + |c₂|) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      refine sq_le_of_absV ?_
      have := abs_sub (v₂ ξ) c₂
      have := hC2 ξ
      linarith
  have iab : Integrable (fun ξ => (aF ξ + bF ξ) ^ 2) μ :=
    int_bddV ((maF.add mbF).pow_const 2)
      (C := (√γ * (√H / √γ + 1 + 2) + √γ * (Real.pi + Real.pi)) ^ 2) fun ξ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        refine sq_le_of_absV ?_
        have := abs_add_le (aF ξ) (bF ξ)
        have := haFC ξ
        have := hbFC ξ
        linarith
  have hsum : ∫ ξ, (v₁ ξ - c₁) ^ 2 ∂μ + ∫ ξ, (v₂ ξ - c₂) ^ 2 ∂μ ≤
      ∫ ξ, (aF ξ + bF ξ) ^ 2 ∂μ := by
    rw [← integral_add i1 i2]
    exact integral_mono (i1.add i2) iab hpt
  have efin : (√γ * rthV ϑ N22 N24 + √γ * √Vφ) ^ 2 = γ * (rthV ϑ N22 N24 + √Vφ) ^ 2 := by
    rw [← mul_add, mul_pow, hsγ2]
  rw [efin] at hmk
  linarith

/-! ## Step 3: the mean displacement -/

/-- **Lemma V, Step 3**: `(E v₂ − σ_p)² ≤ γ·𝔡`, `σ_p = √(γ(1 − e_b))`. -/
theorem stepV_3 (μ : Measure Ξ) [IsProbabilityMeasure μ] {X : Ξ → ℝ} (hv1 : Measurable v₁)
    (hv2 : Measurable v₂) (hv20 : ∀ ξ, 0 ≤ v₂ ξ) {H : ℝ} (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H)
    {γ n eb sstar MP xi N22 : ℝ} (hγ : 0 < γ) (hn : 0 < n) (heb0 : 0 ≤ eb) (hs : 0 < sstar)
    (hV1 : eb ≤ 1 - sstar) (hMP : 0 ≤ MP) (hxi : 0 ≤ xi) (hN22 : 0 ≤ N22)
    (hXm : Measurable X) (hX0 : ∀ ξ, 0 ≤ X ξ) (hX2i : Integrable (fun ξ => X ξ ^ 2) μ)
    (hX2 : ∫ ξ, X ξ ^ 2 ∂μ ≤ (MP * γ / n) ^ 2)
    (hPl : ∫ ξ, (v₁ ξ - ∫ ζ, v₁ ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, X ξ ∂μ)
    (hPs : ∫ ξ, (v₂ ξ - ∫ ζ, v₂ ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, X ξ ∂μ)
    (hV2 : |∫ ξ, v₁ ξ ∂μ - √(γ * eb)| ≤ √(xi * γ / n))
    (h2 : ∫ ξ, uV γ v₁ v₂ ξ ^ 2 ∂μ ≤ N22 ^ 2)
    (hw : eDeltaV n sstar MP xi N22 / sstar < 1) :
    (∫ ξ, v₂ ξ ∂μ - √(γ * (1 - eb))) ^ 2 ≤ γ * dfrakV n sstar MP xi N22 := by
  have hsγ : 0 < √γ := Real.sqrt_pos.mpr hγ
  have hsγ2 : √γ ^ 2 = γ := Real.sq_sqrt hγ.le
  have hum := measurable_uV γ hv1 hv2
  set u := uV γ v₁ v₂ with hu
  have hρu : ∀ ξ, rhoV v₁ v₂ ξ = √γ * (1 + u ξ) := fun ξ => rhoV_eq hγ v₁ v₂ ξ
  have hCu : ∀ ξ, |u ξ| ≤ √H / √γ + 1 := fun ξ => uV_abs_le hγ hH ξ
  have hC1 : ∀ ξ, |v₁ ξ| ≤ √H := fun ξ => by
    apply Real.abs_le_sqrt
    nlinarith [hH ξ, sq_nonneg (v₂ ξ)]
  have hC2 : ∀ ξ, |v₂ ξ| ≤ √H := fun ξ => by
    apply Real.abs_le_sqrt
    nlinarith [hH ξ, sq_nonneg (v₁ ξ)]
  -- `E X ≤ M_P γ/n`
  have hXi : Integrable X μ := by
    refine ((integrable_const (1 : ℝ)).add hX2i).mono' hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ξ)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X ξ - 1)]
  have cX := wcs (P := μ) hXi (integrable_const (1 : ℝ)) hX2i (fun _ => zero_le_one)
    (fun ξ => sq_nonneg _) (fun ξ => le_of_eq (by ring))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at cX
  have hIX : ∫ ξ, X ξ ∂μ ≤ MP * γ / n := le_of_sqV (by positivity) (cX.trans hX2)
  -- the moments
  set m1 : ℝ := ∫ ξ, v₁ ξ ∂μ with hm1
  set m2 : ℝ := ∫ ξ, v₂ ξ ∂μ with hm2
  set V1 : ℝ := ∫ ξ, (v₁ ξ - m1) ^ 2 ∂μ with hV1d
  set V2 : ℝ := ∫ ξ, (v₂ ξ - m2) ^ 2 ∂μ with hV2d
  have hV10 : 0 ≤ V1 := integral_nonneg fun ξ => sq_nonneg _
  have hV20 : 0 ≤ V2 := integral_nonneg fun ξ => sq_nonneg _
  have hm20 : 0 ≤ m2 := integral_nonneg hv20
  have d1 := var_decompV (μ := μ) hv1 hC1 0
  have d2 := var_decompV (μ := μ) hv2 hC2 0
  simp only [sub_zero] at d1 d2
  rw [← hm1, ← hV1d] at d1
  rw [← hm2, ← hV2d] at d2
  have i1 : Integrable (fun ξ => v₁ ξ ^ 2) μ :=
    int_bddV (hv1.pow_const 2) (C := √H ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (hC1 ξ)
  have i2 : Integrable (fun ξ => v₂ ξ ^ 2) μ :=
    int_bddV (hv2.pow_const 2) (C := √H ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (hC2 ξ)
  have iu : Integrable u μ := int_bddV hum hCu
  have iu2 : Integrable (fun ξ => u ξ ^ 2) μ :=
    int_bddV (hum.pow_const 2) (C := (√H / √γ + 1) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact sq_le_of_absV (hCu ξ)
  set Iu : ℝ := ∫ ξ, u ξ ∂μ with hIu
  set Iu2 : ℝ := ∫ ξ, u ξ ^ 2 ∂μ with hIu2
  have hIu20 : 0 ≤ Iu2 := integral_nonneg fun ξ => sq_nonneg _
  have cu := wcs (P := μ) iu (integrable_const (1 : ℝ)) iu2 (fun _ => zero_le_one)
    (fun ξ => sq_nonneg _) (fun ξ => le_of_eq (by ring))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at cu
  have hIuabs := abs_le_of_sq_le_sq' (cu.trans h2) hN22
  -- `E ρ²` in two ways
  have eρ : ∫ ξ, v₁ ξ ^ 2 ∂μ + ∫ ξ, v₂ ξ ^ 2 ∂μ = γ * (1 + 2 * Iu + Iu2) := by
    rw [← integral_add i1 i2]
    have e : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 = γ * (1 + (2 * u ξ + u ξ ^ 2)) := by
      intro ξ
      rw [← rhoV_sq v₁ v₂ ξ, hρu ξ, mul_pow, hsγ2]
      ring
    simp_rw [e]
    have j : Integrable (fun ξ => 2 * u ξ + u ξ ^ 2) μ := (iu.const_mul 2).add iu2
    rw [integral_const_mul, integral_add (integrable_const 1) j,
      integral_add (iu.const_mul 2) iu2, integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  -- the first coordinate
  set a : ℝ := √(γ * eb) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = γ * eb := Real.sq_sqrt (by positivity)
  set s0 : ℝ := √(xi * γ / n) with hs0
  have hs00 : 0 ≤ s0 := Real.sqrt_nonneg _
  have hs02 : s0 ^ 2 = xi * γ / n := Real.sq_sqrt (by positivity)
  set q : ℝ := √((1 - sstar) * xi / n) with hq
  have h1s : 0 ≤ 1 - sstar := by linarith
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = (1 - sstar) * xi / n := Real.sq_sqrt (by positivity)
  have has : a * s0 ≤ γ * q := by
    refine le_of_sqV (by positivity) ?_
    rw [mul_pow, mul_pow, ha2, hs02, hq2]
    have h1 : γ * eb * (xi * γ / n) = γ ^ 2 * (eb * xi / n) := by ring
    have h2' : γ ^ 2 * ((1 - sstar) * xi / n) = γ ^ 2 * ((1 - sstar) * xi / n) := rfl
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hV1 hxi) hn.le
  set d₁ : ℝ := m1 - a with hd₁
  have hd := abs_le.mp hV2
  have hd1sq : d₁ ^ 2 ≤ s0 ^ 2 := sq_le_of_absV hV2
  have had1 : a * d₁ ≤ a * s0 := mul_le_mul_of_nonneg_left hd.2 ha0
  have had2 : -(a * s0) ≤ a * d₁ := by
    have := mul_le_mul_of_nonneg_left hd.1 ha0
    linarith
  have em1 : m1 ^ 2 = d₁ ^ 2 + 2 * (a * d₁) + γ * eb := by
    rw [hd₁, ← ha2]; ring
  -- `|m2² − σ_p²| ≤ γ e_Δ`
  set σp : ℝ := √(γ * (1 - eb)) with hσp
  have h1eb : 0 < 1 - eb := by linarith
  have hσp0 : 0 < σp := Real.sqrt_pos.mpr (by positivity)
  have hσp2 : σp ^ 2 = γ * (1 - eb) := Real.sq_sqrt (by positivity)
  have hkey : m2 ^ 2 - σp ^ 2 = γ * (2 * Iu + Iu2) - V1 - V2 - (d₁ ^ 2 + 2 * (a * d₁)) := by
    rw [hσp2]
    linarith
  have hdn : 0 ≤ d₁ ^ 2 := sq_nonneg _
  have hMPn : MP * γ / n = γ * (MP / n) := by ring
  have hxin : xi * γ / n = γ * (xi / n) := by ring
  have habs : |m2 ^ 2 - σp ^ 2| ≤ γ * eDeltaV n sstar MP xi N22 := by
    have eE : γ * eDeltaV n sstar MP xi N22 =
        γ * (2 * N22 + N22 ^ 2) + 2 * (γ * (MP / n)) + γ * (xi / n) + 2 * (γ * q) := by
      rw [eDeltaV, ← hq]; ring
    rw [eE, hkey, abs_le]
    have hIu2le : γ * Iu2 ≤ γ * N22 ^ 2 := mul_le_mul_of_nonneg_left h2 hγ.le
    have hIu2ge : 0 ≤ γ * Iu2 := mul_nonneg hγ.le hIu20
    have hIule : γ * Iu ≤ γ * N22 := mul_le_mul_of_nonneg_left hIuabs.2 hγ.le
    have hIuge : -(γ * N22) ≤ γ * Iu := by
      have := mul_le_mul_of_nonneg_left hIuabs.1 hγ.le
      linarith
    have hN : 0 ≤ γ * N22 ^ 2 := by positivity
    have hMq : 0 ≤ γ * (MP / n) := by positivity
    have hxq : 0 ≤ γ * (xi / n) := by positivity
    have hgq : 0 ≤ γ * q := by positivity
    have hV1le : V1 ≤ γ * (MP / n) := by rw [← hMPn]; exact hPl.trans hIX
    have hV2le : V2 ≤ γ * (MP / n) := by rw [← hMPn]; exact hPs.trans hIX
    have hd1le : d₁ ^ 2 ≤ γ * (xi / n) := by rw [← hxin, ← hs02]; exact hd1sq
    constructor <;> linarith
  -- the algebra
  have he0 : 0 ≤ eDeltaV n sstar MP xi N22 := by rw [eDeltaV]; positivity
  have hσge : γ * sstar ≤ σp ^ 2 := by
    rw [hσp2]; exact mul_le_mul_of_nonneg_left (by linarith) hγ.le
  exact mean_dispV hm20 hσp0 hγ hs hσge he0 hw habs

/-! ## Step 4: Lemma V -/

/-- **Lemma V (the coupling cost), abstract form.** With `v_p = (√(γ e_b), √(γ(1 − e_b)))`:
`E|v − v_p|² ≤ γ·[(√(κ_ϑ M_P/n) + 𝔯_ϑ)² + ξ_∥/n + 𝔡]`. -/
theorem lemmaV_abs (μ : Measure Ξ) [IsProbabilityMeasure μ] {X : Ξ → ℝ} (hv1 : Measurable v₁)
    (hv2 : Measurable v₂) (hv20 : ∀ ξ, 0 ≤ v₂ ξ) {H : ℝ} (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H)
    {γ ϑ n eb sstar MP xi N22 N24 : ℝ} (hγ : 0 < γ) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hn : 0 < n)
    (heb0 : 0 ≤ eb) (hs : 0 < sstar) (hV1 : eb ≤ 1 - sstar) (hMP : 0 ≤ MP) (hxi : 0 ≤ xi)
    (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24)
    (hXm : Measurable X) (hX0 : ∀ ξ, 0 ≤ X ξ) (hX2i : Integrable (fun ξ => X ξ ^ 2) μ)
    (hX2 : ∫ ξ, X ξ ^ 2 ∂μ ≤ (MP * γ / n) ^ 2)
    (hPl : ∫ ξ, (v₁ ξ - ∫ ζ, v₁ ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, X ξ ∂μ)
    (hPs : ∫ ξ, (v₂ ξ - ∫ ζ, v₂ ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, X ξ ∂μ)
    (hPφ : ∫ ξ, (phiV γ ϑ v₁ v₂ ξ - ∫ ζ, phiV γ ϑ v₁ v₂ ζ ∂μ) ^ 2 ∂μ ≤
      ∫ ξ, X ξ * ellSqV γ ϑ v₁ v₂ ξ ∂μ)
    (hV2 : |∫ ξ, v₁ ξ ∂μ - √(γ * eb)| ≤ √(xi * γ / n))
    (h2 : ∫ ξ, uV γ v₁ v₂ ξ ^ 2 ∂μ ≤ N22 ^ 2) (h4 : ∫ ξ, uV γ v₁ v₂ ξ ^ 4 ∂μ ≤ N24 ^ 4)
    (hw : eDeltaV n sstar MP xi N22 / sstar < 1) :
    ∫ ξ, ((v₁ ξ - √(γ * eb)) ^ 2 + (v₂ ξ - √(γ * (1 - eb))) ^ 2) ∂μ ≤
      γ * ((√(kappaV ϑ N24 * MP / n) + rthV ϑ N22 N24) ^ 2 + xi / n +
        dfrakV n sstar MP xi N22) := by
  have h1ϑ : 0 < 1 - ϑ := by linarith
  have hκ0 : 0 ≤ kappaV ϑ N24 * MP / n := by rw [kappaV]; positivity
  have s2a := stepV_2a μ hv1 hv2 hH hγ hϑ0 hϑ1 hn hMP hN24 hXm hX0 hX2i hX2 h4 hPφ
  have s2b := stepV_2b μ hv1 hv2 hv20 hH hγ hϑ0 hϑ1 hκ0 hN22 hN24 s2a h2 h4
  have s3 := stepV_3 μ hv1 hv2 hv20 hH hγ hn heb0 hs hV1 hMP hxi hN22 hXm hX0 hX2i hX2 hPl hPs
    hV2 h2 hw
  have hC1 : ∀ ξ, |v₁ ξ| ≤ √H := fun ξ => by
    apply Real.abs_le_sqrt
    nlinarith [hH ξ, sq_nonneg (v₂ ξ)]
  have hC2 : ∀ ξ, |v₂ ξ| ≤ √H := fun ξ => by
    apply Real.abs_le_sqrt
    nlinarith [hH ξ, sq_nonneg (v₁ ξ)]
  have d1 := var_decompV (μ := μ) hv1 hC1 (√(γ * eb))
  have d2 := var_decompV (μ := μ) hv2 hC2 (√(γ * (1 - eb)))
  have i1 : Integrable (fun ξ => (v₁ ξ - √(γ * eb)) ^ 2) μ :=
    int_bddV ((hv1.sub_const _).pow_const 2) (C := (√H + |√(γ * eb)|) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      refine sq_le_of_absV ?_
      have := abs_sub (v₁ ξ) (√(γ * eb))
      have := hC1 ξ
      linarith
  have i2 : Integrable (fun ξ => (v₂ ξ - √(γ * (1 - eb))) ^ 2) μ :=
    int_bddV ((hv2.sub_const _).pow_const 2) (C := (√H + |√(γ * (1 - eb))|) ^ 2) fun ξ => by
      rw [abs_of_nonneg (sq_nonneg _)]
      refine sq_le_of_absV ?_
      have := abs_sub (v₂ ξ) (√(γ * (1 - eb)))
      have := hC2 ξ
      linarith
  rw [integral_add i1 i2, d1, d2]
  have hd1 : (∫ ζ, v₁ ζ ∂μ - √(γ * eb)) ^ 2 ≤ γ * (xi / n) := by
    have := sq_le_of_absV hV2
    rw [Real.sq_sqrt (by positivity)] at this
    refine this.trans (le_of_eq ?_)
    ring
  have ecomm : (√(kappaV ϑ N24 * MP / n) + rthV ϑ N22 N24) ^ 2 =
      (rthV ϑ N22 N24 + √(kappaV ϑ N24 * MP / n)) ^ 2 := by ring
  rw [ecomm]
  linarith

/-- **Lemma V in the document's units** (`γ = 2/n`):
`n²·E|v − v_p|² ≤ 2[(√(κ_ϑ M_P) + √n·𝔯_ϑ)² + ξ_∥ + n·𝔡]` (the document:
`n𝔇_c/(1 + δ_c) ≤ n²·E|v − v_p|²`). -/
theorem lemmaV_abs_n (μ : Measure Ξ) [IsProbabilityMeasure μ] {X : Ξ → ℝ} (hv1 : Measurable v₁)
    (hv2 : Measurable v₂) (hv20 : ∀ ξ, 0 ≤ v₂ ξ) {H : ℝ} (hH : ∀ ξ, v₁ ξ ^ 2 + v₂ ξ ^ 2 ≤ H)
    {ϑ n eb sstar MP xi N22 N24 : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) (hn : 0 < n)
    (heb0 : 0 ≤ eb) (hs : 0 < sstar) (hV1 : eb ≤ 1 - sstar) (hMP : 0 ≤ MP) (hxi : 0 ≤ xi)
    (hN22 : 0 ≤ N22) (hN24 : 0 ≤ N24)
    (hXm : Measurable X) (hX0 : ∀ ξ, 0 ≤ X ξ) (hX2i : Integrable (fun ξ => X ξ ^ 2) μ)
    (hX2 : ∫ ξ, X ξ ^ 2 ∂μ ≤ (MP * (2 / n) / n) ^ 2)
    (hPl : ∫ ξ, (v₁ ξ - ∫ ζ, v₁ ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, X ξ ∂μ)
    (hPs : ∫ ξ, (v₂ ξ - ∫ ζ, v₂ ζ ∂μ) ^ 2 ∂μ ≤ ∫ ξ, X ξ ∂μ)
    (hPφ : ∫ ξ, (phiV (2 / n) ϑ v₁ v₂ ξ - ∫ ζ, phiV (2 / n) ϑ v₁ v₂ ζ ∂μ) ^ 2 ∂μ ≤
      ∫ ξ, X ξ * ellSqV (2 / n) ϑ v₁ v₂ ξ ∂μ)
    (hV2 : |∫ ξ, v₁ ξ ∂μ - √(2 / n * eb)| ≤ √(xi * (2 / n) / n))
    (h2 : ∫ ξ, uV (2 / n) v₁ v₂ ξ ^ 2 ∂μ ≤ N22 ^ 2)
    (h4 : ∫ ξ, uV (2 / n) v₁ v₂ ξ ^ 4 ∂μ ≤ N24 ^ 4)
    (hw : eDeltaV n sstar MP xi N22 / sstar < 1) :
    n ^ 2 * ∫ ξ, ((v₁ ξ - √(2 / n * eb)) ^ 2 + (v₂ ξ - √(2 / n * (1 - eb))) ^ 2) ∂μ ≤
      2 * ((√(kappaV ϑ N24 * MP) + √n * rthV ϑ N22 N24) ^ 2 + xi +
        n * dfrakV n sstar MP xi N22) := by
  have h := lemmaV_abs μ hv1 hv2 hv20 hH (γ := 2 / n) (by positivity) hϑ0 hϑ1 hn heb0 hs hV1
    hMP hxi hN22 hN24 hXm hX0 hX2i hX2 hPl hPs hPφ hV2 h2 h4 hw
  have hsn : 0 < √n := Real.sqrt_pos.mpr hn
  have hsn2 : √n ^ 2 = n := Real.sq_sqrt hn.le
  have e1 : √(kappaV ϑ N24 * MP / n) = √(kappaV ϑ N24 * MP) / √n := Real.sqrt_div' _ hn.le
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg n)
  refine h'.trans (le_of_eq ?_)
  rw [e1]
  have e2 : (√(kappaV ϑ N24 * MP) / √n + rthV ϑ N22 N24) ^ 2 =
      (√(kappaV ϑ N24 * MP) + √n * rthV ϑ N22 N24) ^ 2 / n := by
    have e3 : √(kappaV ϑ N24 * MP) / √n + rthV ϑ N22 N24 =
        (√(kappaV ϑ N24 * MP) + √n * rthV ϑ N22 N24) / √n := by field_simp
    rw [e3, div_pow, hsn2]
  rw [e2]
  field_simp

end V

end BstLean.Part151
