import BstLean.Part153Op

/-!
# Part 153: tools for `L^p` norms over the stand-in input

Role: `delegations/statements/p153-spec.md`, items 1 and 2. `lpNorm f p μ` is the Mathlib
`L^p(μ)` norm of `f` as a real number.

* `abs_lpNorm_sub_le`: `|‖f‖_p − ‖g‖_p| ≤ ‖f − g‖_p`.
* `lpNorm_le_mul`: `‖f‖_p ≤ D·‖ℓ‖_p` if `|f| ≤ D·ℓ` pointwise.
* `lpNorm_nat_pow`: `‖f‖_k^k = ∫|f|^k` for a natural number `k ≥ 1`; `eLpNorm_nat_pow`.
* **`mean_lpNorm_le`**: for a family `G θ` of functions of `ξ`, `θ` random:
  `E_θ ‖G θ‖_{L^k(ξ)} ≤ (E_ξ E_θ |G θ ξ|^k)^{1/k}`, in the form used below.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

section lp

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma abs_lpNorm_sub_le {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : Ω → ℝ} (hf : MemLp f p μ)
    (hg : MemLp g p μ) : |lpNorm f p μ - lpNorm g p μ| ≤ lpNorm (f - g) p μ := by
  have h1 := lpNorm_le_lpNorm_add_lpNorm_sub' (f := f) hg hp
  have h2 := lpNorm_le_lpNorm_add_lpNorm_sub' (f := g) hf hp
  rw [lpNorm_sub_comm] at h2
  rw [abs_le]
  constructor <;> linarith

lemma lpNorm_le_mul {p : ℝ≥0∞} {f ℓ : Ω → ℝ} (hℓ : MemLp ℓ p μ) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ x, |f x| ≤ D * ℓ x) : lpNorm f p μ ≤ D * lpNorm ℓ p μ := by
  have h1 : lpNorm f p μ ≤ lpNorm (D • ℓ) p μ :=
    lpNorm_mono_real (hℓ.const_smul D) (fun x => by simpa using h x)
  rw [lpNorm_const_smul] at h1
  simpa [abs_of_nonneg hD] using h1

lemma lpNorm_nat_pow {k : ℕ} (hk : k ≠ 0) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    lpNorm f (k : ℝ≥0∞) μ ^ k = ∫ x, |f x| ^ k ∂μ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hk) (ENNReal.natCast_ne_top k) hf]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun x => by positivity),
    inv_mul_cancel₀ hk', Real.rpow_one]

lemma eLpNorm_nat_pow {k : ℕ} (hk : k ≠ 0) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (k : ℝ≥0∞) μ ^ k = ∫⁻ x, ENNReal.ofReal (|f x| ^ k) ∂μ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hk) (ENNReal.natCast_ne_top k) hf]
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hk', ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_pow (abs_nonneg _)]

end lp

/-- **The mean of an `L^k` norm.** `θ ∼ ν` (a probability measure), `ξ ∼ μ`; `G θ ξ` jointly
measurable, `G θ ∈ L^k(μ)` for each `θ`. If `E_θ |G θ ξ|^k ≤ b ξ` for each `ξ` and
`E_ξ b ≤ C^k`, then `θ ↦ ‖G θ‖_{L^k(μ)}` is integrable and its mean is at most `C`. -/
theorem mean_lpNorm_le {Θ Ξ : Type*} [MeasurableSpace Θ] [MeasurableSpace Ξ] {ν : Measure Θ}
    [IsProbabilityMeasure ν] {μ : Measure Ξ} [SFinite μ] {k : ℕ} (hk : k ≠ 0)
    {G : Θ → Ξ → ℝ} (hG : Measurable (Function.uncurry G))
    (hmem : ∀ θ, MemLp (G θ) (k : ℝ≥0∞) μ)
    {b : Ξ → ℝ} (hb : ∀ ξ, ∫⁻ θ, ENNReal.ofReal (|G θ ξ| ^ k) ∂ν ≤ ENNReal.ofReal (b ξ))
    {C : ℝ} (hC : 0 ≤ C) (hbC : ∫⁻ ξ, ENNReal.ofReal (b ξ) ∂μ ≤ ENNReal.ofReal (C ^ k)) :
    Measurable (fun θ => lpNorm (G θ) (k : ℝ≥0∞) μ) ∧
    Integrable (fun θ => lpNorm (G θ) (k : ℝ≥0∞) μ) ν ∧
      ∫ θ, lpNorm (G θ) (k : ℝ≥0∞) μ ∂ν ≤ C := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  set N : Θ → ℝ := fun θ => lpNorm (G θ) (k : ℝ≥0∞) μ with hN
  have hGm : Measurable fun p : Θ × Ξ => ENNReal.ofReal (|G p.1 p.2| ^ k) :=
    ((continuous_abs.measurable.comp hG).pow_const k).ennreal_ofReal
  have hpow : ∀ θ, ENNReal.ofReal (N θ) ^ k = ∫⁻ ξ, ENNReal.ofReal (|G θ ξ| ^ k) ∂μ := fun θ => by
    simp only [hN]
    rw [ofReal_lpNorm (hmem θ), eLpNorm_nat_pow hk (hmem θ).aestronglyMeasurable]
  have hNm : Measurable N := by
    have e : N = fun θ => ((∫⁻ ξ, ENNReal.ofReal (|G θ ξ| ^ k) ∂μ) ^ (1 / (k : ℝ))).toReal := by
      funext θ
      rw [← hpow θ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hk',
        ENNReal.rpow_one, ENNReal.toReal_ofReal lpNorm_nonneg]
    rw [e]
    exact ((hGm.lintegral_prod_right').pow_const _).ennreal_toReal
  have h1 : ∫⁻ θ, ENNReal.ofReal (N θ) ^ k ∂ν ≤ ENNReal.ofReal (C ^ k) := by
    simp_rw [hpow]
    rw [lintegral_lintegral_swap hGm.aemeasurable]
    exact (lintegral_mono hb).trans hbC
  have h2 : eLpNorm N (k : ℝ≥0∞) ν ≤ ENNReal.ofReal C := by
    have e := eLpNorm_nat_pow (μ := ν) hk hNm.aestronglyMeasurable
    have h3 : eLpNorm N (k : ℝ≥0∞) ν ^ k ≤ ENNReal.ofReal C ^ k := by
      rw [e, ← ENNReal.ofReal_pow hC]
      refine le_trans (le_of_eq (lintegral_congr fun θ => ?_)) h1
      rw [abs_of_nonneg lpNorm_nonneg, ENNReal.ofReal_pow lpNorm_nonneg]
    exact (ENNReal.pow_le_pow_left_iff hk).mp h3
  have h4 : eLpNorm N 1 ν ≤ ENNReal.ofReal C :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)).trans h2
  have hint : Integrable N ν :=
    memLp_one_iff_integrable.mp (h4.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hNm, hint, ?_⟩
  have e : ∫ θ, N θ ∂ν = lpNorm N 1 ν := by
    rw [lpNorm_one_eq_integral_norm hNm.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    exact (Real.norm_of_nonneg lpNorm_nonneg).symm
  rw [e, ← toReal_eLpNorm]
  exact ENNReal.toReal_le_of_le_ofReal hC h4

end BstLean.Part153
