import BstLean.Part153Conc

/-!
# Part 153, item 2: Lemma EN (i), the energy event `E_e`

Paper source: `proofs/option-n/theorem5-06-centre.tex`, Lemma EN (i).

`Γ = GamS A₁ c τ = t·E_ξ|ReLU(A₁y)|²` (`t = 2/m`, `y = c + τξ`; Part153Op). `ρ² = |c|² + nτ²`.

* `integral_swap_of_nonneg`: Tonelli for a nonnegative real function, in the form used here.
* `sqrtGam_lip`: `A₁ ↦ √Γ` is Lipschitz for the Frobenius norm with constant `√(2/m)·ρ`
  (in the standardized matrix `Z₁ = A₁/√(2/n)` and with `m = n²` this is `2ρ/n^{3/2}`).
* `GamS_mean`: `E Γ = v·ρ²` for `A₁ ∼ gaussMat m n v` (`= γ_Aρ²` for `v = 2/n`).
* `sqrtGam_mean`: `vρ²(1 − 2/m) ≤ (E√Γ)² ≤ vρ²`.
* **`Ee_prob`**: `Pr(|√Γ − E√Γ| > √(2L_c v)·√(2/m)·ρ) ≤ 2·exp(−L_c)`.
* **`Ee_bounds`** (`m = n²`, `v = 2/n`): on `E_e`:
  `(√(1 − 2/n²) − 2√L_c/n)²·γ_Aρ² ≤ Γ ≤ (1 + 2√L_c/n)²·γ_Aρ²`.
* **`Ee_delta`**: on `E_e`, if `2√L_c/n ≤ 1/1000` and `n ≥ 100`: `|Γ − γ_Aρ²| ≤ (11/1000)·γ_Aρ²`
  (`δ_e = 0.011`); `Ee_delta_12`: the case `L_c = 12`, `n ≥ 8192`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152

/-- Tonelli's theorem for a nonnegative real function, with the inner means given. -/
theorem integral_swap_of_nonneg {Θ Ξ : Type*} [MeasurableSpace Θ] [MeasurableSpace Ξ]
    {ν : Measure Θ} [SFinite ν] {μ : Measure Ξ} [SFinite μ] {f : Θ → Ξ → ℝ}
    (hf : Measurable (Function.uncurry f)) (h0 : ∀ θ ξ, 0 ≤ f θ ξ)
    (h1 : ∀ θ, Integrable (f θ) μ) {b : Ξ → ℝ}
    (h2 : ∀ ξ, Integrable (fun θ => f θ ξ) ν ∧ ∫ θ, f θ ξ ∂ν = b ξ) (hb : Integrable b μ) :
    Integrable (fun θ => ∫ ξ, f θ ξ ∂μ) ν ∧ ∫ θ, ∫ ξ, f θ ξ ∂μ ∂ν = ∫ ξ, b ξ ∂μ := by
  have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => by
    rw [← (h2 ξ).2]; exact integral_nonneg fun θ => h0 θ ξ
  have hm : Measurable fun p : Θ × Ξ => ENNReal.ofReal (f p.1 p.2) := hf.ennreal_ofReal
  have hsm : StronglyMeasurable fun θ => ∫ ξ, f θ ξ ∂μ :=
    hf.stronglyMeasurable.integral_prod_right' (ν := μ)
  have hg0 : ∀ θ, 0 ≤ ∫ ξ, f θ ξ ∂μ := fun θ => integral_nonneg (h0 θ)
  have key : ∫⁻ θ, ENNReal.ofReal (∫ ξ, f θ ξ ∂μ) ∂ν = ENNReal.ofReal (∫ ξ, b ξ ∂μ) := by
    have e1 : ∀ θ, ENNReal.ofReal (∫ ξ, f θ ξ ∂μ) = ∫⁻ ξ, ENNReal.ofReal (f θ ξ) ∂μ := fun θ =>
      ofReal_integral_eq_lintegral_ofReal (h1 θ) (Filter.Eventually.of_forall (h0 θ))
    simp_rw [e1]
    rw [lintegral_lintegral_swap hm.aemeasurable]
    have e2 : ∀ ξ, ∫⁻ θ, ENNReal.ofReal (f θ ξ) ∂ν = ENNReal.ofReal (b ξ) := fun ξ => by
      rw [← ofReal_integral_eq_lintegral_ofReal (h2 ξ).1
        (Filter.Eventually.of_forall fun θ => h0 θ ξ), (h2 ξ).2]
    simp_rw [e2]
    exact (ofReal_integral_eq_lintegral_ofReal hb (Filter.Eventually.of_forall hb0)).symm
  have hint : Integrable (fun θ => ∫ ξ, f θ ξ ∂μ) ν := by
    refine ⟨hsm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0), key]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0)
    hsm.aestronglyMeasurable, key, ENNReal.toReal_ofReal (integral_nonneg hb0)]

section energy

variable {m n : ℕ}

/-- `|h₁(y)|` as a function of `ξ`. -/
noncomputable def h1n (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  nrm (reluV (A₁ *ᵥ (c + τ • ξ)))

lemma continuous_nrm {ι : Type*} [Fintype ι] : Continuous (nrm : (ι → ℝ) → ℝ) :=
  Real.continuous_sqrt.comp continuous_normSq

lemma continuous_h1n (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    Continuous (h1n A₁ c τ) := continuous_nrm.comp (continuous_h1 A₁ c τ)

lemma memLp_two_of_sq {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hi : Integrable (fun ξ => f ξ ^ 2) (stdGauss (Fin n))) : MemLp f 2 (stdGauss (Fin n)) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hi

lemma lpNorm_two_eq {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (_hf0 : ∀ ξ, 0 ≤ f ξ) :
    lpNorm f 2 (stdGauss (Fin n)) = √(∫ ξ, f ξ ^ 2 ∂stdGauss (Fin n)) := by
  have h := lpNorm_nat_pow (k := 2) (μ := stdGauss (Fin n)) (by norm_num) hf.aestronglyMeasurable
  rw [Nat.cast_ofNat] at h
  simp_rw [sq_abs] at h
  rw [← h, Real.sqrt_sq lpNorm_nonneg]

lemma memLp_h1n (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    MemLp (h1n A₁ c τ) 2 (stdGauss (Fin n)) := by
  refine memLp_two_of_sq (continuous_h1n A₁ c τ) ?_
  simp_rw [h1n, nrm_sq]
  exact integrable_h1_sq A₁ c τ

lemma memLp_nrm_shift (c : Fin n → ℝ) (τ : ℝ) :
    MemLp (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) 2 (stdGauss (Fin n)) := by
  refine memLp_two_of_sq (continuous_nrm.comp
    (continuous_const.add (continuous_const_smul τ))) ?_
  simp_rw [nrm_sq]
  exact (int_normSq_shift c τ).1

/-- `√Γ = √(2/m)·‖ |h₁(y)| ‖_{L²(ξ)}`. -/
lemma sqrtGam_eq (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    √(GamS A₁ c τ) = √(2 / (m : ℝ)) * lpNorm (h1n A₁ c τ) 2 (stdGauss (Fin n)) := by
  rw [lpNorm_two_eq (continuous_h1n A₁ c τ) (fun ξ => nrm_nonneg _)]
  unfold GamS
  rw [Real.sqrt_mul (by positivity)]
  simp_rw [h1n, nrm_sq]

/-- **Lemma EN (i), the Lipschitz constant**: `A₁ ↦ √Γ` is Lipschitz for the Frobenius norm
with constant `√(2/m)·ρ`, `ρ = √(|c|² + nτ²)`. -/
theorem sqrtGam_lip (c : Fin n → ℝ) (τ : ℝ) (A A' : Matrix (Fin m) (Fin n) ℝ) :
    |√(GamS A c τ) - √(GamS A' c τ)| ≤
      (√(2 / (m : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) * √(∑ i, ∑ j, (A i j - A' i j) ^ 2) := by
  set D := √(∑ i, ∑ j, (A i j - A' i j) ^ 2) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hpt : ∀ ξ : Fin n → ℝ, |(h1n A c τ - h1n A' c τ) ξ| ≤ D * nrm (c + τ • ξ) := by
    intro ξ
    have e : A *ᵥ (c + τ • ξ) - A' *ᵥ (c + τ • ξ) = (A - A') *ᵥ (c + τ • ξ) := by
      rw [Matrix.sub_mulVec]
    have hfro : opN (A - A') ≤ D := by
      have := opN_le_frob (A - A')
      simpa [hD, Matrix.sub_apply] using this
    calc |(h1n A c τ - h1n A' c τ) ξ|
        ≤ nrm (reluV (A *ᵥ (c + τ • ξ)) - reluV (A' *ᵥ (c + τ • ξ))) := abs_nrm_sub_le _ _
      _ ≤ nrm (A *ᵥ (c + τ • ξ) - A' *ᵥ (c + τ • ξ)) := nrm_reluV_sub_le _ _
      _ = nrm ((A - A') *ᵥ (c + τ • ξ)) := by rw [e]
      _ ≤ opN (A - A') * nrm (c + τ • ξ) := nrm_mulVec_le _ _
      _ ≤ D * nrm (c + τ • ξ) := mul_le_mul_of_nonneg_right hfro (nrm_nonneg _)
  have h1 := abs_lpNorm_sub_le (p := 2) (by norm_num) (memLp_h1n A c τ) (memLp_h1n A' c τ)
  have h2 := lpNorm_le_mul (memLp_nrm_shift c τ) hD0 hpt
  have h3 : lpNorm (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) 2 (stdGauss (Fin n)) =
      √(normSq c + (n : ℝ) * τ ^ 2) := by
    have hc : Continuous (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) :=
      continuous_nrm.comp (continuous_const.add (continuous_const_smul τ))
    rw [lpNorm_two_eq hc (fun ξ => nrm_nonneg _)]
    simp_rw [nrm_sq]
    rw [(int_normSq_shift c τ).2]
  rw [h3] at h2
  rw [sqrtGam_eq, sqrtGam_eq, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc √(2 / (m : ℝ)) * |lpNorm (h1n A c τ) 2 (stdGauss (Fin n)) -
        lpNorm (h1n A' c τ) 2 (stdGauss (Fin n))|
      ≤ √(2 / (m : ℝ)) * (D * √(normSq c + (n : ℝ) * τ ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.sqrt_nonneg _)
    _ = _ := by ring

lemma measurable_h1_joint (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (Function.uncurry fun (A : Matrix (Fin m) (Fin n) ℝ) (ξ : Fin n → ℝ) =>
      normSq (reluV (A *ᵥ (c + τ • ξ)))) := by
  have hc : Continuous (Function.uncurry fun (A : Matrix (Fin m) (Fin n) ℝ) (ξ : Fin n → ℝ) =>
      normSq (reluV (A *ᵥ (c + τ • ξ)))) :=
    continuous_normSq.comp (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst
      (continuous_const.add ((continuous_const_smul τ).comp continuous_snd))))
  exact hc.measurable

/-- **Lemma EN (i), the mean**: `E Γ = v·ρ²` for `A₁ ∼ gaussMat m n v` (`γ_Aρ²` for `v = 2/n`). -/
theorem GamS_mean (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => GamS A c τ) (gaussMat m n v) ∧
    ∫ A, GamS A c τ ∂gaussMat m n v = v * (normSq c + (n : ℝ) * τ ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hi, he⟩ := integral_swap_of_nonneg (ν := gaussMat m n v) (μ := stdGauss (Fin n))
    (measurable_h1_joint (m := m) c τ) (fun _ _ => normSq_nonneg _)
    (fun A => integrable_h1_sq A c τ)
    (b := fun ξ => (m : ℝ) / 2 * (v * normSq (c + τ • ξ)))
    (fun ξ => layer_relu_sq hv (c + τ • ξ))
    (((int_normSq_shift c τ).1.const_mul v).const_mul _)
  refine ⟨hi.const_mul _, ?_⟩
  unfold GamS
  rw [integral_const_mul, he, integral_const_mul, integral_const_mul, (int_normSq_shift c τ).2]
  field_simp

lemma measurable_GamS (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => GamS A c τ) := by
  unfold GamS
  exact ((measurable_h1_joint (m := m) c τ).stronglyMeasurable.integral_prod_right'
    (ν := stdGauss (Fin n))).measurable.const_mul _

/-- **Lemma EN (i), the mean of `√Γ`**: `√Γ` is integrable, `0 ≤ E√Γ`, and
`vρ²(1 − 2/m) ≤ (E√Γ)² ≤ vρ²`. -/
theorem sqrtGam_mean (hm : 1 ≤ m) (c : Fin n → ℝ) (τ : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => √(GamS A c τ)) (gaussMat m n v) ∧
    0 ≤ ∫ A, √(GamS A c τ) ∂gaussMat m n v ∧
    v * (normSq c + (n : ℝ) * τ ^ 2) * (1 - 2 / (m : ℝ)) ≤
      (∫ A, √(GamS A c τ) ∂gaussMat m n v) ^ 2 ∧
    (∫ A, √(GamS A c τ) ∂gaussMat m n v) ^ 2 ≤ v * (normSq c + (n : ℝ) * τ ^ 2) := by
  obtain ⟨hGi, hGe⟩ := GamS_mean (m := m) hm c τ hv
  set ρ2 := normSq c + (n : ℝ) * τ ^ 2 with hρ2
  have hρ0 : 0 ≤ ρ2 := add_nonneg (normSq_nonneg _) (by positivity)
  have hgm : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => √(GamS A c τ)) :=
    (measurable_GamS c τ).sqrt
  have hgi : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => √(GamS A c τ)) (gaussMat m n v) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hGi) hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun A => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h0 := GamS_nonneg A c τ
    have h1 : √(GamS A c τ) ^ 2 = GamS A c τ := Real.sq_sqrt h0
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (√(GamS A c τ) - 1), Real.sqrt_nonneg (GamS A c τ)]
  set e := ∫ A, √(GamS A c τ) ∂gaussMat m n v with he
  have hL0 : 0 ≤ √(2 / (m : ℝ)) * √ρ2 := by positivity
  obtain ⟨hvi, hvb⟩ := gaussVar_mat_le_sharp (g := fun A => √(GamS A c τ)) hL0
    (sqrtGam_lip (m := m) c τ) hv
  have hexp : ∫ A, (√(GamS A c τ) - e) ^ 2 ∂gaussMat m n v = v * ρ2 - e ^ 2 := by
    have e1 : ∀ A : Matrix (Fin m) (Fin n) ℝ, (√(GamS A c τ) - e) ^ 2 =
        GamS A c τ - 2 * e * √(GamS A c τ) + e ^ 2 := fun A => by
      rw [sub_sq, Real.sq_sqrt (GamS_nonneg A c τ)]; ring
    simp_rw [e1]
    have ea := integral_add (μ := gaussMat m n v)
      (f := fun A : Matrix (Fin m) (Fin n) ℝ => GamS A c τ - 2 * e * √(GamS A c τ))
      (g := fun _ => e ^ 2) (hGi.sub (hgi.const_mul _)) (integrable_const _)
    have eb := integral_sub (μ := gaussMat m n v)
      (f := fun A : Matrix (Fin m) (Fin n) ℝ => GamS A c τ)
      (g := fun A => 2 * e * √(GamS A c τ)) hGi (hgi.const_mul _)
    rw [ea, eb, integral_const_mul, hGe, ← he]
    simp
    ring
  rw [← he] at hvb
  rw [hexp] at hvb
  have hvar0 : 0 ≤ v * ρ2 - e ^ 2 := by
    rw [← hexp]; exact integral_nonneg fun A => sq_nonneg _
  refine ⟨hgi, integral_nonneg fun A => Real.sqrt_nonneg _, ?_, by linarith⟩
  have e2 : (√(2 / (m : ℝ)) * √ρ2) ^ 2 = 2 / (m : ℝ) * ρ2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hρ0]
  rw [e2] at hvb
  nlinarith [hvb]

/-- **Lemma EN (i), the event `E_e`**: `Pr(|√Γ − E√Γ| > √(2L_c v)·√(2/m)·ρ) ≤ 2·exp(−L_c)`.
For `v = 2/n`, `m = n²` the deviation is `√(2L_c)·2ρ/n^{3/2} = √(γ_Aρ²)·2√L_c/n`. -/
theorem Ee_prob (c : Fin n → ℝ) (τ : ℝ) {v : ℝ} (hv : 0 < v) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    (gaussMat m n v).real {A : Matrix (Fin m) (Fin n) ℝ |
      √(2 * Lc * v) * (√(2 / (m : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)) <
        |√(GamS A c τ) - ∫ A, √(GamS A c τ) ∂gaussMat m n v|} ≤ 2 * Real.exp (-Lc) :=
  conc_abs_strict (g := fun A => √(GamS A c τ)) (by positivity) (sqrtGam_lip (m := m) c τ) hv hLc

end energy

/-- The deviation of `E_e` for `v = 2/n`, `m = n²`: `√(γ_Aρ²)·2√L_c/n`. -/
lemma Ee_dev {n : ℕ} (hn : 1 ≤ n) (ρ2 : ℝ) (hρ : 0 ≤ ρ2) {Lc : ℝ} (hLc : 0 ≤ Lc) :
    √(2 * Lc * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √ρ2) =
      √(2 / (n : ℝ) * ρ2) * (2 * √Lc / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm]
  have h1 : 2 * √Lc / n = √(4 * Lc / (n : ℝ) ^ 2) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hn0.le, Real.sqrt_mul (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- **Lemma EN (i), the bounds on `E_e`** (`m = n²`, entry variance `2/n`): if
`|√Γ − E√Γ| ≤ √(2L_c·(2/n))·√(2/n²)·ρ` then
`Γ ≤ (1 + 2√L_c/n)²·γ_Aρ²`, and, if `2√L_c/n ≤ √(1 − 2/n²)`,
`(√(1 − 2/n²) − 2√L_c/n)²·γ_Aρ² ≤ Γ`. Here `γ_Aρ² = (2/n)·(|c|² + nτ²)`. -/
theorem Ee_bounds {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hA : |√(GamS A c τ) - ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ))| ≤
      √(2 * Lc * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2))) :
    GamS A c τ ≤ (1 + 2 * √Lc / n) ^ 2 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ∧
    (2 * √Lc / n ≤ √(1 - 2 / (n : ℝ) ^ 2) →
      (√(1 - 2 / (n : ℝ) ^ 2) - 2 * √Lc / n) ^ 2 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
        GamS A c τ) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  set ρ2 := normSq c + (n : ℝ) * τ ^ 2 with hρ2
  have hρ0 : 0 ≤ ρ2 := add_nonneg (normSq_nonneg _) (by positivity)
  obtain ⟨-, he0, hlo, hhi⟩ := sqrtGam_mean (m := mA n) hmA c τ (v := 2 / (n : ℝ)) (by positivity)
  rw [← hρ2] at hlo hhi
  rw [Ee_dev hn1 ρ2 hρ0 hLc] at hA
  set e := ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ)) with he
  set G0 := 2 / (n : ℝ) * ρ2 with hG0
  have hG00 : 0 ≤ G0 := by positivity
  set s := √G0 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = G0 := Real.sq_sqrt hG00
  set a := 2 * √Lc / n with ha
  have ha0 : 0 ≤ a := by positivity
  set g := √(GamS A c τ) with hg
  have hg0 : 0 ≤ g := Real.sqrt_nonneg _
  have hgg : g ^ 2 = GamS A c τ := Real.sq_sqrt (GamS_nonneg A c τ)
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hm] at hlo
  -- `e ≤ s` and `e ≥ s·√(1 − 2/n²)`
  have he1 : e ≤ s := by
    apply le_of_sq_le_sq _ hs0
    rw [hss]; exact hhi
  have hn2 : (0 : ℝ) ≤ 1 - 2 / (n : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  set r := √(1 - 2 / (n : ℝ) ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = 1 - 2 / (n : ℝ) ^ 2 := Real.sq_sqrt hn2
  have he2 : s * r ≤ e := by
    apply le_of_sq_le_sq _ he0
    rw [mul_pow, hss, hrr]; exact hlo
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  constructor
  · have h1 : g ≤ s * (1 + a) := by nlinarith
    calc GamS A c τ = g ^ 2 := hgg.symm
      _ ≤ (s * (1 + a)) ^ 2 := pow_le_pow_left₀ hg0 h1 2
      _ = (1 + a) ^ 2 * G0 := by rw [mul_pow, hss]; ring
  · intro hra
    have h1 : s * (r - a) ≤ g := by nlinarith
    have h2 : 0 ≤ s * (r - a) := mul_nonneg hs0 (by linarith)
    calc (r - a) ^ 2 * G0 = (s * (r - a)) ^ 2 := by rw [mul_pow, hss]; ring
      _ ≤ g ^ 2 := pow_le_pow_left₀ h2 h1 2
      _ = GamS A c τ := hgg

/-- **Lemma EN (i), the two-sided event with `δ_e = 0.011`**: on `E_e`, if `2√L_c/n ≤ 1/1000`
and `n ≥ 100`: `|Γ − γ_Aρ²| ≤ (11/1000)·γ_Aρ²`. -/
theorem Ee_delta {n : ℕ} (hn : 100 ≤ n) (c : Fin n → ℝ) (τ : ℝ) {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hsmall : 2 * √Lc / n ≤ 1 / 1000) {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hA : |√(GamS A c τ) - ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ))| ≤
      √(2 * Lc * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2))) :
    |GamS A c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      11 / 1000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hup, hlo⟩ := Ee_bounds (by omega) c τ hLc hA
  set G0 := 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) with hG0
  have hG00 : 0 ≤ G0 := by
    have : 0 ≤ normSq c + (n : ℝ) * τ ^ 2 := add_nonneg (normSq_nonneg _) (by positivity)
    positivity
  set a := 2 * √Lc / n with ha
  have ha0 : 0 ≤ a := by positivity
  have hn100 : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 2 / (n : ℝ) ^ 2 ≤ 1 / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hr : (999 : ℝ) / 1000 ≤ √(1 - 2 / (n : ℝ) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hlo' := hlo (by linarith)
  set r := √(1 - 2 / (n : ℝ) ^ 2) with hr'
  have h1 : (1 + a) ^ 2 ≤ 1 + 11 / 1000 := by nlinarith
  have h2 : 1 - 11 / 1000 ≤ (r - a) ^ 2 := by
    have : (998 : ℝ) / 1000 ≤ r - a := by linarith
    nlinarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h2 hG00]
  · nlinarith [mul_le_mul_of_nonneg_right h1 hG00]

/-- `Ee_delta` at the level `L_c = 12` of the paper, for `n ≥ 8192`. -/
theorem Ee_delta_12 {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) (τ : ℝ)
    {A : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hA : |√(GamS A c τ) - ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ))| ≤
      √(2 * 12 * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2))) :
    |GamS A c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      11 / 1000 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) := by
  refine Ee_delta (by omega) c τ (by norm_num) ?_ hA
  have hn0 : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have h12 : √(12 : ℝ) ≤ 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

end BstLean.Part153
