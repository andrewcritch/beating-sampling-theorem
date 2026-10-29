import BstLean.Part132Persp

/-!
# Part 132, item 2: the one-layer step

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §2, §3;
`onW4-opus-prover.md` T3, 2.1 to 2.3.

* `sqrt_mul_sqrt_ge`: `√x·√y ≥ −2 + (5/2)(x + y) − x² − y²` for `x, y ≥ 0`.
* `norm_pair`: for two nonnegative variables `X, Y` with `E X = α²`, `E Y = β²`,
  `E X² ≤ (1 + ε)α⁴`, `E Y² ≤ (1 + ε)β⁴` (no independence): `αβ(1 − 2ε) ≤ E √X√Y ≤ αβ` and
  `E(√X√Y − αβ)² ≤ 5ε·α²β²`. (Paper T3(3), (4) with other constants: `1 − 10/m` in the place of
  `1 − 17/m`, `25/m` in the place of `39/m`; the proof here uses second moments of `X, Y` only.)
* `relu_layer_pair`, `lin_layer_pair`: the same for the norms of the outputs of one Gaussian
  matrix, with ReLU (`ε = 5/m`) and without (`ε = 2/m`).
* `relu_layer_lower`: `E Ψ_G(ReLU(Mh), ReLU(Mh′)) ≥ (m/2)v·[Ψ_{G∘κ}(h, h′) − (10/m)G(0)|h||h′|]`.
* `lin_layer_lower`: `E Ψ_G(Mh, Mh′) ≥ m·v·[Ψ_G(h, h′) − (4/m)G(0)|h||h′|]`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130

/-! ## Two norms with known second moments -/

lemma sqrt_mul_sqrt_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    -2 + 5 / 2 * (x + y) - x ^ 2 - y ^ 2 ≤ √x * √y := by
  obtain ⟨u, hu, rfl⟩ : ∃ u : ℝ, 0 ≤ u ∧ x = u ^ 2 :=
    ⟨√x, Real.sqrt_nonneg _, (Real.sq_sqrt hx).symm⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w : ℝ, 0 ≤ w ∧ y = w ^ 2 :=
    ⟨√y, Real.sqrt_nonneg _, (Real.sq_sqrt hy).symm⟩
  rw [Real.sqrt_sq hu, Real.sqrt_sq hw]
  have h1 : 0 ≤ u * (u - 1) ^ 2 * (u + 2) :=
    mul_nonneg (mul_nonneg hu (sq_nonneg _)) (by linarith)
  have h2 : 0 ≤ w * (w - 1) ^ 2 * (w + 2) :=
    mul_nonneg (mul_nonneg hw (sq_nonneg _)) (by linarith)
  have h3 : 0 ≤ (u - 1) ^ 2 * (u ^ 2 + 2 * u) := mul_nonneg (sq_nonneg _) (by positivity)
  have h4 : 0 ≤ (w - 1) ^ 2 * (w ^ 2 + 2 * w) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith [sq_nonneg (u - 1 + (w - 1))]

lemma sqrt_mul_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √x * √y ≤ (x + y) / 2 := by
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  nlinarith [sq_nonneg (√x - √y)]

section pair

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_of_sq {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ) : Integrable X μ := by
  refine Integrable.mono' (((integrable_const (1 : ℝ)).add hX2).div_const 2)
    hX.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (X ω - 1)]

/-- The normalized form of `norm_pair`. -/
theorem norm_pair_unit {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) {ε : ℝ} (hEX : ∫ ω, X ω ∂μ = 1)
    (hEY : ∫ ω, Y ω ∂μ = 1) (hEX2 : ∫ ω, X ω ^ 2 ∂μ ≤ 1 + ε) (hEY2 : ∫ ω, Y ω ^ 2 ∂μ ≤ 1 + ε) :
    Integrable (fun ω => √(X ω) * √(Y ω)) μ ∧ ∫ ω, √(X ω) * √(Y ω) ∂μ ≤ 1 ∧
    1 - 2 * ε ≤ ∫ ω, √(X ω) * √(Y ω) ∂μ ∧
    Integrable (fun ω => (√(X ω) * √(Y ω) - 1) ^ 2) μ ∧
    ∫ ω, (√(X ω) * √(Y ω) - 1) ^ 2 ∂μ ≤ 5 * ε := by
  have hXi := integrable_of_sq hX hX0 hX2
  have hYi := integrable_of_sq hY hY0 hY2
  have hPm : Measurable (fun ω => √(X ω) * √(Y ω)) := hX.sqrt.mul hY.sqrt
  have hP0 : ∀ ω, 0 ≤ √(X ω) * √(Y ω) := fun ω =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hPi : Integrable (fun ω => √(X ω) * √(Y ω)) μ := by
    refine Integrable.mono' ((hXi.add hYi).div_const 2) hPm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 ω)]
    exact sqrt_mul_sqrt_le (hX0 ω) (hY0 ω)
  have hup : ∫ ω, √(X ω) * √(Y ω) ∂μ ≤ 1 := by
    have h := integral_mono hPi ((hXi.add hYi).div_const 2)
      (fun ω => sqrt_mul_sqrt_le (hX0 ω) (hY0 ω))
    have e : ∫ ω, (X + Y) ω / 2 ∂μ = 1 := by
      simp only [Pi.add_apply]
      rw [integral_div, integral_add hXi hYi, hEX, hEY]; norm_num
    linarith
  have hgi : Integrable (fun ω => -2 + 5 / 2 * (X ω + Y ω) - X ω ^ 2 - Y ω ^ 2) μ :=
    ((((integrable_const (-2 : ℝ)).add ((hXi.add hYi).const_mul (5 / 2))).sub hX2).sub hY2)
  have hlow : 1 - 2 * ε ≤ ∫ ω, √(X ω) * √(Y ω) ∂μ := by
    have h := integral_mono hgi hPi (fun ω => sqrt_mul_sqrt_ge (hX0 ω) (hY0 ω))
    have hg1 : Integrable (fun ω => 5 / 2 * (X ω + Y ω)) μ := (hXi.add hYi).const_mul (5 / 2)
    have hg2 : Integrable (fun ω => -2 + 5 / 2 * (X ω + Y ω)) μ := (integrable_const (-2 : ℝ)).add hg1
    have hg3 : Integrable (fun ω => -2 + 5 / 2 * (X ω + Y ω) - X ω ^ 2) μ := hg2.sub hX2
    have a1 := integral_sub hg3 hY2
    have a2 := integral_sub hg2 hX2
    have a3 := integral_add (integrable_const (-2 : ℝ)) hg1
    have a4 : ∫ ω, 5 / 2 * (X ω + Y ω) ∂μ = 5 / 2 * ∫ ω, (X ω + Y ω) ∂μ := integral_const_mul _ _
    have a5 := integral_add hXi hYi
    beta_reduce at a1 a2 a3
    have a6 : ∫ _ω : Ω, (-2 : ℝ) ∂μ = -2 := by simp
    rw [a1, a2, a3, a4, a5, a6, hEX, hEY] at h
    linarith
  have hXYi : Integrable (fun ω => X ω * Y ω) μ := by
    refine Integrable.mono' ((hX2.add hY2).div_const 2) (hX.mul hY).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hX0 ω) (hY0 ω))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X ω - Y ω)]
  have hXY : ∫ ω, X ω * Y ω ∂μ ≤ 1 + ε := by
    have h := integral_mono hXYi ((hX2.add hY2).div_const 2) (fun ω => by
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (X ω - Y ω)])
    have e : ∫ ω, ((fun ω => X ω ^ 2) + fun ω => Y ω ^ 2) ω / 2 ∂μ =
        (∫ ω, X ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 ∂μ) / 2 := by
      simp only [Pi.add_apply]
      rw [integral_div, integral_add hX2 hY2]
    linarith
  have esq : (fun ω => (√(X ω) * √(Y ω) - 1) ^ 2) =
      fun ω => X ω * Y ω - 2 * (√(X ω) * √(Y ω)) + 1 := by
    funext ω
    have h1 := Real.sq_sqrt (hX0 ω)
    have h2 := Real.sq_sqrt (hY0 ω)
    have : (√(X ω) * √(Y ω)) ^ 2 = X ω * Y ω := by rw [mul_pow, h1, h2]
    nlinarith
  have hsi : Integrable (fun ω => X ω * Y ω - 2 * (√(X ω) * √(Y ω)) + 1) μ :=
    (hXYi.sub (hPi.const_mul 2)).add (integrable_const 1)
  refine ⟨hPi, hup, hlow, by rw [esq]; exact hsi, ?_⟩
  have hd : Integrable (fun ω => X ω * Y ω - 2 * (√(X ω) * √(Y ω))) μ := hXYi.sub (hPi.const_mul 2)
  have a1 := integral_add hd (integrable_const (1 : ℝ))
  have a2 := integral_sub hXYi (hPi.const_mul 2)
  have a3 : ∫ ω, 2 * (√(X ω) * √(Y ω)) ∂μ = 2 * ∫ ω, √(X ω) * √(Y ω) ∂μ := integral_const_mul _ _
  have a6 : ∫ _ω : Ω, (1 : ℝ) ∂μ = 1 := by simp
  beta_reduce at a1 a2
  rw [esq, a1, a2, a3, a6]
  linarith

/-- **Two norms with known second moments** (no independence): `X, Y ≥ 0`, `E X = α²`,
`E Y = β²`, `E X² ≤ (1 + ε)α⁴`, `E Y² ≤ (1 + ε)β⁴`. Then `αβ(1 − 2ε) ≤ E √X√Y ≤ αβ` and
`E(√X√Y − αβ)² ≤ 5ε·α²β²`. -/
theorem norm_pair {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ) {α β ε : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hEX : ∫ ω, X ω ∂μ = α ^ 2) (hEY : ∫ ω, Y ω ∂μ = β ^ 2)
    (hEX2 : ∫ ω, X ω ^ 2 ∂μ ≤ (1 + ε) * α ^ 4) (hEY2 : ∫ ω, Y ω ^ 2 ∂μ ≤ (1 + ε) * β ^ 4) :
    Integrable (fun ω => √(X ω) * √(Y ω)) μ ∧ ∫ ω, √(X ω) * √(Y ω) ∂μ ≤ α * β ∧
    α * β * (1 - 2 * ε) ≤ ∫ ω, √(X ω) * √(Y ω) ∂μ ∧
    Integrable (fun ω => (√(X ω) * √(Y ω) - α * β) ^ 2) μ ∧
    ∫ ω, (√(X ω) * √(Y ω) - α * β) ^ 2 ∂μ ≤ 5 * ε * (α * β) ^ 2 := by
  have hXi := integrable_of_sq hX hX0 hX2
  have hYi := integrable_of_sq hY hY0 hY2
  by_cases hdeg : α = 0 ∨ β = 0
  · -- one of the two variables is `0` almost surely
    have hP : (fun ω => √(X ω) * √(Y ω)) =ᵐ[μ] fun _ => (0 : ℝ) := by
      rcases hdeg with h | h
      · have h0 : ∫ ω, X ω ∂μ = 0 := by rw [hEX, h]; simp
        have := (integral_eq_zero_iff_of_nonneg hX0 hXi).mp h0
        filter_upwards [this] with ω hω
        have : X ω = 0 := hω
        simp [this]
      · have h0 : ∫ ω, Y ω ∂μ = 0 := by rw [hEY, h]; simp
        have := (integral_eq_zero_iff_of_nonneg hY0 hYi).mp h0
        filter_upwards [this] with ω hω
        have : Y ω = 0 := hω
        simp [this]
    have hab : α * β = 0 := by rcases hdeg with h | h <;> simp [h]
    have hP2 : (fun ω => (√(X ω) * √(Y ω) - α * β) ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) := by
      filter_upwards [hP] with ω hω
      rw [hω, hab]; simp
    refine ⟨(integrable_congr hP).mpr (integrable_const 0), ?_, ?_,
      (integrable_congr hP2).mpr (integrable_const 0), ?_⟩
    · rw [integral_congr_ae hP, hab]; simp
    · rw [integral_congr_ae hP, hab]; simp
    · rw [integral_congr_ae hP2, hab]; simp
  · rw [not_or] at hdeg
    have hα' : 0 < α := lt_of_le_of_ne hα (Ne.symm hdeg.1)
    have hβ' : 0 < β := lt_of_le_of_ne hβ (Ne.symm hdeg.2)
    have hu := norm_pair_unit (μ := μ) (X := fun ω => X ω / α ^ 2) (Y := fun ω => Y ω / β ^ 2)
      (ε := ε) (hX.div_const _) (hY.div_const _) (fun ω => div_nonneg (hX0 ω) (by positivity))
      (fun ω => div_nonneg (hY0 ω) (by positivity))
      (by simp_rw [div_pow]; exact hX2.div_const _) (by simp_rw [div_pow]; exact hY2.div_const _)
      (by rw [integral_div, hEX]; field_simp) (by rw [integral_div, hEY]; field_simp)
      (by
        simp_rw [div_pow]
        rw [integral_div, div_le_iff₀ (by positivity)]
        calc ∫ ω, X ω ^ 2 ∂μ ≤ (1 + ε) * α ^ 4 := hEX2
          _ = (1 + ε) * (α ^ 2) ^ 2 := by ring)
      (by
        simp_rw [div_pow]
        rw [integral_div, div_le_iff₀ (by positivity)]
        calc ∫ ω, Y ω ^ 2 ∂μ ≤ (1 + ε) * β ^ 4 := hEY2
          _ = (1 + ε) * (β ^ 2) ^ 2 := by ring)
    obtain ⟨u1, u2, u3, u4, u5⟩ := hu
    have e : ∀ ω, √(X ω / α ^ 2) * √(Y ω / β ^ 2) = √(X ω) * √(Y ω) / (α * β) := by
      intro ω
      rw [Real.sqrt_div (hX0 ω), Real.sqrt_div (hY0 ω), Real.sqrt_sq hα, Real.sqrt_sq hβ]
      field_simp
    simp_rw [e] at u1 u2 u3 u4 u5
    have hab : 0 < α * β := mul_pos hα' hβ'
    have e1 : (fun ω => √(X ω) * √(Y ω)) = fun ω => (α * β) * (√(X ω) * √(Y ω) / (α * β)) := by
      funext ω; field_simp
    have e2 : (fun ω => (√(X ω) * √(Y ω) - α * β) ^ 2) =
        fun ω => (α * β) ^ 2 * (√(X ω) * √(Y ω) / (α * β) - 1) ^ 2 := by
      funext ω; field_simp
    refine ⟨by rw [e1]; exact u1.const_mul _, ?_, ?_, by rw [e2]; exact u4.const_mul _, ?_⟩
    · rw [e1, integral_const_mul]
      calc α * β * _ ≤ α * β * 1 := mul_le_mul_of_nonneg_left u2 hab.le
        _ = α * β := mul_one _
    · rw [e1, integral_const_mul]
      exact mul_le_mul_of_nonneg_left u3 hab.le
    · rw [e2, integral_const_mul]
      calc (α * β) ^ 2 * _ ≤ (α * β) ^ 2 * (5 * ε) := mul_le_mul_of_nonneg_left u5 (by positivity)
        _ = 5 * ε * (α * β) ^ 2 := by ring

end pair

/-! ## The norms of the outputs of one layer -/

variable {m k : ℕ}

/-- **The product of the two output norms of a ReLU layer**: with `p̄ = (m/2)·v·|h||h′|`,
`p̄(1 − 10/m) ≤ E |g||g′| ≤ p̄` and `E(|g||g′| − p̄)² ≤ (25/m)·p̄²`, `g = ReLU(M h)`,
`g′ = ReLU(M h′)`. -/
theorem relu_layer_pair {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h'))) (gaussMat m k v) ∧
    ∫ M, nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) ∂gaussMat m k v ≤
      (m : ℝ) / 2 * v * (nrm h * nrm h') ∧
    (m : ℝ) / 2 * v * (nrm h * nrm h') * (1 - 10 / (m : ℝ)) ≤
      ∫ M, nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) ∂gaussMat m k v ∧
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) -
        (m : ℝ) / 2 * v * (nrm h * nrm h')) ^ 2) (gaussMat m k v) ∧
    ∫ M, (nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) -
        (m : ℝ) / 2 * v * (nrm h * nrm h')) ^ 2 ∂gaussMat m k v ≤
      25 / (m : ℝ) * ((m : ℝ) / 2 * v * (nrm h * nrm h')) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 ≤ (m : ℝ) / 2 * v := by positivity
  have hmeas : ∀ h : Fin k → ℝ, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (reluV (M.mulVec h))) := fun h =>
    measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right h))
  have hsq : ∀ h : Fin k → ℝ, (√((m : ℝ) / 2 * v) * nrm h) ^ 2 = (m : ℝ) / 2 * (v * normSq h) := by
    intro h; rw [mul_pow, Real.sq_sqrt hs, nrm_sq]; ring
  have h4 : ∀ h : Fin k → ℝ, ∫ M, normSq (reluV (M.mulVec h)) ^ 2 ∂gaussMat m k v ≤
      (1 + 5 / (m : ℝ)) * (√((m : ℝ) / 2 * v) * nrm h) ^ 4 := by
    intro h
    rw [(layer_relu_four hv h).2, show (√((m : ℝ) / 2 * v) * nrm h) ^ 4 =
      ((√((m : ℝ) / 2 * v) * nrm h) ^ 2) ^ 2 by ring, hsq]
    apply le_of_eq
    field_simp
    ring
  have key := norm_pair (μ := gaussMat m k v) (hmeas h) (hmeas h')
    (fun M => normSq_nonneg _) (fun M => normSq_nonneg _) (layer_relu_four hv h).1
    (layer_relu_four hv h').1 (ε := 5 / (m : ℝ))
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg h))
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg h'))
    (by rw [(layer_relu_sq hv h).2, hsq]) (by rw [(layer_relu_sq hv h').2, hsq]) (h4 h) (h4 h')
  have e : √((m : ℝ) / 2 * v) * nrm h * (√((m : ℝ) / 2 * v) * nrm h') =
      (m : ℝ) / 2 * v * (nrm h * nrm h') := by
    have := Real.mul_self_sqrt hs
    calc _ = (√((m : ℝ) / 2 * v) * √((m : ℝ) / 2 * v)) * (nrm h * nrm h') := by ring
      _ = _ := by rw [this]
  rw [e] at key
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  refine ⟨k1, k2, ?_, k4, ?_⟩
  · calc _ = (m : ℝ) / 2 * v * (nrm h * nrm h') * (1 - 2 * (5 / (m : ℝ))) := by ring
      _ ≤ _ := k3
  · calc _ ≤ 5 * (5 / (m : ℝ)) * ((m : ℝ) / 2 * v * (nrm h * nrm h')) ^ 2 := k5
      _ = _ := by ring

/-- **The product of the two output norms of a linear layer**: with `p̄ = m·v·|h||h′|`,
`p̄(1 − 4/m) ≤ E |Mh||Mh′| ≤ p̄` and `E(|Mh||Mh′| − p̄)² ≤ (10/m)·p̄²`. -/
theorem lin_layer_pair {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      nrm (M.mulVec h) * nrm (M.mulVec h')) (gaussMat m k v) ∧
    ∫ M, nrm (M.mulVec h) * nrm (M.mulVec h') ∂gaussMat m k v ≤
      (m : ℝ) * v * (nrm h * nrm h') ∧
    (m : ℝ) * v * (nrm h * nrm h') * (1 - 4 / (m : ℝ)) ≤
      ∫ M, nrm (M.mulVec h) * nrm (M.mulVec h') ∂gaussMat m k v ∧
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (nrm (M.mulVec h) * nrm (M.mulVec h') - (m : ℝ) * v * (nrm h * nrm h')) ^ 2)
      (gaussMat m k v) ∧
    ∫ M, (nrm (M.mulVec h) * nrm (M.mulVec h') - (m : ℝ) * v * (nrm h * nrm h')) ^ 2
      ∂gaussMat m k v ≤ 10 / (m : ℝ) * ((m : ℝ) * v * (nrm h * nrm h')) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 ≤ (m : ℝ) * v := by positivity
  have hmeas : ∀ h : Fin k → ℝ, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      normSq (M.mulVec h)) := fun h => measurable_normSq.comp (measurable_mulVec_right h)
  have hsq : ∀ h : Fin k → ℝ, (√((m : ℝ) * v) * nrm h) ^ 2 = (m : ℝ) * (v * normSq h) := by
    intro h; rw [mul_pow, Real.sq_sqrt hs, nrm_sq]; ring
  have h4 : ∀ h : Fin k → ℝ, ∫ M, normSq (M.mulVec h) ^ 2 ∂gaussMat m k v ≤
      (1 + 2 / (m : ℝ)) * (√((m : ℝ) * v) * nrm h) ^ 4 := by
    intro h
    rw [(layer_lin_four hv h).2, show (√((m : ℝ) * v) * nrm h) ^ 4 =
      ((√((m : ℝ) * v) * nrm h) ^ 2) ^ 2 by ring, hsq]
    apply le_of_eq
    field_simp
  have key := norm_pair (μ := gaussMat m k v) (hmeas h) (hmeas h')
    (fun M => normSq_nonneg _) (fun M => normSq_nonneg _) (layer_lin_four hv h).1
    (layer_lin_four hv h').1 (ε := 2 / (m : ℝ))
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg h))
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg h'))
    (by rw [(layer_lin_sq hv h).2, hsq]) (by rw [(layer_lin_sq hv h').2, hsq]) (h4 h) (h4 h')
  have e : √((m : ℝ) * v) * nrm h * (√((m : ℝ) * v) * nrm h') =
      (m : ℝ) * v * (nrm h * nrm h') := by
    have := Real.mul_self_sqrt hs
    calc _ = (√((m : ℝ) * v) * √((m : ℝ) * v)) * (nrm h * nrm h') := by ring
      _ = _ := by rw [this]
  rw [e] at key
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  refine ⟨k1, k2, ?_, k4, ?_⟩
  · calc _ = (m : ℝ) * v * (nrm h * nrm h') * (1 - 2 * (2 / (m : ℝ))) := by ring
      _ ≤ _ := k3
  · calc _ ≤ 5 * (2 / (m : ℝ)) * ((m : ℝ) * v * (nrm h * nrm h')) ^ 2 := k5
      _ = _ := by ring

/-! ## The lower bounds of one layer -/

lemma measurable_psi_relu {G : ℝ → ℝ} (hG : Continuous G) (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi G (reluV (M.mulVec h)) (reluV (M.mulVec h'))) :=
  (measurable_psi hG).comp ((measurable_reluV.comp (measurable_mulVec_right h)).prodMk
    (measurable_reluV.comp (measurable_mulVec_right h')))

lemma measurable_psi_lin {G : ℝ → ℝ} (hG : Continuous G) (h h' : Fin k → ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi (ι := Fin m) G (M.mulVec h) (M.mulVec h')) := by
  have h1 : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => (M.mulVec h, M.mulVec h')) :=
    (measurable_mulVec_right h).prodMk (measurable_mulVec_right h')
  exact Measurable.comp (g := fun p : (Fin m → ℝ) × (Fin m → ℝ) => psi G p.1 p.2)
    (f := fun M : Matrix (Fin m) (Fin k) ℝ => (M.mulVec h, M.mulVec h')) (measurable_psi hG) h1

lemma lower_arith {I IP a b G0 Gt s p0 t q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ G0) (hs : 0 ≤ s)
    (hp0 : 0 ≤ p0) (hq : 0 ≤ q) (heq : a + b * t = Gt) (hPl : s * p0 * (1 - q) ≤ IP)
    (hI : a * IP + b * (s * (p0 * t)) ≤ I) : s * (p0 * Gt - q * G0 * p0) ≤ I := by
  have h1 := mul_le_mul_of_nonneg_left hPl ha0
  have h2 : a * (s * p0 * q) ≤ G0 * (s * p0 * q) :=
    mul_le_mul_of_nonneg_right ha1 (by positivity)
  subst heq
  nlinarith

/-- **The one-layer step, ReLU layer** (paper: onW4c §3, the supporting plane and
`E ĉ = σσ′κ(τ)`): for a Gaussian matrix `M` with `m` rows and variance `v`,
`E Ψ_G(ReLU(Mh), ReLU(Mh′)) ≥ (m/2)·v·[Ψ_{G∘κ}(h, h′) − (10/m)·G(0)·|h||h′|]`. -/
theorem relu_layer_lower {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi G (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) ∧
    (m : ℝ) / 2 * v * (psi (G ∘ kappa) h h' - 10 / (m : ℝ) * G 0 * (nrm h * nrm h')) ≤
      ∫ M, psi G (reluV (M.mulVec h)) (reluV (M.mulVec h')) ∂gaussMat m k v := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hPi, -, hPl, -, -⟩ := relu_layer_pair (m := m) hv hm h h'
  have hint : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      psi G (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) := by
    refine Integrable.mono' hPi (measurable_psi_relu hG.cont h h').aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg hG _ _)]
    exact psi_le_nrm hG _ _
  refine ⟨hint, ?_⟩
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support (kappa_mem_Icc (cosv_mem h h'))
  obtain ⟨hci, hce⟩ := layer_dot_relu (m := m) hv h h'
  have hsum : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      a * (nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h'))) +
        b * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) :=
    (hPi.const_mul a).add (hci.const_mul b)
  have hlow := integral_mono hsum hint (fun M => psi_ge hab _ _)
  have a1 := integral_add (hPi.const_mul a) (hci.const_mul b)
  have a2 : ∫ M : Matrix (Fin m) (Fin k) ℝ, a * (nrm (reluV (M.mulVec h)) *
      nrm (reluV (M.mulVec h'))) ∂gaussMat m k v = a * ∫ M : Matrix (Fin m) (Fin k) ℝ,
      nrm (reluV (M.mulVec h)) * nrm (reluV (M.mulVec h')) ∂gaussMat m k v :=
    integral_const_mul _ _
  have a3 : ∫ M : Matrix (Fin m) (Fin k) ℝ, b * dotp (reluV (M.mulVec h))
      (reluV (M.mulVec h')) ∂gaussMat m k v = b * ∫ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) ∂gaussMat m k v :=
    integral_const_mul _ _
  beta_reduce at a1
  have e : (m : ℝ) / 2 * (v * kernelPhi h h') =
      (m : ℝ) / 2 * v * (nrm h * nrm h' * kappa (cosv h h')) := by
    rw [kernelPhi_eq_psi]; unfold psi; ring
  rw [a1, a2, a3, hce, e] at hlow
  have hfin := lower_arith (q := 10 / (m : ℝ)) ha0 ha1 (by positivity : (0 : ℝ) ≤ (m : ℝ) / 2 * v)
    (nrm_mul_nonneg h h') (by positivity) heq hPl hlow
  exact hfin

/-- **The one-layer step, linear layer** (the last matrix of a network):
`E Ψ_G(Mh, Mh′) ≥ m·v·[Ψ_G(h, h′) − (4/m)·G(0)·|h||h′|]`. -/
theorem lin_layer_lower {G : ℝ → ℝ} (hG : KGood G) {v : ℝ} (hv : 0 ≤ v) (hm : 1 ≤ m)
    (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h'))
      (gaussMat m k v) ∧
    (m : ℝ) * v * (psi G h h' - 4 / (m : ℝ) * G 0 * (nrm h * nrm h')) ≤
      ∫ M, psi G (M.mulVec h) (M.mulVec h') ∂gaussMat m k v := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hPi, -, hPl, -, -⟩ := lin_layer_pair (m := m) hv hm h h'
  have hint : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => psi G (M.mulVec h) (M.mulVec h'))
      (gaussMat m k v) := by
    refine Integrable.mono' hPi (measurable_psi_lin hG.cont h h').aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg hG _ _)]
    exact psi_le_nrm hG _ _
  refine ⟨hint, ?_⟩
  obtain ⟨a, b, ha0, ha1, hb0, hb1, heq, hab⟩ := hG.support (cosv_mem h h')
  obtain ⟨hci, hce⟩ := layer_dot_lin (m := m) hv h h'
  have hsum : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      a * (nrm (M.mulVec h) * nrm (M.mulVec h')) + b * dotp (M.mulVec h) (M.mulVec h'))
      (gaussMat m k v) := (hPi.const_mul a).add (hci.const_mul b)
  have hlow := integral_mono hsum hint (fun M => psi_ge hab _ _)
  have a1 := integral_add (hPi.const_mul a) (hci.const_mul b)
  have a2 : ∫ M : Matrix (Fin m) (Fin k) ℝ, a * (nrm (M.mulVec h) * nrm (M.mulVec h'))
      ∂gaussMat m k v = a * ∫ M : Matrix (Fin m) (Fin k) ℝ,
      nrm (M.mulVec h) * nrm (M.mulVec h') ∂gaussMat m k v := integral_const_mul _ _
  have a3 : ∫ M : Matrix (Fin m) (Fin k) ℝ, b * dotp (M.mulVec h) (M.mulVec h')
      ∂gaussMat m k v = b * ∫ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (M.mulVec h) (M.mulVec h') ∂gaussMat m k v := integral_const_mul _ _
  beta_reduce at a1
  have e : (m : ℝ) * (v * dotp h h') = (m : ℝ) * v * (nrm h * nrm h' * cosv h h') := by
    rw [dotp_eq_cosv_mul h h']; ring
  rw [a1, a2, a3, hce, e] at hlow
  have hfin := lower_arith (q := 4 / (m : ℝ)) ha0 ha1 (by positivity : (0 : ℝ) ≤ (m : ℝ) * v)
    (nrm_mul_nonneg h h') (by positivity) heq hPl hlow
  exact hfin

end BstLean.Part132

open BstLean.Part132 in
#print axioms norm_pair
open BstLean.Part132 in
#print axioms relu_layer_lower
open BstLean.Part132 in
#print axioms lin_layer_lower
