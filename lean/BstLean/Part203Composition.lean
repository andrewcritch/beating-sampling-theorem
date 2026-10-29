import BstLean.Part203Scalar

/-! Part 203: exact composition under the independent residual distribution. -/
namespace BstLean.Part203
open MeasureTheory Real BstLean.Part156 BstLean.Part196

/-- The slope of the World logarithm tangent at v₀. -/
noncomputable def worldK (L s v₀ : ℝ) : ℝ :=
  (exp (s * L) - 1) / (L * (1 + v₀ * (exp (s * L) - 1)))

/-- The constant of the same World logarithm tangent. -/
noncomputable def worldC (L s v₀ : ℝ) : ℝ :=
  tangentC (v₀ * (exp (s * L) - 1)) L

/-- Exact Agent GP after the signed World affine comparison. -/
noncomputable def exactRhs (C K α β Q L : ℝ) : ℝ :=
  C + K * β + log (1 + Q * (exp (L * K * α) - 1)) / L

/-- TG replaces the Agent logarithm by its tangent at u₀. -/
noncomputable def tgRhs (C K α β Q L u₀ : ℝ) : ℝ :=
  C + tangentC u₀ L + K * β +
    Q * (exp (L * K * α) - 1) / (L * (1 + u₀))

lemma exact_le_tg {C K α β Q L u₀ : ℝ} (hL : 0 < L)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hu : -1 < u₀) :
    exactRhs C K α β Q L ≤ tgRhs C K α β Q L u₀ := by
  have hb := bernoulli_pos (x := L * K * α) hQ0 hQ1
  have ht := log_tangent_div (by linarith : -1 < Q * (exp (L * K * α) - 1)) hu hL
  unfold exactRhs tgRhs
  linarith

lemma worldK_pos {L s v₀ : ℝ} (hL : 0 < L) (hs : 0 < s)
    (hv : 0 < 1 + v₀ * (exp (s * L) - 1)) : 0 < worldK L s v₀ := by
  unfold worldK
  exact div_pos (by have := Real.one_lt_exp_iff.mpr (mul_pos hs hL); linarith)
    (mul_pos hL hv)

lemma worldK_neg {L s v₀ : ℝ} (hL : 0 < L) (hs : s < 0)
    (hv : 0 < 1 + v₀ * (exp (s * L) - 1)) : worldK L s v₀ < 0 := by
  unfold worldK
  exact div_neg_of_neg_of_pos
    (by have := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos hs hL); linarith)
    (mul_pos hL hv)

lemma primitive_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ} {L : ℝ}
    (hL : 0 < L) (hm : Measurable p) (h0 : ∀ ω, 0 ≤ p ω)
    (h1 : ∀ ω, p ω ≤ 1) (h : ExactPrimitive μ p L) (s : ℝ) :
    ∫ ω, exp (s * p ω) ∂μ ≤
      exp (log (1 + (∫ ω, p ω ∂μ) * (exp (s * L) - 1)) / L) := by
  have hl := exp_le_exp.mpr (primitive_log μ hL hm h0 h1 h s)
  rwa [exp_log (integral_exp_pos (integrable_exp_mul μ hm h0 h1 s))] at hl

section Composition
variable {ΩW ΩA : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩA]

/-- A signed affine comparison is sufficient; both stages retain exact GP. -/
theorem exact_composition (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {LW LA s v₀ α β : ℝ} (hLW : 0 < LW) (hLA : 0 < LA)
    (hv₀ : 0 < 1 + v₀ * (exp (s * LW) - 1))
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) LW)
    (hA : ExactPrimitive μA P LA)
    (hcmp : ∀ ωA, worldK LW s v₀ * (∫ ωW, p (ωW, ωA) ∂μW) ≤
      worldK LW s v₀ * (α * P ωA + β)) :
    ∫ ω, exp (s * p ω) ∂(μW.prod μA) ≤
      exp (exactRhs (worldC LW s v₀) (worldK LW s v₀) α β (∫ ωA, P ωA ∂μA) LA) := by
  have hint := integrable_exp_mul (μW.prod μA) hm h0 h1 s
  have hbound : Integrable (fun ωA => exp (worldC LW s v₀ + worldK LW s v₀ * β) *
      exp (worldK LW s v₀ * α * P ωA)) μA :=
    (integrable_exp_mul μA hPm hP0 hP1 _).const_mul _
  rw [integral_prod_symm _ hint]
  calc
    _ ≤ ∫ ωA, exp (worldC LW s v₀ + worldK LW s v₀ * β) *
        exp (worldK LW s v₀ * α * P ωA) ∂μA := by
      refine integral_mono hint.integral_prod_right hbound (fun ωA => ?_)
      have hslice : Measurable (fun ωW => p (ωW, ωA)) :=
        hm.comp (measurable_id.prodMk measurable_const)
      obtain ⟨hv0, hv1⟩ := BstLean.Part157.integral_mem_01 μW hslice
        (fun _ => h0 _) (fun _ => h1 _)
      have hb := bernoulli_pos (x := s * LW) hv0 hv1
      have ht := log_tangent_div (by linarith :
          -1 < (∫ ωW, p (ωW, ωA) ∂μW) * (exp (s * LW) - 1))
        (by linarith : -1 < v₀ * (exp (s * LW) - 1)) hLW
      have heq : (∫ ωW, p (ωW, ωA) ∂μW) * (exp (s * LW) - 1) /
          (LW * (1 + v₀ * (exp (s * LW) - 1))) =
          worldK LW s v₀ * (∫ ωW, p (ωW, ωA) ∂μW) := by unfold worldK; ring
      rw [heq] at ht
      refine (primitive_exp μW hLW hslice (fun _ => h0 _) (fun _ => h1 _) (hW ωA) s).trans ?_
      rw [← exp_add]
      apply exp_le_exp.mpr
      change _ ≤ worldC LW s v₀ + worldK LW s v₀ * β + worldK LW s v₀ * α * P ωA
      have := hcmp ωA
      dsimp [worldC]
      nlinarith
    _ = exp (worldC LW s v₀ + worldK LW s v₀ * β) *
        ∫ ωA, exp (worldK LW s v₀ * α * P ωA) ∂μA := integral_const_mul _ _
    _ ≤ exp (worldC LW s v₀ + worldK LW s v₀ * β) *
        exp (log (1 + (∫ ωA, P ωA ∂μA) *
          (exp ((worldK LW s v₀ * α) * LA) - 1)) / LA) :=
      mul_le_mul_of_nonneg_left
        (primitive_exp μA hLA hPm hP0 hP1 hA _) (exp_pos _).le
    _ = _ := by rw [← exp_add]; unfold exactRhs; congr 2 <;> ring

/-- TG is a complete second-logarithm alternative to exact composition. -/
theorem tg_composition (μW : Measure ΩW) (μA : Measure ΩA)
    [IsProbabilityMeasure μW] [IsProbabilityMeasure μA]
    {p : ΩW × ΩA → ℝ} (hm : Measurable p) (h0 : ∀ x, 0 ≤ p x)
    (h1 : ∀ x, p x ≤ 1) {P : ΩA → ℝ} (hPm : Measurable P)
    (hP0 : ∀ x, 0 ≤ P x) (hP1 : ∀ x, P x ≤ 1)
    {LW LA s v₀ α β u₀ : ℝ} (hLW : 0 < LW) (hLA : 0 < LA)
    (hv₀ : 0 < 1 + v₀ * (exp (s * LW) - 1)) (hu₀ : -1 < u₀)
    (hW : ∀ ωA, ExactPrimitive μW (fun ωW => p (ωW, ωA)) LW)
    (hA : ExactPrimitive μA P LA)
    (hcmp : ∀ ωA, worldK LW s v₀ * (∫ ωW, p (ωW, ωA) ∂μW) ≤
      worldK LW s v₀ * (α * P ωA + β)) :
    ∫ ω, exp (s * p ω) ∂(μW.prod μA) ≤
      exp (tgRhs (worldC LW s v₀) (worldK LW s v₀) α β
        (∫ ωA, P ωA ∂μA) LA u₀) := by
  obtain ⟨hq0, hq1⟩ := BstLean.Part157.integral_mem_01 μA hPm hP0 hP1
  exact (exact_composition μW μA hm h0 h1 hPm hP0 hP1 hLW hLA hv₀ hW hA hcmp).trans
    (exp_le_exp.mpr (exact_le_tg hLA hq0 hq1 hu₀))

end Composition
end BstLean.Part203
