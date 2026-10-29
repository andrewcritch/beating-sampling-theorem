import BstLean.Part37Law

/-!
# Part 37, wave 1: the laws `D(θ)`, `D_K(θ)` and the density-ratio transfers

Paper: Lemma `frob` (`E_D p ∈ [ρ⁻¹, ρ] E_U p` for `p ≥ 0`) and Lemma `floor` (`Var_D h ≥ ρ⁻¹ Var_U h`).
Specification §3. Both are stated with `ρ' = 33/20 ≥ e^{1/2}` and `1/ρ' = 20/33 ≤ e^{−1/2}`, a cruder true
bound. For `D_K` (`K ≥ 3`) the density `T_K(q)/Z_K` lies in `[T_3(−1/4)/e^{1/4}, e^{1/4}/T_3(−1/4)]
⊂ [20/33, 33/20]` (file `Part37Law`). Mathlib: `integral_withDensity_eq_integral_smul`,
`uniformSphere_ae_sphere` (Part 29), `uniformSphere_isProbability` (Part 29).

Provers: replace each `sorry` by a proof. Do not edit `Part37Defs.lean` or any statement in this file,
and do not use `native_decide` anywhere.
-/

namespace BstLean.Part37

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (SphereProd floorY4 rawQ Dc)

variable {n : ℕ}

private lemma continuous_qth (θ : Fin n → ℝ) : Continuous (qth θ) := by
  unfold qth
  fun_prop

private lemma continuous_taylor (K : ℕ) : Continuous (taylorExp K) := by
  unfold taylorExp
  fun_prop

private lemma sphere_cont_integrable (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma weighted_integral {w : (Fin n → ℝ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x) (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂(uniformSphere n).withDensity (fun x => ENNReal.ofReal (w x))) =
      ∫ x, f x * w x ∂uniformSphere n := by
  rw [integral_withDensity_eq_integral_toReal_smul
    hw.measurable.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [hw0] with x hx
  simp [ENNReal.toReal_ofReal hx, mul_comm]

private lemma normalized_prob (hn : 1 ≤ n) {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x)
    (hz : 0 < ∫ x, w x ∂uniformSphere n) :
    IsProbabilityMeasure ((uniformSphere n).withDensity
      (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂uniformSphere n))) := by
  have hi := (sphere_cont_integrable hn hw).div_const (∫ y, w y ∂uniformSphere n)
  have h0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x / ∫ y, w y ∂uniformSphere n :=
    hw0.mono (fun x hx => div_nonneg hx hz.le)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi h0, integral_div,
    div_self hz.ne', ENNReal.ofReal_one]

private lemma ratio_bounds (hn : 1 ≤ n) {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) {a b : ℝ} (ha : 0 < a) (hb : b ≤ (33 / 20) * a)
    (hbound : ∀ᵐ x ∂uniformSphere n, a ≤ w x ∧ w x ≤ b) :
    ∀ᵐ x ∂uniformSphere n,
      20 / 33 ≤ w x / (∫ y, w y ∂uniformSphere n) ∧
      w x / (∫ y, w y ∂uniformSphere n) ≤ 33 / 20 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hi := sphere_cont_integrable hn hw
  have hza : a ≤ ∫ x, w x ∂uniformSphere n := by
    simpa using integral_mono_ae (integrable_const a) hi (hbound.mono (fun x hx => hx.1))
  have hzb : (∫ x, w x ∂uniformSphere n) ≤ b := by
    simpa using integral_mono_ae hi (integrable_const b) (hbound.mono (fun x hx => hx.2))
  filter_upwards [hbound] with x hx
  constructor
  · apply (le_div_iff₀ (ha.trans_le hza)).2
    nlinarith
  · apply (div_le_iff₀ (ha.trans_le hza)).2
    nlinarith

private lemma compare_weight {w : (Fin n → ℝ) → ℝ} (hw : Continuous w)
    (hb : ∀ᵐ x ∂uniformSphere n, 20 / 33 ≤ w x ∧ w x ≤ 33 / 20)
    (p : (Fin n → ℝ) → ℝ) (hp : ∀ x, 0 ≤ p x) (hi : Integrable p (uniformSphere n)) :
    (20 / 33) * ∫ x, p x ∂uniformSphere n ≤ ∫ x, p x * w x ∂uniformSphere n ∧
      (∫ x, p x * w x ∂uniformSphere n) ≤ (33 / 20) * ∫ x, p x ∂uniformSphere n := by
  have hw0 : ∀ᵐ x ∂uniformSphere n, 0 ≤ w x :=
    hb.mono (fun x hx => le_trans (by norm_num) hx.1)
  have hprod : Integrable (fun x => p x * w x) (uniformSphere n) := by
    apply (hi.mul_const (33 / 20)).mono' (hi.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    filter_upwards [hb, hw0] with x hx hx0
    change ‖p x * w x‖ ≤ p x * (33 / 20)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp x) hx0)]
    exact mul_le_mul_of_nonneg_left hx.2 (hp x)
  constructor
  · rw [← integral_const_mul]
    apply integral_mono_ae (hi.const_mul _) hprod
    filter_upwards [hb] with x hx
    nlinarith [mul_le_mul_of_nonneg_left hx.1 (hp x)]
  · rw [← integral_const_mul]
    apply integral_mono_ae hprod (hi.const_mul _)
    filter_upwards [hb] with x hx
    nlinarith [mul_le_mul_of_nonneg_left hx.2 (hp x)]

theorem binghamK_isProb (hn : 1 ≤ n) (θ : Fin n → ℝ) (hθ : InBall θ) (K : ℕ) :
    IsProbabilityMeasure (binghamK n K θ) := by
  apply normalized_prob hn ((continuous_taylor K).comp (continuous_qth θ))
    _ (ZK_pos hn θ hθ K)
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  exact (taylor_pos K _ (qth_abs_le θ hθ x hx)).le

theorem bingham_isProb (hn : 1 ≤ n) (θ : Fin n → ℝ) : IsProbabilityMeasure (bingham n θ) := by
  apply normalized_prob hn (Real.continuous_exp.comp (continuous_qth θ)) _ (Zth_pos hn θ)
  exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)

theorem binghamK_ae_sphere (K : ℕ) (θ : Fin n → ℝ) :
    ∀ᵐ x ∂(binghamK n K θ), ∑ i, x i ^ 2 = 1 := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

theorem bingham_ae_sphere (θ : Fin n → ℝ) : ∀ᵐ x ∂(bingham n θ), ∑ i, x i ^ 2 = 1 := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (BstLean.Part29.uniformSphere_ae_sphere n)

/-- Integrals against `D_K` are weighted integrals against the uniform law (every `f`). -/
theorem integral_binghamK (hn : 1 ≤ n) (θ : Fin n → ℝ) (hθ : InBall θ) (K : ℕ)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂binghamK n K θ =
      ∫ x, f x * (taylorExp K (qth θ x) / ZK n K θ) ∂uniformSphere n := by
  apply weighted_integral (((continuous_taylor K).comp (continuous_qth θ)).div_const _)
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  exact div_nonneg (taylor_pos K _ (qth_abs_le θ hθ x hx)).le (ZK_pos hn θ hθ K).le

/-- Integrals against `D` are weighted integrals against the uniform law (every `f`). -/
theorem integral_bingham (hn : 1 ≤ n) (θ : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂bingham n θ = ∫ x, f x * (Real.exp (qth θ x) / Zth n θ) ∂uniformSphere n := by
  apply weighted_integral ((Real.continuous_exp.comp (continuous_qth θ)).div_const _)
  exact Filter.Eventually.of_forall (fun x => div_nonneg (Real.exp_pos _).le (Zth_pos hn θ).le)

/-- **Density comparison for `D_K`**, `K ≥ 3`, nonnegative integrands. -/
theorem binghamK_compare (hn : 1 ≤ n) (θ : Fin n → ℝ) (hθ : InBall θ) (K : ℕ) (hK : 3 ≤ K)
    (p : (Fin n → ℝ) → ℝ) (hp : ∀ x, 0 ≤ p x) (hpi : Integrable p (uniformSphere n)) :
    (20 / 33) * ∫ x, p x ∂uniformSphere n ≤ ∫ x, p x ∂binghamK n K θ ∧
      ∫ x, p x ∂binghamK n K θ ≤ (33 / 20) * ∫ x, p x ∂uniformSphere n := by
  rw [integral_binghamK hn θ hθ K p]
  apply compare_weight (((continuous_taylor K).comp (continuous_qth θ)).div_const _) _ p hp hpi
  apply ratio_bounds hn ((continuous_taylor K).comp (continuous_qth θ))
    (a := 299 / 384) (b := Real.exp (1 / 4)) (by norm_num) exp_quarter_le
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  exact ⟨taylor_lower K hK _ (qth_abs_le θ hθ x hx),
    taylor_upper K _ (qth_abs_le θ hθ x hx)⟩

/-- **Density comparison for `D`**, nonnegative integrands. -/
theorem bingham_compare (hn : 1 ≤ n) (θ : Fin n → ℝ) (hθ : InBall θ)
    (p : (Fin n → ℝ) → ℝ) (hp : ∀ x, 0 ≤ p x) (hpi : Integrable p (uniformSphere n)) :
    (20 / 33) * ∫ x, p x ∂uniformSphere n ≤ ∫ x, p x ∂bingham n θ ∧
      ∫ x, p x ∂bingham n θ ≤ (33 / 20) * ∫ x, p x ∂uniformSphere n := by
  rw [integral_bingham hn θ p]
  apply compare_weight ((Real.continuous_exp.comp (continuous_qth θ)).div_const _) _ p hp hpi
  have hb : Real.exp (1 / 4) ≤ (33 / 20) * Real.exp (-(1 / 4)) := by
    have he : Real.exp (1 / 4) = Real.exp (1 / 2) * Real.exp (-(1 / 4)) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_right exp_half_le (Real.exp_pos _).le
  apply ratio_bounds hn (Real.continuous_exp.comp (continuous_qth θ))
    (a := Real.exp (-(1 / 4))) (b := Real.exp (1 / 4)) (Real.exp_pos _) hb
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  have h := abs_le.mp (qth_abs_le θ hθ x hx)
  exact ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩

/-- **Floor transfer** (Lemma `floor`): `Var_D h ≥ ρ'⁻¹ Var_U h` for `h = f ∘ m_M`, every `M`. -/
theorem var_transfer (hn : 1 ≤ n) (θ : Fin n → ℝ) (hθ : InBall θ) (f0 : ℝ) (g : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (M : CoefIdx n → ℝ) :
    (20 / 33) * varOf (uniformSphere n) f0 g F M ≤ varOf (bingham n θ) f0 g F M := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let h : (Fin n → ℝ) → ℝ := fun x => funF f0 g F
    (BstLean.Part29.mapM (cOf M) (LOf M) (fun k => BstLean.Part29.symOfRaw (aOf M k)) x)
  have hc : Continuous h := by
    unfold h BstLean.Part29.funF BstLean.Part29.mapM BstLean.Part29.symOfRaw
    fun_prop
  let a := Bof (bingham n θ) f0 g F M
  let b := ∫ x, h x ∂uniformSphere n
  have hmin : (∫ x, (h x - b) ^ 2 ∂uniformSphere n) ≤
      ∫ x, (h x - a) ^ 2 ∂uniformSphere n := by
    have he : (∫ x, (h x - a) ^ 2 ∂uniformSphere n) =
        (∫ x, (h x - b) ^ 2 ∂uniformSphere n) + (b - a) ^ 2 := by
      have hpoint : ∀ x, (h x - a) ^ 2 =
          (h x - b) ^ 2 + (2 * (b - a)) * h x + (a ^ 2 - b ^ 2) := by
        intro x
        ring
      simp_rw [hpoint]
      rw [integral_add, integral_add, integral_const_mul, integral_const]
      · simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
        change _ + 2 * (b - a) * b + _ = _
        ring
      · exact sphere_cont_integrable hn ((hc.sub continuous_const).pow 2)
      · exact (sphere_cont_integrable hn hc).const_mul _
      · exact (sphere_cont_integrable hn ((hc.sub continuous_const).pow 2)).add
          ((sphere_cont_integrable hn hc).const_mul _)
      · exact integrable_const _
    rw [he]
    nlinarith [sq_nonneg (b - a)]
  have hcmp := (bingham_compare hn θ hθ (fun x => (h x - a) ^ 2)
    (fun x => sq_nonneg _) (sphere_cont_integrable hn ((hc.sub continuous_const).pow 2))).1
  change (20 / 33) * (∫ x, (h x - b) ^ 2 ∂uniformSphere n) ≤
    ∫ x, (h x - a) ^ 2 ∂bingham n θ
  exact (mul_le_mul_of_nonneg_left hmin (by norm_num)).trans hcmp

end BstLean.Part37

#print axioms BstLean.Part37.binghamK_isProb
#print axioms BstLean.Part37.bingham_isProb
#print axioms BstLean.Part37.binghamK_ae_sphere
#print axioms BstLean.Part37.bingham_ae_sphere
#print axioms BstLean.Part37.integral_binghamK
#print axioms BstLean.Part37.integral_bingham
#print axioms BstLean.Part37.binghamK_compare
#print axioms BstLean.Part37.bingham_compare
#print axioms BstLean.Part37.var_transfer
