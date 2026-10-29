import BstLean.Part107Sb

/-!
# Part 107 S(c): the abstract Corollary S (the average over `W`)
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory

/-- Step 4 of Corollary S in an abstract form. -/
theorem overW {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : Measure Θ} [IsProbabilityMeasure γ]
    (X : Ω × Θ → ℝ) (Q : Θ → ℝ) (vW DW : Ω → ℝ) (n K v J c : ℝ)
    (hXm : Measurable X) (hQ4 : Integrable (fun θ => Q θ ^ 4) γ)
    (hX0 : ∀ z, 0 ≤ X z) (hXQ : ∀ z, X z ≤ Q z.2 ^ 2) (hn : 1 ≤ n)
    (hv : Integrable vW P) (hv2 : Integrable (fun ω => vW ω ^ 2) P) (hD : Integrable DW P)
    (h1 : ∀ᵐ ω ∂P, ∫ θ, X (ω, θ) ∂γ = n * (K - vW ω))
    (h2 : ∀ᵐ ω ∂P, ∫ θ, X (ω, θ) ^ 2 ∂γ ≤ n * (n + 2) * ((K - vW ω) ^ 2 + 2 * DW ω))
    (h3 : ∀ᵐ ω ∂P, (vW ω - c) ^ 2 ≤ DW ω)
    (hvK : v < K) (hEv : ∫ ω, vW ω ∂P ≤ v) (hJ : n * ∫ ω, DW ω ∂P ≤ J) :
    MemLp X 2 (P.prod γ) ∧ n * (K - v) ≤ ∫ z, X z ∂(P.prod γ) ∧
      n * Var[X; P.prod γ] ≤
        (2 + 3 * J * (1 + 2 / n) / (K - v) ^ 2) * (∫ z, X z ∂(P.prod γ)) ^ 2 := by
  have iX2 : Integrable (fun z => X z ^ 2) (P.prod γ) := by
    refine Integrable.mono' (hQ4.comp_snd P) (hXm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (hX0 z)]
    calc X z ^ 2 ≤ (Q z.2 ^ 2) ^ 2 := pow_le_pow_left₀ (hX0 z) (hXQ z) 2
      _ = Q z.2 ^ 4 := by ring
  have hL2 : MemLp X 2 (P.prod γ) := (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 iX2
  have iX : Integrable X (P.prod γ) := hL2.integrable one_le_two
  set Ev := ∫ ω, vW ω ∂P with hEv'
  set V2 := ∫ ω, vW ω ^ 2 ∂P with hV2
  set ED := ∫ ω, DW ω ∂P with hED
  have hEX : ∫ z, X z ∂(P.prod γ) = n * (K - Ev) := by
    rw [integral_prod _ iX, integral_congr_ae h1, integral_const_mul,
      integral_sub (integrable_const _) hv, integral_const]
    simp [hEv']
  have iR : Integrable (fun ω => n * (n + 2) * ((K - vW ω) ^ 2 + 2 * DW ω)) P := by
    have e : (fun ω => n * (n + 2) * ((K - vW ω) ^ 2 + 2 * DW ω)) =
        fun ω => n * (n + 2) * (K ^ 2 - 2 * K * vW ω + vW ω ^ 2 + 2 * DW ω) := by
      funext ω; ring
    rw [e]
    exact ((((integrable_const _).sub (hv.const_mul _)).add hv2).add (hD.const_mul _)).const_mul _
  have hR : ∫ ω, n * (n + 2) * ((K - vW ω) ^ 2 + 2 * DW ω) ∂P =
      n * (n + 2) * (K ^ 2 - 2 * K * Ev + V2 + 2 * ED) := by
    have e : (fun ω => n * (n + 2) * ((K - vW ω) ^ 2 + 2 * DW ω)) =
        fun ω => n * (n + 2) * (K ^ 2 - 2 * K * vW ω + vW ω ^ 2 + 2 * DW ω) := by
      funext ω; ring
    have i1 : Integrable (fun ω => 2 * K * vW ω) P := hv.const_mul _
    have i2 : Integrable (fun ω => K ^ 2 - 2 * K * vW ω) P := (integrable_const _).sub i1
    have i3 : Integrable (fun ω => K ^ 2 - 2 * K * vW ω + vW ω ^ 2) P := i2.add hv2
    have i4 : Integrable (fun ω => 2 * DW ω) P := hD.const_mul _
    rw [e, integral_const_mul, integral_add i3 i4, integral_add i2 hv2,
      integral_sub (integrable_const _) i1, integral_const_mul, integral_const_mul,
      integral_const]
    simp [hEv', hV2, hED]
  have hEX2 : ∫ z, X z ^ 2 ∂(P.prod γ) ≤ n * (n + 2) * (K ^ 2 - 2 * K * Ev + V2 + 2 * ED) := by
    rw [integral_prod _ iX2, ← hR]
    exact integral_mono_ae iX2.integral_prod_left iR h2
  have hVc : V2 - 2 * c * Ev + c ^ 2 ≤ ED := by
    have i1 : Integrable (fun ω => 2 * c * vW ω) P := hv.const_mul _
    have i2 : Integrable (fun ω => vW ω ^ 2 - 2 * c * vW ω) P := hv2.sub i1
    have iL : Integrable (fun ω => (vW ω - c) ^ 2) P := by
      have e : (fun ω => (vW ω - c) ^ 2) = fun ω => vW ω ^ 2 - 2 * c * vW ω + c ^ 2 := by
        funext ω; ring
      rw [e]; exact i2.add (integrable_const _)
    have := integral_mono_ae iL hD h3
    have e : (fun ω => (vW ω - c) ^ 2) = fun ω => vW ω ^ 2 - 2 * c * vW ω + c ^ 2 := by
      funext ω; ring
    rw [e, integral_add i2 (integrable_const _), integral_sub hv2 i1, integral_const_mul,
      integral_const] at this
    simpa [hEv', hV2, hED] using this
  have hED0 : 0 ≤ ED :=
    integral_nonneg_of_ae (h3.mono fun ω h => (sq_nonneg _).trans h)
  have hn0 : 0 < n := by linarith
  have hJ0 : 0 ≤ J := le_trans (mul_nonneg hn0.le hED0) hJ
  have ht : 0 < K - v := by linarith
  have hm : K - v ≤ K - Ev := by linarith
  have hVar : Var[X; P.prod γ] = ∫ z, X z ^ 2 ∂(P.prod γ) - (∫ z, X z ∂(P.prod γ)) ^ 2 := by
    rw [variance_eq_sub hL2]; rfl
  refine ⟨hL2, ?_, ?_⟩
  · rw [hEX]; exact mul_le_mul_of_nonneg_left hm hn0.le
  · rw [hVar, hEX]
    set m := K - Ev with hmdef
    set t := K - v with htdef
    have hm0 : 0 < m := lt_of_lt_of_le ht hm
    have hr : 1 ≤ m ^ 2 / t ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have eq : (2 + 3 * J * (1 + 2 / n) / t ^ 2) * (n * m) ^ 2 =
        2 * n ^ 2 * m ^ 2 + 3 * J * (n * (n + 2)) * (m ^ 2 / t ^ 2) := by
      field_simp
    rw [eq]
    have hS : ∫ z, X z ^ 2 ∂(P.prod γ) ≤ n * (n + 2) * (m ^ 2 + 3 * ED) := by
      refine hEX2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      nlinarith [sq_nonneg (Ev - c)]
    have hA : n * (∫ z, X z ^ 2 ∂(P.prod γ) - (n * m) ^ 2) ≤
        2 * n ^ 2 * m ^ 2 + 3 * (n * (n + 2)) * (n * ED) := by
      have := mul_le_mul_of_nonneg_left hS hn0.le
      nlinarith
    have hB : 3 * (n * (n + 2)) * (n * ED) ≤ 3 * (n * (n + 2)) * J :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    have hC : 3 * (n * (n + 2)) * J ≤ 3 * J * (n * (n + 2)) * (m ^ 2 / t ^ 2) := by
      have : 0 ≤ 3 * J * (n * (n + 2)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hr this]
    linarith

end BstLean.Part107
