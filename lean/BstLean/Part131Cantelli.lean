import BstLean.Part130Sym

/-!
# Part 131, Cantelli's inequality (one-sided Chebyshev)

Role: `delegations/statements/p131-spec.md`, item 2. For a real random variable `J` with finite
variance and `E J > 0`: `Pr(J > 0) ≥ (E J)² / ((E J)² + Var J)`.
Proof: Markov for `(J − E J − a)²` on `{J ≤ 0}` with `a = Var J / E J`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory

/-- **Cantelli's inequality**: `Pr(J > 0) ≥ (E J)²/((E J)² + Var J)` for `E J > 0`. -/
theorem cantelli {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → ℝ) (hJ : MemLp J 2 μ) (hpos : 0 < ∫ ω, J ω ∂μ) :
    (∫ ω, J ω ∂μ) ^ 2 / ((∫ ω, J ω ∂μ) ^ 2 + Var[J; μ]) ≤ μ.real {ω | 0 < J ω} := by
  set m := ∫ ω, J ω ∂μ with hm
  set V := Var[J; μ] with hV
  have hV0 : 0 ≤ V := variance_nonneg J μ
  set a := V / m with ha
  have ha0 : 0 ≤ a := div_nonneg hV0 hpos.le
  have hJi : Integrable J μ := hJ.integrable (by norm_num)
  have hc : MemLp (fun ω => J ω - m) 2 μ := hJ.sub (memLp_const m)
  have hci : Integrable (fun ω => J ω - m) μ := hJi.sub (integrable_const m)
  have hsq : Integrable (fun ω => (J ω - m) ^ 2) μ := hc.integrable_sq
  have hVint : V = ∫ ω, (J ω - m) ^ 2 ∂μ := variance_eq_integral hJ.aestronglyMeasurable.aemeasurable
  have hYi : Integrable (fun ω => (J ω - m - a) ^ 2) μ := by
    have : (fun ω => (J ω - m - a) ^ 2) =
        fun ω => (J ω - m) ^ 2 - 2 * a * (J ω - m) + a ^ 2 := by funext ω; ring
    rw [this]
    exact (hsq.sub (hci.const_mul _)).add (integrable_const _)
  have hYint : ∫ ω, (J ω - m - a) ^ 2 ∂μ = V + a ^ 2 := by
    have : (fun ω => (J ω - m - a) ^ 2) =
        fun ω => (J ω - m) ^ 2 - 2 * a * (J ω - m) + a ^ 2 := by funext ω; ring
    rw [this, integral_add (f := fun ω => (J ω - m) ^ 2 - 2 * a * (J ω - m)) (g := fun _ => a ^ 2)
        (hsq.sub (hci.const_mul _)) (integrable_const _),
      integral_sub (f := fun ω => (J ω - m) ^ 2) (g := fun ω => 2 * a * (J ω - m)) hsq
        (hci.const_mul _), integral_const_mul,
      integral_sub (f := J) (g := fun _ => m) hJi (integrable_const m), ← hVint]
    simp [hm]
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun ω => sq_nonneg (J ω - m - a)) hYi ((m + a) ^ 2)
  rw [hYint] at hmark
  have hsub : {ω | J ω ≤ 0} ⊆ {ω | (m + a) ^ 2 ≤ (J ω - m - a) ^ 2} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    nlinarith
  have hle : μ.real {ω | J ω ≤ 0} ≤ μ.real {ω | (m + a) ^ 2 ≤ (J ω - m - a) ^ 2} :=
    measureReal_mono hsub
  have hma : 0 < m + a := by linarith
  have hneg : (m + a) ^ 2 * μ.real {ω | J ω ≤ 0} ≤ V + a ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hle (sq_nonneg _)) hmark
  have hcov : (1 : ℝ) ≤ μ.real {ω | 0 < J ω} + μ.real {ω | J ω ≤ 0} := by
    have h1 : μ.real (Set.univ : Set Ω) = 1 := by simp
    have h2 : (Set.univ : Set Ω) ⊆ {ω | 0 < J ω} ∪ {ω | J ω ≤ 0} := by
      intro ω _
      rcases lt_or_ge 0 (J ω) with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc (1 : ℝ) = μ.real Set.univ := h1.symm
      _ ≤ μ.real ({ω | 0 < J ω} ∪ {ω | J ω ≤ 0}) := measureReal_mono h2
      _ ≤ _ := measureReal_union_le _ _
  have hden : 0 < m ^ 2 + V := by positivity
  -- `(V + a²)/(m + a)² = V/(m² + V)`
  have hkey : (m ^ 2 + V) * μ.real {ω | J ω ≤ 0} ≤ V := by
    have e1 : m + a = (m ^ 2 + V) / m := by rw [ha]; field_simp
    have e2 : V + a ^ 2 = V * (m ^ 2 + V) / m ^ 2 := by rw [ha]; field_simp
    rw [e1, e2] at hneg
    have hm2 : 0 < m ^ 2 := by positivity
    have h3 : (m ^ 2 + V) ^ 2 * μ.real {ω | J ω ≤ 0} ≤ V * (m ^ 2 + V) := by
      have := mul_le_mul_of_nonneg_left hneg hm2.le
      have e3 : m ^ 2 * (((m ^ 2 + V) / m) ^ 2 * μ.real {ω | J ω ≤ 0}) =
          (m ^ 2 + V) ^ 2 * μ.real {ω | J ω ≤ 0} := by field_simp
      have e4 : m ^ 2 * (V * (m ^ 2 + V) / m ^ 2) = V * (m ^ 2 + V) := by field_simp
      rw [e3, e4] at this
      exact this
    have h4 : (m ^ 2 + V) * ((m ^ 2 + V) * μ.real {ω | J ω ≤ 0}) ≤ (m ^ 2 + V) * V := by
      nlinarith
    exact le_of_mul_le_mul_left h4 hden
  rw [div_le_iff₀ hden]
  nlinarith

/-- Cantelli with bounds: if `E J ≥ j > 0` and `Var J ≤ V` then `Pr(J > 0) ≥ j²/(j² + V)`. -/
theorem cantelli_of_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : Ω → ℝ) (hJ : MemLp J 2 μ) {j V : ℝ} (hj : 0 < j)
    (hjE : j ≤ ∫ ω, J ω ∂μ) (hV : Var[J; μ] ≤ V) :
    j ^ 2 / (j ^ 2 + V) ≤ μ.real {ω | 0 < J ω} := by
  have hpos : 0 < ∫ ω, J ω ∂μ := lt_of_lt_of_le hj hjE
  refine le_trans ?_ (cantelli μ J hJ hpos)
  have hV0 : 0 ≤ Var[J; μ] := variance_nonneg J μ
  have hj2 : j ^ 2 ≤ (∫ ω, J ω ∂μ) ^ 2 := by nlinarith
  have hVV : 0 ≤ V := hV0.trans hV
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg j) (sub_nonneg.mpr hV),
    mul_nonneg (sub_nonneg.mpr hj2) hV0, mul_nonneg (sub_nonneg.mpr hj2) (hV0.trans hV)]

end BstLean.Part131

open BstLean.Part131 in
#print axioms cantelli
open BstLean.Part131 in
#print axioms cantelli_of_bounds
