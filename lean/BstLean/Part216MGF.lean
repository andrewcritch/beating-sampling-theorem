import BstLean.Part216Series
import BstLean.Part182Bern

/-! Bernstein MGF bounds from complete centred-row moments. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The centred first moment is integrated before using the exponential remainder. -/
theorem factorial_mgf {Y : Ω → ℝ} (hY : Measurable Y)
    (hi : ∀ k : ℕ, Integrable (fun x => |Y x| ^ k) μ)
    (h0 : ∫ x, Y x ∂μ = 0) {v b s : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hs : 0 ≤ s) (hbs : b * s < 1)
    (hM : ∀ k : ℕ, 2 ≤ k → ∫ x, |Y x| ^ k ∂μ ≤
      (k.factorial : ℝ) / 2 * v * b ^ (k - 2)) :
    Integrable (fun x => exp (s * Y x)) μ ∧
    mgf Y μ s ≤ exp (v * s ^ 2 / (2 * (1 - b * s))) := by
  obtain ⟨hA, hR⟩ := factorial_remainder hY hi hv hb hs hbs hM
  have hYi : Integrable Y μ := by
    exact (hi 1).mono' hY.aestronglyMeasurable (Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, pow_one]; exact le_rfl)
  have hE : Integrable (fun x => exp (s * Y x)) μ :=
    hA.mono' (hY.const_mul s).exp.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) hs))
  have hAi : Integrable (fun x => s * |Y x|) μ := by
    simpa only [pow_one] using (hi 1).const_mul s
  have hRi := (hA.sub (integrable_const (1 : ℝ))).sub hAi
  have hLi := (integrable_const (1 : ℝ)).add (hYi.const_mul s)
  have hpt : ∀ x, exp (s * Y x) ≤ 1 + s * Y x +
      (exp (s * |Y x|) - 1 - s * |Y x|) := by
    intro x
    have h := BstLean.Part182.bn_exp_sub_le_abs (s * Y x)
    rw [abs_mul, abs_of_nonneg hs] at h
    linarith
  refine ⟨hE, ?_⟩
  have hI := integral_mono hE (hLi.add hRi) hpt
  change (∫ x, exp (s * Y x) ∂μ) ≤
    ∫ x, (1 + s * Y x) + (exp (s * |Y x|) - 1 - s * |Y x|) ∂μ at hI
  rw [integral_add (f := fun x => 1 + s * Y x)
    (g := fun x => exp (s * |Y x|) - 1 - s * |Y x|) hLi hRi,
    integral_add (f := fun _ => (1 : ℝ)) (g := fun x => s * Y x)
      (integrable_const (1 : ℝ)) (hYi.const_mul s),
    integral_const_mul, h0] at hI
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero] at hI
  exact (hI.trans (add_le_add le_rfl hR)).trans (by
    have h := Real.add_one_le_exp (v * s ^ 2 / (2 * (1 - b * s)))
    simpa only [mgf, add_comm] using h)

/-- Independent rows have one MGF bound with the sum of their variance scales. -/
theorem independent_sum_mgf {m : ℕ} {Y : Fin m → Ω → ℝ}
    (hind : iIndepFun Y μ) (hY : ∀ j, Measurable (Y j))
    {v : Fin m → ℝ} {b s : ℝ}
    (hI : ∀ j, Integrable (fun x => exp (s * Y j x)) μ)
    (hM : ∀ j, mgf (Y j) μ s ≤ exp (v j * s ^ 2 / (2 * (1 - b * s)))) :
    Integrable (fun x => exp (s * ∑ j, Y j x)) μ ∧
    mgf (fun x => ∑ j, Y j x) μ s ≤
      exp ((∑ j, v j) * s ^ 2 / (2 * (1 - b * s))) := by
  have hfun : (fun x => ∑ j, Y j x) = ∑ j ∈ Finset.univ, Y j := by
    funext x; simp only [Finset.sum_apply]
  refine ⟨?_, ?_⟩
  · simpa only [Finset.sum_apply] using
      (hind.integrable_exp_mul_sum (s := Finset.univ) hY (fun j _ => hI j))
  rw [hfun]
  rw [hind.mgf_sum hY]
  calc ∏ j, mgf (Y j) μ s ≤ ∏ j, exp (v j * s ^ 2 / (2 * (1 - b * s))) :=
      Finset.prod_le_prod₀ (fun j _ => (mgf_pos (hI j)).le) (fun j _ => hM j)
    _ = _ := by rw [← Real.exp_sum]; congr 1; rw [← Finset.sum_div, ← Finset.sum_mul]

#print axioms factorial_mgf
#print axioms independent_sum_mgf
end BstLean.Part216
