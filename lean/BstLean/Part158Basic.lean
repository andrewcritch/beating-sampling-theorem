import BstLean.Part158Defs

/-!
# Part 158 (file `Basic`): bounds and measurability of the objects of `Part158Defs`

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)

variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι]
  {F : X → (ι → ℝ) → ℝ} {dF : X → (ι → ℝ) → ι → ℝ} {a b C : ℝ}

omit [Fintype ι] in
lemma measurable_pt (c s : ℝ) :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) => c • p.1 + s • p.2) := by fun_prop

lemma Fam.mF3 (h : Fam F dF a b C) (c s : ℝ) :
    Measurable (fun p : (X × (ι → ℝ)) × (ι → ℝ) => F p.1.1 (c • p.1.2 + s • p.2)) :=
  h.mF.comp ((measurable_fst.comp measurable_fst).prodMk
    (((measurable_snd.comp measurable_fst).const_smul c).add (measurable_snd.const_smul s)))

lemma Fam.mdF3 (h : Fam F dF a b C) (c s : ℝ) (k : ι) :
    Measurable (fun p : (X × (ι → ℝ)) × (ι → ℝ) => dF p.1.1 (c • p.1.2 + s • p.2) k) :=
  (measurable_pi_apply k).comp (h.mdF.comp ((measurable_fst.comp measurable_fst).prodMk
    (((measurable_snd.comp measurable_fst).const_smul c).add (measurable_snd.const_smul s))))

lemma Fam.mFx (h : Fam F dF a b C) (x : X) : Measurable (F x) :=
  h.mF.comp measurable_prodMk_left

lemma Fam.mdFx (h : Fam F dF a b C) (x : X) (k : ι) : Measurable (fun ξ => dF x ξ k) :=
  (measurable_pi_apply k).comp (h.mdF.comp measurable_prodMk_left)

lemma Fam.C_nonneg [Nonempty ι] [Nonempty X] (h : Fam F dF a b C) : 0 ≤ C :=
  (abs_nonneg _).trans (h.hC (Classical.arbitrary X) 0 (Classical.arbitrary ι))

lemma Fam.abs_le (h : Fam F dF a b C) (x : X) (ξ : ι → ℝ) : |F x ξ| ≤ b := by
  rw [abs_of_pos (lt_of_lt_of_le h.ha (h.lo x ξ))]; exact h.hi x ξ

lemma Fam.integrable_F (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) :
    Integrable (fun ξ' => F x (c • ξ + s • ξ')) (stdGauss ι) :=
  Integrable.of_bound ((h.mFx x).comp (by fun_prop)).aestronglyMeasurable b
    (Filter.Eventually.of_forall fun ξ' => by rw [Real.norm_eq_abs]; exact h.abs_le _ _)

lemma Fam.integrable_dF (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) (k : ι) :
    Integrable (fun ξ' => dF x (c • ξ + s • ξ') k) (stdGauss ι) :=
  Integrable.of_bound ((h.mdFx x k).comp (by fun_prop)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ξ' => by rw [Real.norm_eq_abs]; exact h.hC _ _ _)

lemma Fam.U_lo (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) : a ≤ U F c s x ξ := by
  have := integral_mono (integrable_const a) (h.integrable_F c s x ξ) (fun ξ' => h.lo x _)
  simpa [U] using this

lemma Fam.U_hi (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) : U F c s x ξ ≤ b := by
  have := integral_mono (h.integrable_F c s x ξ) (integrable_const b) (fun ξ' => h.hi x _)
  simpa [U] using this

lemma Fam.U_pos (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) : 0 < U F c s x ξ :=
  lt_of_lt_of_le h.ha (h.U_lo c s x ξ)

lemma Fam.Abar_le (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) (k : ι) :
    |Abar dF c s x ξ k| ≤ C := by
  unfold Abar
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_dF c s x ξ k).abs (integrable_const C)
    (fun ξ' => h.hC x _ k)
  simpa using this

lemma Fam.wv_le (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) (k : ι) :
    |wv F dF c s x ξ k| ≤ C / a := by
  unfold wv
  rw [abs_div, abs_of_pos (h.U_pos c s x ξ)]
  have h1 := h.Abar_le c s x ξ k
  have hC : 0 ≤ C := (abs_nonneg _).trans h1
  exact div_le_div₀ hC h1 h.ha (h.U_lo c s x ξ)

lemma Fam.log_U_le (h : Fam F dF a b C) (c s : ℝ) (x : X) (ξ : ι → ℝ) :
    |log (U F c s x ξ)| ≤ |log a| + |log b| := by
  have h1 : log a ≤ log (U F c s x ξ) := Real.log_le_log h.ha (h.U_lo c s x ξ)
  have h2 : log (U F c s x ξ) ≤ log b := Real.log_le_log (h.U_pos c s x ξ) (h.U_hi c s x ξ)
  rw [_root_.abs_le]
  constructor
  · have := neg_abs_le (log a); have := abs_nonneg (log b); linarith
  · have := le_abs_self (log b); have := abs_nonneg (log a); linarith

lemma Fam.measurable_U (h : Fam F dF a b C) (c s : ℝ) :
    Measurable (fun p : X × (ι → ℝ) => U F c s p.1 p.2) :=
  ((h.mF3 c s).stronglyMeasurable.integral_prod_right' (ν := stdGauss ι)).measurable

lemma Fam.measurable_Abar (h : Fam F dF a b C) (c s : ℝ) (k : ι) :
    Measurable (fun p : X × (ι → ℝ) => Abar dF c s p.1 p.2 k) :=
  ((h.mdF3 c s k).stronglyMeasurable.integral_prod_right' (ν := stdGauss ι)).measurable

lemma Fam.measurable_wv (h : Fam F dF a b C) (c s : ℝ) (k : ι) :
    Measurable (fun p : X × (ι → ℝ) => wv F dF c s p.1 p.2 k) :=
  (h.measurable_Abar c s k).div (h.measurable_U c s)

lemma Fam.measurable_T (h : Fam F dF a b C) (μ : Measure X) [SFinite μ] (L c s : ℝ) :
    Measurable (T μ L F c s) := by
  have h1 : Measurable (fun p : (ι → ℝ) × X => log (U F c s p.2 p.1)) :=
    ((h.measurable_U c s).comp measurable_swap).log
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.const_mul _

lemma Fam.measurable_Vv (h : Fam F dF a b C) (μ : Measure X) [SFinite μ] (L c s : ℝ) (k : ι) :
    Measurable (fun ξ => Vv μ L F dF c s ξ k) := by
  have h1 : Measurable (fun p : (ι → ℝ) × X => wv F dF c s p.2 p.1 k) :=
    (h.measurable_wv c s k).comp measurable_swap
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.const_mul _

lemma Fam.integrable_logU (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (c s : ℝ)
    (ξ : ι → ℝ) : Integrable (fun x => log (U F c s x ξ)) μ :=
  Integrable.of_bound ((h.measurable_U c s).comp measurable_prodMk_right).log.aestronglyMeasurable
    (|log a| + |log b|) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact h.log_U_le c s x ξ)

lemma Fam.integrable_wv (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (c s : ℝ)
    (ξ : ι → ℝ) (k : ι) : Integrable (fun x => wv F dF c s x ξ k) μ :=
  Integrable.of_bound ((h.measurable_wv c s k).comp measurable_prodMk_right).aestronglyMeasurable
    (C / a) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact h.wv_le c s x ξ k)

lemma Fam.T_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L c s : ℝ)
    (ξ : ι → ℝ) : |T μ L F c s ξ| ≤ |L⁻¹| * ((|log a| + |log b|) * μ.real Set.univ) := by
  unfold T
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_logU μ c s ξ).abs (integrable_const (|log a| + |log b|))
    (fun x => h.log_U_le c s x ξ)
  simpa [mul_comm] using this

lemma Fam.Vv_le (h : Fam F dF a b C) (μ : Measure X) [IsFiniteMeasure μ] (L c s : ℝ)
    (ξ : ι → ℝ) (k : ι) : |Vv μ L F dF c s ξ k| ≤ |L⁻¹| * (C / a * μ.real Set.univ) := by
  unfold Vv
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_integral_le_integral_abs).trans ?_
  have := integral_mono (h.integrable_wv μ c s ξ k).abs (integrable_const (C / a))
    (fun x => h.wv_le c s x ξ k)
  simpa [mul_comm] using this

end BstLean.Part158
