import BstLean.Part202Plane

/-! Centred independent whole rows and the BE inputs for the next Bernstein step. -/
namespace BstLean.Part202
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part184 (rowE)

lemma positive_power_le_abs {sign x : ℝ} (hsign : |sign| ≤ 1) (k : ℕ) :
    max (sign * x) 0 ^ k ≤ |x| ^ k := by
  apply pow_le_pow_left₀ (le_max_right _ _)
  apply max_le
  · calc sign * x ≤ |sign * x| := le_abs_self _
      _ = |sign| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right hsign (abs_nonneg _)
      _ = _ := one_mul _
  · exact abs_nonneg _

section
variable {V P : Type*} [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ν : Measure P} [IsProbabilityMeasure ν] {d m : ℕ}
variable {a : V → Fin d → ℝ} {ell : ℝ}

lemma row_square_integrable (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) :
    Integrable (fun q => |rowFluct S q| ^ 2) (ν.prod (stdGauss (Fin m))) :=
  (lintegral_ofReal_ne_top_iff_integrable
    (S.measurable_fluct.abs.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun q => sq_nonneg _)).mp
        (ne_of_lt ((row_variance S ha hK).trans_lt ENNReal.ofReal_lt_top))

lemma row_integrable (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) :
    Integrable (rowFluct S) (ν.prod (stdGauss (Fin m))) := by
  refine ((integrable_const (1 : ℝ)).add (row_square_integrable S ha hK)).mono'
    S.measurable_fluct.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs]
  change |rowFluct S q| ≤ 1 + |rowFluct S q| ^ 2
  nlinarith [sq_nonneg (|rowFluct S q| - 1), sq_nonneg (|rowFluct S q|)]

/-- All absolute row moments are integrable before the exponential series is used. -/
theorem row_moment_integrable (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (k : ℕ) :
    Integrable (fun q => |rowFluct S q| ^ k) (ν.prod (stdGauss (Fin m))) := by
  by_cases hk : 3 ≤ k
  · exact (lintegral_ofReal_ne_top_iff_integrable
      (S.measurable_fluct.abs.pow_const k).aestronglyMeasurable
        (Eventually.of_forall fun q => pow_nonneg (abs_nonneg _) k)).mp
      (ne_of_lt ((row_factorial_moment S ha hK k hk).trans_lt ENNReal.ofReal_lt_top))
  · have hc : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · simp
    · simpa only [pow_one] using (row_integrable S ha hK).abs
    · exact row_square_integrable S ha hK

/-- The real integral form of the factorial row bound. -/
theorem row_factorial_real (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (k : ℕ) (hk : 3 ≤ k) :
    ∫ q, |rowFluct S q| ^ k ∂ν.prod (stdGauss (Fin m)) ≤
      (k.factorial : ℝ) * beta ^ (k - 2) * rowScale μ a ell ^ k := by
  have hb := row_factorial_moment S ha hK k hk
  rw [← ofReal_integral_eq_lintegral_ofReal (row_moment_integrable S ha hK k)
    (Eventually.of_forall fun q => pow_nonneg (abs_nonneg _) k)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg beta_pos.le _))
      (pow_nonneg rowScale_nonneg _))).mp hb

/-- A row is centred only in its fresh coordinates at fixed retained coordinates. -/
lemma row_conditionally_centred (S : RowSplit μ ν a m ell) (ξ : P) :
    ∫ η, rowFluct S (ξ, η) ∂stdGauss (Fin m) = 0 := by
  obtain ⟨Kc, hKc⟩ := S.bounded_c ξ
  obtain ⟨Kw, hKw⟩ := S.bounded_w
  have hc : Measurable (S.c ξ) :=
    S.measurable_c.comp (measurable_const.prodMk measurable_id (α := V))
  have ie : Integrable (rowE μ (S.c ξ) S.w 1) (stdGauss (Fin m)) := by
    simpa only [pow_one] using BstLean.Part184.rowE_pow_integrable hc S.measurable_w
      hKc hKw S.mean_w (sq_nonneg ell) S.covariance_w (by norm_num : (0 : ℝ) ≤ 1) 1
  change (∫ η, rowE μ (S.c ξ) S.w 1 η -
    (∫ η', rowE μ (S.c ξ) S.w 1 η' ∂stdGauss (Fin m)) ∂stdGauss (Fin m)) = 0
  rw [integral_sub (f := rowE μ (S.c ξ) S.w 1)
    (g := fun _ => ∫ η', rowE μ (S.c ξ) S.w 1 η' ∂stdGauss (Fin m))
      ie (integrable_const _)]
  simp

/-- Integrate the plane only after proving conditional centring. -/
theorem row_centred (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) :
    ∫ q, rowFluct S q ∂ν.prod (stdGauss (Fin m)) = 0 := by
  rw [integral_prod _ (row_integrable S ha hK)]
  simp_rw [row_conditionally_centred]
  simp

/-- Whole rows are independent under their product distribution. -/
theorem whole_rows_independent (S : RowSplit μ ν a m ell) (N : ℕ) :
    iIndepFun (fun i : Fin N => fun q : Fin N → P × (Fin m → ℝ) => rowFluct S (q i))
      (Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) :=
  iIndepFun_pi (fun _ => S.measurable_fluct.aemeasurable)

/-- The sum of whole-row variances supplies the paper Bernstein variance scale. -/
theorem total_row_variance (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (N : ℕ) :
    ∑ i : Fin N, ∫⁻ q : Fin N → P × (Fin m → ℝ),
      ENNReal.ofReal (|rowFluct S (q i)| ^ 2)
        ∂(Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) ≤
    ENNReal.ofReal (2 * N * rowScale μ a ell ^ 2) := by
  have hf := S.measurable_fluct.abs.pow_const 2 |>.ennreal_ofReal
  have he : ∀ i : Fin N, ∫⁻ q : Fin N → P × (Fin m → ℝ),
      ENNReal.ofReal (|rowFluct S (q i)| ^ 2)
        ∂(Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) =
      ∫⁻ p, ENNReal.ofReal (|rowFluct S p| ^ 2) ∂ν.prod (stdGauss (Fin m)) :=
    fun i => (measurePreserving_eval (fun _ : Fin N => ν.prod (stdGauss (Fin m))) i).lintegral_comp hf
  simp_rw [he]
  refine (Finset.sum_le_sum fun i _ => row_variance S ha hK).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), rowScale_sq]
  congr 1
  ring

/-- Positive-part moments at both signs supply `(k!/2) V b^(k-2)`.
The variance scale is `V = 2 N scale^2`; the Bernstein scale is `b = beta scale`. -/
theorem total_row_positive_moment (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (N k : ℕ) (hk : 3 ≤ k)
    (sign : ℝ) (hsign : |sign| ≤ 1) :
    ∑ i : Fin N, ∫⁻ q : Fin N → P × (Fin m → ℝ),
      ENNReal.ofReal (max (sign * rowFluct S (q i)) 0 ^ k)
        ∂(Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) ≤
    ENNReal.ofReal ((k.factorial : ℝ) / 2 * (2 * N * rowScale μ a ell ^ 2) *
      (beta * rowScale μ a ell) ^ (k - 2)) := by
  have hf : Measurable (fun q => ENNReal.ofReal (max (sign * rowFluct S q) 0 ^ k)) :=
    ((S.measurable_fluct.const_mul sign).max measurable_const).pow_const k |>.ennreal_ofReal
  have he : ∀ i : Fin N, ∫⁻ q : Fin N → P × (Fin m → ℝ),
      ENNReal.ofReal (max (sign * rowFluct S (q i)) 0 ^ k)
        ∂(Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) =
      ∫⁻ p, ENNReal.ofReal (max (sign * rowFluct S p) 0 ^ k) ∂ν.prod (stdGauss (Fin m)) :=
    fun i => (measurePreserving_eval (fun _ : Fin N => ν.prod (stdGauss (Fin m))) i).lintegral_comp hf
  have hrow : (∫⁻ p, ENNReal.ofReal (max (sign * rowFluct S p) 0 ^ k)
      ∂ν.prod (stdGauss (Fin m))) ≤
      ENNReal.ofReal ((k.factorial : ℝ) * beta ^ (k - 2) * rowScale μ a ell ^ k) := by
    exact (lintegral_mono (fun p : P × (Fin m → ℝ) =>
      ENNReal.ofReal_le_ofReal (positive_power_le_abs (x := rowFluct S p) hsign k))).trans
        (row_factorial_moment S ha hK k hk)
  simp_rw [he]
  refine (Finset.sum_le_sum fun _ _ => hrow).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow, show rowScale μ a ell ^ k = rowScale μ a ell ^ 2 * rowScale μ a ell ^ (k - 2) by
    rw [← pow_add, Nat.add_sub_of_le (by omega : 2 ≤ k)]]
  ring

end
end BstLean.Part202
