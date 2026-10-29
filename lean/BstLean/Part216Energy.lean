import BstLean.Part216Tail

/-! Bernstein bounds for the independent whole rows supplied by Part202. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part202

variable {V P : Type*} [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ν : Measure P} [IsProbabilityMeasure ν] {d m : ℕ}
variable {a : V → Fin d → ℝ} {ell : ℝ}

lemma row_factorial_all (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (k : ℕ) (hk : 2 ≤ k) :
    ∫ q, |rowFluct S q| ^ k ∂ν.prod (stdGauss (Fin m)) ≤
      (k.factorial : ℝ) / 2 * (2 * rowScale μ a ell ^ 2) *
        (BstLean.Part202.beta * rowScale μ a ell) ^ (k - 2) := by
  by_cases hk2 : k = 2
  · subst k
    have hv := row_variance S ha hK
    rw [← ofReal_integral_eq_lintegral_ofReal (row_square_integrable S ha hK)
      (Eventually.of_forall fun q => sq_nonneg _)] at hv
    have hr := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity : 0 ≤ 2 * ell ^ 2) covarianceTrace_nonneg)).mp hv
    convert hr using 1 <;> norm_num [rowScale_sq] <;> ring
  · have h := row_factorial_real S ha hK k (by omega)
    convert h using 1
    rw [mul_pow, show rowScale μ a ell ^ k =
      rowScale μ a ell ^ 2 * rowScale μ a ell ^ (k - 2) by
        rw [← pow_add, Nat.add_sub_of_le hk]]
    ring

/-- The retained plane is integrated inside each row before the MGF is used. -/
theorem whole_row_mgf (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {sign s : ℝ} (hsign : |sign| = 1)
    (hs : 0 ≤ s) (hbs : (BstLean.Part202.beta * rowScale μ a ell) * s < 1) :
    Integrable (fun q => exp (s * (sign * rowFluct S q))) (ν.prod (stdGauss (Fin m))) ∧
    mgf (fun q => sign * rowFluct S q) (ν.prod (stdGauss (Fin m))) s ≤
      exp ((2 * rowScale μ a ell ^ 2) * s ^ 2 /
        (2 * (1 - (BstLean.Part202.beta * rowScale μ a ell) * s))) := by
  have he : ∀ q, |sign * rowFluct S q| = |rowFluct S q| := by
    intro q; rw [abs_mul, hsign, one_mul]
  apply factorial_mgf (S.measurable_fluct.const_mul sign)
    (fun k => by simpa only [he] using row_moment_integrable S ha hK k)
    (by rw [integral_const_mul, row_centred S ha hK, mul_zero])
    (by positivity) (mul_nonneg beta_pos.le rowScale_nonneg) hs hbs
  intro k hk
  simpa only [he] using row_factorial_all S ha hK k hk

noncomputable def wholeRowSum (S : RowSplit μ ν a m ell) (N : ℕ)
    (q : Fin N → P × (Fin m → ℝ)) : ℝ := ∑ j, rowFluct S (q j)

/-- Independent complete rows give the paper total variance scale `2 N scale²`. -/
theorem whole_sum_mgf (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (N : ℕ) {sign s : ℝ} (hsign : |sign| = 1)
    (hs : 0 ≤ s) (hbs : (BstLean.Part202.beta * rowScale μ a ell) * s < 1) :
    Integrable (fun q => exp (s * (sign * wholeRowSum S N q)))
      (Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) ∧
    mgf (fun q => sign * wholeRowSum S N q)
      (Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) s ≤
      exp ((2 * N * rowScale μ a ell ^ 2) * s ^ 2 /
        (2 * (1 - (BstLean.Part202.beta * rowScale μ a ell) * s))) := by
  let ρ := ν.prod (stdGauss (Fin m))
  let R := Measure.pi fun _ : Fin N => ρ
  let Y : Fin N → (Fin N → P × (Fin m → ℝ)) → ℝ := fun j q => sign * rowFluct S (q j)
  have hY : ∀ j, Measurable (Y j) :=
    fun j => (S.measurable_fluct.comp (measurable_pi_apply j)).const_mul sign
  have hind : iIndepFun Y R := iIndepFun_pi
    (fun _ => (S.measurable_fluct.const_mul sign).aemeasurable)
  have hi : ∀ j, Integrable (fun q => exp (s * Y j q)) R := by
    intro j
    exact (measurePreserving_eval (fun _ : Fin N => ρ) j).integrable_comp_of_integrable
      (whole_row_mgf S ha hK hsign hs hbs).1
  have hm : ∀ j, mgf (Y j) R s ≤ exp ((2 * rowScale μ a ell ^ 2) * s ^ 2 /
      (2 * (1 - (BstLean.Part202.beta * rowScale μ a ell) * s))) := by
    intro j
    unfold mgf
    rw [integral_comp_eval (μ := fun _ : Fin N => ρ) (i := j)
      (((S.measurable_fluct.const_mul sign).const_mul s).exp.aestronglyMeasurable)]
    exact (whole_row_mgf S ha hK hsign hs hbs).2
  have hsum := independent_sum_mgf hind hY hi hm
  have hc : (∑ _j : Fin N, 2 * rowScale μ a ell ^ 2) =
      2 * N * rowScale μ a ell ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hc] at hsum
  simpa only [wholeRowSum, Finset.mul_sum, Y] using hsum

/-- The analytic BE tail retains independence of complete rows. -/
theorem whole_sum_tail (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (N : ℕ) (hN : 0 < N)
    (hscale : 0 < rowScale μ a ell) {τ : ℝ} (hτ : 0 ≤ τ) :
    (Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))).real
      {q | sqrt (2 * (2 * N * rowScale μ a ell ^ 2) * τ) +
        (BstLean.Part202.beta * rowScale μ a ell) * τ < |wholeRowSum S N q|} ≤ 2 * exp (-τ) :=
  bernstein_tail (by positivity) (mul_nonneg beta_pos.le rowScale_nonneg) hτ
    (fun sign hsign s hs hbs => whole_sum_mgf S ha hK N hsign hs hbs)

#print axioms row_factorial_all
#print axioms whole_row_mgf
#print axioms whole_sum_mgf
#print axioms whole_sum_tail
end BstLean.Part216
