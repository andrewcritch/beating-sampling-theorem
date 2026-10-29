import BstLean.Part208RadiusIntegral
import BstLean.Part182SchurI
import BstLean.Part150P45b

/-! Part 208: the paper's inverse-radius mean under the actual stand-in distribution. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

theorem inverse_radius_lintegral {n : ℕ} (hn : 4 < n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ ξ, ENNReal.ofReal (1 / normSq (c + τ • ξ)) ∂stdGauss (Fin n) ≤
      ENNReal.ofReal (1 / (((n : ℝ) - 4) * τ ^ 2 + normSq c)) := by
  have hm : Measurable (Function.uncurry fun (ξ : Fin n → ℝ) (t : ℝ) =>
      ENNReal.ofReal (exp (-(t * normSq (c + τ • ξ))))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    unfold normSq
    fun_prop
  calc
    ∫⁻ ξ, ENNReal.ofReal (1 / normSq (c + τ • ξ)) ∂stdGauss (Fin n)
      ≤ ∫⁻ ξ, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(t * normSq (c + τ • ξ)))))
          ∂stdGauss (Fin n) := by
        apply lintegral_mono
        intro ξ
        dsimp only
        rcases (normSq_nonneg (c + τ • ξ)).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · exact (BstLean.Part151.lint_exp_neg hpos).ge
    _ = ∫⁻ t in Ioi (0 : ℝ), (∫⁻ ξ, ENNReal.ofReal (exp (-(t * normSq (c + τ • ξ))))
          ∂stdGauss (Fin n)) := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (radiusKernel n (τ ^ 2) (normSq c) t) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        have ht0 : 0 < t := ht
        have hi : Integrable (fun ξ : Fin n → ℝ => exp (-(t * normSq (c + τ • ξ))))
            (stdGauss (Fin n)) := by
          refine Integrable.of_bound (by unfold normSq; fun_prop) 1
            (Filter.Eventually.of_forall fun ξ => ?_)
          rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
          exact neg_nonpos.mpr (mul_nonneg ht.le (normSq_nonneg _))
        rw [← ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun ξ => (exp_pos _).le), laplace_vec_exact ht.le]
        congr 1
        unfold radiusKernel
        congr 1
        have hb : 0 < 1 + 2 * t * τ ^ 2 := by positivity
        rw [sqrt_eq_rpow, ← rpow_neg hb.le, ← rpow_natCast, ← rpow_mul hb.le]
        congr 1
        ring
    _ ≤ _ := radiusKernel_lintegral_le hn (sq_pos_of_pos hτ) (normSq_nonneg c)

/-- The noncentral mean bound holds for every centre, including zero. -/
theorem inverse_radius_mean {n : ℕ} (hn : 4 < n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n) ≤
      1 / (((n : ℝ) - 4) * τ ^ 2 + normSq c) := by
  have hi := (BstLean.Part151.inv_moment (by omega) hτ c).1
  have hl := inverse_radius_lintegral hn c hτ
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ξ => div_nonneg zero_le_one (normSq_nonneg _))] at hl
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  have hc := normSq_nonneg c
  simpa only [one_div] using (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hl

/-- The missing paper radius source, in the normalization used by Part199. -/
theorem Ew_paper {n : ℕ} (hn : 4 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ ξ, BstLean.Part182.wN c τ ξ ∂stdGauss (Fin n) ≤
      (BstLean.Part150.thetaC c τ / n) / (1 - 4 * BstLean.Part150.thetaC c τ / n) := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  have hc := normSq_nonneg c
  have hden : 0 < ((n : ℝ) - 4) * τ ^ 2 + normSq c := by positivity
  have hrho : 0 < normSq c + (n : ℝ) * τ ^ 2 := by positivity
  simp only [BstLean.Part182.wN, integral_const_mul]
  refine (mul_le_mul_of_nonneg_left (inverse_radius_mean hn c hτ) (sq_nonneg τ)).trans
    (le_of_eq ?_)
  rw [BstLean.Part150.thetaC, BstLean.Part150.rhoC_sqP]
  field_simp
  <;> ring

end BstLean.Part208
