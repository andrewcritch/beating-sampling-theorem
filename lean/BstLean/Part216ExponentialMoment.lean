import BstLean.Part216Tail
import Mathlib.MeasureTheory.Integral.Layercake
import BstLean.Part152LM

/-! Moments obtained by integrating an analytic exponential tail. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An exponential tail gives factorial moments at every positive integer order. -/
theorem exponential_tail_moment {T : Ω → ℝ} (hT : Measurable T)
    (hT0 : ∀ x, 0 ≤ T x) {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ u : ℝ, 0 < u → μ.real {x | u < T x} ≤ C * exp (-u))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ x, ENNReal.ofReal (T x ^ k) ∂μ ≤ ENNReal.ofReal (C * (k.factorial : ℝ)) := by
  let g : ℝ → ℝ := fun u => (k : ℝ) * u ^ (k - 1)
  have hg : Continuous g := by fun_prop
  have hgn : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ g u :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
      have hu0 : 0 < u := hu
      dsimp [g]; positivity)
  have hl := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Eventually.of_forall hT0) hT.aemeasurable (fun u _ => hg.intervalIntegrable _ _) hgn
  have hprim : ∀ a : ℝ, ∫ u in (0 : ℝ)..a, g u = a ^ k := by
    intro a
    dsimp [g]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have he : k - 1 + 1 = k := by omega
    rw [he, zero_pow (by omega), sub_zero]
    push_cast
    field_simp [show (k : ℝ) ≠ 0 by exact_mod_cast (by omega : k ≠ 0)]
    rw [show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by exact_mod_cast he]
    ring
  simp only [hprim] at hl
  rw [hl]
  have hi : IntegrableOn (fun u : ℝ => u ^ ((k - 1 : ℕ) : ℝ) * exp (-1 * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by
      have := Nat.cast_nonneg (α := ℝ) (k - 1); linarith) one_pos one_pos
  have hiv : IntegrableOn (fun u : ℝ => C * exp (-u) * g u) (Ioi 0) := by
    have h := hi.const_mul (C * (k : ℝ))
    change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
    exact h.congr (Eventually.of_forall fun u => by
      simp only [rpow_natCast, rpow_one, neg_mul, one_mul, g]
      ring)
  have hval : ∫ u in Ioi (0 : ℝ), C * exp (-u) * g u = C * (k.factorial : ℝ) := by
    have he : (fun u : ℝ => C * exp (-u) * g u) =
        fun u => (C * (k : ℝ)) * (u ^ ((k - 1 : ℕ) : ℝ) * exp (-1 * u ^ (1 : ℝ))) := by
      funext u
      simp only [rpow_natCast, rpow_one, neg_mul, one_mul, g]
      ring
    rw [he, integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow one_pos (by
      have := Nat.cast_nonneg (α := ℝ) (k - 1); linarith) one_pos]
    have heq : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      exact_mod_cast (show k - 1 + 1 = k by omega)
    rw [heq]
    simp only [div_one, one_rpow, one_div, mul_one]
    rw [show k = (k - 1) + 1 by omega]
    push_cast
    rw [Gamma_nat_eq_factorial]
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hiv]
  · apply lintegral_mono_ae
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Eventually.of_forall fun u hu => ?_
    have hu0 : 0 < u := hu
    have hg0 : 0 ≤ g u := by dsimp [g]; positivity
    rw [ENNReal.ofReal_mul (mul_nonneg hC (exp_pos _).le)]
    apply mul_le_mul' _ le_rfl
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (htail u hu0)
  · apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Eventually.of_forall fun u hu => by
      have hu0 : 0 < u := hu
      dsimp [g]; positivity

#print axioms exponential_tail_moment
end BstLean.Part216
