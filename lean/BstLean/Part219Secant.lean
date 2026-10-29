import BstLean.Part219Kernel

/-! The weighted secant has the paper coefficient, including both sphere endpoints. -/
namespace BstLean.Part219
open Real Set MeasureTheory Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

lemma weighted_secant_interval {a b w : ℝ} (hab : a < b)
    (ha : -1 ≤ a) (hb : b ≤ 1) (hw : 0 ≤ w)
    (hbound : ∀ v ∈ Ioo a b, kernelSecond v * w ≤ 77 / 100) :
    |kernelSlope b - kernelSlope a| * w ≤ 77 / 100 * |b - a| := by
  obtain ⟨v, hv, hs⟩ := exists_hasDerivAt_eq_slope kernelSlope kernelSecond hab
    continuous_kernelSlope.continuousOn
    (fun v hv => kernelSlope_derivative ⟨lt_of_le_of_lt ha hv.1, lt_of_lt_of_le hv.2 hb⟩)
  have hd : kernelSlope b - kernelSlope a = kernelSecond v * (b - a) := by
    exact ((eq_div_iff (sub_ne_zero.mpr hab.ne')).mp hs).symm
  rw [hd, abs_mul, abs_of_nonneg (kernelSecond_nonneg v)]
  calc
    _ = (kernelSecond v * w) * |b - a| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound v hv) (abs_nonneg _)

/-- The paper coefficient 0.77 follows from analytic derivative bounds, not a sampled check. -/
theorem kernel_weighted_secant {r q : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) (27 / 50)) :
    |kernelSlope r - kernelSlope q| * √(1 - r ^ 2) ≤ 77 / 100 * |r - q| := by
  rcases lt_trichotomy r q with h | h | h
  · have hb := weighted_secant_interval h hr.1 (by linarith [hq.2]) (sqrt_nonneg (1 - r ^ 2))
      (fun v hv => by
        have hv' : v ∈ Ioo (-1 : ℝ) 1 :=
          ⟨lt_of_le_of_lt hr.1 hv.1, by linarith [hv.2, hq.2]⟩
        by_cases hv0 : 0 ≤ v
        · have hw : √(1 - r ^ 2) ≤ 1 := by
            apply (sqrt_le_iff).mpr
            exact ⟨zero_le_one, by nlinarith [sq_nonneg r]⟩
          exact (mul_le_mul_of_nonneg_left hw (kernelSecond_nonneg v)).trans
            (by simpa only [mul_one] using kernelSecond_central ⟨hv0, le_trans hv.2.le hq.2⟩)
        · have hw : √(1 - r ^ 2) ≤ √(1 - v ^ 2) := by
            apply sqrt_le_sqrt
            nlinarith [hv.1, not_le.mp hv0]
          exact (mul_le_mul_of_nonneg_left hw (kernelSecond_nonneg v)).trans
            (kernelSecond_weighted hv'))
    simpa only [abs_sub_comm q r, abs_sub_comm (kernelSlope q) (kernelSlope r)] using hb
  · simp [h]
  · apply weighted_secant_interval h (by linarith [hq.1]) hr.2 (sqrt_nonneg _)
    intro v hv
    have hv' : v ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by linarith [hq.1, hv.1], lt_of_lt_of_le hv.2 hr.2⟩
    have hw : √(1 - r ^ 2) ≤ √(1 - v ^ 2) := by
      apply sqrt_le_sqrt
      nlinarith [hv.1, hv.2, hq.1]
    exact (mul_le_mul_of_nonneg_left hw (kernelSecond_nonneg v)).trans
      (kernelSecond_weighted hv')

/-- The scalar secant bounds the actual projected pair remainder. -/
theorem idealRemainder_sharp {n : ℕ} {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (27 / 50))
    {x z : Fin n → ℝ} (hx : normSq x = 1) (hz : normSq z = 1) :
    nrm (idealRemainder q x z) ≤ 77 / 100 * |x ⬝ᵥ z - q| := by
  rw [idealRemainder_length q hx hz]
  have hdot : |x ⬝ᵥ z| ≤ 1 := by
    have hh := BstLean.Part153.abs_dot_le_nrm x z
    simpa only [nrm, hx, hz, sqrt_one, mul_one] using hh
  exact kernel_weighted_secant (abs_le.mp hdot) hq

#print axioms kernel_weighted_secant
#print axioms idealRemainder_sharp
end BstLean.Part219
