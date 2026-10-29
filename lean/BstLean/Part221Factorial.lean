import BstLean.Part216ExponentialMoment
import BstLean.Part217Moment

/-! The finite factorial alternative for shifted-tail moments. -/
namespace BstLean.Part221
open MeasureTheory Real Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exponential_tail_moment_scaled {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ0 : ∀ x, 0 ≤ Z x) {t : ℝ} (ht : 0 < t)
    (htail : ∀ v : ℝ, 0 < v → μ.real {x | v < Z x} ≤ exp (-t * v)) (k : ℕ) :
    (∫⁻ x, ENNReal.ofReal (Z x ^ k) ∂μ) ≤ ENNReal.ofReal ((k.factorial : ℝ) / t ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hscaled : ∀ u : ℝ, 0 < u → μ.real {x | u < t * Z x} ≤ 1 * exp (-u) := by
    intro u hu
    have he : {x | u < t * Z x} = {x | u / t < Z x} := by
      ext x
      change u < t * Z x ↔ u / t < Z x
      rw [div_lt_iff₀ ht, mul_comm (Z x) t]
    rw [he]
    have h := htail (u / t) (div_pos hu ht)
    have hv : -t * (u / t) = -u := by field_simp
    simpa only [hv, one_mul] using h
  have h := BstLean.Part216.exponential_tail_moment (hZ.const_mul t)
    (fun x => mul_nonneg ht.le (hZ0 x)) zero_le_one hscaled k hk
  have he (x : Ω) : Z x ^ k = (1 / t) ^ k * (t * Z x) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  simp_rw [he, ENNReal.ofReal_mul (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 / t) _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [div_pow, div_eq_mul_inv, mul_comm]

noncomputable def factorialMoment (ell : ℕ) (a t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (ell + 1), a ^ (ell - k) *
    (ell.choose k : ℝ) * ((k.factorial : ℝ) / t ^ k)

theorem shifted_tail_factorial {L : Ω → ℝ} (hL : Measurable L)
    (hL0 : ∀ x, 0 ≤ L x) {a t c : ℝ} (ha : 0 < a) (ht : 0 < t) (hc : 0 ≤ c)
    (htail : ∀ v : ℝ, 0 < v → μ.real {x | a + v < L x} ≤
      exp (-t * v - c * v ^ 2 / 2)) (ell : ℕ) :
    (∫⁻ x, ENNReal.ofReal (L x ^ ell) ∂μ) ≤ ENNReal.ofReal (factorialMoment ell a t) := by
  let Z : Ω → ℝ := fun x => max (L x - a) 0
  have hZ : Measurable Z := (hL.sub_const a).max measurable_const
  have hZ0 : ∀ x, 0 ≤ Z x := fun _ => le_max_right _ _
  have hZtail : ∀ v : ℝ, 0 < v → μ.real {x | v < Z x} ≤ exp (-t * v) := by
    intro v hv
    have he : {x | v < Z x} = {x | a + v < L x} := by
      ext x
      dsimp [Z]; rw [lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; left; linarith
    rw [he]
    refine (htail v hv).trans (exp_le_exp.mpr ?_)
    nlinarith [mul_nonneg hc (sq_nonneg v)]
  have hpt (x : Ω) : L x ^ ell ≤ (a + Z x) ^ ell := by
    apply pow_le_pow_left₀ (hL0 x)
    have := le_max_left (L x - a) 0
    dsimp [Z]; linarith
  have hsum (x : Ω) : (a + Z x) ^ ell =
      ∑ k ∈ Finset.range (ell + 1), (a ^ (ell - k) * (ell.choose k : ℝ)) * Z x ^ k := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc (∫⁻ x, ENNReal.ofReal (L x ^ ell) ∂μ)
      ≤ ∫⁻ x, ENNReal.ofReal ((a + Z x) ^ ell) ∂μ :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ∑ k ∈ Finset.range (ell + 1), ENNReal.ofReal (a ^ (ell - k) * (ell.choose k : ℝ)) *
        (∫⁻ x, ENNReal.ofReal (Z x ^ k) ∂μ) := by
      have he (x : Ω) : ENNReal.ofReal ((a + Z x) ^ ell) =
          ∑ k ∈ Finset.range (ell + 1), ENNReal.ofReal (a ^ (ell - k) * (ell.choose k : ℝ)) *
            ENNReal.ofReal (Z x ^ k) := by
        rw [hsum x, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        exact Finset.sum_congr rfl fun k _ => ENNReal.ofReal_mul (by positivity)
      simp_rw [he]
      rw [lintegral_finsetSum]
      · simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      · intro k hk
        exact measurable_const.mul (ENNReal.measurable_ofReal.comp (hZ.pow_const k))
    _ ≤ ∑ k ∈ Finset.range (ell + 1), ENNReal.ofReal (a ^ (ell - k) * (ell.choose k : ℝ)) *
        ENNReal.ofReal ((k.factorial : ℝ) / t ^ k) := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul' le_rfl
        (exponential_tail_moment_scaled hZ hZ0 ht hZtail k)
    _ = ENNReal.ofReal (factorialMoment ell a t) := by
      unfold factorialMoment
      rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
      apply Finset.sum_congr rfl
      intro k hk
      exact (ENNReal.ofReal_mul (by positivity : 0 ≤ a ^ (ell - k) * (ell.choose k : ℝ))).symm

theorem shifted_tail_factorial_integrable {L : Ω → ℝ} (hL : Measurable L)
    (hL0 : ∀ x, 0 ≤ L x) {a t c : ℝ} (ha : 0 < a) (ht : 0 < t) (hc : 0 ≤ c)
    (htail : ∀ v : ℝ, 0 < v → μ.real {x | a + v < L x} ≤
      exp (-t * v - c * v ^ 2 / 2)) (ell : ℕ) :
    Integrable (fun x => L x ^ ell) μ ∧
      (∫ x, L x ^ ell ∂μ) ≤ factorialMoment ell a t := by
  have hb := shifted_tail_factorial hL hL0 ha ht hc htail ell
  have hi : Integrable (fun x => L x ^ ell) μ :=
    (lintegral_ofReal_ne_top_iff_integrable (hL.pow_const _).aestronglyMeasurable
      (ae_of_all _ fun x => pow_nonneg (hL0 x) _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun x => pow_nonneg (hL0 x) _)] at hb
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hb
  unfold factorialMoment
  exact Finset.sum_nonneg fun k _ => by positivity

end BstLean.Part221
