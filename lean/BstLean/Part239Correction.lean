import BstLean.Part239Exact
import BstLean.Part213Norm
import BstLean.Part223MomentBounds

/-! The exact finite-width correction applies to the normalized independent row sum. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real
open BstLean.Part213

noncomputable def exactCorrection (p m : ℕ) : ℝ :=
  partitionPolynomial p m ^ (p : ℝ)⁻¹ / (m : ℝ)

lemma exactCorrection_nonneg (p m : ℕ) : 0 ≤ exactCorrection p m := by
  unfold exactCorrection
  exact div_nonneg (Real.rpow_nonneg (partitionPolynomial_nonneg p m) _) (Nat.cast_nonneg m)

lemma exactCorrection_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    exactCorrection p m ^ p = partitionPolynomial p m / (m : ℝ) ^ p := by
  rw [exactCorrection, div_pow,
    Real.rpow_inv_natCast_pow (partitionPolynomial_nonneg p m) hp]

/-- This is the paper's exact normalized row correction at every positive even order. -/
theorem normalized_rows_exact {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hp : 1 ≤ p)
    {B : ℝ} (hB : 0 ≤ B)
    (f : Fin m → X → ℝ) (hm : ∀ j, Measurable (f j))
    (h0 : ∀ j x, 0 ≤ f j x) (hf : ∀ j, Integrable (f j) ρ)
    (hi : ∀ j k, k ≤ 2 * p → Integrable (fun x => f j x ^ k) ρ)
    (hc : ∀ j k, k ≤ 2 * p →
      Integrable (fun x => (f j x - ∫ y, f j y ∂ρ) ^ k) ρ)
    (hM : ∀ j k, 2 ≤ k → k ≤ 2 * p → ∫ x, f j x ^ k ∂ρ ≤ B ^ k) :
    eLpNorm (fun y : Fin m → X => (m : ℝ)⁻¹ *
      ∑ j, (f j (y j) - ∫ x, f j x ∂ρ)) (2 * p : ℕ)
      (Measure.pi fun _ : Fin m => ρ) ≤ ENNReal.ofReal (exactCorrection (2 * p) m * B) := by
  have hp0 : 2 * p ≠ 0 := by omega
  have he : Even (2 * p) := ⟨p, by omega⟩
  have hsum := nonnegative_rows_exact ρ hB f hm h0 hf hi hc hM
  have hmi : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg m)
  have hmeas : Measurable (fun y : Fin m → X => (m : ℝ)⁻¹ *
      ∑ j, (f j (y j) - ∫ x, f j x ∂ρ)) :=
    (Finset.measurable_sum _ fun j _ => (hm j).comp (measurable_pi_apply j) |>.sub_const _).const_mul _
  apply moment_norm_bound hmeas hp0 (mul_nonneg (exactCorrection_nonneg _ _) hB)
  simp only [abs_mul, abs_of_nonneg hmi, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg hmi _), he.pow_abs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl hsum).trans_eq ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg hmi _), exactCorrection_pow hp0 m]
  congr 1
  rw [div_eq_mul_inv, inv_pow]
  ring

#print axioms exactCorrection_pow
#print axioms normalized_rows_exact

/-- A single highest-order source moment supplies all the lower row orders. -/
theorem iid_rows_exact {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {m p : ℕ} (hp : 1 ≤ p)
    {f : X → ℝ} {B : ℝ} (h0 : ∀ x, 0 ≤ f x) (hf : Integrable f ρ)
    (hi : ∀ k, k ≤ 2 * p → Integrable (fun x => f x ^ k) ρ)
    (hc : ∀ k, k ≤ 2 * p → Integrable (fun x => (f x - ∫ y, f y ∂ρ) ^ k) ρ)
    (hM : BstLean.Part223.MomentBound ρ (2 * p) f B) :
    eLpNorm (fun y : Fin m → X => (m : ℝ)⁻¹ * ∑ j, (f (y j) - ∫ x, f x ∂ρ))
      (2 * p : ℕ) (Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (exactCorrection (2 * p) m * B) := by
  apply normalized_rows_exact ρ hp hM.nonneg (fun _ => f) (fun _ => hM.measurable)
    (fun _ => h0) (fun _ => hf) (fun _ => hi) (fun _ => hc)
  intro _ k hk hk2p
  have hl := hM.lower (by omega : 1 ≤ k) hk2p (by simp)
  have he : ENNReal.ofReal (∫ x, f x ^ k ∂ρ) =
      ∫⁻ x, ENNReal.ofReal (|f x| ^ k) ∂ρ := by
    simp only [abs_of_nonneg (h0 _)]
    exact ofReal_integral_eq_lintegral_ofReal (hi k hk2p)
      (Filter.Eventually.of_forall fun x => pow_nonneg (h0 x) k)
  have hLm := hl.moment
  rw [← he] at hLm
  have hh := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hM.nonneg k) hLm
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun x => pow_nonneg (h0 x) k)] using hh

#print axioms iid_rows_exact
end BstLean.Part239
