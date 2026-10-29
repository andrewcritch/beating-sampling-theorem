import BstLean.Part213Partition
import BstLean.Part213Norm
import BstLean.Part202Moment

/-! Top-order moments supply all lower row orders. The order-sixteen RA
factors follow on the complete row product, before any event restriction. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsProbabilityMeasure ρ]

lemma lower_power_integrable {f : X → ℝ} (hf : Measurable f) {K k : ℕ}
    (hk : k ≤ K) (hi : Integrable (fun x => |f x| ^ K) ρ) :
    Integrable (fun x => f x ^ k) ρ := by
  refine ((integrable_const (1 : ℝ)).add hi).mono'
    (hf.pow_const k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  change |f x| ^ k ≤ 1 + |f x| ^ K
  by_cases h : |f x| ≤ 1
  · have h1 := pow_le_one₀ (abs_nonneg (f x)) h (n := k)
    linarith [pow_nonneg (abs_nonneg (f x)) K]
  · have h1 := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge h)) hk
    linarith

/-- One top-order bound supplies each lower absolute moment. -/
lemma lower_moment_bound {f : X → ℝ} (hf : Measurable f) {K k : ℕ}
    (hK : K ≠ 0) (hk : k ≤ K) (hi : Integrable (fun x => |f x| ^ K) ρ)
    {A : ℝ} (hA : 0 ≤ A) (hM : ∫ x, |f x| ^ K ∂ρ ≤ A ^ K) :
    ∫ x, |f x| ^ k ∂ρ ≤ A ^ k := by
  refine (BstLean.Part202.moment_interpolation hf hK hk hi).trans ?_
  have h := Real.rpow_le_rpow
    (integral_nonneg fun x => pow_nonneg (abs_nonneg _) K) hM
    (show 0 ≤ (k : ℝ) / K by positivity)
  simpa only [BstLean.Part202.pow_rpow_ratio hA k K hK] using h

/-- Centring a nonnegative row costs at most a factor two in its norm. -/
theorem nonnegative_centring {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {K : ℕ} (hK : 1 ≤ K) (hi : Integrable (fun x => f x ^ K) ρ)
    {A : ℝ} (hA : 0 ≤ A) (hM : ∫ x, f x ^ K ∂ρ ≤ A ^ K) :
    ∫⁻ x, ENNReal.ofReal (|f x - ∫ y, f y ∂ρ| ^ K) ∂ρ ≤
      ENNReal.ofReal ((2 * A) ^ K) := by
  have hK0 : K ≠ 0 := by omega
  have hea : (fun x => |f x| ^ K) = fun x => f x ^ K := by
    funext x
    rw [abs_of_nonneg (hf0 x)]
  have ia : Integrable (fun x => |f x| ^ K) ρ := by rw [hea]; exact hi
  have hmean0 : 0 ≤ ∫ x, f x ∂ρ := integral_nonneg hf0
  have hmean : ∫ x, f x ∂ρ ≤ A := by
    have h := lower_moment_bound hf hK0 (show 1 ≤ K from hK) ia hA
      (by simpa only [hea] using hM)
    simpa only [pow_one, abs_of_nonneg (hf0 _)] using h
  have hF : ∫⁻ x, ENNReal.ofReal (|f x| ^ K) ∂ρ ≤ ENNReal.ofReal (A ^ K) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ia
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) K)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [hea] using hM
  have hG : ∫⁻ x, ENNReal.ofReal (|-(∫ y, f y ∂ρ)| ^ K) ∂ρ ≤ ENNReal.ofReal (A ^ K) := by
    simp only [abs_neg, abs_of_nonneg hmean0, lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hmean0 hmean K)
  have h := moment_minkowski hf (measurable_const (a := -(∫ y, f y ∂ρ)))
    hK hA hA hF hG
  simpa only [sub_eq_add_neg, ← two_mul] using h

/-- The paper row-sum factor through order sixteen follows from one top moment. -/
theorem nonnegative_rows16 {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) (hp16 : 2 * p ≤ 16)
    {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => f x ^ (2 * p)) ρ)
    {A : ℝ} (hA : 0 ≤ A) (hM : ∫ x, f x ^ (2 * p) ∂ρ ≤ A ^ (2 * p)) :
    ∫⁻ y, ENNReal.ofReal ((∑ j : Fin m, (f (y j) - ∫ x, f x ∂ρ)) ^ (2 * p))
      ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (partitionBound 1 (2 * p) * (m : ℝ) ^ p * (2 * A) ^ (2 * p)) := by
  let φ : X → ℝ := fun x => f x - ∫ y, f y ∂ρ
  have hφ : Measurable φ := hf.sub measurable_const
  have htop := nonnegative_centring hf hf0 (by omega : 1 ≤ 2 * p) hi hA hM
  have itop : Integrable (fun x => |φ x| ^ (2 * p)) ρ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hφ.abs.pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)).mp
      (ne_of_lt (htop.trans_lt ENNReal.ofReal_lt_top))
  have hreal : ∫ x, |φ x| ^ (2 * p) ∂ρ ≤ (2 * A) ^ (2 * p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal itop
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)] at htop
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htop
  have ifun : Integrable f ρ := by
    have ia : Integrable (fun x => |f x| ^ (2 * p)) ρ := by
      simpa only [abs_of_nonneg (hf0 _)] using hi
    simpa only [pow_one] using lower_power_integrable hf (show 1 ≤ 2 * p by omega) ia
  refine centred_rows_partition16 ρ hm hp16 (show 0 ≤ 2 * A by positivity)
    (fun _ => φ) (fun _ => hφ) ?_ ?_ ?_
  · intro j k hk
    exact lower_power_integrable hφ hk itop
  · intro j
    dsimp [φ]
    rw [integral_sub ifun (integrable_const _)]
    simp
  · intro j k _ hk
    exact lower_moment_bound hφ (by omega : 2 * p ≠ 0) hk itop
      (show 0 ≤ 2 * A by positivity) hreal

/-- RA16 location follows from the same majorant at orders two and sixteen. -/
theorem location_RA16_from_rows {m : ℕ} (hm : 1 ≤ m) {β : X → ℝ}
    (hβ : Measurable β) (hβ0 : ∀ x, 0 ≤ β x)
    (hi : Integrable (fun x => β x ^ 16) ρ)
    {B : (Fin m → X) → ℝ} {N A2 A16 r : ℝ}
    (hN : 0 ≤ N) (hA2 : 0 ≤ A2) (hA16 : 0 ≤ A16) (hr : 0 ≤ r)
    (hsecond : ∫ x, β x ^ 2 ∂ρ = A2 ^ 2)
    (h16 : ∫ x, β x ^ 16 ∂ρ ≤ A16 ^ 16)
    (hprice : 715 * (m : ℝ) ^ 4 * 2 ^ 8 ≤ ((m : ℝ) * r) ^ 8)
    (hpoint : ∀ y, B y ^ 16 ≤ N ^ 8 * (∑ j, β (y j) ^ 2) ^ 8) :
    ∫⁻ y, ENNReal.ofReal (B y ^ 16) ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal (N ^ 8 * (m : ℝ) ^ 8 * (A2 ^ 2 + r * A16 ^ 2) ^ 8) := by
  apply location_RA16 hβ hN hA2 hr hpoint
  simp only [Even.pow_abs (by decide : Even 8)]
  have h := nonnegative_rows16 hm (by norm_num : 1 ≤ 4) (by norm_num : 2 * 4 ≤ 16)
    (hβ.pow_const 2) (fun x => sq_nonneg (β x))
    (by simpa only [← pow_mul] using hi) (sq_nonneg A16)
    (by simpa only [← pow_mul] using h16)
  rw [hsecond, partitionBound_eight] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hh := mul_le_mul_of_nonneg_right hprice (pow_nonneg hA16 16)
  convert hh using 1 <;> ring

/-- RA16 energy follows from the same majorant at orders one and sixteen. -/
theorem energy_RA16_from_rows {m : ℕ} (hm : 1 ≤ m) {β : X → ℝ}
    (hβ : Measurable β) (hβ0 : ∀ x, 0 ≤ β x)
    (hi : Integrable (fun x => β x ^ 16) ρ)
    {B : (Fin m → X) → ℝ} {A1 A16 r : ℝ}
    (hA1 : 0 ≤ A1) (hA16 : 0 ≤ A16) (hr : 0 ≤ r)
    (hfirst : ∫ x, β x ∂ρ = A1) (h16 : ∫ x, β x ^ 16 ∂ρ ≤ A16 ^ 16)
    (hprice : 1216070380 * (m : ℝ) ^ 8 * 2 ^ 16 ≤ ((m : ℝ) * r) ^ 16)
    (hpoint : ∀ y, B y ^ 16 ≤ (∑ j, β (y j)) ^ 16) :
    ∫⁻ y, ENNReal.ofReal (B y ^ 16) ∂(Measure.pi fun _ : Fin m => ρ) ≤
      ENNReal.ofReal ((m : ℝ) ^ 16 * (A1 + r * A16) ^ 16) := by
  apply energy_RA16 hβ hβ0 hA1 hA16 hr hpoint
  simp only [Even.pow_abs (by decide : Even 16)]
  have h := nonnegative_rows16 hm (by norm_num : 1 ≤ 8) (by norm_num : 2 * 8 ≤ 16)
    hβ hβ0 hi hA16 h16
  rw [hfirst, partitionBound_sixteen] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hh := mul_le_mul_of_nonneg_right hprice (pow_nonneg hA16 16)
  convert hh using 1 <;> ring

#print axioms nonnegative_centring
#print axioms nonnegative_rows16
#print axioms location_RA16_from_rows
#print axioms energy_RA16_from_rows
end BstLean.Part213
