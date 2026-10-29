import BstLean.Part184Row
import BstLean.Part151R
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Gaussian quadratic moments at every positive integer order. -/
namespace BstLean.Part202
open MeasureTheory ProbabilityTheory Real Filter Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss gaussMom)
open BstLean.Part130
open BstLean.Part151 (QR TR IR gfun)

/-- Weighted Jensen includes a zero total weight. -/
lemma weighted_pow {V : Type*} [MeasurableSpace V] {μ : Measure V}
    {D q : V → ℝ} (hD : Measurable D) (iD : Integrable D μ)
    (hD0 : ∀ v, 0 ≤ D v) (hq : Measurable q) (hq0 : ∀ v, 0 ≤ q v)
    {K : ℝ} (hK : ∀ v, q v ≤ K) {p : ℕ} (hp : 1 ≤ p) :
    (∫ v, D v * q v ∂μ) ^ p ≤
      (∫ v, D v ∂μ) ^ (p - 1) * ∫ v, D v * q v ^ p ∂μ := by
  let ν := μ.withDensity (fun v => ENNReal.ofReal (D v))
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal iD.2
  have hm : ν.real univ = ∫ v, D v ∂μ := by
    rw [measureReal_def, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal iD
        (Eventually.of_forall hD0), ENNReal.toReal_ofReal (integral_nonneg hD0)]
  have ii : ∀ f : V → ℝ, (∫ v, f v ∂ν) = ∫ v, D v * f v ∂μ := by
    intro f
    rw [integral_withDensity_eq_integral_toReal_smul
      (hD.ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hD0 _), smul_eq_mul]
  have iq : Integrable q ν := Integrable.of_bound hq.aestronglyMeasurable (max K 0)
    (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 v)]
      exact (hK v).trans (le_max_left _ _))
  have iqp : Integrable (fun v => q v ^ p) ν :=
    Integrable.of_bound (hq.pow_const p).aestronglyMeasurable ((max K 0) ^ p)
      (Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hq0 v) p)]
        exact pow_le_pow_left₀ (hq0 v) ((hK v).trans (le_max_left _ _)) p)
  have hT0 : 0 ≤ ∫ v, D v ∂μ := integral_nonneg hD0
  rcases hT0.eq_or_lt with hT | hT
  · have hν : ν = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      have hz : (ν univ).toReal = 0 := by rw [← measureReal_def, hm, ← hT]
      exact ((ENNReal.toReal_eq_zero_iff (ν univ)).mp hz).resolve_right (measure_ne_top _ _)
    have hz : ∫ v, D v * q v ∂μ = 0 := by rw [← ii q, hν]; simp
    rw [hz, zero_pow (by omega)]
    exact mul_nonneg (pow_nonneg hT0 _) (integral_nonneg fun v =>
      mul_nonneg (hD0 v) (pow_nonneg (hq0 v) _))
  · haveI : NeZero ν := ⟨by
      intro hν
      have hz : ν.real univ = 0 := by rw [hν]; simp
      rw [hm] at hz
      linarith⟩
    have hj := (convexOn_pow p).map_average_le (continuous_pow p).continuousOn
      isClosed_Ici (Eventually.of_forall fun v => Set.mem_Ici.mpr (hq0 v)) iq iqp
    rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul, hm, ii q,
      ii (fun v => q v ^ p), ← div_eq_inv_mul, ← div_eq_inv_mul] at hj
    rw [div_pow, div_le_div_iff₀ (pow_pos hT _) hT] at hj
    have he : (∫ v, D v ∂μ) ^ p =
        (∫ v, D v ∂μ) ^ (p - 1) * (∫ v, D v ∂μ) := by
      rw [← pow_succ, Nat.sub_add_cancel hp]
    rw [he] at hj
    nlinarith

/-- The weighted integral controls every integer power of the quadratic form. -/
lemma QR_pow_weighted {V : Type*} [MeasurableSpace V] {μ : Measure V}
    {d : ℕ} {a b : V → Fin d → ℝ} (ha : Measurable a) (hb : Measurable b)
    (iT : Integrable (fun v => normSq (a v - b v)) μ) {p : ℕ} (hp : 1 ≤ p)
    (z : Fin d → ℝ) :
    QR μ a b z ^ p ≤ TR μ a b ^ (p - 1) * IR p μ a b z := by
  let D : V → ℝ := fun v => normSq (a v - b v)
  let x : V → ℝ := fun v => (z ⬝ᵥ (a v - b v)) ^ 2
  let q : V → ℝ := fun v => x v / D v
  have hD : Measurable D := measurable_normSq.comp (ha.sub hb)
  have hx : Measurable x :=
    ((continuous_const.dotProduct continuous_id).measurable.comp (ha.sub hb)).pow_const 2
  have hq : Measurable q := hx.div hD
  have hq0 : ∀ v, 0 ≤ q v := fun v => div_nonneg (sq_nonneg _) (normSq_nonneg _)
  have hzero : ∀ v, D v = 0 → x v = 0 := by
    intro v h
    have hs := BstLean.Part151.dot_sq_le z (a v - b v)
    change x v ≤ normSq z * D v at hs
    rw [h, mul_zero] at hs
    exact le_antisymm hs (sq_nonneg _)
  have hqK : ∀ v, q v ≤ normSq z := by
    intro v
    rcases (normSq_nonneg (a v - b v)).eq_or_lt with h | h
    · change 0 = D v at h
      change x v / D v ≤ _
      rw [← h]
      simpa using normSq_nonneg z
    · exact (div_le_iff₀ h).mpr (BstLean.Part151.dot_sq_le _ _)
  have he : ∀ v, D v * q v = x v := by
    intro v
    by_cases h : D v = 0
    · simp [q, h, hzero v h]
    · dsimp [q]; field_simp
  have hep : ∀ v, D v * q v ^ p = gfun p (x v) (D v) := by
    intro v
    by_cases h : D v = 0
    · simp [q, gfun, h, hzero v h, zero_pow (by omega : p ≠ 0)]
    · dsimp [q, gfun]
      rw [div_pow, show D v ^ p = D v ^ (p - 1) * D v by
        rw [← pow_succ, Nat.sub_add_cancel hp]]
      field_simp
  have hw := weighted_pow hD iT (fun v => normSq_nonneg _) hq hq0 hqK hp
  simp_rw [he, hep] at hw
  exact hw

/-- The trace alone controls every Gaussian quadratic moment. -/
theorem quadratic_moment {V : Type*} [MeasurableSpace V] {μ : Measure V}
    [IsProbabilityMeasure μ] {d : ℕ} {a b : V → Fin d → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (iT : Integrable (fun v => normSq (a v - b v)) μ) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal (QR μ a b z ^ p) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (gaussMom (2 * p) * TR μ a b ^ p) := by
  have hT := BstLean.Part151.TR_nonneg μ a b
  have h := BstLean.Part151.EI_mul_le ha hb iT (by norm_num : (0 : ℝ) ≤ 1)
    hp (pow_nonneg hT (p - 1))
  simp only [Real.sqrt_one, one_smul, one_pow, mul_one] at h
  refine (lintegral_mono fun z => ENNReal.ofReal_le_ofReal
    (QR_pow_weighted ha hb iT hp z)).trans (h.trans (le_of_eq ?_))
  congr 1
  rw [show TR μ a b ^ p = TR μ a b ^ (p - 1) * TR μ a b by
    rw [← pow_succ, Nat.sub_add_cancel hp]]
  ring

end BstLean.Part202
