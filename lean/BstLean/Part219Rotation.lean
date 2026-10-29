import BstLean.Part219LatitudeBound
import BstLean.Part219Overlap

/-! The sharp rotation inequality supplies centred latitude moments. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)
open BstLean.Part150 (thetaC)

lemma moment_of_norm {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {p : ℕ} (hp : 0 < p) (hm : AEStronglyMeasurable f μ)
    (hf : ∀ x, 0 ≤ f x) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f p μ ≤ ENNReal.ofReal B) :
    Integrable (fun x => f x ^ p) μ ∧ (∫ x, f x ^ p ∂μ) ≤ B ^ p := by
  have hmem : MemLp f (p : ℝ≥0∞) μ := h.trans_lt ENNReal.ofReal_lt_top
  have hi := hmem.integrable_norm_pow (by omega : p ≠ 0)
  simp only [Real.norm_eq_abs, abs_of_nonneg (hf _)] at hi
  refine ⟨hi, ?_⟩
  have hh := pow_le_pow_left₀ lpNorm_nonneg (ENNReal.toReal_le_of_le_ofReal hB h) p
  change lpNorm f (p : ℝ≥0∞) μ ^ p ≤ B ^ p at hh
  rw [lpNorm_nat_pow (by omega) hm] at hh
  simpa only [abs_of_nonneg (hf _)] using hh

noncomputable def latitudeAllowance (n k : ℕ) (θ : ℝ) : ℝ :=
  radiusCoefficient n (4 * k) θ / n * √((n : ℝ) + 4 * k - 1)

lemma latitudeAllowance_nonneg {n k : ℕ} (hn : 8 * k + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ latitudeAllowance n k (thetaC c τ) := by
  unfold latitudeAllowance
  rw [radiusCoefficient_identity (by omega) c hτ]
  have hnR : 8 * (k : ℝ) + 2 < n := by exact_mod_cast hn
  apply mul_nonneg _ (sqrt_nonneg _)
  exact div_nonneg (sq_nonneg _) (add_nonneg (normSq_nonneg _)
    (mul_nonneg (by push_cast; linarith) (sq_nonneg _)))

theorem latitude_centered_norm {n k : ℕ} (hk : 1 ≤ k) (hn : 8 * k + 2 < n)
    {u : Fin n → ℝ} (hu : normSq u = 1) (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    eLpNorm (fun x => |u ⬝ᵥ standPoint (a • u) τ x - u ⬝ᵥ inputMean (a • u) τ|)
      (2 * k) (stdGauss (Fin n)) ≤ ENNReal.ofReal
        (BstLean.Part195.rotationConstant k * latitudeAllowance n k (thetaC (a • u) τ)) := by
  let c := a • u
  let G := latitudeAllowance n k (thetaC c τ)
  have hG : 0 ≤ G := latitudeAllowance_nonneg hn c hτ
  have he := latitudeEnvelope_norm hk hn c hτ
  have hen : eLpNorm (latitudeEnvelope c τ) ((2 * k : ℕ) : ℝ≥0∞)
      (stdGauss (Fin n)) ≤ ENNReal.ofReal G := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, G, latitudeAllowance] using he
  obtain ⟨hi, hb⟩ := moment_of_norm (by omega : 0 < 2 * k)
    (measurable_latitudeEnvelope c τ).aestronglyMeasurable (latitudeEnvelope_nonneg c τ) hG hen
  have hΓ : Integrable (fun x => (latitudeEnvelope c τ x ^ 2) ^ k)
      (stdGauss (Fin n)) := by simpa only [← pow_mul] using hi
  have hgrad : ∀ᵐ x ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun x => u ⬝ᵥ sphPt (c + τ • x)) x (Pi.single i 1)) ^ 2 ≤
        latitudeEnvelope c τ x ^ 2 := by
    filter_upwards [ae_normSq_ne (by omega) c hτ.ne'] with x hx
    exact latitude_gradient_envelope hu a hτ.le hx
  have hlip : BstLean.Part148.EuLip (fun x => u ⬝ᵥ x) 1 := by
    simpa only [nrm, hu, sqrt_one] using dot_euLip u
  have hr := BstLean.Part195.rotation_singular_dimension hk (by omega) c hτ zero_le_one hlip
    (fun x => sq_nonneg (latitudeEnvelope c τ x)) hΓ hgrad
  have hmean := dot_integral u (integrable_standPoint (by omega) c τ)
  change (∫ x, u ⬝ᵥ sphPt (c + τ • x) ∂stdGauss (Fin n)) = u ⬝ᵥ inputMean c τ at hmean
  rw [hmean] at hr
  have hC : 0 ≤ BstLean.Part195.rotationConstant k := BstLean.Part195.rotationConstant_nonneg k
  have hb' := mul_le_mul_of_nonneg_left hb (pow_nonneg hC (2 * k))
  simp only [← pow_mul] at hr
  have hbound : (∫ x, |u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ| ^ (2 * k)
      ∂stdGauss (Fin n)) ≤ (BstLean.Part195.rotationConstant k * G) ^ (2 * k) := by
    simpa only [mul_pow, standPoint] using hr.trans hb'
  have hm : Measurable (fun x => |u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ|) := by
    simpa only [Function.comp_apply, dotLinear_apply] using
      (((dotLinear u).continuous.measurable.comp (measurable_standPoint c τ)).sub_const
        (u ⬝ᵥ inputMean c τ)).abs
  have hfi : Integrable (fun x => |u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ| ^ (2 * k))
      (stdGauss (Fin n)) := by
    apply Integrable.of_bound (hm.pow_const _).aestronglyMeasurable
      ((1 + |u ⬝ᵥ inputMean c τ|) ^ (2 * k))
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((abs_sub _ _).trans (add_le_add (projection_abs_le_one (by omega) hu c τ x) le_rfl)) _
  have hlin : (∫⁻ x, ENNReal.ofReal
      (|u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ| ^ (2 * k)) ∂stdGauss (Fin n)) ≤
      ENNReal.ofReal ((BstLean.Part195.rotationConstant k * G) ^ (2 * k)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfi
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal hbound
  have h := norm_le_of_moment (by omega : 0 < 2 * k) hm.aestronglyMeasurable
    (fun x => abs_nonneg _) (mul_nonneg hC hG) hlin
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

#print axioms latitude_centered_norm
end BstLean.Part219
