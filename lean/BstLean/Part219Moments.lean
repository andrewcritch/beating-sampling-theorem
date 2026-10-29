import BstLean.Part219Norm
import BstLean.Part212Latitude
import BstLean.Part215SharpRadius

/-! Inverse-radius and Gaussian-radius bounds in the input norm notation. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)
open BstLean.Part150 (thetaC)

lemma norm_le_of_moment {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {p : ℕ} (hp : 0 < p) (hm : AEStronglyMeasurable f μ)
    (hf : ∀ x, 0 ≤ f x) {B : ℝ} (hB : 0 ≤ B)
    (h : (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤ ENNReal.ofReal (B ^ p)) :
    eLpNorm f p μ ≤ ENNReal.ofReal B := by
  apply (ENNReal.rpow_le_rpow_iff (by exact_mod_cast hp : (0 : ℝ) < p)).mp
  rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast, eLpNorm_nat_pow (by omega) hm,
    ← ENNReal.ofReal_pow hB]
  simpa only [abs_of_nonneg (hf _)] using h

lemma radial_norm {n j : ℕ} (hj : 1 ≤ j) (hn : 2 * j + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    eLpNorm (radial c τ) (2 * j) (stdGauss (Fin n)) ≤
      ENNReal.ofReal (√(radiusCoefficient n j (thetaC c τ) / n)) := by
  have hR : 0 ≤ radiusCoefficient n j (thetaC c τ) / n := by
    rw [radiusCoefficient_identity hn c hτ]
    have hnR : 2 * (j : ℝ) + 2 < n := by exact_mod_cast hn
    exact div_nonneg (sq_nonneg _) (add_nonneg (normSq_nonneg _)
      (mul_nonneg (by linarith) (sq_nonneg _)))
  have he (x : Fin n → ℝ) : radial c τ x ^ (2 * j) =
      (τ ^ 2 / normSq (c + τ • x)) ^ j := by
    rw [pow_mul, radial, div_pow, nrm_sq]
  have hb : (√(radiusCoefficient n j (thetaC c τ) / n)) ^ (2 * j) =
      (radiusCoefficient n j (thetaC c τ) / n) ^ j := by rw [pow_mul, sq_sqrt hR]
  have hh := BstLean.Part212.inverseLatitude_moment hj hn c hτ
  have h := norm_le_of_moment (μ := stdGauss (Fin n)) (p := 2 * j) (by omega)
    (measurable_radial c τ).aestronglyMeasurable (radial_nonneg c hτ.le)
    (sqrt_nonneg (radiusCoefficient n j (thetaC c τ) / n)) (by
      simp only [he, hb]
      exact hh)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

noncomputable def latitudeEnvelope {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (x : Fin n → ℝ) : ℝ := τ ^ 2 / normSq (c + τ • x) * nrm x

lemma measurable_latitudeEnvelope {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (latitudeEnvelope c τ) :=
  (measurable_const.div ((cont_ns c τ).measurable)).mul BstLean.Part130.measurable_normSq.sqrt

lemma latitudeEnvelope_nonneg {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (x) :
    0 ≤ latitudeEnvelope c τ x :=
  mul_nonneg (div_nonneg (sq_nonneg _) (normSq_nonneg _)) (nrm_nonneg _)

/-- Holder uses inverse moment 4k and the Gaussian radial moment 4k. -/
theorem latitudeEnvelope_norm {n k : ℕ} (hk : 1 ≤ k) (hn : 8 * k + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    eLpNorm (latitudeEnvelope c τ) (2 * k) (stdGauss (Fin n)) ≤
      ENNReal.ofReal (radiusCoefficient n (4 * k) (thetaC c τ) / n *
        √((n : ℝ) + 4 * k - 1)) := by
  let A := radiusCoefficient n (4 * k) (thetaC c τ) / n
  let B := (n : ℝ) + 4 * k - 1
  have hnR : 8 * (k : ℝ) + 2 < n := by exact_mod_cast hn
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : 0 ≤ A := by
    dsimp [A]
    rw [radiusCoefficient_identity (by omega) c hτ]
    exact div_nonneg (sq_nonneg _) (add_nonneg (normSq_nonneg _)
      (mul_nonneg (by push_cast; linarith) (sq_nonneg _)))
  have hB : 0 ≤ B := by dsimp [B]; linarith
  let f := fun x : Fin n → ℝ => ENNReal.ofReal ((τ ^ 2 / normSq (c + τ • x)) ^ (2 * k))
  let g := fun x : Fin n → ℝ => ENNReal.ofReal (nrm x ^ (2 * k))
  have hf : Measurable f :=
    ((measurable_const.div (cont_ns c τ).measurable).pow_const _).ennreal_ofReal
  have hg : Measurable g := (BstLean.Part130.measurable_normSq.sqrt.pow_const _).ennreal_ofReal
  have hfi : (∫⁻ x, f x ^ (2 : ℝ) ∂stdGauss (Fin n)) ≤ ENNReal.ofReal (A ^ (4 * k)) := by
    simp only [f, ENNReal.rpow_two, ← ENNReal.ofReal_pow
      (pow_nonneg (div_nonneg (sq_nonneg τ) (normSq_nonneg _)) _), ← pow_mul]
    simpa only [show 2 * k * 2 = 4 * k by omega,
      BstLean.Part212.inverseLatitudeCoefficient, radiusCoefficient, A] using
      BstLean.Part212.inverseLatitude_moment (j := 4 * k) (by omega) (by omega) c hτ
  have hgi : (∫⁻ x, g x ^ (2 : ℝ) ∂stdGauss (Fin n)) ≤ ENNReal.ofReal (B ^ (2 * k)) := by
    simp only [g, ENNReal.rpow_two, ← ENNReal.ofReal_pow (pow_nonneg (nrm_nonneg _) _),
      ← pow_mul, show 2 * k * 2 = 2 * (2 * k) by omega]
    change (∫⁻ x, ENNReal.ofReal (BstLean.Part53.radF53 x ^ (2 * (2 * k)))
      ∂stdGauss (Fin n)) ≤ _
    rw [BstLean.Part212.radius_even_lintegral n (2 * k) (by omega)]
    apply ENNReal.ofReal_le_ofReal
    refine (BstLean.Part212.radialProduct_upper n (2 * k) (by omega)).trans ?_
    apply pow_le_pow_left₀ (by push_cast; linarith) _ (2 * k)
    dsimp [B]
    push_cast
    linarith
  have hroot (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
      ENNReal.ofReal (x ^ (2 * j)) ^ (1 / 2 : ℝ) = ENNReal.ofReal (x ^ j) := by
    rw [show 2 * j = j * 2 by omega, pow_mul, ENNReal.ofReal_pow (pow_nonneg hx j),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (stdGauss (Fin n))
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    hf.aemeasurable hg.aemeasurable
  have hi : (∫⁻ x, ENNReal.ofReal (latitudeEnvelope c τ x ^ (2 * k))
      ∂stdGauss (Fin n)) ≤ ENNReal.ofReal ((A * √B) ^ (2 * k)) := by
    have he : (fun x => ENNReal.ofReal (latitudeEnvelope c τ x ^ (2 * k))) = f * g := by
      funext x
      rw [latitudeEnvelope, mul_pow, ENNReal.ofReal_mul (pow_nonneg
        (div_nonneg (sq_nonneg _) (normSq_nonneg _)) _)]
      rfl
    rw [he]
    refine hh.trans ((mul_le_mul' (ENNReal.rpow_le_rpow hfi (by norm_num))
      (ENNReal.rpow_le_rpow hgi (by norm_num))).trans_eq ?_)
    rw [show 4 * k = 2 * (2 * k) by omega, hroot A hA, hroot B hB,
      ← ENNReal.ofReal_mul (pow_nonneg hA _), mul_pow, pow_mul (√B), sq_sqrt hB]
  have h := norm_le_of_moment (p := 2 * k) (by omega)
    (measurable_latitudeEnvelope c τ).aestronglyMeasurable
    (latitudeEnvelope_nonneg c τ) (mul_nonneg hA (sqrt_nonneg B)) hi
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

#print axioms radial_norm
#print axioms latitudeEnvelope_norm
end BstLean.Part219
