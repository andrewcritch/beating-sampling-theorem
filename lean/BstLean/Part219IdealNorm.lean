import BstLean.Part219IdealPointwise
import BstLean.Part219Rotation

/-! The deterministic ideal input norm keeps the paper moment orders and secant coefficient. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (thetaC)
open BstLean.Part29 (stdGauss)

theorem idealSize_pointwise {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ q : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (hq : q ∈ Icc (0 : ℝ) (27 / 50)) {ξ : Fin n → ℝ}
    (hy : normSq (a • u + τ • ξ) ≠ 0) :
    idealSize (a • u) τ ξ ≤
      (kernelSlope q * (u ⬝ᵥ inputMean (a • u) τ)) * latitudeEnvelope (a • u) τ ξ +
        (77 / 100) * (radial (a • u) τ ξ *
          (√(radiusCoefficient n 1 (thetaC (a • u) τ) / n) +
            (u ⬝ᵥ inputMean (a • u) τ) *
              |u ⬝ᵥ standPoint (a • u) τ ξ - u ⬝ᵥ inputMean (a • u) τ| +
            |(u ⬝ᵥ inputMean (a • u) τ) ^ 2 - q|)) := by
  set c := a • u
  set x := standPoint c τ ξ
  set α := u ⬝ᵥ inputMean c τ
  have hα : 0 ≤ α := inputMean_axial_nonneg (by omega) u ha hτ
  have hk : 0 ≤ kernelSlope q := kernelSlope_nonneg q
  have hr : 0 ≤ radial c τ ξ := radial_nonneg c hτ.le ξ
  have hm : nrm (kernelSlope q • (projT x *ᵥ inputMean c τ)) =
      kernelSlope q * α * nrm (projT x *ᵥ u) := by
    rw [inputMean_axial (by omega) hu a hτ, Matrix.mulVec_smul, nrm_smul,
      nrm_smul, abs_of_nonneg hk, abs_of_nonneg hα]
    ring
  have hb := ideal_average_sharp_pointwise hn hu ha hτ hq (normSq_sphPt (by omega) _)
    (x := x)
  have ht := mul_le_mul_of_nonneg_left (latitude_tangent_envelope hu a hτ.le hy)
    (mul_nonneg hk hα)
  rw [idealSize, ideal_average_split (by omega) c τ q ξ]
  have hs := mul_le_mul_of_nonneg_left (nrm_add_le
    (kernelSlope q • (projT x *ᵥ inputMean c τ))
    (∫ z, idealRemainder q x (standPoint c τ z) ∂stdGauss (Fin n))) hr
  rw [hm] at hs
  have hh := mul_le_mul_of_nonneg_left hb hr
  rw [dotProduct_comm x u] at hh
  nlinarith

lemma norm_mul_48 {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    {F G : ℝ} (hF : 0 ≤ F)
    (hf : eLpNorm f 48 μ ≤ ENNReal.ofReal F)
    (hg : eLpNorm g 48 μ ≤ ENNReal.ofReal G) :
    eLpNorm (fun x => f x * g x) 24 μ ≤ ENNReal.ofReal (F * G) := by
  haveI : ENNReal.HolderTriple 48 48 24 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num
  have hh := eLpNorm_smul_le_mul_eLpNorm_of_pos (μ := μ) (φ := f) (f := g)
    (p := 48) (q := 48) (r := 24) (by norm_num)
  exact hh.trans ((mul_le_mul' hf hg).trans_eq (ENNReal.ofReal_mul hF).symm)

noncomputable def idealAllowance (n : ℕ) (θ q α : ℝ) : ℝ :=
  kernelSlope q * α * latitudeAllowance n 12 θ +
    (77 / 100) * √(radiusCoefficient n 24 θ / n) *
      (√(radiusCoefficient n 1 θ / n) +
        α * (BstLean.Part195.rotationConstant 24 * latitudeAllowance n 24 θ) + |α ^ 2 - q|)

/-- The ideal estimate is deterministic; the coefficient is the actual axial mean. -/
theorem ideal_norm_actual_coefficient {n : ℕ} (hn : 195 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ q : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (hq : q ∈ Icc (0 : ℝ) (27 / 50)) :
    eLpNorm (idealSize (a • u) τ) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (idealAllowance n (thetaC (a • u) τ) q (u ⬝ᵥ inputMean (a • u) τ)) := by
  let c := a • u
  let α := u ⬝ᵥ inputMean c τ
  let Z := fun x => |u ⬝ᵥ standPoint c τ x - α|
  let S := √(radiusCoefficient n 1 (thetaC c τ) / n)
  let B := |α ^ 2 - q|
  let G := BstLean.Part195.rotationConstant 24 * latitudeAllowance n 24 (thetaC c τ)
  let R := √(radiusCoefficient n 24 (thetaC c τ) / n)
  have hα : 0 ≤ α := inputMean_axial_nonneg (by omega) u ha hτ
  have hG : 0 ≤ G := mul_nonneg (BstLean.Part195.rotationConstant_nonneg _)
    (latitudeAllowance_nonneg (by omega) c hτ)
  have hS : 0 ≤ S := sqrt_nonneg _
  have hB : 0 ≤ B := abs_nonneg _
  have hmain : eLpNorm (latitudeEnvelope c τ) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (latitudeAllowance n 12 (thetaC c τ)) := by
    convert latitudeEnvelope_norm (k := 12) (by norm_num) (by omega) c hτ using 1 <;>
      norm_num [latitudeAllowance]
  have hmain' : eLpNorm (fun x => (kernelSlope q * α) * latitudeEnvelope c τ x) 24
      (stdGauss (Fin n)) ≤ ENNReal.ofReal (kernelSlope q * α * latitudeAllowance n 12 (thetaC c τ)) := by
    rw [eLpNorm_mul_nonneg _ _ _ (mul_nonneg (kernelSlope_nonneg _) hα),
      ENNReal.ofReal_mul (mul_nonneg (kernelSlope_nonneg _) hα)]
    exact mul_le_mul_right hmain _
  have hz : eLpNorm Z 48 (stdGauss (Fin n)) ≤ ENNReal.ofReal G := by
    convert latitude_centered_norm (k := 24) (by norm_num) (by omega) hu a hτ using 1 <;>
      norm_num [Z, α, c, G]
  have hs : eLpNorm (fun _ : Fin n → ℝ => S) 48 (stdGauss (Fin n)) = ENNReal.ofReal S := by
    rw [eLpNorm_const' S (by norm_num) (by norm_num)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hS]
  have hb : eLpNorm (fun _ : Fin n → ℝ => B) 48 (stdGauss (Fin n)) = ENNReal.ofReal B := by
    rw [eLpNorm_const' B (by norm_num) (by norm_num)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hB]
  have haz : eLpNorm (fun x => α * Z x) 48 (stdGauss (Fin n)) ≤ ENNReal.ofReal (α * G) := by
    rw [eLpNorm_mul_nonneg _ _ _ hα, ENNReal.ofReal_mul hα]
    exact mul_le_mul_right hz _
  have hbracket : eLpNorm (fun x => S + α * Z x + B) 48 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (S + α * G + B) := by
    have h1 := eLpNorm_add_le (μ := stdGauss (Fin n)) (p := 48)
      (f := fun _ => S) (g := fun x => α * Z x) (by norm_num)
    have h2 := eLpNorm_add_le (μ := stdGauss (Fin n)) (p := 48)
      (f := fun x => S + α * Z x) (g := fun _ => B) (by norm_num)
    have hh := h2.trans (add_le_add (h1.trans (add_le_add hs.le haz)) hb.le)
    rw [ENNReal.ofReal_add (add_nonneg hS (mul_nonneg hα hG)) hB,
      ENNReal.ofReal_add hS (mul_nonneg hα hG)]
    exact hh
  have hr : eLpNorm (radial c τ) 48 (stdGauss (Fin n)) ≤ ENNReal.ofReal R := by
    convert radial_norm (j := 24) (by norm_num) (by omega) c hτ using 1 <;> norm_num
  have hproduct := norm_mul_48 (stdGauss (Fin n)) (radial c τ)
    (fun x => S + α * Z x + B) (sqrt_nonneg _) hr hbracket
  have hrem : eLpNorm (fun x => (77 / 100) * (radial c τ x * (S + α * Z x + B))) 24
      (stdGauss (Fin n)) ≤ ENNReal.ofReal ((77 / 100) * (R * (S + α * G + B))) := by
    rw [eLpNorm_mul_nonneg _ _ _ (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_right hproduct _
  have hp : ∀ᵐ x ∂stdGauss (Fin n), |idealSize c τ x| ≤
      (kernelSlope q * α) * latitudeEnvelope c τ x +
        (77 / 100) * (radial c τ x * (S + α * Z x + B)) := by
    filter_upwards [ae_normSq_ne (by omega) c hτ.ne'] with x hx
    have hi0 : 0 ≤ idealSize c τ x :=
      mul_nonneg (radial_nonneg c hτ.le x) (nrm_nonneg _)
    rw [abs_of_nonneg hi0]
    exact idealSize_pointwise (by omega) hu ha hτ hq hx
  have hmono := eLpNorm_mono_ae_real (p := (24 : ℝ≥0∞))
    (measurable_idealSize c τ).aestronglyMeasurable hp
  have hadd := eLpNorm_add_le (μ := stdGauss (Fin n)) (p := (24 : ℝ≥0∞))
    (f := fun x => (kernelSlope q * α) * latitudeEnvelope c τ x)
    (g := fun x => (77 / 100) * (radial c τ x * (S + α * Z x + B))) (by norm_num)
  refine hmono.trans (hadd.trans ((add_le_add hmain' hrem).trans_eq ?_))
  rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (kernelSlope_nonneg _) hα)
    (latitudeAllowance_nonneg (by omega) c hτ)) (by dsimp [R, S, B]; positivity)]
  congr 1
  unfold idealAllowance
  dsimp [R, S, G, B, α, c]
  ring

#print axioms idealSize_pointwise
#print axioms ideal_norm_actual_coefficient
end BstLean.Part219
