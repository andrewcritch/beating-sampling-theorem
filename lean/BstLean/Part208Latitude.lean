import BstLean.Part198Radial

/-! Part 208: exact directional moments for weighted latitude integration. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part53 (unitF53 radF53 measurable_unitF)

lemma direction_dot_measurable {n : ℕ} (v : Fin n → ℝ) :
    Measurable (fun z => v ⬝ᵥ unitF53 z) := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp measurable_unitF)

theorem direction_dot_integrable {n : ℕ} (v : Fin n → ℝ) :
    Integrable (fun z => v ⬝ᵥ unitF53 z) (stdGauss (Fin n)) := by
  refine Integrable.of_bound (direction_dot_measurable v).aestronglyMeasurable
    (BstLean.Part153.nrm v)
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (BstLean.Part153.abs_dot_le_nrm v (unitF53 z)).trans ?_
  have h := BstLean.Part162.radF_unitF_le z
  have h0 := BstLean.Part153.nrm_nonneg v
  change _ ≤ _
  have he : BstLean.Part153.nrm (unitF53 z) = radF53 (unitF53 z) := rfl
  rw [he]
  nlinarith

theorem direction_dot_sq_integrable {n : ℕ} (v : Fin n → ℝ) :
    Integrable (fun z => (v ⬝ᵥ unitF53 z) ^ 2) (stdGauss (Fin n)) := by
  refine Integrable.of_bound ((direction_dot_measurable v).pow_const 2).aestronglyMeasurable
    (normSq v)
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := BstLean.Part153.abs_dot_le_nrm v (unitF53 z)
  have hr : BstLean.Part153.nrm (unitF53 z) ≤ 1 := BstLean.Part162.radF_unitF_le z
  have h1 : |v ⬝ᵥ unitF53 z| ≤ BstLean.Part153.nrm v :=
    h.trans (by nlinarith [BstLean.Part153.nrm_nonneg v])
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [sq_abs, BstLean.Part153.nrm_sq] at h2

/-- The directional first moment vanishes; the direction distribution is symmetric. -/
theorem gaussian_direction_first {n : ℕ} (v : Fin n → ℝ) :
    ∫ z, v ⬝ᵥ unitF53 z ∂stdGauss (Fin n) = 0 := by
  have he : ∀ z : Fin n → ℝ, unitF53 (-z) = -unitF53 z := by
    intro z
    ext i
    simp [unitF53, radF53]
  have h := integral_map (μ := stdGauss (Fin n)) (φ := fun z => -z)
    (by fun_prop) (f := fun z => v ⬝ᵥ unitF53 z)
    (direction_dot_measurable v).aestronglyMeasurable
  rw [BstLean.Part33.stdGauss_neg_invariant] at h
  simp_rw [he, dotProduct_neg] at h
  rw [integral_neg] at h
  linarith

/-- At a fixed latitude the transverse direction gives its exact dimension factor. -/
theorem latitude_second {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (a b : ℝ) :
    ∫ z, (a + b * (v ⬝ᵥ unitF53 z)) ^ 2 ∂stdGauss (Fin n) =
      a ^ 2 + b ^ 2 * normSq v / n := by
  have hi := direction_dot_integrable v
  have hi2 := direction_dot_sq_integrable v
  have he : ∀ z : Fin n → ℝ, (a + b * (v ⬝ᵥ unitF53 z)) ^ 2 =
      a ^ 2 + (2 * a * b) * (v ⬝ᵥ unitF53 z) + b ^ 2 * (v ⬝ᵥ unitF53 z) ^ 2 := by
    intro z; ring
  simp_rw [he]
  have hsum := integral_add ((integrable_const (a ^ 2)).add (hi.const_mul (2*a*b)))
    (hi2.const_mul (b^2))
  simp only [Pi.add_apply] at hsum
  rw [hsum,
    integral_add (integrable_const _) (hi.const_mul _), integral_const,
    integral_const_mul, integral_const_mul, gaussian_direction_first,
    BstLean.Part198.gaussian_direction_second hn v]
  simp [mul_div_assoc]

/-- The core weight can depend on latitude and radius. It is independent of the
fresh transverse direction in this disintegrated integral. -/
theorem weighted_latitude_second {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (q a b : Y → ℝ)
    (ha : Integrable (fun y => q y * a y ^ 2) μ)
    (hb : Integrable (fun y => q y * b y ^ 2) μ) :
    (∫ y, q y * (∫ z, (a y + b y * (v ⬝ᵥ unitF53 z)) ^ 2
      ∂stdGauss (Fin n)) ∂μ) =
      (∫ y, q y * a y ^ 2 ∂μ) + (∫ y, q y * b y ^ 2 ∂μ) * normSq v / n := by
  simp_rw [latitude_second hn]
  have he : ∀ y, q y * (a y ^ 2 + b y ^ 2 * normSq v / n) =
      q y * a y ^ 2 + (q y * b y ^ 2) * (normSq v / n) := by intro y; ring
  simp_rw [he]
  rw [integral_add ha (hb.mul_const _), integral_mul_const]
  ring

/-- A radial weight retains the exact transverse second moment before any
restriction that depends on the Agent matrices. -/
theorem radial_affine_second {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ)
    (q a b : ℝ → ℝ) (hq : Measurable q) (ha : Measurable a) (hb : Measurable b)
    (hi₀ : Integrable (fun z : Fin n → ℝ => q (radF53 z) * a (radF53 z) ^ 2)
      (stdGauss (Fin n)))
    (hi₁ : Integrable (fun z : Fin n → ℝ => (v ⬝ᵥ unitF53 z) *
      (2 * q (radF53 z) * a (radF53 z) * b (radF53 z))) (stdGauss (Fin n)))
    (hi₂ : Integrable (fun z : Fin n → ℝ => (v ⬝ᵥ unitF53 z) ^ 2 *
      (q (radF53 z) * b (radF53 z) ^ 2)) (stdGauss (Fin n))) :
    (∫ z, q (radF53 z) * (a (radF53 z) + b (radF53 z) *
      (v ⬝ᵥ unitF53 z)) ^ 2 ∂stdGauss (Fin n)) =
      (∫ z, q (radF53 z) * a (radF53 z) ^ 2 ∂stdGauss (Fin n)) +
      normSq v / n * ∫ z, q (radF53 z) * b (radF53 z) ^ 2 ∂stdGauss (Fin n) := by
  have he : ∀ z : Fin n → ℝ,
      q (radF53 z) * (a (radF53 z) + b (radF53 z) * (v ⬝ᵥ unitF53 z)) ^ 2 =
      q (radF53 z) * a (radF53 z) ^ 2 +
      (v ⬝ᵥ unitF53 z) * (2 * q (radF53 z) * a (radF53 z) * b (radF53 z)) +
      (v ⬝ᵥ unitF53 z) ^ 2 * (q (radF53 z) * b (radF53 z) ^ 2) := by
    intro z; ring
  simp_rw [he]
  have hsum := integral_add (hi₀.add hi₁) hi₂
  simp only [Pi.add_apply] at hsum
  rw [hsum, integral_add hi₀ hi₁,
    BstLean.Part162.polar_integral_mul (fun u => v ⬝ᵥ u)
      (fun r => 2 * q r * a r * b r) (by unfold dotProduct; fun_prop) (by fun_prop),
    BstLean.Part162.polar_integral_mul (fun u => (v ⬝ᵥ u) ^ 2)
      (fun r => q r * b r ^ 2) (by unfold dotProduct; fun_prop) (by fun_prop),
    gaussian_direction_first, BstLean.Part198.gaussian_direction_second hn v]
  ring

end BstLean.Part208
