import BstLean.Part218PairMoments
import BstLean.Part56PropD_Polar

/-! Gaussian radius independence transfers homogeneous functions to the input sphere. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137
open BstLean.Part53 BstLean.Part214

theorem sphere_gaussian_direction {N : ℕ} (hN : 1 ≤ N) :
    Measure.map (unitF53 (ι := Fin N)) (stdGauss (Fin N)) = uniformSphere N := by
  ext s hs
  rw [Measure.map_apply measurable_unitF hs, ← lintegral_indicator_one hs,
    BstLean.Part56.uniformSphere_lintegral_gauss N hN _ (measurable_one.indicator hs),
    ← lintegral_indicator_one (measurable_unitF hs)]
  rfl

/-- The radial factor is exact for every measurable homogeneous function of even degree. -/
theorem gaussian_homogeneous {N : ℕ} (hN : 1 ≤ N) (k : ℕ) {f : (Fin N → ℝ) → ℝ}
    (mf : Measurable f) (hf : ∀ a : ℝ, 0 ≤ a → ∀ x, f (a • x) = a ^ (2 * k) * f x) :
    (∫ x, f x ∂stdGauss (Fin N)) = BstLean.Part36.rhoD N k * ∫ u, f u ∂uniformSphere N := by
  have hm : Measurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => radF53 p.2 • unitF53 p.1) :=
    (measurable_radF.comp measurable_snd).smul (measurable_unitF.comp measurable_fst)
  rw [← BstLean.Part162.polar_swap_map (d := N), integral_map hm.aemeasurable mf.aestronglyMeasurable]
  have hrad (x : Fin N → ℝ) : 0 ≤ radF53 x := sqrt_nonneg _
  change (∫ p : (Fin N → ℝ) × (Fin N → ℝ), f (radF53 p.2 • unitF53 p.1)
    ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) = _
  simp_rw [hf _ (hrad _)]
  have he : ∀ x : Fin N → ℝ, radF53 x ^ (2 * k) = normSq x ^ k := by
    intro x
    rw [pow_mul, BstLean.Part162.radF_sq]
    rfl
  simp_rw [he]
  have hp := integral_prod_mul (μ := stdGauss (Fin N)) (ν := stdGauss (Fin N))
    (fun x => f (unitF53 x)) (fun y => normSq y ^ k)
  have hswap : (fun p : (Fin N → ℝ) × (Fin N → ℝ) => normSq p.2 ^ k * f (unitF53 p.1)) =
      fun p => f (unitF53 p.1) * normSq p.2 ^ k := by funext p; ring
  rw [hswap, hp, gaussian_normSq_pow]
  have hu := integral_map (μ := stdGauss (Fin N)) measurable_unitF.aemeasurable mf.aestronglyMeasurable
  rw [sphere_gaussian_direction hN] at hu
  rw [← hu]
  ring

lemma dotp_smul_first {N : ℕ} (a : ℝ) (x y : Fin N → ℝ) : dotp (a • x) y = a * dotp x y := by
  unfold dotp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_assoc]

/-- This supplies the actual first-layer two-coordinate sphere kernel. -/
theorem sphere_relu_pair {N : ℕ} (hN : 1 ≤ N) (x y : Fin N → ℝ) :
    (∫ u, relu (dotp u x) * relu (dotp u y) ∂uniformSphere N) = kernelPhi x y / (2 * N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have mf : Measurable (fun u => relu (dotp u x) * relu (dotp u y)) := by
    unfold dotp relu; fun_prop
  have hh := gaussian_homogeneous hN 1 mf (by
    intro a ha u
    rw [dotp_smul_first, dotp_smul_first, relu_mul_of_nonneg ha, relu_mul_of_nonneg ha]
    ring)
  have hg := (rowPair137 (v := 1) (by norm_num) x y).2.1
  simp only [sqrt_one, one_smul, one_mul] at hg
  change (∫ u, relu (dotp u x) * relu (dotp u y) ∂stdGauss (Fin N)) = kernelPhi x y / 2 at hg
  rw [hg] at hh
  simp [BstLean.Part36.rhoD] at hh
  apply (eq_div_iff (by positivity : (2 : ℝ) * N ≠ 0)).mpr
  linarith

end BstLean.Part218
#print axioms BstLean.Part218.gaussian_homogeneous
#print axioms BstLean.Part218.sphere_relu_pair
