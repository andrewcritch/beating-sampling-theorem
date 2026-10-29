import BstLean.Part212Maximum
import BstLean.Part212Radius
import BstLean.Part219Rotation
import Mathlib.Analysis.MeanInequalities

/-! A simpler latitude supplier: exact chi-square moments and AM-GM.
It avoids a dimension-dependent Chernoff threshold and tail integral. -/
namespace BstLean.BlueprintLow
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)
open BstLean.Part167 (Mx Mx_nonneg Mx_pow_le measurable_Mx)
open BstLean.Part212

theorem radialProduct_arithmetic (d k : ℕ) (hk : 1 ≤ k) :
    radialProduct d k ≤ ((d : ℝ) + k - 1) ^ k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsum (l : ℕ) : ∑ i ∈ Finset.range l, ((d : ℝ) + 2 * i) = (l : ℝ) * (d + l - 1) := by
    induction l with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hs := hsum k
  have h := Real.geom_mean_le_arith_mean (Finset.range k) (fun _ => (1 : ℝ))
    (fun i => (d : ℝ) + 2 * i) (fun _ _ => zero_le_one)
    (by simpa using hk0) (fun _ _ => by positivity)
  simp only [rpow_one, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, hs, mul_div_cancel_left₀ _ hk0.ne'] at h
  change radialProduct d k ^ ((k : ℝ)⁻¹) ≤ (d : ℝ) + k - 1 at h
  have hh := pow_le_pow_left₀ (rpow_nonneg (by unfold radialProduct; positivity) _) h k
  rwa [rpow_inv_natCast_pow (by unfold radialProduct; positivity) (by omega)] at hh

theorem maximum_even_moment {m d p : ℕ} (hm : 0 < m) (hd : 1 ≤ d) :
    (∫⁻ G : Fin m → Fin d → ℝ, ENNReal.ofReal (Mx hm G ^ (2 * p))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) ≤
      ENNReal.ofReal ((m : ℝ) * radialProduct d p) := by
  have hpt : ∀ G : Fin m → Fin d → ℝ, ENNReal.ofReal (Mx hm G ^ (2 * p)) ≤
      ∑ i, ENNReal.ofReal (radF53 (G i) ^ (2 * p)) := by
    intro G
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)]
    exact ENNReal.ofReal_le_ofReal (Mx_pow_le hm G (2 * p))
  apply (lintegral_mono hpt).trans
  have hmi : ∀ i : Fin m, Measurable (fun G : Fin m → Fin d → ℝ =>
      ENNReal.ofReal (radF53 (G i) ^ (2 * p))) := fun i =>
    ((measurable_radF.comp (measurable_pi_apply i)).pow_const _).ennreal_ofReal
  rw [lintegral_finsetSum _ (fun i _ => hmi i)]
  have hrow (i : Fin m) : (∫⁻ G : Fin m → Fin d → ℝ,
      ENNReal.ofReal (radF53 (G i) ^ (2 * p))
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) = ENNReal.ofReal (radialProduct d p) := by
    have he := (MeasureTheory.measurePreserving_eval (fun _ : Fin m => stdGauss (Fin d)) i).lintegral_comp
      ((measurable_radF.pow_const (2 * p)).ennreal_ofReal)
    simp only [Function.eval] at he
    rw [he, radius_even_lintegral d p hd]
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Order 160 of the maximum row norm, using its order 640 and the exact
radial product. The arithmetic mean is d+319, instead of d+640. -/
theorem maximum160_sharp {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d) :
    (∫⁻ G : Fin m → Fin d → ℝ, ENNReal.ofReal (Mx hm G ^ 160)
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) ≤
      ENNReal.ofReal ((m : ℝ) ^ (1 / 4 : ℝ) * ((d : ℝ) + 319) ^ 80) := by
  let μ := Measure.pi (fun _ : Fin m => stdGauss (Fin d))
  have hp : IsProbabilityMeasure μ := by dsimp [μ]; unfold stdGauss; infer_instance
  let K := (m : ℝ) ^ (1 / 4 : ℝ) * ((d : ℝ) + 319) ^ 80
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpow : K ^ 4 = (m : ℝ) * ((d : ℝ) + 319) ^ 320 := by
    have he := rpow_inv_natCast_pow (x := (m : ℝ)) (n := 4) (Nat.cast_nonneg _) (by norm_num)
    norm_num only [Nat.cast_ofNat] at he
    dsimp [K]
    rw [mul_pow, ← pow_mul, he]
  have hhigh : (∫⁻ G, ENNReal.ofReal ((Mx hm G ^ 160) ^ 4) ∂μ) ≤ ENNReal.ofReal (K ^ 4) := by
    simp only [← pow_mul, hpow]
    have hh := maximum_even_moment (p := 320) hm hd
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    convert radialProduct_arithmetic d 320 (by norm_num) using 1 <;> congr 1 <;> ring
  have hZ : Measurable (fun G : Fin m → Fin d → ℝ => Mx hm G ^ 160) :=
    (measurable_Mx hm).pow_const 160
  have hZ0 : ∀ G : Fin m → Fin d → ℝ, 0 ≤ Mx hm G ^ 160 := fun G => pow_nonneg (Mx_nonneg hm G) _
  have hnorm : eLpNorm (fun G => Mx hm G ^ 160) (4 : ℕ) μ ≤ ENNReal.ofReal K := by
    apply BstLean.Part219.norm_le_of_moment (by norm_num) hZ.aestronglyMeasurable hZ0 hK
    simpa only [ENNReal.ofReal_pow (hZ0 _)] using hhigh
  have hnorm1 : eLpNorm (fun G => Mx hm G ^ 160) (1 : ℕ) μ ≤ ENNReal.ofReal K :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : ((1 : ℕ) : ℝ≥0∞) ≤ (4 : ℕ))).trans hnorm
  have hz := BstLean.Part219.moment_of_norm (p := 1) (by norm_num)
    hZ.aestronglyMeasurable hZ0 hK hnorm1
  simp only [pow_one] at hz
  rw [← ofReal_integral_eq_lintegral_ofReal hz.1 (ae_of_all _ hZ0)]
  exact ENNReal.ofReal_le_ofReal hz.2

end BstLean.BlueprintLow
