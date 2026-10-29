import BstLean.Part221NumericalPlane
import Mathlib.Analysis.MeanInequalities

/-! Sharper rational plane and sphere factors at order 160. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part152 BstLean.Part209 BstLean.Part212

lemma radialProduct80_le_mean {d : ℕ} (hd : 1 ≤ d) :
    radialProduct d 80 ≤ ((d : ℝ) + 79) ^ 80 := by
  have hz : ∀ i ∈ Finset.range 80, (0 : ℝ) ≤ (d : ℝ) + 2 * i := by intros; positivity
  have h := geom_mean_le_arith_mean_weighted (Finset.range 80)
    (fun _ => (1 / 80 : ℝ)) (fun i => (d : ℝ) + 2 * i)
    (by intros; norm_num) (by norm_num) hz
  rw [finsetProd_rpow _ _ hz] at h
  have hi : (∑ i ∈ Finset.range 80, (i : ℝ)) = 3160 := by
    have hnat : (∑ i ∈ Finset.range 80, i) = 3160 := by norm_num [Finset.sum_range_id]
    rw [← Nat.cast_sum]
    exact_mod_cast hnat
  have he : (∑ i ∈ Finset.range 80, (1 / 80 : ℝ) * ((d : ℝ) + 2 * i)) = d + 79 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hi]
    norm_num
    <;> ring
  rw [he] at h
  change radialProduct d 80 ^ (1 / 80 : ℝ) ≤ (d : ℝ) + 79 at h
  have hp := pow_le_pow_left₀ (rpow_nonneg (radialProduct_pos hd 80).le _) h 80
  have hroot : (radialProduct d 80 ^ (1 / 80 : ℝ)) ^ (80 : ℕ) = radialProduct d 80 := by
    simpa only [Nat.cast_ofNat, one_div] using
      rpow_inv_natCast_pow (radialProduct_pos hd 80).le (by norm_num : (80 : ℕ) ≠ 0)
  rwa [hroot] at hp

theorem exactRadiusSquared160_sharp {n : ℕ} (hn : 8000 ≤ n) :
    exactRadius (n - 1 - 1) 80 ^ 2 ≤ 10101 / 10000 := by
  have hd : 2 ≤ n - 1 - 1 := by omega
  have hdR : (7998 : ℝ) ≤ (n - 1 - 1 : ℕ) := by exact_mod_cast (show 7998 ≤ n - 1 - 1 by omega)
  have hr : (((n - 1 - 1 : ℕ) : ℝ) + 79) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤
      10101 / 10000 := by rw [div_le_iff₀ (by linarith)]; linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 10101 / 10000)
  rw [← pow_mul, exactRadius_pow hd (by norm_num)]
  calc
    radialProduct (n - 1 - 1) 80 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 80 ≤
        ((((n - 1 - 1 : ℕ) : ℝ) + 79) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) ^ 80 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (radialProduct80_le_mean (by omega))
        (pow_nonneg (by linarith) _)
    _ ≤ _ := pow_le_pow_left₀ (div_nonneg (by positivity) (by linarith)) hr _

lemma gaussMomConst80_sharp : gaussMomConst 80 ≤ 783 / 100 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 783 / 100)
  rw [show 160 = 2 * 80 from rfl, gaussMomConst_pow (by norm_num)]
  norm_num

lemma twoGaussConst40_sharp : twoGaussConst 40 ≤ 57 / 10 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 57 / 10)
  rw [show 80 = 2 * 40 from rfl, twoGaussConst_pow (by norm_num)]
  norm_num

theorem countPlaneSquared160_sharp {n : ℕ} (hn : 8000 ≤ n) :
    countPlaneSquared160 n ≤ 251 / 500 * (n : ℝ) ^ 2 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : activeB n 40 ≤ 57 / 20 * (n : ℝ) := by
    unfold activeB
    have := mul_le_mul_of_nonneg_left twoGaussConst40_sharp
      (show (0 : ℝ) ≤ n / 2 by positivity)
    linarith
  have hn2 : 8000 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs : √((n : ℝ) ^ 2 / 2 + activeB n 40) ≤ 8842 / 12500 * (n : ℝ) := by
    apply sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hb, hn2]⟩
  have htwo : √(2 : ℝ) ≤ 71 / 50 := by
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sqrt_nonneg (2 : ℝ)]
  have hsum : √((n : ℝ) ^ 2 / 2 + activeB n 40) + √2 + gaussMomConst 80 ≤
      708517 / 1000000 * (n : ℝ) := by linarith [gaussMomConst80_sharp]
  have hg0 := gaussMomConst_nonneg 80
  unfold countPlaneSquared160
  calc
    _ ≤ (708517 / 1000000 * (n : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hsum 2
    _ ≤ _ := by nlinarith [sq_nonneg (n : ℝ)]

theorem planeEigenMoment160_sharp {n : ℕ} (hn : 8000 ≤ n) :
    PlaneEigenMoment160 (mA n) (251 / 500 * (n : ℝ) ^ 2) :=
  (planeEigenMoment160_count (by omega : 1 ≤ n)).trans
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (countPlaneSquared160_pos n).le
      (countPlaneSquared160_sharp hn) 80))

end BstLean.Part221
