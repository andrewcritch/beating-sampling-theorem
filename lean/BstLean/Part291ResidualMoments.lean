import BstLean.Part291Weighted

/-! The full-centre and ordinary covariance interfaces give the two residual
terms in the weighted mean estimate, in unscaled hidden-vector units. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160

theorem residualTest_mean {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (v : Fin (mA n) → ℝ) :
    (∫ ξ, residualTest D c v ξ ∂stdGauss (Fin n)) =
      ∑ j, res (D.bA c.1 c.2.1.1) (muStand D c) j * v j := by
  unfold residualTest
  simp_rw [res_symm]
  exact hStand_mean hn D c (res (D.bA c.1 c.2.1.1) v)

theorem residualTest_mean_bound {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {xi : ℝ} (hcen : CENTRE_at D c xi) (v : Fin (mA n) → ℝ) (hv : normSq v = 1) :
    |∫ ξ, residualTest D c v ξ ∂stdGauss (Fin n)| ≤ √xi := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have he : xi * (2 / (n : ℝ)) / n = 2 / (n : ℝ) ^ 2 * xi := by ring
  unfold CENTRE_at at hcen
  rw [hm, he] at hcen
  have hb : normSq (muStand D c - D.bA c.1 c.2.1.1) ≤ xi :=
    le_of_mul_le_mul_left hcen (by positivity)
  rw [residualTest_mean hn D c v]
  have er : res (D.bA c.1 c.2.1.1) (muStand D c) =
      res (D.bA c.1 c.2.1.1) (muStand D c - D.bA c.1 c.2.1.1) := by
    rw [res_sub, BstLean.Part160.res_self, sub_zero]
  rw [er, res_symm]
  apply le_sqrt_of_sq_le
  rw [sq_abs]
  have h := sum_mul_sq_le (muStand D c - D.bA c.1 c.2.1.1) (res (D.bA c.1 c.2.1.1) v)
  have hv' : normSq (res (D.bA c.1 c.2.1.1) v) ≤ 1 := by simpa only [hv] using normSq_res_le _ v
  exact h.trans ((mul_le_mul_of_nonneg_left hv' (normSq_nonneg _)).trans (by simpa only [mul_one] using hb))

theorem residualTest_variance_bound {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {N : ℝ} (hN : 0 ≤ N) (hcov : COV_at D c N)
    (v : Fin (mA n) → ℝ) (hv : normSq v = 1) :
    (∫ ξ, (residualTest D c v ξ - ∫ ζ, residualTest D c v ζ ∂stdGauss (Fin n)) ^ 2
      ∂stdGauss (Fin n)) ≤ N := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  let w := res (D.bA c.1 c.2.1.1) v
  have h := hcov w
  have he : N * (2 / (n : ℝ)) / n * normSq w = 2 / (n : ℝ) ^ 2 * (N * normSq w) := by ring
  change 2 / (mA n : ℝ) * _ ≤ N * (2 / (n : ℝ)) / n * normSq w at h
  rw [hm, he] at h
  have hh := le_of_mul_le_mul_left h (by positivity : 0 < 2 / (n : ℝ) ^ 2)
  have hv' : normSq w ≤ 1 := by simpa only [hv] using normSq_res_le (D.bA c.1 c.2.1.1) v
  have hfinal := hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv' hN)
  apply le_trans (le_of_eq ?_) hfinal
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    rw [residualTest_mean hn D c v]
    unfold residualTest
    simp_rw [res_symm]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by dsimp [w]; ring

end BstLean.BlueprintLow
