import BstLean.Part221SharpPlane

/-! The sphere coefficient at order 1664. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part152 BstLean.Part209 BstLean.Part212

lemma radialProduct_le_arithMean {d j : ℕ} (hd : 1 ≤ d) (hj : 1 ≤ j) :
    radialProduct d j ≤ ((d : ℝ) + j - 1) ^ j := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hz : ∀ i ∈ Finset.range j, (0 : ℝ) ≤ (d : ℝ) + 2 * i := by intros; positivity
  have hsum : (∑ _i ∈ Finset.range j, (1 / (j : ℝ))) = 1 := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have h := geom_mean_le_arith_mean_weighted (Finset.range j)
    (fun _ => (1 / (j : ℝ))) (fun i => (d : ℝ) + 2 * i)
    (by intros; positivity) hsum hz
  rw [finsetProd_rpow _ _ hz] at h
  have hi : 2 * (∑ i ∈ Finset.range j, (i : ℝ)) = (j : ℝ) * ((j : ℝ) - 1) := by
    have hnat := Finset.sum_range_id_mul_two j
    have hc : ((∑ i ∈ Finset.range j, i : ℕ) : ℝ) * 2 =
        (j : ℝ) * ((j - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [Nat.cast_sum, Nat.cast_sub hj] at hc
    norm_num only [Nat.cast_one] at hc
    linarith
  have he : (∑ i ∈ Finset.range j, (1 / (j : ℝ)) * ((d : ℝ) + 2 * i)) =
      (d : ℝ) + j - 1 := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, hi]
    simp only [Finset.card_range, nsmul_eq_mul]
    field_simp
    <;> ring
  rw [he] at h
  change radialProduct d j ^ (1 / (j : ℝ)) ≤ (d : ℝ) + j - 1 at h
  have hp := pow_le_pow_left₀ (rpow_nonneg (radialProduct_pos hd j).le _) h j
  have hroot : (radialProduct d j ^ (1 / (j : ℝ))) ^ j = radialProduct d j := by
    simpa only [one_div] using
      rpow_inv_natCast_pow (radialProduct_pos hd j).le (by omega : j ≠ 0)
  rwa [hroot] at hp

lemma radialProduct832_le_mean {d : ℕ} (hd : 1 ≤ d) :
    radialProduct d 832 ≤ ((d : ℝ) + 831) ^ 832 := by
  have h := radialProduct_le_arithMean hd (by norm_num : 1 ≤ (832 : ℕ))
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1 <;> congr 1 <;> ring

theorem exactRadiusSquared1664_sharp {n : ℕ} (hn : 8000 ≤ n) :
    exactRadius (n - 1 - 1) 832 ^ 2 ≤ 11041 / 10000 := by
  have hd : 2 ≤ n - 1 - 1 := by omega
  have hdR : (7998 : ℝ) ≤ (n - 1 - 1 : ℕ) := by exact_mod_cast (show 7998 ≤ n - 1 - 1 by omega)
  have hr : (((n - 1 - 1 : ℕ) : ℝ) + 831) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤
      11041 / 10000 := by rw [div_le_iff₀ (by linarith)]; linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (832 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 11041 / 10000)
  rw [← pow_mul, exactRadius_pow hd (by norm_num)]
  calc
    radialProduct (n - 1 - 1) 832 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 832 ≤
        ((((n - 1 - 1 : ℕ) : ℝ) + 831) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) ^ 832 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (radialProduct832_le_mean (by omega))
        (pow_nonneg (by linarith) _)
    _ ≤ _ := pow_le_pow_left₀ (div_nonneg (by positivity) (by linarith)) hr _

end BstLean.Part221
