import BstLean.Part227Hidden

/-! Part 227: the product window for the actual computed World centre. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159

/-- A squared norm window transfers through a controlled centre distance. -/
theorem scaled_norm_window {m : ℕ} (a b : Fin m → ℝ) {t L U E : ℝ}
    (ht : 0 ≤ t) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hLE : √E ≤ √L) (haL : L ≤ t * normSq a) (haU : t * normSq a ≤ U)
    (hab : t * normSq (b - a) ≤ E) :
    (√L - √E) ^ 2 ≤ t * normSq b ∧
      t * normSq b ≤ (√U + √E) ^ 2 := by
  have hu : 0 ≤ U := (mul_nonneg ht (normSq_nonneg a)).trans haU
  have hb : 0 ≤ t * normSq b := mul_nonneg ht (normSq_nonneg b)
  have he1 : b = a + (b - a) := by abel
  have hupper := BstLean.Part204.normSq_triangle_scaled a (b - a) ht haU hab
  rw [← he1] at hupper
  have he2 : a = b + (a - b) := by abel
  have hab' : t * normSq (a - b) ≤ E := by rw [normSq_sub_comm]; exact hab
  have hlower := BstLean.Part204.normSq_triangle_scaled b (a - b) ht le_rfl hab'
  rw [← he2] at hlower
  have hs := Real.sqrt_le_sqrt (haL.trans hlower)
  rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hs
  have hs' : √L - √E ≤ √(t * normSq b) := by linarith
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hLE) hs' 2
  rw [Real.sq_sqrt hb] at hsq
  exact ⟨hsq, hupper⟩

noncomputable def perturbation (n : ℕ) : ℝ := 645 / 10 ^ 4 / (mW n : ℝ)
noncomputable def kernelError (n : ℕ) : ℝ := 2 / (10 ^ 5 * (n : ℝ) ^ 2)

noncomputable def productLower (n : ℕ) (eB : ℝ) : ℝ :=
  (√(kap1 (2 * n) - eB) - √(perturbation n)) ^ 2 /
    ((1001 / 1000) * (kap1 (2 * n) + kernelError n) ^ 2)

noncomputable def productUpper (n : ℕ) (eB : ℝ) : ℝ :=
  (√(kap1 (2 * n) + eB) + √(perturbation n)) ^ 2 /
    ((999 / 1000) * (kap1 (2 * n) - kernelError n) ^ 2)

/-- The normalization is exact at the integer width. -/
lemma normalized_energy {n : ℕ} (hn : 1 ≤ n) (b : Fin (mW n) → ℝ) :
    (n : ℝ) * (2 / (mW n : ℝ) * normSq b) =
      ((2 * n : ℕ) : ℝ) / (mW n : ℝ) * normSq b := by
  push_cast
  ring

/-- The norm event bounds the computed centre in units of the World variance. -/
theorem computed_norm_window {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n} {eB : ℝ}
    (hB : θ ∈ goodB n eB) (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n)
    (hL : 0 ≤ kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(kap1 (2 * n) - eB)) :
    (√(kap1 (2 * n) - eB) - √(perturbation n)) ^ 2 ≤
        (n : ℝ) * (2 / (mW n : ℝ) * normSq (bWp θ)) ∧
      (n : ℝ) * (2 / (mW n : ℝ) * normSq (bWp θ)) ≤
        (√(kap1 (2 * n) + eB) + √(perturbation n)) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (n : ℝ) * (2 / ((2 * n : ℕ) : ℝ)) = 1 := by
    push_cast
    field_simp
  have hBn := mul_le_mul_of_nonneg_left (abs_le.mp hB).1 hnpos.le
  have hBp := mul_le_mul_of_nonneg_left (abs_le.mp hB).2 hnpos.le
  have hhat : Bh (2 * n) (mW n) θ = 2 / (mW n : ℝ) * normSq (bhat θ) := rfl
  simp only [mul_sub, mul_neg, ← mul_assoc, hγ, one_mul, hhat] at hBn hBp
  have hd := mul_le_mul_of_nonneg_left
    (BstLean.Part204.bWp_dist hn (BstLean.Part201.constC hn) hS hA) hnpos.le
  simp only [← mul_assoc, hγ, one_mul] at hd
  have hw := scaled_norm_window (bhat θ) (bWp θ)
    (t := (n : ℝ) * (2 / (mW n : ℝ)))
    (L := kap1 (2 * n) - eB) (U := kap1 (2 * n) + eB) (E := perturbation n)
    (by positivity) hL
    (show 0 ≤ perturbation n by unfold perturbation; positivity) hLE
    (by linarith only [hBn]) (by linarith only [hBp])
    (by simpa only [perturbation, mul_assoc] using hd)
  simpa only [mul_assoc] using hw

/-- Positive denominator guards suffice for the exact dimension-dependent product window. -/
theorem product_window {n : ℕ} (hn : 4096 ≤ n) {θ : WHid n} {eB : ℝ}
    (hB : θ ∈ goodB n eB) (hS : θ ∈ goodS n) (hA : θ ∈ goodAo n)
    (hL : 0 ≤ kap1 (2 * n) - eB)
    (hLE : √(perturbation n) ≤ √(kap1 (2 * n) - eB))
    (hk : kernelError n < kap1 (2 * n)) :
    productLower n eB ≤ 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ∧
      2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ ≤ productUpper n eB := by
  obtain ⟨hbl, hbu⟩ := computed_norm_window hn hB hS hA hL hLE
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdk : 0 ≤ kernelError n := by unfold kernelError; positivity
  have hkpos : 0 < kap1 (2 * n) := lt_of_le_of_lt hdk hk
  have hdiff : 0 < kap1 (2 * n) - kernelError n := sub_pos.mpr hk
  have hclose := BstLean.Part201.kapT_close_strong hn
  change |kapT n - kap1 (2 * n)| ≤ kernelError n at hclose
  obtain ⟨hkl, hku⟩ := abs_le.mp hclose
  have hkt : 0 < kapT n := by linarith
  have hS' : |SWp θ / 2 - 1| ≤ 1 / 1000 := hS
  obtain ⟨hsl, hsu⟩ := abs_le.mp hS'
  have hspos : 0 < SWp θ / 2 := by linarith
  have hden : 0 < (SWp θ / 2) * kapT n ^ 2 := by positivity
  have hdlo : (999 / 1000) * (kap1 (2 * n) - kernelError n) ^ 2 ≤
      (SWp θ / 2) * kapT n ^ 2 :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (sq_nonneg _) (by linarith)
  have hdhi : (SWp θ / 2) * kapT n ^ 2 ≤
      (1001 / 1000) * (kap1 (2 * n) + kernelError n) ^ 2 :=
    mul_le_mul (by linarith) (pow_le_pow_left₀ hkt.le (by linarith) 2)
      (sq_nonneg _) (by norm_num)
  have heq : 2 / (mW n : ℝ) * normSq (bWp θ) * ccP n θ =
      ((n : ℝ) * (2 / (mW n : ℝ) * normSq (bWp θ))) /
        ((SWp θ / 2) * kapT n ^ 2) := by unfold ccP; ring
  rw [heq]
  constructor
  · exact (div_le_div_of_nonneg_left (sq_nonneg _) hden hdhi).trans
      (div_le_div_of_nonneg_right hbl hden.le)
  · exact (div_le_div_of_nonneg_right hbu hden.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hdlo)

end BstLean.Part227
#print axioms BstLean.Part227.scaled_norm_window
#print axioms BstLean.Part227.computed_norm_window
#print axioms BstLean.Part227.product_window
