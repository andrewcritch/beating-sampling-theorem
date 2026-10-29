import BstLean.Part222CentreSource

/-! The S12 scalar conclusions retain their actual computed-centre normalization. -/
namespace BstLean.Part222
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part188

lemma hiddenCentre_nonneg {n J : ℕ}
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) (B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (j : Fin (mA n)) :
    0 ≤ BstLean.Part211.hiddenCentre (J := J) A B c τ j := by
  unfold BstLean.Part211.hiddenCentre BstLean.Part150.bT
  simp only [Pi.smul_apply, smul_eq_mul]
  apply mul_nonneg
  · unfold BstLean.Part150.rhoC
    exact inv_nonneg.mpr (sqrt_nonneg _)
  · unfold BstLean.Part150.binMean
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg (BstLean.Part150.binW_nonneg _ _) (by unfold relu; exact le_max_left _ _)

lemma scaled_projection_square {m : ℕ} (d b : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |(√t • d) ⬝ᵥ ((nrm b)⁻¹ • b)|^2 = t*|(∑ j, d j*b j)/nrm b|^2 := by
  have he : (√t • d) ⬝ᵥ ((nrm b)⁻¹ • b) = √t*(nrm b)⁻¹*(∑ j, d j*b j) := by
    unfold dotProduct
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by ring
  rw [he, sq_abs, sq_abs, mul_pow, mul_pow, sq_sqrt ht, div_pow]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem centre_at_of_raw_bound {n : ℕ} (D : Design n) (c : Ret n) {xi : ℝ}
    (hc : normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)-
      D.bA c.1 c.2.1.1) ≤ xi) : CENTRE_at D c xi := by
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  have he : xi*(2/(n : ℝ))/n = (2/(n : ℝ)^2)*xi := by
    rw [mul_div_assoc, div_div, pow_two]
    ring
  unfold CENTRE_at
  rw [hm, he]
  exact mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2/(n : ℝ)^2)

theorem fullError_normalization {n J : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : D.bA c.1 c.2.1.1 = BstLean.Part211.hiddenCentre (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) :
    BstLean.Part211.fullError (J := J) c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) =
      normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)-D.bA c.1 c.2.1.1) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  rw [hb]
  unfold BstLean.Part211.fullError
  rw [hm]
  field_simp

theorem parallelError_normalization {n J : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : D.bA c.1 c.2.1.1 = BstLean.Part211.hiddenCentre (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) :
    BstLean.Part211.parallelError (J := J) c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) =
      |(∑ j, (muStand D c-D.bA c.1 c.2.1.1) j*D.bA c.1 c.2.1.1 j)/
        nrm (D.bA c.1 c.2.1.1)|^2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  rw [hb]
  unfold BstLean.Part211.parallelError
  rw [scaled_projection_square _ _ (by positivity), hm]
  have he : muStand D c = hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := rfl
  rw [he]
  field_simp

theorem energy_normalization {n J : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hτ : 0 < D.tau0 c)
    (hb : D.bA c.1 c.2.1.1 = BstLean.Part211.hiddenCentre (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) :
    centreEnergy D c = BstLean.Part211.hiddenEnergy (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  have h := BstLean.Part211.computed_hidden_normalization (J := J) hn
    c.2.1.1.1 c.2.1.1.2 c.1.2 hτ
  change _ = BstLean.Part211.hiddenEnergy (J := J) c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) at h
  rw [← h, hm]
  unfold centreEnergy
  rw [hb]
  change normSq (BstLean.Part211.hiddenCentre (J := J) _ _ _ _)/(n : ℝ) = _
  field_simp
  simp only [BstLean.Part211.hiddenCentre, one_div]

/-- S12's parallel scalar bound supplies the sharp parallel interface. -/
theorem parallelCentre_of_s12 {n J : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    (hb : D.bA c.1 c.2.1.1 = BstLean.Part211.hiddenCentre (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c))
    (hbpos : 0 < normSq (D.bA c.1 c.2.1.1)) {xi : ℝ} (hxi : 0 ≤ xi)
    (hp : BstLean.Part211.parallelError (J := J)
      c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ xi) : ParallelCentre D c xi := by
  apply parallelCentre_of_projection hn D c hxi hbpos
  rw [parallelError_normalization hn D c hb] at hp
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (sqrt_nonneg _)
    (by rw [sq_sqrt hxi]; exact hp)

#print axioms fullError_normalization
#print axioms hiddenCentre_nonneg
#print axioms centre_at_of_raw_bound
#print axioms parallelError_normalization
#print axioms energy_normalization
#print axioms parallelCentre_of_s12
end BstLean.Part222
