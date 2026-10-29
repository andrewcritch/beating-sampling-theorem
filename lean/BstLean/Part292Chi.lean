import BstLean.Part153PPs
import BstLean.Part153Asm

/-! Sharp chi-square payments for a fixed selected set of rows. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part153

theorem chi_lower_threshold_mono {a b x : ℝ} (hx : 0 ≤ x)
    (ha : x ≤ a) (hab : a ≤ b) :
    a - 2*sqrt (a*x) ≤ b - 2*sqrt (b*x) := by
  have ha0 : 0 ≤ a := hx.trans ha
  have hb0 : 0 ≤ b := ha0.trans hab
  have hsA := sq_sqrt (mul_nonneg ha0 hx)
  have hsB := sq_sqrt (mul_nonneg hb0 hx)
  have hax : x ≤ sqrt (a*x) := le_sqrt_of_sq_le (by nlinarith)
  have h0 : 0 ≤ b-a+2*sqrt (a*x) := by positivity
  have hp : 0 ≤ (b-a)*(b-a+4*(sqrt (a*x)-x)) := by positivity
  have hsq : (2*sqrt (b*x))^2 ≤ (b-a+2*sqrt (a*x))^2 := by nlinarith
  have hle := (sq_le_sq₀ (by positivity : 0 ≤ 2*sqrt (b*x)) h0).mp hsq
  linarith

theorem matrix_chi_lower {m d : ℕ} (hm : 0 < m) (hd : 0 < d) {x : ℝ}
    (hx : 0 ≤ x) :
    (gaussMat m d 1).real {G | ∑ i, normSq (G i) <
      (m : ℝ)*d - 2*sqrt ((m : ℝ)*d*x)} ≤ exp (-x) := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero d := ⟨by omega⟩
  have h := chiSq_lower_LM (ι := Fin m × Fin d) hx
  unfold gaussMat
  rw [map_measureReal_apply (by fun_prop) (measurableSet_lt (by unfold normSq; fun_prop) measurable_const)]
  apply le_trans (measureReal_mono ?_) h
  intro G hG
  simp only [mem_preimage, mem_setOf_eq, sqrt_one, one_mul, Matrix.of_apply] at hG
  simp only [mem_setOf_eq, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simpa only [normSq, Fintype.sum_prod_type, Matrix.of_apply] using hG.le

theorem selected_chi_lower {m d : ℕ} (hd : 0 < d)
    (S : Finset (Fin m)) {D x : ℝ} (hx : 0 ≤ x) (hD : x ≤ D)
    (hD0 : 0 < D) (hcard : D ≤ (S.card : ℝ)*d) :
    (gaussMat m d 1).real {G | ∑ i ∈ S, normSq (G i) <
      D-2*sqrt (D*x)} ≤ exp (-x) := by
  have hS : 0 < S.card := by
    by_contra hh
    have hz : S.card = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul] at hcard
    linarith
  let e := S.orderEmbOfFin rfl
  have hsum (G : Matrix (Fin m) (Fin d) ℝ) :
      ∑ i ∈ S, normSq (G i) = ∑ i : Fin S.card, normSq (G (e i)) := by
    have h := Finset.sum_map Finset.univ e.toEmbedding (fun i => normSq (G i))
    rw [Finset.map_orderEmbOfFin_univ] at h
    exact h
  have h := matrix_chi_lower hS hd hx
  rw [← gaussMat_submatrix_rows 1 e e.injective,
    map_measureReal_apply (measurable_submatrix_rows e)
      (measurableSet_lt (by unfold normSq; fun_prop) measurable_const)] at h
  apply le_trans (measureReal_mono ?_) h
  intro G hG
  change ∑ i, normSq (G.submatrix e id i) < _
  have hG' : ∑ i ∈ S, normSq (G i) < D-2*sqrt (D*x) := hG
  rw [hsum] at hG'
  exact hG'.trans_le (chi_lower_threshold_mono hx hD hcard)

theorem count_lower_band {n : ℕ} (hn : 8000 ≤ n) :
    (stdGauss (Fin (mA n))).real
      {z | ∑ i, BstLean.Part151.mask (z i) < (n : ℝ)^2/2-sqrt 6*n} ≤ exp (-12) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := cnt_tail_lower (m := mA n) (by positivity : 0 ≤ sqrt 6/(n : ℝ))
  have ht : ((1/2 : ℝ)-sqrt 6/n)*(mA n : ℝ) = (n : ℝ)^2/2-sqrt 6*n := by
    simp only [mA, Nat.cast_pow]
    field_simp <;> ring
  have he : -2*(sqrt 6/(n : ℝ))^2*(mA n : ℝ) = -12 := by
    simp only [mA, Nat.cast_pow, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    field_simp <;> ring
  simpa only [ht, he] using h

end BstLean.Part292
