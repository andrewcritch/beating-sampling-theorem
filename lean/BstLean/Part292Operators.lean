import BstLean.Part292SourceNumbers
import BstLean.Part278Good

/-! The two operator events are paid at exp(-18) each and supply the odd-rule size fields. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part152 (opN)

noncomputable def lowSecondOperator (n : ℕ) : ℝ := sqrt (tA n)*(2*(n : ℝ)+6)

theorem lowOperator_paid {n : ℕ} (hn : 8000 ≤ n) :
    (gaussMat (mA n) n (2/(n : ℝ))).real {A | lowOperator n < opN A} ≤ exp (-18) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := BstLean.Part152.opN_tail' (p := mA n) (q := n)
    (by positivity : 0 < 2/(n : ℝ)) (by norm_num : (0 : ℝ) ≤ 6)
  norm_num only [show -(6 : ℝ)^2/2 = -18 by norm_num] at h
  simp only [mA, Nat.cast_pow, sqrt_sq (Nat.cast_nonneg n)] at h
  apply (measureReal_mono ?_).trans h
  intro A hA
  change lowOperator n < opN A at hA
  change lowOperator n ≤ opN A
  exact hA.le

theorem lowSecondOperator_paid {n : ℕ} (hn : 8000 ≤ n) :
    (gaussMat (mA n) (mA n) (tA n)).real {A | lowSecondOperator n < opN A} ≤ exp (-18) := by
  have ht : 0 < tA n := by
    have hn0 : 0 < n := by omega
    unfold tA mA
    positivity
  have h := BstLean.Part152.opN_tail' (p := mA n) (q := mA n) ht
    (by norm_num : (0 : ℝ) ≤ 6)
  norm_num only [show -(6 : ℝ)^2/2 = -18 by norm_num] at h
  simp only [mA, Nat.cast_pow, sqrt_sq (Nat.cast_nonneg n)] at h
  have he : sqrt (tA n)*((n : ℝ)+n+6) = lowSecondOperator n := by
    unfold lowSecondOperator
    ring
  rw [he] at h
  apply (measureReal_mono ?_).trans h
  intro A hA
  change lowSecondOperator n < opN A at hA
  change lowSecondOperator n ≤ opN A
  exact hA.le

theorem lowSecondOperator_le {n : ℕ} (hn : 8000 ≤ n) : lowSecondOperator n ≤ 3 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by norm_num)
  unfold lowSecondOperator
  rw [mul_pow, sq_sqrt (tA_nonneg n)]
  unfold tA mA
  push_cast
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hn0 2)]
  nlinarith

theorem low_odd_row_energy {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hA : OpB (A1 c) (lowOperator n)) {s : ℝ} (hs : s^2 ≤ 1) :
    ∑ i, BstLean.Part278.aw c s i^2 ≤ 5*(n : ℝ)^2 := by
  have h := BstLean.Part278.frob_le c hA
  have hO := lowOperator_square hn
  calc
    _ ≤ ∑ i, 2*∑ j, A1 c i j^2 :=
      Finset.sum_le_sum fun i _ => BstLean.Part278.aw_sq_le (by omega) c s hs i
    _ = 2*∑ i, ∑ j, A1 c i j^2 := by rw [Finset.mul_sum]
    _ ≤ 2*((n : ℝ)*lowOperator n^2) := by linarith
    _ ≤ 5*(n : ℝ)^2 := by nlinarith [mul_le_mul_of_nonneg_left hO (Nat.cast_nonneg n)]

theorem low_odd_passF {n : ℕ} (hn : 8001 ≤ n) (c : Ret n)
    (hA : OpB (A1 c) (lowOperator n)) (hB : OpB (A2 c) (lowSecondOperator n))
    (g : ℕ) (hs : nodeS c g^2 ≤ 1) : |passF c g| ≤ 9*n := by
  have hnR : (8001 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hB3 : OpB (A2 c) 3 := BstLean.Part278.OpB_mono hB
    (by unfold lowSecondOperator; positivity) (lowSecondOperator_le (by omega))
  have h := BstLean.Part278.passF_le hn (BstLean.Part278.Jz_pos (by omega)) c hB3 g
    (low_odd_row_energy (by omega) c hA hs)
  apply h.trans
  rw [div_le_iff₀ (sqrt_pos.mpr hn0)]
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, sq_sqrt hn0.le]
  have hnum : (440 : ℝ) ≤ 81*(n : ℝ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hnum (sq_nonneg (n : ℝ))]

end BstLean.Part292
