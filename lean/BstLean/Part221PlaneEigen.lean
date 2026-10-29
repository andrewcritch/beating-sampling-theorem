import BstLean.Part167PB

/-! The exact upper eigenvalue of the two-dimensional gated plane matrix. -/
namespace BstLean.Part221
open MeasureTheory Real
open BstLean.Part130 BstLean.Part167
open BstLean.Part151 (mask mask_sq mask_nonneg)

noncomputable def eigenTwo (a b c : ℝ) : ℝ :=
  (a + c + √((a - c) ^ 2 + 4 * b ^ 2)) / 2

lemma eigenTwo_quadratic (a b c x y : ℝ) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≤
      eigenTwo a b c * (x ^ 2 + y ^ 2) := by
  have hd : 0 ≤ (a - c) ^ 2 + 4 * b ^ 2 := by positivity
  have hr := Real.sq_sqrt hd
  have hCS : ((a - c) * (x ^ 2 - y ^ 2) + 4 * b * x * y) ^ 2 ≤
      ((a - c) ^ 2 + 4 * b ^ 2) * (x ^ 2 + y ^ 2) ^ 2 := by
    apply sub_nonneg.mp
    calc
      _ = ((a - c) * (2 * x * y) - 2 * b * (x ^ 2 - y ^ 2)) ^ 2 := by ring
      _ ≥ 0 := sq_nonneg _
  have hm : 0 ≤ √((a - c) ^ 2 + 4 * b ^ 2) * (x ^ 2 + y ^ 2) := by positivity
  have hsq : (√((a - c) ^ 2 + 4 * b ^ 2) * (x ^ 2 + y ^ 2)) ^ 2 =
      ((a - c) ^ 2 + 4 * b ^ 2) * (x ^ 2 + y ^ 2) ^ 2 := by rw [mul_pow, hr]
  have hlin : (a - c) * (x ^ 2 - y ^ 2) + 4 * b * x * y ≤
      √((a - c) ^ 2 + 4 * b ^ 2) * (x ^ 2 + y ^ 2) := by
    exact le_of_sq_le_sq (hCS.trans_eq hsq.symm) hm
  unfold eigenTwo
  linarith only [hlin]

lemma eigenTwo_le (a b c : ℝ) : eigenTwo a b c ≤ max a c + |b| := by
  have hs : √((a - c) ^ 2 + 4 * b ^ 2) ≤ |a - c| + 2 * |b| := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_abs (a-c), sq_abs b, mul_nonneg (abs_nonneg (a-c)) (abs_nonneg b)]
  unfold eigenTwo
  rcases le_total a c with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)] at *; linarith
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)] at *; linarith

noncomputable def planeEigen {m : ℕ} (ξ₁ ξ₂ : Fin m → ℝ) : ℝ :=
  eigenTwo (L11 ξ₁) (L12 ξ₁ ξ₂) (L22 ξ₁ ξ₂)

lemma planeEigen_nonneg {m : ℕ} (ξ₁ ξ₂ : Fin m → ℝ) : 0 ≤ planeEigen ξ₁ ξ₂ := by
  unfold planeEigen eigenTwo
  have := L11_nonneg ξ₁
  have := L22_nonneg ξ₁ ξ₂
  positivity

lemma planeEigen_le_lamP {m : ℕ} (ξ₁ ξ₂ : Fin m → ℝ) : planeEigen ξ₁ ξ₂ ≤ lamP ξ₁ ξ₂ :=
  eigenTwo_le _ _ _

lemma measurable_planeEigen {m : ℕ} :
    Measurable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => planeEigen z.1 z.2) := by
  have hmask : Measurable mask := BstLean.Part151.measurable_mask
  unfold planeEigen eigenTwo L11 L12 L22
  fun_prop


theorem planeEigen_det (y ξ₁ ξ₂ : Fin m → ℝ) :
    (∑ j, mask (ξ₁ j) * y j * ξ₁ j) ^ 2 + (∑ j, mask (ξ₁ j) * y j * ξ₂ j) ^ 2 ≤
      normSq y * planeEigen ξ₁ ξ₂ := by
  set P1 := ∑ j, mask (ξ₁ j) * y j * ξ₁ j
  set P2 := ∑ j, mask (ξ₁ j) * y j * ξ₂ j
  set S := P1 ^ 2 + P2 ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have eS : S = ∑ j, (mask (ξ₁ j) * y j) * (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) := by
    have : ∀ j, (mask (ξ₁ j) * y j) * (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) =
        P1 * (mask (ξ₁ j) * y j * ξ₁ j) + P2 * (mask (ξ₁ j) * y j * ξ₂ j) := by
      intro j
      have h2 : mask (ξ₁ j) * mask (ξ₁ j) = mask (ξ₁ j) := by rw [← sq, mask_sq]
      linear_combination (y j * (P1 * ξ₁ j + P2 * ξ₂ j)) * h2
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS]; ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => mask (ξ₁ j) * y j)
    (fun j => mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j))
  rw [← eS] at hCS
  have hA : ∑ j, (mask (ξ₁ j) * y j) ^ 2 ≤ normSq y := by
    unfold normSq
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, mask_sq]
    have : mask (ξ₁ j) ≤ 1 := by unfold mask; split_ifs <;> norm_num
    nlinarith [sq_nonneg (y j), mask_nonneg (ξ₁ j)]
  have hB : ∑ j, (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) ^ 2 =
      P1 ^ 2 * L11 ξ₁ + 2 * (P1 * P2) * L12 ξ₁ ξ₂ + P2 ^ 2 * L22 ξ₁ ξ₂ := by
    have e : ∀ j, (mask (ξ₁ j) * (P1 * ξ₁ j + P2 * ξ₂ j)) ^ 2 =
        P1 ^ 2 * (mask (ξ₁ j) * ξ₁ j ^ 2) + 2 * (P1 * P2) * (mask (ξ₁ j) * ξ₁ j * ξ₂ j) +
          P2 ^ 2 * (mask (ξ₁ j) * ξ₂ j ^ 2) := fun j => by rw [mul_pow, mask_sq]; ring
    rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rfl
  have hB2 : P1 ^ 2 * L11 ξ₁ + 2 * (P1 * P2) * L12 ξ₁ ξ₂ + P2 ^ 2 * L22 ξ₁ ξ₂ ≤
      S * planeEigen ξ₁ ξ₂ := by
    have h := eigenTwo_quadratic (L11 ξ₁) (L12 ξ₁ ξ₂) (L22 ξ₁ ξ₂) P1 P2
    change _ ≤ S * eigenTwo (L11 ξ₁) (L12 ξ₁ ξ₂) (L22 ξ₁ ξ₂)
    dsimp only [S]
    nlinarith only [h]
  rw [hB] at hCS
  have hlam := planeEigen_nonneg ξ₁ ξ₂
  have hS2 : S ^ 2 ≤ normSq y * (S * planeEigen ξ₁ ξ₂) :=
    hCS.trans (mul_le_mul hA hB2 (by
      rw [← hB]; exact Finset.sum_nonneg fun j _ => sq_nonneg _) (normSq_nonneg y))
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (normSq_nonneg y) hlam
  · have : S * S ≤ S * (normSq y * planeEigen ξ₁ ξ₂) := by nlinarith
    exact le_of_mul_le_mul_left this hpos


end BstLean.Part221
