import BstLean.Part280Table

/-! The whole clipped latitude interval has one geometry certificate. -/
namespace BstLean.Part293
open Real BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

def TableWorldGuard {n : ℕ} (wr : WRet n) : Prop :=
  windowW wr ∧ BstLean.Part150.thetaC wr.2 (tau0p wr.1) ≤ 528 / 1000

theorem circle_upper_rational {N a b : ℝ} (hN : 8000 ≤ N)
    (hc : a ^ 2 + N * b ^ 2 = 1) (hl : 46 / 100 ≤ N * b ^ 2) :
    a + 6 * b ≤ 78038 / 100000 := by
  have hbb := mul_le_mul_of_nonneg_right hN (sq_nonneg b)
  have hA : 2 * (734847 / 1000000 : ℝ) * a ≤
      1 - N * b ^ 2 + (734847 / 1000000 : ℝ) ^ 2 := by
    nlinarith only [hc, sq_nonneg (a - (734847 / 1000000 : ℝ))]
  have hB : 2 * (7583 / 1000000 : ℝ) * b ≤
      N * b ^ 2 / 8000 + (7583 / 1000000 : ℝ) ^ 2 := by
    nlinarith only [hbb, sq_nonneg (b - (7583 / 1000000 : ℝ))]
  linarith only [hA, hB, hl]

theorem circle_bulk_rational {N a b s : ℝ} (hN : 8000 ≤ N)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a ^ 2 + N * b ^ 2 = 1)
    (hl : 46 / 100 ≤ N * b ^ 2) (hu : N * b ^ 2 ≤ 54 / 100)
    (hs : a - 6 * b ≤ s ∧ s ≤ a + 6 * b) :
    0 ≤ s ∧ 391 / 1000 ≤ 1 - s ^ 2 ∧ 1 - s ^ 2 ≤ 605 / 1000 := by
  have hsu := hs.2.trans (circle_upper_rational hN hc hl)
  have hal : (6782 / 10000 : ℝ) ≤ a := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 6782 / 10000) ha).mp
    nlinarith only [hc, hu]
  have hbu : b ≤ (8216 / 1000000 : ℝ) := by
    apply (sq_le_sq₀ hb (by norm_num : (0 : ℝ) ≤ 8216 / 1000000)).mp
    have hbb := mul_le_mul_of_nonneg_right hN (sq_nonneg b)
    nlinarith only [hbb, hu]
  have hsl : (628904 / 1000000 : ℝ) ≤ s := by linarith [hs.1]
  have hs0 : 0 ≤ s := le_trans (by norm_num) hsl
  refine ⟨hs0, ?_, ?_⟩
  · have h := pow_le_pow_left₀ hs0 hsu 2
    norm_num at h
    linarith only [h]
  · have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 628904 / 1000000) hsl 2
    norm_num at h
    linarith only [h]

theorem table_bulk_geometry {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hw : TableWorldGuard c.1) {s : ℝ}
    (hs : nodeL c ≤ s ∧ s ≤ nodeH c) :
    0 ≤ s ∧ 391 / 1000 ≤ 1 - s ^ 2 ∧ 1 - s ^ 2 ≤ 605 / 1000 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let r := rhoR c
  have hr2 : r ^ 2 = normSq c.1.2 + (n : ℝ) * tauR c ^ 2 :=
    sq_sqrt (add_nonneg (normSq_nonneg _) (by positivity))
  have ht : 0 < tauR c := hw.1.1
  have hr : 0 < r := sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hn0 (sq_pos_of_pos ht)))
  let a := √(normSq c.1.2) / r
  let b := tauR c / r
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a ^ 2 + (n : ℝ) * b ^ 2 = 1 := by
    dsimp [a, b]
    rw [div_pow, div_pow, sq_sqrt (normSq_nonneg _)]
    field_simp
    nlinarith [hr2]
  have htheta : BstLean.Part150.thetaC c.1.2 (tauR c) = (n : ℝ) * b ^ 2 := by
    unfold BstLean.Part150.thetaC
    change _ / r ^ 2 = _
    dsimp [b]
    rw [div_pow]
    ring
  have hl : 46 / 100 ≤ (n : ℝ) * b ^ 2 := by rw [← htheta]; exact hw.1.2.1
  have hu : (n : ℝ) * b ^ 2 ≤ 54 / 100 := by
    rw [← htheta]
    exact hw.2.trans (by norm_num)
  apply circle_bulk_rational hnR ha hb hab hl hu
  have hL : nodeL c = a - 6 * b := by dsimp [nodeL, a, b]; ring
  have hH : nodeH c = a + 6 * b := by dsimp [nodeH, a, b]; ring
  simpa only [hL, hH] using hs

theorem normalized_node_width {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hw : TableWorldGuard c.1) :
    (n : ℝ) * √(n : ℝ) * (nodeD c / 2) ≤ 0.008612 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht : 0 < tauR c := hw.1.1
  have hr : 0 < rhoR c := sqrt_pos.mpr
    (add_pos_of_nonneg_of_pos (normSq_nonneg _) (mul_pos hn0 (sq_pos_of_pos ht)))
  have htheta : (n : ℝ) * (tauR c / rhoR c) ^ 2 ≤ 54 / 100 := by
    have h := hw.2.trans (by norm_num : (528 / 1000 : ℝ) ≤ 54 / 100)
    change (n : ℝ) * tauR c ^ 2 / rhoR c ^ 2 ≤ 54 / 100 at h
    simpa only [div_pow, mul_div_assoc] using h
  have hb : √(n : ℝ) * (tauR c / rhoR c) ≤ √(54 / 100 : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
    rw [mul_pow, sq_sqrt hn0.le, sq_sqrt (by norm_num : (0 : ℝ) ≤ 54 / 100)]
    exact htheta
  have he : (n : ℝ) * √(n : ℝ) * (nodeD c / 2) =
      (6 / 512 : ℝ) * (√(n : ℝ) * (tauR c / rhoR c)) := by
    unfold nodeD nodeL nodeH Js
    push_cast
    field_simp <;> ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left hb (by norm_num)).trans
  have hs : √(54 / 100 : ℝ) ≤ 0.734847 := sqrt_le_iff.mpr (by norm_num)
  linarith

end BstLean.Part293
