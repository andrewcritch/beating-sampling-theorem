import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! Part 246: the Gamma ratio `φ(x) = Γ(x + 1/2)/Γ(x)`.
`φ(x) φ(x + 1/2) = x`, `φ(x)² ≤ x` (log-convexity), and the sharper upper bound
`φ(x)² ≤ x - 1/4 + 1/(32x) + 1/(64x²)` from a monotone ratio and the Wendel limit. -/
namespace BstLean.Part246
open Real

/-- `φ(x) = Γ(x + 1/2)/Γ(x)`. -/
noncomputable def phiG (x : ℝ) : ℝ := Gamma (x + 1 / 2) / Gamma x

lemma phiG_pos {x : ℝ} (hx : 0 < x) : 0 < phiG x :=
  div_pos (Gamma_pos_of_pos (by linarith)) (Gamma_pos_of_pos hx)

lemma phiG_mul {x : ℝ} (hx : 0 < x) : phiG x * phiG (x + 1 / 2) = x := by
  unfold phiG
  have h1 : x + 1 / 2 + 1 / 2 = x + 1 := by ring
  rw [h1, Gamma_add_one hx.ne']
  have g1 := (Gamma_pos_of_pos hx).ne'
  have g2 := (Gamma_pos_of_pos (show 0 < x + 1 / 2 by linarith)).ne'
  field_simp

/-- Wendel: `φ(x)² ≤ x` (log-convexity of `Γ`). -/
lemma phiG_sq_le {x : ℝ} (hx : 0 < x) : phiG x ^ 2 ≤ x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := x) (t := x + 1) (a := 1 / 2)
    (b := 1 / 2) hx (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have e : 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 := by ring
  rw [e, Gamma_add_one hx.ne'] at h
  have g1 := Gamma_pos_of_pos hx
  have g2 := Gamma_pos_of_pos (show 0 < x + 1 / 2 by linarith)
  have h2 : Gamma x ^ (1 / 2 : ℝ) * (x * Gamma x) ^ (1 / 2 : ℝ) = √x * Gamma x := by
    rw [mul_rpow hx.le g1.le]
    simp only [← Real.sqrt_eq_rpow]
    rw [show √(Gamma x) * (√x * √(Gamma x)) = √x * (√(Gamma x) * √(Gamma x)) by ring,
      Real.mul_self_sqrt g1.le]
  rw [h2] at h
  unfold phiG
  rw [div_pow, div_le_iff₀ (by positivity)]
  have h3 := pow_le_pow_left₀ g2.le h 2
  rw [mul_pow, Real.sq_sqrt hx.le] at h3
  exact h3

lemma phiG_succ {x : ℝ} (hx : 0 < x) : phiG (x + 1) = phiG x * (x + 1 / 2) / x := by
  unfold phiG
  have e : x + 1 + 1 / 2 = (x + 1 / 2) + 1 := by ring
  rw [e, Gamma_add_one (show x + 1 / 2 ≠ 0 by linarith), Gamma_add_one hx.ne']
  have g1 := (Gamma_pos_of_pos hx).ne'
  field_simp

/-- The comparison function `U(x) = x - 1/4 + 1/(32x) + 1/(64x²)`. -/
noncomputable def Uf (x : ℝ) : ℝ := x - 1 / 4 + 1 / (32 * x) + 1 / (64 * x ^ 2)

lemma Uf_pos {x : ℝ} (hx : 0 < x) : 0 < Uf x := by
  unfold Uf
  have h1 : 0 < 1 / (64 * x ^ 2) := by positivity
  have h2 : x - 1 / 4 + 1 / (32 * x) > 0 := by
    have : x + 1 / (32 * x) - 1 / 4 = (32 * x ^ 2 - 8 * x + 1) / (32 * x) := by
      field_simp; ring
    have hnum : 0 < 32 * x ^ 2 - 8 * x + 1 := by nlinarith [sq_nonneg (x - 1 / 8)]
    have : 0 < (32 * x ^ 2 - 8 * x + 1) / (32 * x) := by positivity
    linarith
  linarith

lemma Uf_ratio {x : ℝ} (hx : 0 < x) : x ^ 2 * Uf (x + 1) ≤ (x + 1 / 2) ^ 2 * Uf x := by
  unfold Uf
  have hx1 : 0 < x + 1 := by linarith
  rw [← sub_nonneg]
  have e : (x + 1 / 2) ^ 2 * (x - 1 / 4 + 1 / (32 * x) + 1 / (64 * x ^ 2)) -
      x ^ 2 * (x + 1 - 1 / 4 + 1 / (32 * (x + 1)) + 1 / (64 * (x + 1) ^ 2)) =
      (6 * x ^ 3 + 9 * x ^ 2 + 8 * x + 1) / (4 * (64 * x ^ 2 * (x + 1) ^ 2)) := by
    field_simp; ring
  rw [e]; positivity

lemma ratio_le_Uf {y : ℝ} (hy : 1 ≤ y) : y / Uf y ≤ 1 + 1 / y := by
  have hU : y - 1 / 4 ≤ Uf y := by
    unfold Uf; have : 0 ≤ 1 / (32 * y) := by positivity
    have : 0 ≤ 1 / (64 * y ^ 2) := by positivity
    linarith
  have hy0 : 0 < y := by linarith
  have hUp := Uf_pos hy0
  rw [div_le_iff₀ hUp]
  have : (1 + 1 / y) * (y - 1 / 4) ≥ y := by
    have e : (1 + 1 / y) * (y - 1 / 4) = y + 3 / 4 - 1 / (4 * y) := by field_simp; ring
    rw [e]
    have : 1 / (4 * y) ≤ 1 / 4 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  nlinarith

/-- **Sharp upper bound** `φ(x)² ≤ x - 1/4 + 1/(32x) + 1/(64x²)`. -/
theorem phiG_sq_le_Uf {x : ℝ} (hx : 0 < x) : phiG x ^ 2 ≤ Uf x := by
  set v : ℕ → ℝ := fun k => phiG (x + k) ^ 2 / Uf (x + k) with hv
  have hmono : ∀ k, v k ≤ v (k + 1) := by
    intro k
    have hxk : 0 < x + k := by positivity
    simp only [hv]
    push_cast
    rw [show x + (k + 1 : ℝ) = (x + k) + 1 by ring, phiG_succ hxk]
    have hU0 := Uf_pos hxk
    have hU1 := Uf_pos (show 0 < x + k + 1 by linarith)
    have hp := phiG_pos hxk
    rw [div_le_div_iff₀ hU0 hU1]
    have hr := Uf_ratio hxk
    have e : (phiG (x + k) * (x + k + 1 / 2) / (x + k)) ^ 2 =
        phiG (x + k) ^ 2 * (x + k + 1 / 2) ^ 2 / (x + k) ^ 2 := by
      field_simp
    rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hr (sq_nonneg (phiG (x + k)))
    nlinarith [this]
  have hle : ∀ k, v 0 ≤ v k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact ih.trans (hmono k)
  have hW : ∀ k : ℕ, v k ≤ (x + k) / Uf (x + k) := by
    intro k
    have hxk : 0 < x + k := by positivity
    exact div_le_div_of_nonneg_right (phiG_sq_le hxk) (Uf_pos hxk).le
  have h01 : v 0 ≤ 1 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε + 1)
    have hε1 : 0 < 1 / ε := by positivity
    have hy : 1 ≤ x + k := by linarith
    have h1 := (hle k).trans ((hW k).trans (ratio_le_Uf hy))
    have h2 : 1 / (x + (k : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by linarith)]
      have : 1 / ε < x + k := by linarith
      rw [div_lt_iff₀ hε] at this
      linarith
    linarith
  simp only [hv, Nat.cast_zero, add_zero] at h01
  rwa [div_le_one (Uf_pos hx)] at h01

end BstLean.Part246
