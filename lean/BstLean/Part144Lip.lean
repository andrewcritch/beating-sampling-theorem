import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Part 144, real inequalities: a global lower parabola and a Lipschitz step

Role: `delegations/statements/p144-spec.md` (tools for the sharper form of item 2).
Pure real-number inequalities; no measure theory.

* `parab_lower`: for `A > 0`, `0 ≤ B ≤ 2Ac`, `c > 0`: if `P ≥ 0` and `P ≥ A − B/x` for `x > 0`,
  then `P ≥ q(x)`, `q(x) = (A − B/c) + (B/c²)(x − c) − (A/c²)(x − c)² = (A·x − B)(2c − x)/c²`,
  for every real `x`.
* `lip_lower`: if `P ≥ 0` and `P ≥ A − B/V`, `V = X − kk²w/(4X)`, where `X > 0` and `V > 0`,
  then `P ≥ q(X) − A³kk²/(4B²)·w` (`x ↦ max(0, A − B/x)` is Lipschitz with constant `A²/B`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

/-- a global lower parabola for `max(0, A − B/x)`: `q(x) = (A·x − B)(2c − x)/c²` -/
theorem parab_lower {A B c x P : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c) (hBA : B ≤ 2 * A * c)
    (hP0 : 0 ≤ P) (hP : 0 < x → A - B / x ≤ P) :
    (A - B / c) + B / c ^ 2 * (x - c) - A / c ^ 2 * (x - c) ^ 2 ≤ P := by
  have hc2 : 0 < c ^ 2 := by positivity
  have key : (A - B / c) + B / c ^ 2 * (x - c) - A / c ^ 2 * (x - c) ^ 2 =
      (A * x - B) * (2 * c - x) / c ^ 2 := by
    field_simp
    ring
  rw [key]
  have hneg : (A * x - B) * (2 * c - x) ≤ 0 → (A * x - B) * (2 * c - x) / c ^ 2 ≤ P := fun h =>
    (div_nonpos_of_nonpos_of_nonneg h hc2.le).trans hP0
  rcases le_or_gt x 0 with hx | hx
  · apply hneg
    have h1 : A * x - B ≤ 0 := by nlinarith
    have h2 : 0 ≤ 2 * c - x := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg h1 h2
  · rcases le_or_gt B (A * x) with h | h
    · rcases le_or_gt (2 * c - x) 0 with h2 | h2
      · apply hneg
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) h2
      · refine le_trans ?_ (hP hx)
        have e : A - B / x = (A * x - B) / x := by field_simp
        rw [e, div_le_div_iff₀ hc2 hx]
        nlinarith [mul_nonneg (sub_nonneg.2 h) (sq_nonneg (x - c))]
    · apply hneg
      have h2 : 0 ≤ 2 * c - x := by nlinarith
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) h2

/-- the pointwise lower bound: a parabola in `X` minus a multiple of `w` -/
theorem lip_lower {A B c X w kk P : ℝ} (hA : 0 < A) (hB : 0 < B) (hc : 0 < c)
    (hBA : B ≤ 2 * A * c) (hk : 0 < kk) (hX : 0 ≤ X) (hw : 0 ≤ w) (hP0 : 0 ≤ P)
    (hP : 0 < X → 0 < X - kk ^ 2 * w / (4 * X) →
      A - B / (X - kk ^ 2 * w / (4 * X)) ≤ P) :
    (A - B / c) + B / c ^ 2 * (X - c) - A / c ^ 2 * (X - c) ^ 2 -
        A ^ 3 * kk ^ 2 / (4 * B ^ 2) * w ≤ P := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hΛ : 0 ≤ A ^ 3 * kk ^ 2 / (4 * B ^ 2) * w := by positivity
  rcases le_or_gt (A * X) B with hle | hAX
  · -- `X ≤ x0`: the parabola is nonpositive
    have key : (A - B / c) + B / c ^ 2 * (X - c) - A / c ^ 2 * (X - c) ^ 2 =
        (A * X - B) * (2 * c - X) / c ^ 2 := by
      field_simp
      ring
    have h2 : 0 ≤ 2 * c - X := by nlinarith
    have h3 : (A * X - B) * (2 * c - X) / c ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) h2) hc2.le
    rw [key]
    linarith
  · have hXpos : 0 < X := by
      rcases hX.eq_or_lt with h | h
      · rw [← h] at hAX; simp at hAX; linarith
      · exact h
    set a' : ℝ := kk ^ 2 * w / (4 * X) with ha'
    have ha0 : 0 ≤ a' := by positivity
    have hh0 : 0 ≤ A - B / X := by
      rw [sub_nonneg, div_le_iff₀ hXpos]; exact hAX.le
    have h1 : (A - B / c) + B / c ^ 2 * (X - c) - A / c ^ 2 * (X - c) ^ 2 ≤ A - B / X :=
      parab_lower hA hB.le hc hBA hh0 (fun _ => le_rfl)
    have hinv : 1 / X ≤ A / B := by
      rw [div_le_div_iff₀ hXpos hB]; linarith
    have h3 : A ^ 2 / B * a' ≤ A ^ 3 * kk ^ 2 / (4 * B ^ 2) * w := by
      have e1 : A ^ 2 / B * a' = A ^ 2 * kk ^ 2 * w / (4 * B) * (1 / X) := by
        rw [ha']; field_simp
      have e2 : A ^ 3 * kk ^ 2 / (4 * B ^ 2) * w = A ^ 2 * kk ^ 2 * w / (4 * B) * (A / B) := by
        field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have h2 : A - B / X - A ^ 2 / B * a' ≤ P := by
      rcases le_or_gt B (A * (X - a')) with hcase | hcase
      · have hV : 0 < X - a' := by
          by_contra hcon
          have : X - a' ≤ 0 := not_lt.mp hcon
          nlinarith
        have hPV := hP hXpos hV
        have hBB : B * B ≤ (A * X) * (A * (X - a')) := mul_le_mul hAX.le hcase hB.le (by positivity)
        have e0 : B / (X - a') - B / X = B * a' / (X * (X - a')) := by
          field_simp
          ring
        have h4 : B * a' / (X * (X - a')) ≤ A ^ 2 / B * a' := by
          rw [div_le_iff₀ (mul_pos hXpos hV)]
          have e : A ^ 2 / B * a' * (X * (X - a')) = a' / B * ((A * X) * (A * (X - a'))) := by ring
          have e2 : B * a' = a' / B * (B * B) := by field_simp
          rw [e, e2]
          exact mul_le_mul_of_nonneg_left hBB (div_nonneg ha0 hB.le)
        linarith
      · have h5 : A - B / X ≤ A / B * (A * X - B) := by
          have e : A - B / X = (A * X - B) * (1 / X) := by field_simp
          have e2 : A / B * (A * X - B) = (A * X - B) * (A / B) := by ring
          rw [e, e2]
          exact mul_le_mul_of_nonneg_left hinv (by linarith)
        have h6 : A / B * (A * X - B) ≤ A ^ 2 / B * a' := by
          have e : A ^ 2 / B * a' = A / B * (A * a') := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
    linarith

end BstLean.Part144

open BstLean.Part144 in
#print axioms parab_lower
open BstLean.Part144 in
#print axioms lip_lower
