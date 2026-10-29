import BstLean.Part213Rows

/-! The exact centering correction removes the factor two for nonnegative rows. -/
namespace BstLean.Part239
open MeasureTheory ProbabilityTheory Real

lemma pow_add_linear_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    a ^ (n + 2) + (n + 2 : ℕ) * a ^ (n + 1) * b + b ^ (n + 2) ≤
      (a + b) ^ (n + 2) := by
  induction n with
  | zero => norm_num; nlinarith
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (add_nonneg ha hb)
    have hp : 0 ≤ a * b ^ (n + 2) + (n + 2 : ℕ) * a ^ (n + 1) * b ^ 2 := by
      positivity
    push_cast at *
    simp only [pow_succ] at *
    nlinarith

lemma pow_center_lower_left {x u : ℝ} (hx : 0 ≤ x) (hxu : x ≤ u) (n : ℕ) :
    (u - x) ^ (n + 2) ≤
      x ^ (n + 2) - (n + 2 : ℕ) * u ^ (n + 1) * x + (n + 1 : ℕ) * u ^ (n + 2) := by
  have hu : 0 ≤ u := hx.trans hxu
  have hh : 0 ≤ u - x := sub_nonneg.mpr hxu
  induction n with
  | zero => norm_num; nlinarith
  | succ n ih =>
    have hi := mul_le_mul_of_nonneg_left ih hx
    have hpow : (u - x) ^ n ≤ u ^ n := pow_le_pow_left₀ hh (by linarith) n
    have hrem : (u - 2 * x) * (u - x) ^ (n + 2) ≤
        (n + 2 : ℕ) * u ^ (n + 1) * (u - x) ^ 2 := by
      calc
        _ ≤ u * (u - x) ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hh _)
        _ = u * (u - x) ^ n * (u - x) ^ 2 := by rw [pow_add]; ring
        _ ≤ u * u ^ n * (u - x) ^ 2 := by gcongr
        _ ≤ (n + 2 : ℕ) * u ^ (n + 1) * (u - x) ^ 2 := by
          have hn : (1 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
          have hz : 0 ≤ u ^ (n + 1) * (u - x) ^ 2 := by positivity
          calc
            _ = 1 * (u ^ (n + 1) * (u - x) ^ 2) := by rw [pow_succ]; ring
            _ ≤ (n + 2 : ℕ) * (u ^ (n + 1) * (u - x) ^ 2) :=
              mul_le_mul_of_nonneg_right hn hz
            _ = _ := by ring
    push_cast at *
    simp only [pow_succ] at *
    nlinarith

/-- The paper's scalar correction holds at every integer order at least two. -/
theorem centering_pointwise {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (n : ℕ) :
    |x - u| ^ (n + 2) ≤
      x ^ (n + 2) - (n + 2 : ℕ) * u ^ (n + 1) * x + (n + 1 : ℕ) * u ^ (n + 2) := by
  by_cases h : x ≤ u
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    exact pow_center_lower_left hx h n
  · have hux : u ≤ x := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr hux)]
    have hp := pow_add_linear_lower hu (sub_nonneg.mpr hux) n
    rw [add_sub_cancel] at hp
    push_cast at hp ⊢
    rw [pow_succ u (n + 1)] at hp ⊢
    nlinarith

#print axioms centering_pointwise

/-- Integration gives the exact subtraction of the mean power. -/
theorem centering_moment {X : Type*} [MeasurableSpace X]
    (ρ : Measure X) [IsProbabilityMeasure ρ] {f : X → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f ρ) (n : ℕ)
    (hp : Integrable (fun x => f x ^ (n + 2)) ρ)
    (hc : Integrable (fun x => |f x - ∫ y, f y ∂ρ| ^ (n + 2)) ρ) :
    ∫ x, |f x - ∫ y, f y ∂ρ| ^ (n + 2) ∂ρ ≤
      (∫ x, f x ^ (n + 2) ∂ρ) - (∫ x, f x ∂ρ) ^ (n + 2) := by
  let u := ∫ x, f x ∂ρ
  have hu : 0 ≤ u := integral_nonneg hf0
  let c := (n + 2 : ℕ) * u ^ (n + 1)
  let d := (n + 1 : ℕ) * u ^ (n + 2)
  calc
    _ ≤ ∫ x, (f x ^ (n + 2) - c * f x + d) ∂ρ := by
      apply integral_mono hc ((hp.sub (hf.const_mul c)).add (integrable_const d))
      intro x
      exact centering_pointwise (hf0 x) hu n
    _ = _ := by
      have hs : Integrable (fun x => f x ^ (n + 2) - c * f x) ρ := hp.sub (hf.const_mul c)
      rw [integral_add hs (integrable_const d),
        integral_sub hp (hf.const_mul c), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
      dsimp [c, d, u]
      push_cast
      simp only [pow_succ]
      ring

#print axioms centering_moment
end BstLean.Part239
