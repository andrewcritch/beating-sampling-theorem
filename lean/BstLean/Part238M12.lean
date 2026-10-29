import BstLean.Part238Cover
import BstLean.Part235Core
import BstLean.Part235Wide

/-! Part 238: the core gain certificate on the M1/M2 range, `n ≥ 11883` and `θ ∈ [.46, .528]`,
for the core window `(2.8, 7.5, 3.2)` and overlap cap `.63` (Part 235 core geometry).
It also discharges the radius and centre guards of the sharp covariance transfer. -/
namespace BstLean.Part238
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part157 BstLean.Part160 BstLean.Part182
  BstLean.Part208
open BstLean.Part199 (Window radiusMinus exampleCore exampleWide example_nested OverlapGuard)
open BstLean.Part150 (thetaC rhoC rhoC_sqP)
open BstLean.Part153 (nrm nrm_sq Xi4)

/-- **Core geometry on the M1/M2 range.** For `n ≥ 11883`, a centre `c`, a scale `τ > 0` and
`θ = thetaC c τ ∈ [.46, .528]`, with `a = |c|`: the core radius lower bound is positive,
`2.8 τ ≤ a`, and the integrated tangential gain satisfies `χ₁ ≤ 0.51` at cap `cp = .63`. -/
theorem chi_core_M12 {n : ℕ} (hn : 11883 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθlo : 46 / 100 ≤ thetaC c τ) (hθhi : thetaC c τ ≤ 528 / 1000) :
    0 < axialRadiusLower n (nrm c) τ exampleCore.t exampleCore.z ∧
    τ * exampleCore.t ≤ nrm c ∧
    chiCore n (nrm c) τ exampleCore.t exampleCore.z
      (axialProjLower n (nrm c) τ exampleCore.t exampleCore.z) (63 / 100) ≤ 51 / 100 := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set θ := thetaC c τ with hθd
  set a := nrm c with had
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = normSq c := nrm_sq c
  set q := normSq c + (n : ℝ) * τ ^ 2 with hqd
  have hq0 : 0 < q := by
    have := normSq_nonneg c
    positivity
  have hθq : θ * q = (n : ℝ) * τ ^ 2 := by
    rw [hθd]
    unfold thetaC
    rw [rhoC_sqP, ← hqd]
    field_simp
  have hτ2 : (n : ℝ) * τ ^ 2 ≤ 528 / 1000 * q := by
    rw [← hθq]; exact mul_le_mul_of_nonneg_right hθhi hq0.le
  have ha2q : a ^ 2 = q - θ * q := by rw [hθq, ha2, hqd]; ring
  -- the cross term `a τ`
  have haτ : a * τ ≤ q / 218 := by
    have h1 : (n : ℝ) * (a * τ) ^ 2 = (q - θ * q) * (θ * q) := by
      rw [← ha2q, hθq]; ring
    have h2 : (q - θ * q) * (θ * q) ≤ q ^ 2 / 4 := by
      have e : q ^ 2 / 4 - (q - θ * q) * (θ * q) = q ^ 2 * (θ - 1 / 2) ^ 2 := by ring
      have := mul_nonneg (sq_nonneg q) (sq_nonneg (θ - 1 / 2))
      linarith
    have h4 : 47524 * (a * τ) ^ 2 ≤ q ^ 2 := by
      have h5 := mul_le_mul_of_nonneg_right (show (47524 : ℝ) ≤ 4 * n by linarith)
        (sq_nonneg (a * τ))
      have e : 4 * (n : ℝ) * (a * τ) ^ 2 = 4 * ((n : ℝ) * (a * τ) ^ 2) := by ring
      rw [e, h1] at h5
      linarith
    have h3 : (a * τ) ^ 2 ≤ (q / 218) ^ 2 := by
      have e : (q / 218) ^ 2 = q ^ 2 / 47524 := by ring
      rw [e, le_div_iff₀ (by norm_num)]
      linarith
    have haτ0 : 0 ≤ a * τ := mul_nonneg ha0 hτ.le
    exact (pow_le_pow_iff_left₀ haτ0 (by positivity) two_ne_zero).1 h3
  have haτ0 : 0 ≤ a * τ := mul_nonneg ha0 hτ.le
  -- the square-root term
  set s := √((n : ℝ) * (75 / 10)) with hsd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ≤ 2514 / 100000 * (n : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by positivity)
    nlinarith
  have hτs : τ ^ 2 * s ≤ 1328 / 100000 * q := by
    have h1 : τ ^ 2 * s ≤ τ ^ 2 * (2514 / 100000 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    nlinarith
  have hτ2q : τ ^ 2 ≤ 528 / 1000 * q / 11883 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 11883 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR (sq_nonneg _)
    linarith
  -- the core radius lower bound
  have hRl : 9477 / 10000 * q ≤ axialRadiusLower n a τ exampleCore.t exampleCore.z := by
    unfold axialRadiusLower
    change 9477 / 10000 * q ≤ a ^ 2 + τ ^ 2 * ((n : ℝ) - 2 * s) - 2 * a * τ * (28 / 10)
    have e : a ^ 2 + τ ^ 2 * ((n : ℝ) - 2 * s) - 2 * a * τ * (28 / 10) =
        (q - θ * q) + θ * q - 2 * (τ ^ 2 * s) - 56 / 10 * (a * τ) := by
      rw [← ha2q, hθq]; ring
    rw [e]
    linarith
  have hR : 0 < axialRadiusLower n a τ exampleCore.t exampleCore.z := by
    have : 0 < 9477 / 10000 * q := by positivity
    linarith
  -- the centre guard
  have hat : τ * exampleCore.t ≤ a := by
    change τ * (28 / 10) ≤ a
    have h1 : (τ * (28 / 10)) ^ 2 ≤ a ^ 2 := by
      have : a ^ 2 ≥ 472 / 1000 * q := by
        rw [ha2q]; have := mul_le_mul_of_nonneg_right hθhi hq0.le; linarith
      have e : (τ * (28 / 10)) ^ 2 = 784 / 100 * τ ^ 2 := by ring
      rw [e]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) ha0 two_ne_zero).1 h1
  refine ⟨hR, hat, ?_⟩
  -- upper bound for `s₊`
  set sp := axialPlaneUpper n a τ exampleCore.t exampleCore.z with hspd
  have hsp : sp ≤ (10261 / 10000 - θ) / (9477 / 10000) := by
    rw [hspd]
    unfold axialPlaneUpper
    rw [div_le_div_iff₀ hR (by norm_num)]
    have hnum : (a + τ * exampleCore.t) ^ 2 ≤ (10261 / 10000 - θ) * q := by
      change (a + τ * (28 / 10)) ^ 2 ≤ _
      have e : (a + τ * (28 / 10)) ^ 2 = (q - θ * q) + 56 / 10 * (a * τ) + 784 / 100 * τ ^ 2 := by
        rw [← ha2q]; ring
      rw [e]
      have e2 : (10261 / 10000 - θ) * q = 10261 / 10000 * q - θ * q := by ring
      rw [e2]
      linarith
    have hU0 : 0 ≤ 10261 / 10000 - θ := by linarith
    calc (a + τ * exampleCore.t) ^ 2 * (9477 / 10000)
        ≤ ((10261 / 10000 - θ) * q) * (9477 / 10000) :=
          mul_le_mul_of_nonneg_right hnum (by norm_num)
      _ = (10261 / 10000 - θ) * (9477 / 10000 * q) := by ring
      _ ≤ (10261 / 10000 - θ) * axialRadiusLower n a τ exampleCore.t exampleCore.z :=
          mul_le_mul_of_nonneg_left hRl hU0
  have hsp0 : 0 ≤ sp := by
    rw [hspd]; unfold axialPlaneUpper; exact div_nonneg (sq_nonneg _) hR.le
  -- lower bound for `s₋`
  set sm := axialProjLower n a τ exampleCore.t exampleCore.z with hsmd
  have hsm1 : sm ≤ 1 := axialProjLower_le_one n (by
      rcases ha0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hat; change τ * (28 / 10) ≤ 0 at hat; nlinarith) hτ
    exampleCore.t_nonneg exampleCore.z_nonneg hat
  have hsm : (1 - θ - 257 / 10000) / (1053 / 1000) ≤ sm := by
    rw [hsmd]
    unfold axialProjLower
    change (1 - θ - 257 / 10000) / (1053 / 1000) ≤ (a - τ * (28 / 10)) ^ 2 /
      (a ^ 2 + 2 * a * τ * (28 / 10) + τ ^ 2 * ((n : ℝ) + 2 * s + 2 * (75 / 10)))
    have hDp : a ^ 2 + 2 * a * τ * (28 / 10) + τ ^ 2 * ((n : ℝ) + 2 * s + 2 * (75 / 10)) ≤
        1053 / 1000 * q := by
      have e : a ^ 2 + 2 * a * τ * (28 / 10) + τ ^ 2 * ((n : ℝ) + 2 * s + 2 * (75 / 10)) =
          (q - θ * q) + 56 / 10 * (a * τ) + θ * q + 2 * (τ ^ 2 * s) + 15 * τ ^ 2 := by
        rw [← ha2q, hθq]; ring
      rw [e]
      linarith
    have ha472 : a ^ 2 ≥ 472 / 1000 * q := by
      rw [ha2q]; have := mul_le_mul_of_nonneg_right hθhi hq0.le; linarith
    have hDp0 : 0 < a ^ 2 + 2 * a * τ * (28 / 10) + τ ^ 2 * ((n : ℝ) + 2 * s + 2 * (75 / 10)) := by
      have h1 : 0 ≤ τ ^ 2 * ((n : ℝ) + 2 * s + 2 * (75 / 10)) := by positivity
      have h2 : 0 ≤ 2 * a * τ * (28 / 10) := by positivity
      have h3 : 0 < 472 / 1000 * q := by positivity
      linarith
    have hnum : (1 - θ - 257 / 10000) * q ≤ (a - τ * (28 / 10)) ^ 2 := by
      have e : (a - τ * (28 / 10)) ^ 2 = (q - θ * q) - 56 / 10 * (a * τ) + 784 / 100 * τ ^ 2 := by
        rw [← ha2q]; ring
      rw [e]
      have e2 : (1 - θ - 257 / 10000) * q = q - θ * q - 257 / 10000 * q := by ring
      rw [e2]
      have := sq_nonneg τ
      linarith
    rw [div_le_div_iff₀ (by norm_num) hDp0]
    have hL0 : 0 ≤ 1 - θ - 257 / 10000 := by linarith
    calc (1 - θ - 257 / 10000) *
          (a ^ 2 + 2 * a * τ * (28 / 10) + τ ^ 2 * ((n : ℝ) + 2 * s + 2 * (75 / 10)))
        ≤ (1 - θ - 257 / 10000) * (1053 / 1000 * q) := mul_le_mul_of_nonneg_left hDp hL0
      _ = ((1 - θ - 257 / 10000) * q) * (1053 / 1000) := by ring
      _ ≤ (a - τ * (28 / 10)) ^ 2 * (1053 / 1000) :=
          mul_le_mul_of_nonneg_right hnum (by norm_num)
  -- the gain
  unfold chiCore
  have hd : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hd]
  have hinv : 1 / ((n : ℝ) - 1) ≤ 1 / 11882 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have h1sm : 0 ≤ 1 - sm := by linarith
  have hprod : sp * (1 - sm) ≤ (10261 / 10000 - θ) / (9477 / 10000) *
      (1 - (1 - θ - 257 / 10000) / (1053 / 1000)) :=
    mul_le_mul hsp (by linarith) h1sm (by
      have : 0 ≤ 10261 / 10000 - θ := by linarith
      positivity)
  have hpoly : (10261 / 10000 - θ) / (9477 / 10000) *
      (1 - (1 - θ - 257 / 10000) / (1053 / 1000)) + 1 / 11882 ≤
      51 / 100 * (1 - (63 / 100) ^ 2) := by
    nlinarith [sq_nonneg (θ - 4737 / 10000)]
  rw [div_le_iff₀ (by norm_num)]
  linarith

end BstLean.Part238
