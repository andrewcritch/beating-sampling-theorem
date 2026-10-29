import BstLean.Part228Chernoff
import BstLean.Part197Log
import BstLean.Part193Cover

/-! Analytic exponents and deterministic block transfer for latitude tails. -/
namespace BstLean.Part228
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part161 (Ix muI)
open BstLean.Part157 (latitude)
open BstLean.Part193

noncomputable def chernoffExponent (n : ℕ) (a τ b t : ℝ) : ℝ :=
  t * a ^ 2 / (1 - 2 * t * τ ^ 2) - log (1 - 2 * t * τ ^ 2) / 2 -
    ((n - 1 : ℕ) : ℝ) * log (1 + 2 * t * endpointRatio b * τ ^ 2) / 2

theorem chernoffMajorant_eq_exp (n : ℕ) {a τ b t : ℝ}
    (hax : 0 < 1 - 2 * t * τ ^ 2)
    (htr : 0 < 1 + 2 * t * endpointRatio b * τ ^ 2) :
    chernoffMajorant n a τ b t = exp (chernoffExponent n a τ b t) := by
  have he (x : ℝ) (hx : 0 < x) : (√x)⁻¹ = exp (-(log x / 2)) := by
    rw [exp_neg, exp_half, exp_log hx]
  unfold chernoffMajorant chernoffExponent
  rw [he _ hax, he _ htr, ← exp_nat_mul, ← exp_add, ← exp_add]
  congr 1
  ring

/-- The installed logarithm remainder supplies either side of the exponent. -/
theorem chernoffExponent_enclosure (n : ℕ) {a τ b t Lax Uax Ltr Utr : ℝ}
    (ha : Lax ≤ log (1 - 2 * t * τ ^ 2))
    (ha' : log (1 - 2 * t * τ ^ 2) ≤ Uax)
    (hr : Ltr ≤ log (1 + 2 * t * endpointRatio b * τ ^ 2))
    (hr' : log (1 + 2 * t * endpointRatio b * τ ^ 2) ≤ Utr) :
    t * a ^ 2 / (1 - 2 * t * τ ^ 2) - Uax / 2 - ((n - 1 : ℕ) : ℝ) * Utr / 2 ≤
      chernoffExponent n a τ b t ∧
    chernoffExponent n a τ b t ≤
      t * a ^ 2 / (1 - 2 * t * τ ^ 2) - Lax / 2 - ((n - 1 : ℕ) : ℝ) * Ltr / 2 := by
  have h1 := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (n - 1) : (0 : ℝ) ≤ _)
  have h2 := mul_le_mul_of_nonneg_left hr' (Nat.cast_nonneg (n - 1) : (0 : ℝ) ≤ _)
  unfold chernoffExponent
  constructor <;> linarith

theorem chernoffMajorant_le_exp (n : ℕ) {a τ b t E : ℝ}
    (hax : 0 < 1 - 2 * t * τ ^ 2)
    (htr : 0 < 1 + 2 * t * endpointRatio b * τ ^ 2)
    (he : chernoffExponent n a τ b t ≤ E) : chernoffMajorant n a τ b t ≤ exp E := by
  rw [chernoffMajorant_eq_exp n hax htr]
  exact exp_le_exp.mpr he

/-- All frontier dimensions have positive deviation-six endpoints below one. -/
theorem normalized_bulk_frontier {n : ℕ} (hn : 4096 ≤ n) {θ : ℝ}
    (hθl : 46 / 100 ≤ θ) (hθu : θ ≤ 54 / 100) :
    0 < √(1 - θ) - 6 * √(θ / n) ∧
      √(1 - θ) - 6 * √(θ / n) < √(1 - θ) + 6 * √(θ / n) ∧
      √(1 - θ) + 6 * √(θ / n) < 1 := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0 : 0 < θ := by linarith
  have haL : (3 / 5 : ℝ) ≤ √(1 - θ) := le_sqrt_of_sq_le (by nlinarith)
  have haU : √(1 - θ) ≤ (4 / 5 : ℝ) := sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hs : √(θ / n) ≤ (1 / 80 : ℝ) := by
    apply sqrt_le_iff.mpr
    constructor
    · norm_num
    · rw [div_le_iff₀ hn0]
      nlinarith
  have hs0 : 0 < √(θ / n) := sqrt_pos.mpr (div_pos hθ0 hn0)
  constructor
  · linarith
  · constructor <;> linarith

theorem latitude_tail_root (n : ℕ) {a τ lo hi tl tu : ℝ}
    (ha : 0 ≤ a) (hτ : 0 < τ) (hlo : 0 < lo) (hlo1 : lo < 1)
    (hhi : 0 < hi) (hhi1 : hi < 1) (htl : tl ≤ 0) (htu : 0 ≤ tu)
    (hlax : 0 < 1 - 2 * tl * τ ^ 2)
    (hltr : 0 < 1 + 2 * tl * endpointRatio lo * τ ^ 2)
    (huax : 0 < 1 - 2 * tu * τ ^ 2)
    (hutr : 0 < 1 + 2 * tu * endpointRatio hi * τ ^ 2) :
    √(2 * (muI n).real {p | latitude a τ p ∉ Icc lo hi}) ≤
      latitudeTailRoot n a τ lo hi tl tu := by
  apply sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left
    (latitude_interval_tail n ha hτ hlo hlo1 hhi hhi1 htl htu hlax hltr huax hutr)
    (by norm_num)

/-- A block selects tilt parameters and bounds both exponents.
Its root contains the actual axial price and both actual exponent bounds. -/
structure LatitudeBlock (n : ℕ) (a τ lo hi : ℝ) where
  lowerTilt : ℝ
  upperTilt : ℝ
  lowerExponent : ℝ
  upperExponent : ℝ
  centre_nonneg : 0 ≤ a
  tau_pos : 0 < τ
  lower_pos : 0 < lo
  lower_lt_one : lo < 1
  upper_pos : 0 < hi
  upper_lt_one : hi < 1
  lower_tilt : lowerTilt ≤ 0
  upper_tilt : 0 ≤ upperTilt
  lower_axial : 0 < 1 - 2 * lowerTilt * τ ^ 2
  lower_transverse : 0 < 1 + 2 * lowerTilt * endpointRatio lo * τ ^ 2
  upper_axial : 0 < 1 - 2 * upperTilt * τ ^ 2
  upper_transverse : 0 < 1 + 2 * upperTilt * endpointRatio hi * τ ^ 2
  lower_bound : chernoffExponent n a τ lo lowerTilt ≤ lowerExponent
  upper_bound : chernoffExponent n a τ hi upperTilt ≤ upperExponent

noncomputable def LatitudeBlock.mass {n : ℕ} {a τ lo hi : ℝ}
    (B : LatitudeBlock n a τ lo hi) : ℝ :=
  exp (-(a ^ 2 / (2 * τ ^ 2))) + exp B.lowerExponent + exp B.upperExponent

noncomputable def LatitudeBlock.root {n : ℕ} {a τ lo hi : ℝ}
    (B : LatitudeBlock n a τ lo hi) : ℝ := √(2 * B.mass)

theorem LatitudeBlock.mass_bound {n : ℕ} {a τ lo hi : ℝ}
    (B : LatitudeBlock n a τ lo hi) :
    (muI n).real {p | latitude a τ p ∉ Icc lo hi} ≤ B.mass := by
  have h := latitude_interval_tail n B.centre_nonneg B.tau_pos B.lower_pos B.lower_lt_one
    B.upper_pos B.upper_lt_one B.lower_tilt B.upper_tilt B.lower_axial B.lower_transverse
    B.upper_axial B.upper_transverse
  exact h.trans (add_le_add (add_le_add le_rfl
    (chernoffMajorant_le_exp n B.lower_axial B.lower_transverse B.lower_bound))
    (chernoffMajorant_le_exp n B.upper_axial B.upper_transverse B.upper_bound))

theorem LatitudeBlock.root_bound {n : ℕ} {a τ lo hi : ℝ}
    (B : LatitudeBlock n a τ lo hi) :
    √(2 * (muI n).real {p | latitude a τ p ∉ Icc lo hi}) ≤ B.root :=
  sqrt_le_sqrt (mul_le_mul_of_nonneg_left B.mass_bound (by norm_num))

/-- The deterministic cover selects one block. Its proof adds no cell payment. -/
theorem latitude_blocks_cover {α ι : Type*} {domain : Set α}
    (C : FiniteCover α ι domain) (n : α → ℕ) (a τ lo hi : α → ℝ) (R : ι → ℝ)
    (h : ∀ i ∈ C.indices, ∀ x ∈ domain, x ∈ C.cell i →
      ∃ B : LatitudeBlock (n x) (a x) (τ x) (lo x) (hi x), B.root ≤ R i) :
    ∀ x ∈ domain, ∃ i ∈ C.indices,
      √(2 * (muI (n x)).real {p | latitude (a x) (τ x) p ∉ Icc (lo x) (hi x)}) ≤ R i := by
  intro x hx
  obtain ⟨i, hi', hxi⟩ := C.covers x hx
  obtain ⟨B, hB⟩ := h i hi' x hx hxi
  exact ⟨i, hi', B.root_bound.trans hB⟩

end BstLean.Part228
