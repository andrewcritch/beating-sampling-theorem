import BstLean.Part216NetworkLocation
import BstLean.Part216Constants

/-! The actual location pass has one weighted order24 moment. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170

variable {n : ℕ}
variable {G : Type*} [MeasurableSpace G]

/-- Weighted node integration uses the same first-layer data and the same transverse array.
The location order24 supply reads the latitude order12 bound only once. -/
theorem network_location24_weighted (hn : 3 ≤ n) (c : Ret n) (ν : Measure G) (node : G → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O H : ℝ} (hO : 0 ≤ O)
    (h1 : OpB (A1 c) O) (hH : 0 ≤ H)
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS c (node g) ^ 2) ^ 12) ∂ν ≤ ENNReal.ofReal (H ^ 12)) :
    ∫⁻ g, ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N, ENNReal.ofReal (|locationPassFluct c (node g) ξ₁ ξ₂ N| ^ 24)
      ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) ∂ν ≤
      ENNReal.ofReal ((k24 * (sqrt (n : ℝ) *
        sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) / 2) * sqrt H) ^ 24) := by
  let L := sqrt (n : ℝ) * sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) / 2
  let C := k24 * L
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := mul_nonneg k24_nonneg hL
  have hq : ∀ g, 0 ≤ 1 - nodeS c (node g) ^ 2 := fun g => sub_nonneg.mpr (hs g)
  have hfactor : ∀ q : ℝ, 0 ≤ q → sqrt (n : ℝ) *
      sqrt (tA n * (q * O ^ 2 / ((n : ℝ) - 2))) / 2 = L * sqrt q := by
    intro q hq0
    rw [show tA n * (q * O ^ 2 / ((n : ℝ) - 2)) =
      q * (tA n * (O ^ 2 / ((n : ℝ) - 2))) by ring, sqrt_mul hq0]
    dsimp [L]
    ring
  have hnode : ∀ g, (∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N,
      ENNReal.ofReal (|locationPassFluct c (node g) ξ₁ ξ₂ N| ^ 24)
        ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n))) ≤
        ENNReal.ofReal ((C * sqrt (1 - nodeS c (node g) ^ 2)) ^ 24) := by
    intro g
    have h := network_location24_planes hn c (node g) (hs g) hO h1 (hq g) le_rfl
    rw [hfactor _ (hq g)] at h
    have heq : 2 * (L * sqrt (1 - nodeS c (node g) ^ 2)) ^ 24 *
        (2 ^ 12 * ((12 : ℕ).factorial : ℝ)) = (C * sqrt (1 - nodeS c (node g) ^ 2)) ^ 24 := by
      dsimp [C]
      simp only [mul_pow, k24_pow]
      ring
    rw [heq] at h
    exact h
  have hpow : ∀ x : ℝ, 0 ≤ x → (C * sqrt x) ^ 24 = C ^ 24 * x ^ 12 := by
    intro x hx
    rw [mul_pow, show (24 : ℕ) = 2 * 12 by rfl]
    simp only [pow_mul, sq_sqrt hx]
  refine (lintegral_mono hnode).trans ?_
  simp_rw [hpow _ (hq _), ENNReal.ofReal_mul (pow_nonneg hC 24)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl h12).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (pow_nonneg hC 24), ← hpow H hH]

#print axioms network_location24_weighted
end BstLean.Part216
