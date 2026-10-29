import BstLean.Part213Taylor
import BstLean.Part213Sharp
import BstLean.Part213CollectedMoment

/-! Conditional network node RA16 on the complete plane-row product.
Retained World data and the first Agent layer stay fixed. These theorems
add no event restriction to the row product and no probability charge. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (biasF biasW tA)
open BstLean.Part186.RA
variable {n : ℕ}

/-- The actual location node uses the exact collected second moment. -/
theorem conditional_location_RA16 (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AF2 √Smin Dm)
    {A16 r : ℝ} (h16 : 0 ≤ A16) (hr : 0 ≤ r)
    (hM : ∫ p, radiusPolynomial (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm) p ^ 16 ∂ρ2 ≤ A16 ^ 16)
    (hprice : 715 * (mA n : ℝ) ^ 4 * 2 ^ 8 ≤ ((mA n : ℝ) * r) ^ 8) :
    ∫⁻ y, ENNReal.ofReal
      (biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 16)
        ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ≤
      ENNReal.ofReal ((n : ℝ) ^ 8 * (mA n : ℝ) ^ 8 *
        (collectedSecond (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm) + r * A16 ^ 2) ^ 8) := by
  let a0 := AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  let a1 := AF1 √Smin Dm Vm Pm (√(tA n) * O)
  let a2 := AF2 √Smin Dm
  have ha0 : 0 ≤ a0 := hA0
  have ha1 : 0 ≤ a1 := hA1
  have ha2 : 0 ≤ a2 := hA2
  let β := radiusPolynomial a0 a1 a2
  let C2 := collectedSecond a0 a1 a2
  have hC2 : 0 ≤ C2 := by
    change 0 ≤ collectedSecond a0 a1 a2
    rw [← (radius_polynomial_second a0 a1 a2).2]
    exact integral_nonneg fun p => sq_nonneg _
  have hm : 1 ≤ mA n := by
    unfold mA
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 1) hn 2
  have hβ : Measurable β := by unfold β radiusPolynomial planeRadius RR; fun_prop
  have hβ0 : ∀ p, 0 ≤ β p := by
    intro p
    dsimp [β, radiusPolynomial]
    have hR : 0 ≤ planeRadius p := sqrt_nonneg _
    positivity
  have hsecond : ∫ p, β p ^ 2 ∂ρ2 = (√C2) ^ 2 := by
    rw [sq_sqrt hC2]
    exact (radius_polynomial_second a0 a1 a2).2
  have hpoint : ∀ y : Fin (mA n) → ℝ × ℝ,
      biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 16 ≤
        (n : ℝ) ^ 8 * (∑ j, β (y j) ^ 2) ^ 8 := by
    intro y
    have h := node_location_polynomial hn c g hs hO h1 hSm H
      (fun j => (y j).1) (fun j => (y j).2) hA0 hA1 hA2
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 8) h 2
    convert hh using 1 <;>
      (try simp only [β, radiusPolynomial, planeRadius, RR, rhoJ, a0, a1, a2]) <;> ring
  have h := location_RA16_from_rows hm hβ hβ0
    (radius_polynomial_power a0 a1 a2 16).1 (Nat.cast_nonneg n) (sqrt_nonneg C2)
    h16 hr hsecond hM hprice hpoint
  simpa only [sq_sqrt hC2] using h

/-- The actual energy node uses the exact radius-polynomial mean. -/
theorem conditional_energy_RA16 (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA2 : 0 ≤ AW2 Dm Pm (√(tA n) * O))
    (hA1 : 0 ≤ AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
    {A16 r : ℝ} (h16 : 0 ≤ A16) (hr : 0 ≤ r)
    (hM : ∫ p, radiusPolynomial (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) (AW2 Dm Pm (√(tA n) * O)) p ^ 16 ∂ρ2 ≤ A16 ^ 16)
    (hprice : 1216070380 * (mA n : ℝ) ^ 8 * 2 ^ 16 ≤ ((mA n : ℝ) * r) ^ 16) :
    ∫⁻ y, ENNReal.ofReal
      (biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 16)
        ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ≤
      ENNReal.ofReal ((mA n : ℝ) ^ 16 *
        ((AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) + (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) * √(π / 2) + 2 * (AW2 Dm Pm (√(tA n) * O)) + r * A16) ^ 16) := by
  let a0 := AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm
  let a1 := AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)
  let a2 := AW2 Dm Pm (√(tA n) * O)
  have ha0 : 0 ≤ a0 := hA0
  have ha1 : 0 ≤ a1 := hA1
  have ha2 : 0 ≤ a2 := hA2
  let β := radiusPolynomial a0 a1 a2
  let A1 := a0 + a1 * √(π / 2) + 2 * a2
  have hm : 1 ≤ mA n := by
    unfold mA
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 1) hn 2
  have hβ : Measurable β := by unfold β radiusPolynomial planeRadius RR; fun_prop
  have hβ0 : ∀ p, 0 ≤ β p := by
    intro p
    dsimp [β, radiusPolynomial]
    have hR : 0 ≤ planeRadius p := sqrt_nonneg _
    positivity
  have hA : 0 ≤ A1 := by dsimp [A1]; positivity
  have hfirst : ∫ p, β p ∂ρ2 = A1 := (radius_polynomial_mean a0 a1 a2).2
  have hpoint : ∀ y : Fin (mA n) → ℝ × ℝ,
      biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 16 ≤
        (∑ j, β (y j)) ^ 16 := by
    intro y
    have h := node_energy_polynomial hn c g hs hO h1 hSm H
      (fun j => (y j).1) (fun j => (y j).2) hA1
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 8) h 2
    convert hh using 1 <;>
      (try simp only [β, radiusPolynomial, planeRadius, RR, rhoJ, a0, a1, a2]) <;> ring
  exact energy_RA16_from_rows hm hβ hβ0 (radius_polynomial_power a0 a1 a2 16).1
    hA h16 hr hfirst hM hprice hpoint

#print axioms conditional_location_RA16
#print axioms conditional_energy_RA16
end BstLean.Part213
