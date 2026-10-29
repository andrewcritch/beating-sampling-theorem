import BstLean.Part213NetworkRA
import BstLean.Part213Price

/-! The actual node RA16 bounds use the paper factors at every positive
integer dimension. Statistics and top-order row moments remain inputs. -/
namespace BstLean.Part213
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (biasF biasW tA)
open BstLean.Part186.RA
variable {n : ℕ}

/-- The location correction uses the exact paper factor without a price premise. -/
theorem conditional_location_RA16_paper (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA1 : 0 ≤ AF1 √Smin Dm Vm Pm (√(tA n) * O)) (hA2 : 0 ≤ AF2 √Smin Dm)
    {A16 : ℝ} (h16 : 0 ≤ A16)
    (hM : ∫ p, radiusPolynomial (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm) p ^ 16 ∂ρ2 ≤ A16 ^ 16) :
    ∫⁻ y, ENNReal.ofReal
      (biasF c g (fun j => (y j).1) (fun j => (y j).2) ^ 16)
        ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ≤
      ENNReal.ofReal ((n : ℝ) ^ 8 * (mA n : ℝ) ^ 8 *
        (collectedSecond (AF0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AF1 √Smin Dm Vm Pm (√(tA n) * O)) (AF2 √Smin Dm) + (locationR16 n) * A16 ^ 2) ^ 8) := by
  exact conditional_location_RA16 hn c g hs hO h1 hSm H hA0 hA1 hA2 h16
    (by unfold locationR16; positivity) hM (location_price_network hn).le

/-- The energy correction uses the exact paper factor without a price premise. -/
theorem conditional_energy_RA16_paper (hn : 1 ≤ n) (c : Ret n) (g : ℕ) (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ}
    (hO : 0 ≤ O) (h1 : OpB (A1 c) O) {Smin Smax Dm Hm Vm Pm : ℝ} (hSm : 0 < Smin)
    (H : NodeStat c g Smin Smax Dm Hm Vm Pm)
    (hA0 : 0 ≤ AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm)
    (hA2 : 0 ≤ AW2 Dm Pm (√(tA n) * O))
    (hA1 : 0 ≤ AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O))
    {A16 : ℝ} (h16 : 0 ≤ A16)
    (hM : ∫ p, radiusPolynomial (AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) (AW2 Dm Pm (√(tA n) * O)) p ^ 16 ∂ρ2 ≤ A16 ^ 16) :
    ∫⁻ y, ENNReal.ofReal
      (biasW c g (fun j => (y j).1) (fun j => (y j).2) ^ 16)
        ∂(Measure.pi fun _ : Fin (mA n) => ρ2) ≤
      ENNReal.ofReal ((mA n : ℝ) ^ 16 *
        ((AW0 √Smin (tA n * O ^ 2 + Smax) Hm Vm Pm) + (AW1 √Smin √Smax Dm Vm Pm (√(tA n) * O)) * √(π / 2) + 2 * (AW2 Dm Pm (√(tA n) * O)) + (energyR16 n) * A16) ^ 16) := by
  exact conditional_energy_RA16 hn c g hs hO h1 hSm H hA0 hA2 hA1 h16
    (by unfold energyR16; positivity) hM (energy_price_network hn).le

#print axioms conditional_location_RA16_paper
#print axioms conditional_energy_RA16_paper
end BstLean.Part213

