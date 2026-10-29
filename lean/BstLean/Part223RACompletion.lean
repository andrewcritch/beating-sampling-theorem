import BstLean.Part223WeightedRA

/-! Complete scalar data with exact row moments and integrate the resulting RA prices. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part220
open BstLean.Part213

noncomputable def completeRAData (d : RAData) (n : ℕ) (O : ℝ) : RAData :=
  { d with
    topF := radiusPolynomialRoot16 (d.f0 n O) (d.f1 n O) d.f2
    topW := radiusPolynomialRoot16 (d.w0 n O) (d.w1 n O) (d.w2 n O) }

theorem completeRAData_supply {n : ℕ} (c : Ret n) (g : ℕ) {O : ℝ}
    (hO : 0 ≤ O) (d : RAData) (hmin : 0 < d.Smin)
    (h : NodeStat c g d.Smin d.Smax d.D d.H d.V d.P) :
    NodeRASupply c g O (completeRAData d n O) := by
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := RAData_coefficients_nonneg c g hO d h
  exact ⟨hmin, h, hf0, hf1, hf2, hw0, hw1, hw2,
    radiusPolynomialRoot16_nonneg _ _ _, radiusPolynomialRoot16_nonneg _ _ _,
    (radiusPolynomialRoot16_pow _ _ _).symm.le,
    (radiusPolynomialRoot16_pow _ _ _).symm.le⟩

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem completeRAData_weighted {n : ℕ} (hn : 1 ≤ n) (O : ℝ)
    (d : X → RAData) (D : RAData)
    (hf0 : MomentBound μ 16 (fun x => (d x).f0 n O) (D.f0 n O))
    (hf1 : MomentBound μ 16 (fun x => (d x).f1 n O) (D.f1 n O))
    (hf2 : MomentBound μ 16 (fun x => (d x).f2) D.f2)
    (hw0 : MomentBound μ 16 (fun x => (d x).w0 n O) (D.w0 n O))
    (hw1 : MomentBound μ 16 (fun x => (d x).w1 n O) (D.w1 n O))
    (hw2 : MomentBound μ 16 (fun x => (d x).w2 n O) (D.w2 n O)) :
    (∫⁻ x, ENNReal.ofReal ((completeRAData (d x) n O).locationBound n O) ∂μ) ≤
      ENNReal.ofReal ((completeRAData D n O).locationBound n O) ∧
    (∫⁻ x, ENNReal.ofReal ((completeRAData (d x) n O).energyBound n O) ∂μ) ≤
      ENNReal.ofReal ((completeRAData D n O).energyBound n O) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrF : 0 ≤ locationR16 n := by unfold locationR16; positivity
  have hrW : 0 ≤ energyR16 n := by unfold energyR16; positivity
  exact ⟨integrated_location_price hf0 hf1 hf2 hrF (by positivity),
    integrated_energy_price hw0 hw1 hw2 hrW (by positivity)⟩

#print axioms completeRAData_supply
#print axioms completeRAData_weighted
end BstLean.Part223
