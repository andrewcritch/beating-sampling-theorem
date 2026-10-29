import BstLean.Part242Integral
import BstLean.Part169Scale
import BstLean.Part241Price

/-! FB24 supplies the corrected exceptional product at orders 24 and 8. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

theorem SY_exceptional_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X}
    (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (hKm : (μ.restrict K) univ ≤ 1)
    (n : ℕ) (hn : 0 < n) {γ d ε vmax aw af F24 : ℝ}
    (hγ : 0 < γ) (hd : 1 / 5 ≤ d) (haw : 0 < aw) (haf : 0 < af)
    (hF24 : 0 < F24) (hT : 0 < ε - vmax / d)
    {fb ft wb wt V : X → ℝ}
    (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb) (mwt : Measurable wt)
    (hSbd : ∀ x ∈ K, γ * d ≤ γ * (wb x - fb x ^ 2 - V x))
    (hVm : ∀ x ∈ K, |V x| ≤ vmax)
    (hW : LBound (μ.restrict K) 8 (fun x => (n : ℝ) * (wb x - wt x)) aw)
    (hF : LBound (μ.restrict K) 8 (fun x => (n : ℝ) * (fb x - ft x)) af)
    (hf : LBound (μ.restrict K) 24 fb F24) :
    μ.real (K ∩ {x | ε < |γ * max (1 / 5) (wt x - ft x ^ 2) /
      (γ * (wb x - fb x ^ 2 - V x)) - 1|}) ≤
        BstLean.Part241.exceptionalMass n d ε vmax aw af F24 := by
  obtain ⟨iW8, bW8⟩ := hW.evenIntegral (by norm_num) (by decide : Even 8)
  obtain ⟨iF8, bF8⟩ := hF.evenIntegral (by norm_num) (by decide : Even 8)
  obtain ⟨if24, bf24⟩ := hf.evenIntegral (by norm_num) (by decide : Even 24)
  have hW6 := hW.lower (by norm_num) (by norm_num) (by norm_num : (6 : ℝ≥0∞) ≤ 8) hKm
  have iW6 := (hW6.evenIntegral (by norm_num) (by decide : Even 6)).1
  have hprod := SY_exceptional_product hf hF
  have iP := (hprod.evenIntegral (by norm_num) (by decide : Even 6)).1
  have ifF : IntegrableOn
      (fun x => fb x ^ 6 * ((n : ℝ) * (fb x - ft x)) ^ 6) K μ := by
    simpa only [IntegrableOn, mul_pow] using iP
  exact BstLean.Part169.scale_mass hK hK1 n hn hγ hd haw haf hF24 hT
    mfb mft mwb mwt hSbd hVm iW6 iW8 iF8 if24 ifF bW8 bF8 bf24

end BstLean.Part242
