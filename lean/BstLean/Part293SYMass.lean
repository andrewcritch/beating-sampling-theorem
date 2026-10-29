import BstLean.Part242Mass
import BstLean.Part289Mass

/-! The corrected order-24 exceptional-product argument for an arbitrary positive floor. -/
namespace BstLean.Part293
open MeasureTheory Real Set BstLean.Part242 BstLean.Part289
open scoped ENNReal

theorem biasMoments_of_LBounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {K : Set X} (hKm : (μ.restrict K) univ ≤ 1)
    (n : ℕ) {fb ft wb wt V : X → ℝ} {aw af F24 Cv : ℝ}
    (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (haw : 0 < aw) (haf : 0 < af) (hF24 : 0 < F24) (hCv : 0 < Cv)
    (hW : LBound (μ.restrict K) 8 (fun x => (n : ℝ) * (wb x - wt x)) aw)
    (hF : LBound (μ.restrict K) 8 (fun x => (n : ℝ) * (fb x - ft x)) af)
    (hf : LBound (μ.restrict K) 24 fb F24)
    (hV : LBound (μ.restrict K) 2 (fun x => (n : ℝ) * V x) Cv) :
    BiasMoments μ K n fb ft wb wt V aw af F24 Cv := by
  have W2 := hW.lower (p := 2) (by norm_num) (by norm_num) (by norm_num) hKm
  have W6 := hW.lower (p := 6) (by norm_num) (by norm_num) (by norm_num) hKm
  have F2 := hF.lower (p := 2) (by norm_num) (by norm_num) (by norm_num) hKm
  have F4 := hF.lower (p := 4) (by norm_num) (by norm_num) (by norm_num) hKm
  have f4 := hf.lower (p := 4) (by norm_num) (by norm_num) (by norm_num) hKm
  have fF6 := SY_exceptional_product hf hF
  have fF2 := fF6.lower (p := 2) (by norm_num) (by norm_num) (by norm_num) hKm
  obtain ⟨iw8, bw8⟩ := hW.evenIntegral (by norm_num) (by decide : Even 8)
  obtain ⟨if8, bf8⟩ := hF.evenIntegral (by norm_num) (by decide : Even 8)
  obtain ⟨if24, bf24⟩ := hf.evenIntegral (by norm_num) (by decide : Even 24)
  obtain ⟨if4, bf4⟩ := f4.evenIntegral (by norm_num) (by decide : Even 4)
  obtain ⟨iv2, bv2⟩ := hV.squareIntegral
  refine {
    mfb := mfb, mft := mft, mwb := mwb, mwt := mwt, mV := mV
    haw := haw, haf := haf, hHf := hF24, hCv := hCv
    iW2 := W2.squareIntegral.1
    iW6 := (W6.evenIntegral (by norm_num) (by decide : Even 6)).1
    iW8 := iw8
    iF2 := F2.squareIntegral.1
    iF4 := (F4.evenIntegral (by norm_num) (by decide : Even 4)).1
    iF8 := if8
    if4 := if4, if24 := if24
    ifF2 := ?_, ifF6 := ?_
    iV := iv2, hW8 := bw8, hF8 := bf8, hf4 := bf4, hf24 := bf24, hV := bv2 }
  · simpa only [IntegrableOn, mul_pow] using fF2.squareIntegral.1
  · simpa only [IntegrableOn, mul_pow] using
      (fF6.evenIntegral (by norm_num) (by decide : Even 6)).1

theorem SY_exceptional_mass_floor {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X}
    (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) (hKm : (μ.restrict K) univ ≤ 1)
    (n : ℕ) (hn : 0 < n) {s₀ γ d ε vmax aw af F24 Cv : ℝ}
    (hs₀ : 0 < s₀) (hγ : 0 < γ) (hd : s₀ ≤ d) (haw : 0 < aw) (haf : 0 < af)
    (hF24 : 0 < F24) (hCv : 0 < Cv) (hT : 0 < ε - vmax / d)
    {fb ft wb wt V : X → ℝ}
    (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (hSbd : ∀ x ∈ K, γ * d ≤ γ * (wb x - fb x ^ 2 - V x))
    (hVm : ∀ x ∈ K, |V x| ≤ vmax)
    (hW : LBound (μ.restrict K) 8 (fun x => (n : ℝ) * (wb x - wt x)) aw)
    (hF : LBound (μ.restrict K) 8 (fun x => (n : ℝ) * (fb x - ft x)) af)
    (hf : LBound (μ.restrict K) 24 fb F24)
    (hV : LBound (μ.restrict K) 2 (fun x => (n : ℝ) * V x) Cv) :
    μ.real (K ∩ {x | ε < |γ * max s₀ (wt x - ft x ^ 2) /
      (γ * (wb x - fb x ^ 2 - V x)) - 1|}) ≤
        BstLean.Part241.exceptionalMass n d ε vmax aw af F24 :=
  scale_mass_floor hK hK1 hn hs₀ hγ hd
    (biasMoments_of_LBounds μ hKm n mfb mft mwb mwt mV haw haf hF24 hCv hW hF hf hV)
    hT hSbd hVm

end BstLean.Part293

/-- info: 'BstLean.Part293.SY_exceptional_mass_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.SY_exceptional_mass_floor
