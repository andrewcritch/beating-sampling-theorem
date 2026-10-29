import BstLean.Part292Collected

/-! Order 416 controls the collected coefficients at order 104 on the
same node measure. The proof uses Holder, not node independence. -/
namespace BstLean.Part292
open MeasureTheory Real
open BstLean.Part223 (MomentBound)
open BstLean.Part239

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem collected_coefficient_moments (hmass : μ Set.univ ≤ 1)
    {D V P : X → ℝ} {d v p lo hi σ Γ C sp : ℝ}
    (hD : MomentBound μ 416 D d) (hV : MomentBound μ 416 V v)
    (hP : MomentBound μ 104 P p) (hD0 : ∀ x, 0 ≤ D x) (hV0 : ∀ x, 0 ≤ V x)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hσ : 0 ≤ σ)
    (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hsp : 0 ≤ sp) :
    MomentBound μ 104 (fun x => lowF0 lo hi σ Γ (D x) (V x) (P x)) (lowF0 lo hi σ Γ d v p) ∧
    MomentBound μ 104 (fun x => lowF1 lo hi σ C (D x) (V x) (P x)) (lowF1 lo hi σ C d v p) ∧
    MomentBound μ 104 (fun x => lowF2 hi σ (D x)) (lowF2 hi σ d) ∧
    MomentBound μ 104 (fun x => lowW0 lo hi σ Γ (D x) (V x) (P x)) (lowW0 lo hi σ Γ d v p) ∧
    MomentBound μ 104 (fun x => lowW1 lo hi σ C sp (D x) (V x) (P x)) (lowW1 lo hi σ C sp d v p) ∧
    MomentBound μ 104 (fun x => lowW2 lo hi C (D x) (P x)) (lowW2 lo hi C d p) := by
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  have hD104 := hD.lower (by norm_num : 1 ≤ 104) (by norm_num) hmass
  have hD208 := hD.lower (by norm_num : 1 ≤ 208) (by norm_num) hmass
  have hV104 := hV.lower (by norm_num : 1 ≤ 104) (by norm_num) hmass
  have hD2 := hD208.power (k := 104) (r := 2)
  have hDV := moment_mul104 (hD104.sqrt hD0) (hV104.sqrt hV0)
  have hDD := moment_mul104 (hD104.sqrt hD0) hD208
  have hF0 := ((hD104.scale (by positivity :
    0 ≤ sqrt hi * BstLean.Part153.phiG 0 / (2 * σ))).add (by norm_num)
    (((hV104.scale (by positivity : 0 ≤ (sqrt lo)⁻¹)).add (by norm_num)
      (hD2.scale (sqrt_nonneg hi))).scale (by positivity :
        0 ≤ BstLean.Part153.phiG 0 / (2 * sqrt 2 * σ ^ 3)))).add (by norm_num)
    (hP.scale (by positivity :
      0 ≤ (3 / 2) * BstLean.Part153.phiG 0 * Γ / (σ * sqrt lo * lo ^ 4)))
  have hF1 := (((hDV.add (by norm_num) (hDD.scale (sqrt_nonneg hi))).scale
    (by positivity : 0 ≤ BstLean.Part153.phiG 1 / σ ^ 2))).add (by norm_num)
    (hP.scale (by positivity : 0 ≤ 4 * sqrt 2 * C / lo ^ 4))
  have hF2 := hD104.scale (by positivity :
    0 ≤ sqrt hi * BstLean.Part153.phiG 0 / (sqrt 2 * σ))
  have hW0 := ((hD104.scale hhi).add (by norm_num)
    ((hV104.add (by norm_num) (hD2.scale hhi)).scale
      (by positivity : 0 ≤ BstLean.Part153.phiG 1 / (2 * σ ^ 2)))).add (by norm_num)
    (hP.scale (by positivity : 0 ≤ 4 * Γ / lo ^ 4))
  have hW1 := ((((hDV.scale (sqrt_nonneg hi)).add (by norm_num) (hDD.scale hhi)).scale
    (by positivity : 0 ≤ sqrt 2 * BstLean.Part153.phiG 0 / σ))).add (by norm_num)
    (hP.scale (by positivity : 0 ≤ 4 * sqrt 2 * C * sp / lo ^ 4))
  have hW2 := (hD104.scale hhi).add (by norm_num)
    (hP.scale (by positivity : 0 ≤ 28 * C ^ 2 / lo ^ 4))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hF0 using 1 <;> unfold lowF0 <;> first | (funext x; ring) | ring
  · convert hF1 using 1 <;> unfold lowF1 <;> first | (funext x; ring) | ring
  · exact hF2
  · exact hW0
  · convert hW1 using 1 <;> unfold lowW1 <;> first | (funext x; ring) | ring
  · exact hW2

end BstLean.Part292

/-- info: 'BstLean.Part292.collected_coefficient_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.collected_coefficient_moments
