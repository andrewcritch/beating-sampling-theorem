import BstLean.Part223MomentBounds
import BstLean.Part223StatisticNorm

/-! The weighted statistics event supplies integrated scalar bounds. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (mkR)

theorem paperStatistics_momentBound {n J : ℕ} (hn : 1 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {O C : ℝ} (hOp : OpB A O) (hC : 0 ≤ C)
    (hE : A ∈ paperStatisticsEvent wr ν node C) (i : Fin 3) :
    MomentBound ν 64 (fun g => paperNodeStatistic wr (node g) i A) C := by
  refine ⟨measurable_of_countable _, hC, ?_⟩
  simpa only [abs_of_nonneg (paperNodeStatistic_nonneg _ _ _ _)] using
    paperStatisticsEvent_real hn wr hc ν node hs A hOp hE i

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem scalar_statistics_moments (hmass : μ univ ≤ 1)
    {M₁ M₂ M₃ : X → ℝ} {C a b e : ℝ}
    (h1 : MomentBound μ 64 M₁ C) (h2 : MomentBound μ 64 M₂ C)
    (h3 : MomentBound μ 64 M₃ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) :
    MomentBound μ 64 (fun x => a * (M₁ x + M₂ x)) (a * (C + C)) ∧
    MomentBound μ 32 (fun x => b * M₃ x + (a * (M₁ x + M₂ x)) ^ 2)
      (b * C + (a * (C + C)) ^ 2) ∧
    MomentBound μ 16 (fun x => e * M₃ x ^ 4) (e * C ^ 4) := by
  have hD := (h1.add (by norm_num) h2).scale ha
  have hV := ((h3.lower (by norm_num : 1 ≤ 32) (by norm_num) hmass).scale hb).add
    (by norm_num) (hD.power (k := 32) (r := 2))
  exact ⟨hD, hV, (h3.power (k := 16) (r := 4)).scale he⟩

theorem scalar_root_product {D V : X → ℝ} {d v : ℝ}
    (hD : MomentBound μ 16 D d) (hV : MomentBound μ 16 V v)
    (hD0 : ∀ x, 0 ≤ D x) (hV0 : ∀ x, 0 ≤ V x) :
    MomentBound μ 16 (fun x => sqrt (D x) * sqrt (V x)) (sqrt d * sqrt v) :=
  (hD.sqrt hD0).mul16 (hV.sqrt hV0)

/-- The installed row coefficients preserve the integrated statistics bounds. -/
theorem row_coefficients_moments {D H V P : X → ℝ} {d h v p sm Γ C sp : ℝ}
    (hD : MomentBound μ 16 D d) (hH : MomentBound μ 16 H h)
    (hV : MomentBound μ 16 V v) (hP : MomentBound μ 16 P p)
    (hD0 : ∀ x, 0 ≤ D x) (hV0 : ∀ x, 0 ≤ V x)
    (hsm : 0 ≤ sm) (hΓ : 0 ≤ Γ) (hC : 0 ≤ C) (hsp : 0 ≤ sp) :
    MomentBound μ 16 (fun x => AF0 sm Γ (H x) (V x) (P x)) (AF0 sm Γ h v p) ∧
    MomentBound μ 16 (fun x => AF1 sm (D x) (V x) (P x) C) (AF1 sm d v p C) ∧
    MomentBound μ 16 (fun x => AF2 sm (D x)) (AF2 sm d) ∧
    MomentBound μ 16 (fun x => AW0 sm Γ (H x) (V x) (P x)) (AW0 sm Γ h v p) ∧
    MomentBound μ 16 (fun x => AW1 sm sp (D x) (V x) (P x) C) (AW1 sm sp d v p C) ∧
    MomentBound μ 16 (fun x => AW2 (D x) (P x) C) (AW2 d p C) := by
  have hp0 := (BstLean.Part153.phiG_pos 0).le
  have hp1 := (BstLean.Part153.phiG_pos 1).le
  have hroot := scalar_root_product hD hV hD0 hV0
  have h0 := ((hH.scale (by positivity : 0 ≤ BstLean.Part153.phiG 0 / (2 * sm))).add
    (by norm_num) (hV.scale (by positivity :
      0 ≤ (1 / 2 : ℝ) * (BstLean.Part153.phiG 0 / (sqrt 2 * sm ^ 3))))).add
        (by norm_num) (hP.scale (by positivity :
          0 ≤ (3 / 2 : ℝ) * BstLean.Part153.phiG 0 / sm * Γ))
  have h1 := (hroot.scale (by positivity :
      0 ≤ (1 / 2 : ℝ) * (2 * BstLean.Part153.phiG 1 / sm ^ 2))).add
    (by norm_num) (hP.scale (by positivity : 0 ≤ 2 * (2 * sqrt 2 * C)))
  have h2 := hD.scale (by positivity :
    0 ≤ (1 / 2 : ℝ) * (sqrt 2 * BstLean.Part153.phiG 0 / sm))
  have hw0 := (hH.add (by norm_num)
    (hV.scale (by positivity : 0 ≤ BstLean.Part153.phiG 1 / (2 * sm ^ 2)))).add
      (by norm_num) (hP.scale (by positivity : 0 ≤ 4 * Γ))
  have hw1 := (hroot.scale (by positivity : 0 ≤ sqrt 2 * BstLean.Part153.phiG 0 / sm)).add
    (by norm_num) (hP.scale (by positivity : 0 ≤ 4 * sqrt 2 * C * sp))
  have hw2 := hD.add (by norm_num) (hP.scale (by positivity : 0 ≤ 28 * C ^ 2))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert h0 using 1 <;> unfold AF0 <;> first | (funext x; ring) | ring
  · convert h1 using 1 <;> unfold AF1 <;> first | (funext x; ring) | ring
  · convert h2 using 1 <;> unfold AF2 <;> first | (funext x; ring) | ring
  · convert hw0 using 1 <;> unfold AW0 <;> first | (funext x; ring) | ring
  · convert hw1 using 1 <;> unfold AW1 <;> first | (funext x; ring) | ring
  · convert hw2 using 1 <;> unfold AW2 <;> first | (funext x; ring) | ring

#print axioms paperStatistics_momentBound
#print axioms scalar_statistics_moments
#print axioms row_coefficients_moments
end BstLean.Part223
