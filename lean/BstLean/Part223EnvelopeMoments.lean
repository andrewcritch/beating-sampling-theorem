import BstLean.Part223ScalarEnvelope

/-! The single weighted statistics event bounds both deterministic RA prices. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (tA mkR)
open BstLean.Part220

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem envelope_coefficients_moments {n : ℕ} (hn : 10 ≤ n) (hmass : μ univ ≤ 1)
    {Q O Sm SM C : ℝ} (hQ : 0 ≤ Q) (hO : 0 ≤ O) (hSm : 0 ≤ Sm) (hSM : 0 ≤ SM)
    {M : Fin 3 → X → ℝ} (hM0 : ∀ i x, 0 ≤ M i x)
    (hM : ∀ i, MomentBound μ 64 (M i) C) :
    let d := fun x => envelopeData n Q O Sm SM (M 0 x) (M 1 x) (M 2 x)
    let D := envelopeData n Q O Sm SM C C C
    MomentBound μ 16 (fun x => (d x).f0 n O) (D.f0 n O) ∧
    MomentBound μ 16 (fun x => (d x).f1 n O) (D.f1 n O) ∧
    MomentBound μ 16 (fun x => (d x).f2) D.f2 ∧
    MomentBound μ 16 (fun x => (d x).w0 n O) (D.w0 n O) ∧
    MomentBound μ 16 (fun x => (d x).w1 n O) (D.w1 n O) ∧
    MomentBound μ 16 (fun x => (d x).w2 n O) (D.w2 n O) := by
  obtain ⟨ha, hb, he⟩ := envelope_nonneg (O := O) (Sm := Sm) hn hQ
  obtain ⟨hD, hV, hP⟩ := scalar_statistics_moments hmass (hM 0) (hM 1) (hM 2) ha hb he
  have hD16 := hD.lower (by norm_num : 1 ≤ 16) (by norm_num) hmass
  have hV16 := hV.lower (by norm_num : 1 ≤ 16) (by norm_num) hmass
  have ht := tA_nonneg n
  exact row_coefficients_moments (sm := sqrt Sm) (Γ := tA n * O ^ 2 + SM)
    (C := sqrt (tA n) * O) (sp := sqrt SM) hD16 hD16 hV16 hP
    (fun x => mul_nonneg ha (add_nonneg (hM0 0 x) (hM0 1 x)))
    (fun x => add_nonneg (mul_nonneg hb (hM0 2 x)) (sq_nonneg _))
    (sqrt_nonneg Sm) (by positivity) (by positivity) (sqrt_nonneg SM)

theorem envelope_weighted_prices {n : ℕ} [SFinite μ]
    (hn : 10 ≤ n) (hmass : μ univ ≤ 1)
    {Q O Sm SM C : ℝ} (hQ : 0 ≤ Q) (hO : 0 ≤ O) (hSm : 0 ≤ Sm) (hSM : 0 ≤ SM)
    {M : Fin 3 → X → ℝ} (hM0 : ∀ i x, 0 ≤ M i x)
    (hM : ∀ i, MomentBound μ 64 (M i) C) :
    let d := fun x => completeRAData
      (envelopeData n Q O Sm SM (M 0 x) (M 1 x) (M 2 x)) n O
    let D := completeRAData (envelopeData n Q O Sm SM C C C) n O
    (∫⁻ x, ENNReal.ofReal ((d x).locationBound n O) ∂μ) ≤ ENNReal.ofReal (D.locationBound n O) ∧
    (∫⁻ x, ENNReal.ofReal ((d x).energyBound n O) ∂μ) ≤ ENNReal.ofReal (D.energyBound n O) := by
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ :=
    envelope_coefficients_moments hn hmass hQ hO hSm hSM hM0 hM
  exact completeRAData_weighted (by omega) O _ _ hf0 hf1 hf2 hw0 hw1 hw2

/-- The paper event gives both scalar RA prices through integrated moments. -/
theorem paperEvent_RA_prices {n J : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) {Q O Sm SM C : ℝ}
    (hQ : 0 ≤ Q) (hO : 0 ≤ O) (hSm : 0 ≤ Sm) (hSM : 0 ≤ SM) (hC : 0 ≤ C)
    (hOp : OpB A O) (hE : A ∈ paperStatisticsEvent wr ν node C) :
    let d := fun g => completeRAData (envelopeData n Q O Sm SM
      (paperNodeStatistic wr (node g) 0 A) (paperNodeStatistic wr (node g) 1 A)
      (paperNodeStatistic wr (node g) 2 A)) n O
    let D := completeRAData (envelopeData n Q O Sm SM C C C) n O
    (∫⁻ g, ENNReal.ofReal ((d g).locationBound n O) ∂ν) ≤ ENNReal.ofReal (D.locationBound n O) ∧
    (∫⁻ g, ENNReal.ofReal ((d g).energyBound n O) ∂ν) ≤ ENNReal.ofReal (D.energyBound n O) := by
  exact envelope_weighted_prices (n := n) (Q := Q) (O := O) (Sm := Sm) (SM := SM)
    (C := C) (M := fun i g => paperNodeStatistic wr (node g) i A) hn hmass hQ hO hSm hSM
    (fun i g => paperNodeStatistic_nonneg wr (node g) i A)
    (fun i => paperStatistics_momentBound (by omega) wr hc ν node hs A hOp hC hE i)

#print axioms envelope_coefficients_moments
#print axioms envelope_weighted_prices
#print axioms paperEvent_RA_prices
end BstLean.Part223
