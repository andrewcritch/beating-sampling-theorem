import BstLean.Part223RACompletion

/-! A fixed latitude cap gives scalar envelopes before weighted integration. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (tA mkR)
open BstLean.Part220

noncomputable def envelopeD (n : ℕ) (Q : ℝ) : ℝ := Q * tA n / ((n : ℝ) - 2)
noncomputable def envelopeV (n : ℕ) (Q : ℝ) : ℝ := 8 * tA n / n * Q / ((n : ℝ) - 2)
noncomputable def envelopeGap (n : ℕ) (Q O Sm : ℝ) : ℝ :=
  Sm / 2 - 2 * tA n * (Q * O ^ 2 / ((n : ℝ) - 2))
noncomputable def envelopeP (n : ℕ) (Q O Sm : ℝ) : ℝ :=
  BstLean.Part162.cLS 4 ^ 8 * (8 * tA n / n * Q) ^ 4 * inverseRadius8 (n - 1) /
    envelopeGap n Q O Sm ^ 8

noncomputable def envelopeData (n : ℕ) (Q O Sm SM M1 M2 M3 : ℝ) : RAData :=
  { Smin := Sm, Smax := SM
    D := envelopeD n Q * (M1 + M2)
    H := envelopeD n Q * (M1 + M2)
    V := envelopeV n Q * M3 + (envelopeD n Q * (M1 + M2)) ^ 2
    P := envelopeP n Q O Sm * M3 ^ 4
    topF := 0, topW := 0 }

lemma envelope_nonneg {n : ℕ} (hn : 10 ≤ n) {Q O Sm : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ envelopeD n Q ∧ 0 ≤ envelopeV n Q ∧ 0 ≤ envelopeP n Q O Sm := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 ≤ (n : ℝ) - 2 := by linarith
  have ht := tA_nonneg n
  have hi := (inverseRadius8_pos (by omega : 8 < n - 1)).le
  unfold envelopeD envelopeV envelopeP
  exact ⟨by positivity, by positivity, by positivity⟩

theorem paperEnvelope_bounds {n : ℕ} (hn : 10 ≤ n) {s Q O Sm M1 M2 M3 : ℝ}
    (hs : s ^ 2 ≤ 1) (hq : 1 - s ^ 2 ≤ Q)
    (h1 : 0 ≤ M1) (h2 : 0 ≤ M2) (h3 : 0 ≤ M3)
    (hgap : 0 < envelopeGap n Q O Sm) :
    paperPlaneBound n s M1 M2 ≤ envelopeD n Q * (M1 + M2) ∧
    paperVarianceBound n s M1 M2 M3 ≤
      envelopeV n Q * M3 + (envelopeD n Q * (M1 + M2)) ^ 2 ∧
    paperExceptionalBound n s O Sm M3 ≤ envelopeP n Q O Sm * M3 ^ 4 := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 2 := by linarith
  have ht := tA_nonneg n
  have hq0 : 0 ≤ 1 - s ^ 2 := sub_nonneg.mpr hs
  have hQ : 0 ≤ Q := hq0.trans hq
  have hi := (inverseRadius8_pos (by omega : 8 < n - 1)).le
  have hD0 : 0 ≤ paperPlaneBound n s M1 M2 := by unfold paperPlaneBound; positivity
  have hD : paperPlaneBound n s M1 M2 ≤ envelopeD n Q * (M1 + M2) := by
    unfold paperPlaneBound envelopeD
    calc
      _ ≤ Q * tA n * (M1 + M2) / ((n : ℝ) - 2) := by gcongr
      _ = _ := by ring
  have hK : energyGradientCoefficient n s ≤ 8 * tA n / n * Q := by
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hK0 : 0 ≤ energyGradientCoefficient n s := by
    unfold energyGradientCoefficient
    positivity
  have hV : paperVarianceBound n s M1 M2 M3 ≤
      envelopeV n Q * M3 + (envelopeD n Q * (M1 + M2)) ^ 2 := by
    unfold paperVarianceBound
    have hlin := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK h3) hden.le
    have hh := add_le_add hlin (pow_le_pow_left₀ hD0 hD 2)
    convert hh using 1 <;> unfold envelopeV <;> ring
  have hcap : planeTraceCap n s O ≤ 2 * tA n * (Q * O ^ 2 / ((n : ℝ) - 2)) := by
    unfold planeTraceCap
    gcongr
  have hgaple : envelopeGap n Q O Sm ≤ Sm / 2 - planeTraceCap n s O := by
    unfold envelopeGap
    linarith only [hcap]
  have hnum : energyEighthBound n s M3 ≤
      BstLean.Part162.cLS 4 ^ 8 * (8 * tA n / n * Q * M3) ^ 4 * inverseRadius8 (n - 1) := by
    unfold energyEighthBound
    gcongr
  refine ⟨hD, hV, ?_⟩
  unfold paperExceptionalBound
  calc
    _ ≤ (BstLean.Part162.cLS 4 ^ 8 * (8 * tA n / n * Q * M3) ^ 4 *
        inverseRadius8 (n - 1)) / envelopeGap n Q O Sm ^ 8 :=
      div_le_div₀ (by positivity) hnum (by positivity)
        (pow_le_pow_left₀ hgap.le hgaple 8)
    _ = envelopeP n Q O Sm * M3 ^ 4 := by unfold envelopeP; ring

theorem envelopeNodeStat {n : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (g : ℕ) (hs : nodeS (mkR wr (0, 0)) g ^ 2 ≤ 1)
    (X : Matrix (Fin (mA n)) (Fin n) ℝ) {Q O Sm SM : ℝ}
    (hq : 1 - nodeS (mkR wr (0, 0)) g ^ 2 ≤ Q)
    (hO : 0 ≤ O) (hOp : OpB X O)
    (hmin : Sm ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g))
    (hmax : vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g) ≤ SM)
    (hgap : 0 < envelopeGap n Q O Sm)
    (hk : ∀ᵐ v ∂BstLean.Part29.stdGauss (Fin (n - 1)),
      ∀ j, (X *ᵥ BstLean.Part161.xLat (mkR wr (0, 0)) (nodeS (mkR wr (0, 0)) g)
        (BstLean.Part53.unitF53 v)) j ≠ 0) :
    let M := fun i => paperNodeStatistic wr g i X
    let d := envelopeData n Q O Sm SM (M 0) (M 1) (M 2)
    NodeStat (mkR wr (X, 0)) g d.Smin d.Smax d.D d.H d.V d.P := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have ht := tA_nonneg n
  have hcap : planeTraceCap n (nodeS (mkR wr (0, 0)) g) O ≤
      2 * tA n * (Q * O ^ 2 / ((n : ℝ) - 2)) := by
    unfold planeTraceCap
    gcongr
    linarith
  have hgap' : 0 < Sm / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) g) O := by
    unfold envelopeGap at hgap
    linarith only [hgap, hcap]
  have H := nodeStat_of_paperStatistics hn wr hc g hs X hO hOp hmin hmax hgap' hk
  obtain ⟨hD, hV, hP⟩ := paperEnvelope_bounds hn hs hq
    (paperNodeStatistic_nonneg wr g 0 X) (paperNodeStatistic_nonneg wr g 1 X)
    (paperNodeStatistic_nonneg wr g 2 X) hgap
  exact ⟨hmin, hmax, H.hD.trans hD, H.hH.trans hD, H.hV.trans hV, H.hP.trans hP⟩

#print axioms paperEnvelope_bounds
#print axioms envelopeNodeStat
end BstLean.Part223
