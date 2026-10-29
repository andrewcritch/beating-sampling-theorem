import BstLean.Part233Conditional
import BstLean.Part233Distance
import BstLean.Part233Ao
import BstLean.Part233Group

/-! The grouped charge connects to the unchanged World event and restricted moment. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part227
open BstLean.Part205
open BstLean.Part153 (nrm)
open BstLean.Part141 (rowS)

/-- Both conditional failures use the complete second-layer Gaussian distribution. -/
theorem distanceGroup_charge {n : ℕ} {E : Set (Matrix (Fin (mW n)) (Fin (2 * n)) ℝ)}
    (hE : MeasurableSet E) (hn : 1 ≤ n) {δ pD pA Xc : ℝ}
    (hδ : (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).real Eᶜ ≤ δ)
    (hpD : 0 ≤ pD) (hpA : 0 ≤ pA)
    (hs : ∀ M₁ ∈ E, ∀ M₂, (M₁, M₂) ∈ goodS n)
    (hd : ∀ M₁ ∈ E, (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).real
      {M₂ | (M₁, M₂) ∉ goodDist n Xc} ≤ pD)
    (ha : ∀ M₁ ∈ E, (gaussMat (mW n) (mW n) (2 / (mW n : ℝ))).real
      {M₂ | (M₁, M₂) ∉ goodAo n} ≤ pA) :
    (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤ δ + pD + pA :=
  grouped_conditional_charge hE (goodDist_meas hn Xc)
    measurableSet_goodS measurableSet_goodAo hδ hpD hpA hs hd ha

/-- The analytic concentration route supplies the grouped bound under explicit first-layer reserves. -/
theorem distanceGroup_charge_of_concentration {n : ℕ} (hn : 4096 ≤ n)
    {E : Set (Matrix (Fin (mW n)) (Fin (2 * n)) ℝ)} (hE : MeasurableSet E)
    {δ Xc M a V ε e : ℝ}
    (hδ : (gaussMat (mW n) (2 * n) (2 / ((2 * n : ℕ) : ℝ))).real Eᶜ ≤ δ)
    (ha0 : 0 ≤ a) (hgap : M ≤ a) (hV : 0 < V) (hε0 : 0 ≤ ε)
    (he : 0 < e) (hε : ε ≤ 1 / 1000)
    (hcut : a ^ 2 ≤ 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)))
    (hAcut : 8 * (1 + ε) * (1 + e) ≤ (10 : ℝ) ^ 8)
    (hS : ∀ M₁ ∈ E, |rowS M₁ / (mW n : ℝ) / 2 - 1| ≤ ε)
    (hM0 : 0 ≤ M)
    (hmean : ∀ M₁ ∈ E, 2 / (mW n : ℝ) * worldDelta M₁ ≤ M ^ 2)
    (hL0 : ∀ M₁ ∈ E, 0 < (√(firstQ M₁) + nrm (h1bar M₁)) / (mW n : ℝ))
    (hL : ∀ M₁ ∈ E, ((√(firstQ M₁) + nrm (h1bar M₁)) / (mW n : ℝ)) ^ 2 ≤ V) :
    (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤
      δ + exp (-(a - M) ^ 2 / (2 * V)) +
        exp (-(mW n : ℝ) * (e - log (1 + e)) / 2) := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  apply distanceGroup_charge hE (by omega) hδ (by positivity) (by positivity)
  · intro M₁ h₁ M₂
    exact (hS M₁ h₁).trans hε
  · intro M₁ h₁
    exact conditional_distance_tail_of_variance (by omega) hm M₁ ha0 hgap hV hcut
      (standardDistanceRoot_mean (by omega) hm M₁ hM0 (hmean M₁ h₁))
      (hL0 M₁ h₁) (hL M₁ h₁)
  · intro M₁ h₁
    have hs := (abs_le.mp (hS M₁ h₁)).2
    exact goodAo_conditional_charge hm M₁ hε0 he (by linarith) hAcut

noncomputable def groupedWorldParameters {n : ℕ} {sp p₂ Xc dT eB : ℝ}
    (c : FrameCertificate n sp p₂ Xc dT eB) (groupPayment Alo Ahi ζ : ℝ) :
    BstLean.Part192.WorldParameters :=
  { worldParameters c 1 Alo Ahi ζ with
    hiddenCharge := groupedCharge n sp p₂ dT eB groupPayment }

/-- The grouped route changes the hidden payment and preserves every analytic field. -/
noncomputable def worldPackage_of_group {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB groupPayment Alo Ahi ζ : ℝ}
    (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hgroup : (hidGauss (2 * n) (mW n)).real (distanceGroup n Xc)ᶜ ≤ groupPayment)
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 < dT) (hdT : dT ≤ 1 / 400000) (heB : 0 < eB)
    (c : FrameCertificate n sp p₂ Xc dT eB)
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    BstLean.Part192.WorldPackage (BstLean.Part192.paperProgram n)
      (groupedWorldParameters c groupPayment Alo Ahi ζ) := by
  let W := worldPackage hn hsp hp₂ (distancePayment := 1) (by exact measureReal_le_one)
    hXc hdT0 hdT heB c hk hAlo hlo hhi hζ0 hζ1
  exact rechargedWorld W _
    (hidden_charge_of_group hn (by linarith) (by linarith) hdT0 heB hgroup)

end BstLean.Part233
#print axioms BstLean.Part233.distanceGroup_charge
#print axioms BstLean.Part233.distanceGroup_charge_of_concentration
#print axioms BstLean.Part233.worldPackage_of_group
