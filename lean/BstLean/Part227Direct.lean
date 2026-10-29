import BstLean.Part227Package
import BstLean.Part218ConcreteDistance

/-! Part 227: the variant-E World package from the concrete first-layer supply. -/
namespace BstLean.Part227
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part136 BstLean.Part137
open BstLean.Part140 BstLean.Part157 BstLean.Part159 BstLean.Part192

noncomputable def directDistancePayment (n : ℕ) (εω ph Δ Xc : ℝ) (ε : Fin 4 → ℝ) : ℝ :=
  BstLean.Part218.e1Charge (2 * n) (mW n) εω ph ε +
    ((4 * ((2 * n : ℕ) : ℝ) ^ 2 / (mW n : ℝ)) * (1 + εω) ^ 2 * √(Δ / 2) *
      ((1 - BstLean.Part218.firstRatio (2 * n)) * √(1 - BstLean.Part218.firstRatio (2 * n)) *
        BstLean.Part218.sixthConstant (BstLean.Part218.e1CovarianceRatio (2 * n) (mW n) εω ε))) /
      (Xc - ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ) ^ 2

/-- The direct distance charge is proved from explicit scalar mean and reserve bounds. -/
theorem direct_hidden_charge {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB εω ph Δ : ℝ} {ε : Fin 4 → ℝ}
    (hsp : 0 < sp) (hp₂ : 0 < p₂) (hdT : 0 < dT) (heB : 0 < eB)
    (hεω : 0 < εω) (hεω1 : εω < 1) (hph : 0 < ph) (hε : ∀ i, 0 < ε i)
    (hΔ0 : 0 ≤ Δ) (hΔ : BstLean.Part218.e1MeanBound (2 * n) (mW n) εω ph ε ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ < Xc) :
    (hidGauss (2 * n) (mW n)).real (hidden n sp p₂ Xc dT eB)ᶜ ≤
      hiddenChargeWithDistance n sp p₂ dT eB (directDistancePayment n εω ph Δ Xc ε) :=
  hidden_charge_of_distance hn hsp hp₂ hdT heB
    (BstLean.Part218.concrete_distance_charge hn hεω hεω1 hph hε hΔ0 hΔ hX)

/-- S08 and S09 discharge the distance premise of the parameterized World constructor. -/
noncomputable def directWorldPackage {n : ℕ} (hn : 4096 ≤ n)
    {sp p₂ Xc dT eB εω ph Δ Alo Ahi ζ : ℝ} {ε : Fin 4 → ℝ}
    (hsp : 4 / 100 ≤ sp) (hp₂ : 4 / 10000 ≤ p₂)
    (hXc : Xc ≤ 3 / 4) (hdT0 : 0 < dT) (hdT : dT ≤ 1 / 400000) (heB : 0 < eB)
    (hεω : 0 < εω) (hεω1 : εω < 1) (hph : 0 < ph) (hε : ∀ i, 0 < ε i)
    (hΔ0 : 0 ≤ Δ) (hΔ : BstLean.Part218.e1MeanBound (2 * n) (mW n) εω ph ε ≤ Δ)
    (hX : ((2 * n : ℕ) : ℝ) * (1 + εω) * Δ < Xc)
    (c : FrameCertificate n sp p₂ Xc dT eB)
    (hk : kernelError n < kap1 (2 * n))
    (hAlo : 1 < Alo) (hlo : Alo ≤ productLower n eB)
    (hhi : productUpper n eB ≤ Ahi) (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    WorldPackage (paperProgram n)
      (worldParameters c (directDistancePayment n εω ph Δ Xc ε) Alo Ahi ζ) :=
  worldPackage hn hsp hp₂
    (BstLean.Part218.concrete_distance_charge hn hεω hεω1 hph hε hΔ0 hΔ hX)
    hXc hdT0 hdT heB c hk hAlo hlo hhi hζ0 hζ1

end BstLean.Part227
#print BstLean.Part227.directWorldPackage
#print axioms BstLean.Part227.direct_hidden_charge
#print axioms BstLean.Part227.directWorldPackage
