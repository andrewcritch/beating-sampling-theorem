import BstLean.Part291FrameConstants
import BstLean.Part291LocalCentreNetwork
import BstLean.Part291TICells

namespace BstLean.BlueprintLow
open Real Set BstLean.Part255 BstLean.Part206 BstLean.Part211

/-- A checked continuum rectangle, including the source formula bounds. -/
structure FrameRectangleCertificate (nlo nhi : ℕ) (lo hi : ℝ) (p : Parameters) where
  full : ℝ
  energy : ℝ
  cov : ℝ
  schur : ℝ
  cap : ℝ
  W2 : ℝ
  V : ℝ
  mass : ℝ
  rootN : ℝ
  rootB : ℝ
  rootU : ℝ
  rootV : ℝ
  nonneg : 0 ≤ full ∧ 0 ≤ energy ∧ 0 ≤ cov ∧ 0 ≤ schur ∧ 0 ≤ W2
  scalar : FrameScalarCertificate
    ⟨schur,cap,W2 * full,V,mass,rootN,rootB,rootU,rootV⟩
  centre : ∀ n ∈ Icc nlo nhi,
    fullFormula n n 0.011 1.25 1.14 0.46 hi (0.004172 + 0.34 * hi) 1.269 ≤ full
  energy_source : ∀ n, 8000 ≤ n → ∀ q : ℝ, 0 ≤ q → q ≤ 1 - lo →
    energyRatio n (gMinus n) q ≤ 1 ∧
    energyUpper n (gMinus n) (gPlus n) (finiteEnergy n n (11/1000)) q ≤ energy
  enclosures : ∀ n ∈ Icc nlo nhi, ∀ θ ∈ Icc lo hi,
    FrameEnclosures n θ full energy p cov schur cap W2 V mass

end BstLean.BlueprintLow
