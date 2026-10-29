import BstLean.Part248Network
import BstLean.Part242MixtureConstants
import BstLean.Part162Pap
import BstLean.Part162Int
import BstLean.Part222Mass

/-! Scalar formulas copied from the Part291 interface, isolated from its
unfinished analytic imports. Part293LowAdapter checks the definitional match. -/
namespace BstLean.Part293.Model
open Real BstLean.Part162 BstLean.Part195 BstLean.Part242 BstLean.Part248

noncomputable def agentEnergyCap : ℝ := 707768 / 1000000
noncomputable def agentDirectionCap : ℝ := 109292 / 1000000
noncomputable def agentEnergyMomentCap : ℝ := 21008487 / 1000000
noncomputable def agentParallelCap : ℝ := 53854 / 1000000

noncomputable def lowLatitudeT (n q : ℕ) : ℝ :=
  rotationConstant q * √(3.042 / ((n : ℝ) * ((n : ℝ) - 1 - 2 * q)))
noncomputable def lowLatitudeV (n : ℕ) : ℝ := 3.042 / ((n : ℝ) * ((n : ℝ) - 3))
noncomputable def lowMixtureWidth (n : ℕ) : ℝ := 3.5 * lowLatitudeT n 12
noncomputable def lowMixtureMean (n : ℕ) : ℝ :=
  √agentEnergyCap + √(agentParallelCap / n)
noncomputable def lowMixtureY (n : ℕ) : ℝ := 1 - lowMixtureMean n ^ 2
noncomputable def lowMixtureX (n q : ℕ) : ℝ :=
  deficitConstant q (agentEnergyMomentCap / n) (lowMixtureMean n) (√(agentDirectionCap / n))
noncomputable def lowMixtureXhat (n q : ℕ) : ℝ :=
  mixtureConstant (lowMixtureX n q) (agentEnergyMomentCap / n)
    (lowLatitudeT n q) 0.0045 (lowLatitudeV n)
noncomputable def lowMixtureReciprocal (n : ℕ) : ℝ :=
  bound3 0.18 (lowMixtureY n) (lowMixtureXhat n 4) (lowMixtureXhat n 8) (lowMixtureXhat n 12)
noncomputable def lowMixtureA (n : ℕ) : ℝ :=
  mixA (lowMixtureWidth n) 0.18 (lowMixtureReciprocal n) (lowLatitudeV n) 0.0045
noncomputable def lowMixtureD (n : ℕ) (χ : ℝ) : ℝ :=
  mixD n χ (lowMixtureReciprocal n) (lowLatitudeV n) 0.0045
noncomputable def lowMixtureChi (n : ℕ) : ℝ := 1 + 2 * √(12 / (n : ℝ)) + 24 / n
noncomputable def lowMixtureBeta (n : ℕ) : ℝ :=
  BstLean.Part222.massBound n agentDirectionCap (agentEnergyMomentCap / n)
    agentParallelCap agentEnergyCap 0.0066 0.18 / n
noncomputable def lowMixtureB (n : ℕ) : ℝ := 2 * (1 / (3.5 : ℝ)) ^ 24 + lowMixtureBeta n
noncomputable def lowMixtureEpsilon (n : ℕ) : ℝ := eps0 (lowMixtureWidth n) (√(0.18 : ℝ))
noncomputable def lowMixtureL (n : ℕ) : ℝ := n * lowMixtureChi n * (2 * lowMixtureWidth n) ^ 2 / 0.18
noncomputable def lowMixtureI (n j : ℕ) : ℝ :=
  iotaP 0.0045 (2 * j) + √(0.0045 : ℝ) / (1 - 0.0045) + lowMixtureWidth n / √(0.18 * (1 - 0.0045))
noncomputable def lowMixtureE (n j : ℕ) : ℝ :=
  (2 + 2 * lowMixtureWidth n / √(0.18 : ℝ)) * lowMixtureI n j * lowLatitudeT n j / √(0.18 : ℝ)
noncomputable def lowMixtureLocation (n j : ℕ) : ℝ :=
  √((n : ℝ) * lowMixtureChi n / 0.18) * lowMixtureI n j * lowLatitudeT n j
noncomputable def lowMixtureK (n : ℕ) : ℝ := (1 - lowMixtureEpsilon n ^ 2)⁻¹
noncomputable def lowMixtureT2 (n : ℕ) : ℝ :=
  lowMixtureK n * ((n : ℝ) * lowMixtureA n / 2 + lowMixtureD n (lowMixtureChi n) +
    √(lowMixtureL n * lowMixtureA n * lowMixtureD n (lowMixtureChi n)))
noncomputable def lowMixtureT (n j : ℕ) : ℝ :=
  tK (lowMixtureK n) n (√(lowMixtureL n)) (lowMixtureE n j) (lowMixtureLocation n j)
noncomputable def lowMixtureQ (n : ℕ) : ℝ :=
  lowMixtureK n * ((n : ℝ) * lowMixtureA n ^ 2 / 4 +
    (1 + lowMixtureEpsilon n) * lowMixtureA n * lowMixtureD n (lowMixtureChi n)) +
    lowMixtureT2 n ^ 2 / 2 + lowMixtureT2 n * lowMixtureT n 4 ^ 2 / 6 +
    lowMixtureT n 4 ^ 4 / 24 + lowMixtureT n 6 ^ 5 / 120 +
    exp (lowMixtureK n * ((n : ℝ) * lowMixtureEpsilon n ^ 2 / 2 +
      lowMixtureL n * (1 + lowMixtureEpsilon n))) * lowMixtureT n 6 ^ 6 / 720

end BstLean.Part293.Model
