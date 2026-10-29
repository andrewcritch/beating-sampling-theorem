import BstLean.Part291AgentCombined
import BstLean.Part293LowMixtureNormalization
import BstLean.Part293LowDisplacement

/-! Definitional checks connect the independently checked scalar model to
the actual Part291 constants. This module waits for Part291's dependencies. -/
namespace BstLean.Part293

theorem actual_lowChi_normalized (n : ℕ) :
    BstLean.BlueprintLow.lowMixtureChi n = Envelope.chi (1 / n) := by
  change Model.lowMixtureChi n = _
  exact lowChi_normalized n

theorem actual_lowEpsilon_normalized {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.BlueprintLow.lowMixtureEpsilon n = Envelope.eps (1 / n) := by
  change Model.lowMixtureEpsilon n = _
  exact lowEpsilon_normalized hn

theorem actual_lowDisplacement_normalized {n : ℕ} (hn : 8000 ≤ n) :
    Real.sqrt (BstLean.BlueprintLow.lowMixtureB n) / (1 - 0.0045) *
      (BstLean.BlueprintLow.lowMixtureD n (BstLean.BlueprintLow.lowMixtureChi n) / 2 +
        n * (2 * (1 + BstLean.BlueprintLow.agentEnergyMomentCap / n) *
          BstLean.BlueprintLow.lowLatitudeT n 4) ^ 2 / (4 * 0.18 ^ 2)) =
      Envelope.Dd (1 / n) := by
  change Real.sqrt (Model.lowMixtureB n) / (1 - 0.0045) *
    (Model.lowMixtureD n (Model.lowMixtureChi n) / 2 +
      n * (2 * (1 + Model.agentEnergyMomentCap / n) * Model.lowLatitudeT n 4) ^ 2 /
        (4 * 0.18 ^ 2)) = _
  exact lowDisplacement_normalized hn

theorem actual_lowQ_normalized {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.BlueprintLow.lowMixtureQ n = Envelope.chi2 (1 / n) := by
  change Model.lowMixtureQ n = _
  exact lowQ_normalized hn

theorem actual_lowB_normalized {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.BlueprintLow.lowMixtureB n = Envelope.B (1 / n) := by
  change Model.lowMixtureB n = _
  exact lowB_normalized hn

theorem actual_lowA_normalized {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.BlueprintLow.lowMixtureA n = Envelope.A (1 / n) := by
  change Model.lowMixtureA n = _
  exact lowA_normalized hn

theorem actual_lowD_normalized {n : ℕ} (hn : 8000 ≤ n) :
    BstLean.BlueprintLow.lowMixtureD n (BstLean.BlueprintLow.lowMixtureChi n) =
      Envelope.D (1 / n) := by
  change Model.lowMixtureD n (Model.lowMixtureChi n) = _
  exact lowD_normalized hn

end BstLean.Part293
