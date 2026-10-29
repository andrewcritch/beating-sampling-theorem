import BstLean.Part243Bridge

/-! Part 243: finite coverage with the new packages preserves the uncapped upper branch. -/
namespace BstLean.Part243
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)

structure IntervalInputs (lo hi : ℕ) where
  positive_dimension : 1 ≤ lo
  worldParameters : ℕ → WorldParameters
  agentParameters : ℕ → AgentParameters
  world : ∀ n, lo ≤ n → n ≤ hi → WorldPackage (paperProgram n) (worldParameters n)
  certificate : ∀ n, lo ≤ n → n ≤ hi →
    MasterCertificate n (worldParameters n) (agentParameters n)
  agent : ∀ n (hn : lo ≤ n) (hN : n ≤ hi) (t : ℝ),
    AgentPackage n (BstLean.Part159.Hof (world n hn hN).hidden)
      (certificate n hn hN).worldRadius (agentParameters n).frame (agentParameters n).root
        (agentParameters n).charge t
  charge_compatible : ∀ n (hn : lo ≤ n) (hN : n ≤ hi),
    (agentParameters n).charge ≤ (certificate n hn hN).retainedCharge

theorem interval_bridge {lo hi : ℕ} (B : IntervalInputs lo hi)
    {n : ℕ} (hn : lo ≤ n) (hN : n ≤ hi) :
    BridgeStatement (paperProgram n) (1 / 100) := by
  apply (bridge_identity (paperProgram n)).2
  intro t
  exact checked_junction (B.positive_dimension.trans hn) (B.world n hn hN) t
    (B.certificate n hn hN) (B.agent n hn hN t) (B.charge_compatible n hn hN)

/-- A supplied finite bridge has no dimension gap at the accepted upper branch. -/
theorem combine_upper {lo : ℕ} (B : IntervalInputs lo 16199)
    {n : ℕ} (hn : lo ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  by_cases h : 16200 ≤ n
  · exact BstLean.Part190.classifier_paper_uncond_16200 h t
  · exact (bridge_identity (paperProgram n)).1 (interval_bridge B hn (by omega)) t

end BstLean.Part243
#print axioms BstLean.Part243.interval_bridge
#print axioms BstLean.Part243.combine_upper
