import BstLean.Part192Baseline
import BstLean.Part192Energy
import BstLean.Part192Identities

/-! Part 192: the legacy and sharp Agent interfaces remain separate.
AgentJunctionPackage supplies the charged inputs of the master junction.
AgentCell and AgentPackage in Interfaces specify the later sharp analytic route.
The moment sources are attached evidence. They add no payment to the master ledger. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part159 (Hof GPap)
open BstLean.Part156 (hWL hAL cWL)

structure MomentParameters where
  energyCharge : ℝ
  scale8Bound : ℝ
  locationBound : ℝ
  statisticsCharge : ℝ
  locationBias8 : ℝ
  energyBias8 : ℝ

/-- The retained complement is charged on the hidden World event, before the cutoff.
The full/parallel centre and frame/root use one common event after the cutoff. -/
structure AgentJunctionPackage {n : ℕ} (P : Program n) {w : WorldParameters}
    (W : WorldPackage P w) (a : AgentParameters) (m : MomentParameters) (radius t : ℝ) where
  event : Set (Ret n)
  event_measurable : MeasurableSet event
  retained_charge : (retDist P.design.toCentres).real (Hof W.hidden ∩ eventᶜ) ≤ a.charge
  window : ∀ c ∈ goodSet (Hof W.hidden) event (HbarW P.design) radius,
    0 < P.design.tau0 c ∧
    a.noiseLo ≤ BstLean.Part150.thetaC c.1.2 (P.design.tau0 c) ∧
    BstLean.Part150.thetaC c.1.2 (P.design.tau0 c) ≤ a.noiseHi
  full_centre : CENTRE_hyp P.design a.centre
    (goodSet (Hof W.hidden) event (HbarW P.design) radius)
  parallel_centre : ∀ c ∈ goodSet (Hof W.hidden) event (HbarW P.design) radius,
    0 < normSq (P.design.bA c.1 c.2.1.1) →
    BstLean.Part188.ParallelCentre P.design c a.centre
  frame : FRAME_A_hyp P.design (a.frame / n)
    (goodSet (Hof W.hidden) event (HbarW P.design) radius)
  root : REPLA_mix_hyp P.design t a.root
    (goodSet (Hof W.hidden) event (HbarW P.design) radius)
  energy : EnergySupply n m.energyCharge m.scale8Bound m.locationBound
  statistics : AgentStatistics n m.statisticsCharge m.locationBias8 m.energyBias8

noncomputable def junction16200Parameters : AgentParameters :=
  { agentLedgerParameters with
    charge := 5111 / 1000000 - BstLean.Part188.Base159_R.δPap -
      BstLean.Part188.Base159_R.vPap / hWL ^ 2
    noiseLo := 46 / 100 }

noncomputable def moment16200Parameters (n : ℕ) : MomentParameters where
  energyCharge := 1 / 10 ^ 6
  scale8Bound := 1005 / 1000 * √(2 / (n : ℝ))
  locationBound := 1005 / 1000
  statisticsCharge := 122 / 1000000
  locationBias8 := 194 / n
  energyBias8 := 148 / n

theorem agent_junction16200 {n : ℕ} (hn : 16200 ≤ n) (hN : n ≤ 16384) (t : ℝ) :
    Nonempty (AgentJunctionPackage (paperProgram n) (world16200 hn)
      junction16200Parameters (moment16200Parameters n) hWL t) := by
  obtain ⟨B⟩ := baseline16200 hn hN t
  have hD := B.program_identity
  have hH := B.hidden_identity
  have hev := B.events
  have hi := B.agent_inputs
  have hframe := B.agent_frame
  have hroot := B.agent_root
  rw [hD, hH] at hev hi hframe hroot
  have hcharge : B.retainedCharge ≤ junction16200Parameters.charge := by
    have h := B.retained_budget
    rw [B.hiddenCharge_identity, B.worldMoment_identity] at h
    dsimp [junction16200Parameters]
    linarith
  refine ⟨{
    event := B.event
    event_measurable := hev.2.1
    retained_charge := hev.2.2.2.2.2.2.trans hcharge
    window := hi.window
    full_centre := full_centre16200 hn hi
    parallel_centre := fun c hc hb => parallel_centre16200 hn hi hc hb
    frame := hframe
    root := hroot
    energy := energy16200 hn
    statistics := statistics16200 hn hN }⟩

/-- The source interfaces and the scalar certificate have separate coverage fields.
The bridge field is an obligation; S02 will derive it from compatible inputs. -/
structure IntervalJunction (lo hi : ℕ) where
  worldParameters : ℕ → WorldParameters
  agentParameters : ℕ → AgentParameters
  momentParameters : ℕ → MomentParameters
  radius : ℕ → ℝ
  world : ∀ n, lo ≤ n → n ≤ hi → WorldPackage (paperProgram n) (worldParameters n)
  agent : ∀ (n : ℕ) (hn : lo ≤ n) (hN : n ≤ hi) (t : ℝ),
    AgentJunctionPackage (paperProgram n) (world n hn hN) (agentParameters n)
      (momentParameters n) (radius n) t
  certificate : ∀ n, lo ≤ n → n ≤ hi →
    EndpointCertificate n (worldParameters n) (agentParameters n)
  radius_identity : ∀ n (hn : lo ≤ n) (hN : n ≤ hi),
    (certificate n hn hN).worldRadius = radius n
  charge_compatible : ∀ n (hn : lo ≤ n) (hN : n ≤ hi),
    (agentParameters n).charge ≤ (certificate n hn hN).retainedCharge
  bridge : ∀ n, lo ≤ n → n ≤ hi → BridgeStatement (paperProgram n) (1 / 100)

end BstLean.Part192
#print axioms BstLean.Part192.agent_junction16200
