import BstLean.Part190Uncond
import BstLean.Part188Interfaces

/-! Part 192: parameterized interfaces for the exact-moment program.
The structures contain proved inputs. Their fields assert no new dimension floor.
All Agent input averages use the stand-in distribution from Part 157. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160
open BstLean.Part159 (Hof hellHid)
open BstLean.Part169 (paperDesignP)

structure Program (n : ℕ) where
  design : Design n
  design_eq : design = paperDesignP n
  centres_eq : design.toCentres = paperCentres n

noncomputable def paperProgram (n : ℕ) : Program n := ⟨paperDesignP n, rfl, rfl⟩

structure WorldParameters where
  hiddenCharge : ℝ
  frame : ℝ
  moment : ℝ
  productLo : ℝ
  productHi : ℝ
  noiseLo : ℝ
  noiseHi : ℝ

/-- The hidden event and calibration use the computed World centre. -/
structure WorldPackage {n : ℕ} (P : Program n) (p : WorldParameters) where
  hidden : Set (WHid n)
  hidden_measurable : MeasurableSet hidden
  scale : WHid n → ℝ
  scale_measurable : Measurable scale
  scale_eq : ∀ c, P.design.tau0 c = scale c.1.1
  calibration : WHid n → ℝ
  calibration_measurable : Measurable calibration
  hidden_charge : (BstLean.Part136.hidGauss (2 * n) (mW n)).real hiddenᶜ ≤ p.hiddenCharge
  product_window : ∀ θ ∈ hidden,
    p.productLo ≤ 2 / (mW n : ℝ) * normSq (P.design.bW θ) * calibration θ ∧
    2 / (mW n : ℝ) * normSq (P.design.bW θ) * calibration θ ≤ p.productHi
  scale_identity : ∀ θ ∈ hidden, 0 < scale θ ∧ scale θ ^ 2 =
    2 / (mW n : ℝ) * normSq (P.design.bW θ) *
      (2 / (mW n : ℝ) * normSq (P.design.bW θ) * calibration θ - 1)
  lowerEvent : Set (Ret n)
  upperEvent : Set (Ret n)
  lower_measurable : MeasurableSet lowerEvent
  upper_measurable : MeasurableSet upperEvent
  noise_window : ∀ c ∈ Hof hidden ∩ (lowerEvent ∩ upperEvent),
    p.noiseLo ≤ BstLean.Part150.thetaC c.1.2 (P.design.tau0 c) ∧
    BstLean.Part150.thetaC c.1.2 (P.design.tau0 c) ≤ p.noiseHi
  frame_bound : FRAME_W_hyp P.design.toCentres (p.frame / n) (Hof hidden)
  moment_integrable : IntegrableOn (fun c => HbarW P.design c ^ 2)
    (Hof hidden) (retDist P.design.toCentres)
  restricted_moment : ∫ c in Hof hidden, HbarW P.design c ^ 2
    ∂retDist P.design.toCentres ≤ p.moment

structure AgentParameters where
  charge : ℝ
  frame : ℝ
  root : ℝ
  covariance : ℝ
  centre : ℝ
  cutoff : ℝ
  mass : ℝ
  noiseLo : ℝ
  noiseHi : ℝ
  energyOrder : ℕ
  directionOrder : ℕ
  energyBound : ℝ
  directionBound : ℝ

/-- A cell separates full/parallel centre, covariance, residual and moment inputs.
The covariance field is the TI conclusion, not a new TI proof.
The energy and direction orders are independent parameters. -/
structure AgentCell {n : ℕ} (P : Program n) (p : AgentParameters) (c : Ret n) : Prop where
  full_centre : CENTRE_at P.design c p.centre
  parallel_centre : BstLean.Part188.ParallelCentre P.design c p.centre
  covariance_bound : COV_at P.design c p.covariance
  residual_mass : MASS_at P.design c p.cutoff p.mass
  energy_integrable : Integrable
    (fun ξ => (√(BstLean.Part188.inputEnergy P.design c ξ) - 1) ^ p.energyOrder)
    (stdGauss (Fin n))
  energy_moment : ∫ ξ, (√(BstLean.Part188.inputEnergy P.design c ξ) - 1) ^ p.energyOrder
    ∂stdGauss (Fin n) ≤ p.energyBound ^ p.energyOrder
  direction_integrable : Integrable
    (fun ξ => BstLean.Part151.gradSq (BstLean.Part188.centreCoordinate P.design c) ξ ^
      p.directionOrder) (stdGauss (Fin n))
  direction_moment : ∫ ξ,
    BstLean.Part151.gradSq (BstLean.Part188.centreCoordinate P.design c) ξ ^ p.directionOrder
    ∂stdGauss (Fin n) ≤ (p.directionBound / n) ^ p.directionOrder

/-- The residual cutoff set inside MASS_at differs from the retained event. -/
structure AgentPackage {n : ℕ} (P : Program n) (p : AgentParameters) (t : ℝ)
    (worldWindow : Set (WRet n)) where
  hiddenEvent : Set (WRet n × AHid n)
  hidden_measurable : MeasurableSet hiddenEvent
  conditional_charge : ∀ wr ∈ worldWindow,
    (BstLean.Part153.nuA n).real {θ | (wr, θ) ∉ hiddenEvent} ≤ p.charge
  retainedEvent : Set (Ret n)
  retained_measurable : MeasurableSet retainedEvent
  retained_identity : retainedEvent =
    {c | c.1 ∈ worldWindow ∧ (c.1, c.2.1.1) ∈ hiddenEvent}
  noise_window : ∀ c ∈ retainedEvent, 0 < P.design.tau0 c ∧
    p.noiseLo ≤ BstLean.Part150.thetaC c.1.2 (P.design.tau0 c) ∧
    BstLean.Part150.thetaC c.1.2 (P.design.tau0 c) ≤ p.noiseHi
  analytic : ∀ c ∈ retainedEvent, AgentCell P p c
  frame_bound : FRAME_A_hyp P.design (p.frame / n) retainedEvent
  replacement_root : REPLA_mix_hyp P.design t p.root retainedEvent

/-- One closed scalar cell. Formula enclosures and coverage remain proof obligations. -/
structure ScalarCertificate (n : ℕ) (w : WorldParameters) (a : AgentParameters) where
  dimensionLo : ℕ
  dimensionHi : ℕ
  dimension_mem : dimensionLo ≤ n ∧ n ≤ dimensionHi
  noiseLo : ℝ
  noiseHi : ℝ
  overlapLo : ℝ
  overlapHi : ℝ
  radiusLo : ℝ
  radiusHi : ℝ
  frameLo : ℝ
  frameHi : ℝ
  noise_order : noiseLo ≤ noiseHi
  overlap_order : overlapLo ≤ overlapHi
  radius_order : 0 ≤ radiusLo ∧ radiusLo ≤ radiusHi
  frame_order : 0 < frameLo ∧ frameLo ≤ frameHi
  worldFrame_pos : 0 < w.frame
  agentFrame_pos : 0 < a.frame
  worldRadius : ℝ
  worldRadius_pos : 0 < worldRadius
  agentRoot_nonneg : 0 ≤ a.root
  retainedCharge : ℝ
  samplingCharge : ℝ
  upperTail : ℝ
  lowerTail : ℝ
  retainedCharge_nonneg : 0 ≤ retainedCharge
  samplingCharge_nonneg : 0 ≤ samplingCharge
  upperTail_nonneg : 0 ≤ upperTail
  lowerTail_nonneg : 0 ≤ lowerTail
  totalBudget : ℝ
  ledger : w.hiddenCharge + w.moment / worldRadius ^ 2 + retainedCharge +
    samplingCharge + upperTail + lowerTail ≤ totalBudget
  budget : totalBudget ≤ 1 / 100

/-- S02 will derive this obligation from compatible packages and scalar bounds. -/
def BridgeStatement {n : ℕ} (P : Program n) (failure : ℝ) : Prop :=
  ∀ t : ℝ, 1 - failure ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
    {x | successNet x.1 t (progOut P.design t BstLean.Part156.aL (10 ^ 12) x.1 x.2)}

structure IntervalBridge (lo hi : ℕ) where
  parametersW : ℕ → WorldParameters
  parametersA : ℕ → AgentParameters
  worldWindow : ∀ n, Set (WRet n)
  world : ∀ n, lo ≤ n → n ≤ hi → WorldPackage (paperProgram n) (parametersW n)
  agent : ∀ n, lo ≤ n → n ≤ hi → ∀ t,
    AgentPackage (paperProgram n) (parametersA n) t (worldWindow n)
  certificate : ∀ n, lo ≤ n → n ≤ hi →
    ScalarCertificate n (parametersW n) (parametersA n)
  bridge : ∀ n, lo ≤ n → n ≤ hi → BridgeStatement (paperProgram n) (1 / 100)

lemma paper_centres (n : ℕ) : (paperProgram n).design.toCentres = paperCentres n := rfl
lemma paper_design (n : ℕ) : (paperProgram n).design = paperDesignP n := rfl
lemma stand_identity {n : ℕ} (P : Program n) (c : Ret n) (ξ : Fin n → ℝ) :
    hStand P.design c ξ = hStand (paperDesignP n) c ξ := by rw [P.design_eq]
lemma residual_identity {n : ℕ} (P : Program n) (c : Ret n) (ξ : Fin n → ℝ) :
    res (P.design.bA c.1 c.2.1.1) (hStand P.design c ξ) =
      res ((paperCentres n).bA c.1 c.2.1.1) (hStand (paperDesignP n) c ξ) := by
  rw [P.design_eq]; rfl
lemma output_identity {n : ℕ} (P : Program n) (t : ℝ) (θ : Net3 n)
    (σ : Fin (10 ^ 12) → DrawSp n) :
    progOut P.design t BstLean.Part156.aL (10 ^ 12) θ σ =
      progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) θ σ := by rw [P.design_eq]
lemma success_identity {n : ℕ} (θ : Net3 n) (t U : ℝ) :
    successNet θ t U ↔ pTargetT θ t ≤ U ∧ U ≤ max (10 * pTargetT θ t) (1 / 100) := Iff.rfl
lemma bridge_identity {n : ℕ} (P : Program n) : BridgeStatement P (1 / 100) ↔
    ∀ t : ℝ, 99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t
        (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  unfold BridgeStatement
  rw [P.design_eq]
  norm_num

end BstLean.Part192
#print axioms BstLean.Part192.paper_centres
#print axioms BstLean.Part192.paper_design
#print axioms BstLean.Part192.stand_identity
#print axioms BstLean.Part192.residual_identity
#print axioms BstLean.Part192.output_identity
#print axioms BstLean.Part192.success_identity
#print axioms BstLean.Part192.bridge_identity
