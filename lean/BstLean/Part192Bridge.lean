import BstLean.Part192World
import BstLean.Part192Agent

/-! Part 192: scalar endpoint and bridge interfaces.
The baseline bridge reuses the existing theorem. The interval combination keeps its
uncapped upper branch. No theorem derives a bridge from incomplete certificate data. -/

namespace BstLean.Part192
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part156 (aL hAL hWL dsL cWL Eplus Eminus)

/-- These are actual endpoint formulas, not names for unchecked decimal outputs. -/
structure EndpointCertificate (n : ℕ) (w : WorldParameters) (a : AgentParameters)
    extends ScalarCertificate n w a where
  sampleRoot : ℝ
  positiveTilt : ℝ
  negativeTilt : ℝ
  positiveExponent : ℝ
  negativeExponent : ℝ
  sampleRoot_pos : 0 < sampleRoot
  positiveTilt_pos : 0 < positiveTilt
  negativeTilt_neg : negativeTilt < 0
  positiveExponent_nonneg : 0 ≤ positiveExponent
  negativeExponent_nonneg : 0 ≤ negativeExponent
  positive_enclosure : Eplus aL (a.root + sampleRoot) worldRadius
    w.frame a.frame positiveTilt ≤ -positiveExponent
  negative_enclosure : Eminus aL (a.root + sampleRoot) worldRadius
    w.frame a.frame negativeTilt ≤ -negativeExponent
  positive_tail : exp (-((n : ℝ) * positiveExponent)) ≤ upperTail
  negative_tail : exp (-((n : ℝ) * negativeExponent)) ≤ lowerTail
  sampling_payment : 2 * exp (-100) ≤ samplingCharge

noncomputable def agentLedgerParameters : AgentParameters where
  charge := 122 / 1000000
  frame := 193 / 100
  root := hAL
  covariance := 647 / 1000
  centre := 41 / 400
  cutoff := 4482 / 10000
  mass := 0
  noiseLo := 465 / 1000
  noiseHi := 528 / 1000
  energyOrder := 32
  directionOrder := 12
  energyBound := 1
  directionBound := 1

/-- The unused analytic parameters assert no AgentCell supply.
This certificate checks the existing scalar ledger and endpoint enclosures only. -/
noncomputable def certificate16200 {n : ℕ} (hn : 16200 ≤ n) :
    EndpointCertificate n world16200Parameters agentLedgerParameters := by
  let up : ℝ := ((683381106559 / 1000000000000) ^ 2) ^ 8
  let um : ℝ := ((1347175989 / 1953125000) ^ 2) ^ 8
  let retained : ℝ := 5111 / 1000000 - BstLean.Part188.Base159_R.δPap -
    BstLean.Part188.Base159_R.vPap / hWL ^ 2
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have htail : up + um ≤ 611 / 125000 := by dsimp [up, um]; norm_num
  refine {
    dimensionLo := 16200
    dimensionHi := n
    dimension_mem := ⟨hn, le_rfl⟩
    noiseLo := 465 / 1000
    noiseHi := 528 / 1000
    overlapLo := 0
    overlapHi := 1
    radiusLo := 0
    radiusHi := hWL
    frameLo := cWL
    frameHi := 193 / 100
    noise_order := by norm_num
    overlap_order := by norm_num
    radius_order := by norm_num [hWL]
    frame_order := by norm_num [cWL]
    worldFrame_pos := by norm_num [world16200Parameters, cWL]
    agentFrame_pos := by norm_num [agentLedgerParameters]
    worldRadius := hWL
    worldRadius_pos := by norm_num [hWL]
    agentRoot_nonneg := by norm_num [agentLedgerParameters, hAL]
    retainedCharge := retained
    samplingCharge := 1 / 10 ^ 6
    upperTail := up
    lowerTail := um
    retainedCharge_nonneg := by
      norm_num [retained, BstLean.Part188.Base159_R.δPap,
        BstLean.Part188.Base159_R.vPap, hWL]
    samplingCharge_nonneg := by norm_num
    upperTail_nonneg := by dsimp [up]; positivity
    lowerTail_nonneg := by dsimp [um]; positivity
    totalBudget := 1 / 100
    ledger := ?_
    budget := le_rfl
    sampleRoot := dsL
    positiveTilt := 311 / 2000
    negativeTilt := -(823 / 2000)
    positiveExponent := 188001277 / 500000000000
    negativeExponent := 366834679 / 1000000000000
    sampleRoot_pos := by norm_num [dsL]
    positiveTilt_pos := by norm_num
    negativeTilt_neg := by norm_num
    positiveExponent_nonneg := by norm_num
    negativeExponent_nonneg := by norm_num
    positive_enclosure := BstLean.Part190.Frame16200.Ep_16200K16
    negative_enclosure := BstLean.Part190.Frame16200.Em_16200K16
    positive_tail := BstLean.Part160.tail8 hnR (by norm_num)
      BstLean.Part190.Frame16200.up_16200K16
    negative_tail := BstLean.Part160.tail8 hnR (by norm_num)
      BstLean.Part190.Frame16200.um_16200K16
    sampling_payment := BstLean.Part157.two_exp_neg_100 }
  dsimp [world16200Parameters, retained]
  linarith

/-- The existing chain proves the interface for each fixed arbitrary threshold. -/
theorem bridge16200 {n : ℕ} (hn : 16200 ≤ n) :
    BridgeStatement (paperProgram n) (1 / 100) :=
  (bridge_identity (paperProgram n)).2
    (fun t => BstLean.Part190.classifier_paper_uncond_16200 hn t)

/-- A finite lower bridge and the existing upper branch have no dimension gap. -/
theorem combine_upper_branch {lo : ℕ} (B : IntervalBridge lo 16199)
    {n : ℕ} (hn : lo ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t aL (10 ^ 12) x.1 x.2)} := by
  by_cases h : 16200 ≤ n
  · exact BstLean.Part190.classifier_paper_uncond_16200 h t
  · exact (bridge_identity (paperProgram n)).1 (B.bridge n hn (by omega)) t

/-- The new bridge has the same conclusion as Part 172 on its original range. -/
theorem bridge_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    (bridge_identity (paperProgram n)).1 (bridge16200 (by omega)) t =
      BstLean.Part172.classifier_paper_uncond hn hN t := rfl

end BstLean.Part192
#print axioms BstLean.Part192.certificate16200
#print axioms BstLean.Part192.bridge16200
#print axioms BstLean.Part192.combine_upper_branch
#print axioms BstLean.Part192.bridge_eq_172
#check BstLean.Part192.combine_upper_branch
