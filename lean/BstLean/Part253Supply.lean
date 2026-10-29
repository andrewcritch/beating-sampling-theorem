import BstLean.Part253Scalar
import BstLean.Part222Supply

/-! Actual source events supply the network fields. The unproved numerical
centre and direction certificates remain explicit in SourceInputs. -/
namespace BstLean.Part253
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part211

theorem paper_centre_eq (c : Ret 12225) :
    (paperDesignP 12225).bA c.1 c.2.1.1 = hiddenCentre (J := 12225)
      c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c) := by
  ext j
  change BstLean.Part150.bT 12225 12225 c.2.1.1.1 c.2.1.1.2 c.1.2
      ((paperDesignP 12225).tau0 c) j /
      BstLean.Part150.rhoC c.1.2 ((paperDesignP 12225).tau0 c) = _
  simp only [hiddenCentre, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem paper_centre_nonneg (c : Ret 12225) (j : Fin (mA 12225)) :
    0 ≤ (paperDesignP 12225).bA c.1 c.2.1.1 j := by
  rw [paper_centre_eq]
  exact BstLean.Part222.hiddenCentre_nonneg _ _ _ _ j

theorem energy_on_event (c : Ret 12225)
    (hc : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2 ((paperDesignP 12225).tau0 c)) :
    EnergyMoment (paperDesignP 12225) c energyCap := by
  have h := BstLean.Part222.energyMoment_on_event (by norm_num) (paperDesignP 12225) c hc
  have hle : BstLean.Part222.energyAllowance 12225 ≤ energyCap := energy_allowance_le
  exact ⟨h.1.trans hle, h.2.1, h.2.2.trans (pow_le_pow_left₀ h.1 hle 32)⟩

/-- These are the remaining scalar and source-event obligations, rather than
assumed conclusions about the network frame, mass, centre or direction. -/
structure SourceInputs (c : Ret 12225) (i : Fin 60) where
  J : ℕ
  J_pos : 1 ≤ J
  delta : ℝ
  k : ℝ
  k3 : ℝ
  thetaLo : ℝ
  thetaHi : ℝ
  S : ℝ
  MP : ℝ
  qWorld : ℝ
  lowerEnergy : ℝ
  eta : ℝ
  v : ℝ → ℝ
  certificate : CentreCertificate 12225 J delta k k3 thetaLo thetaHi S MP qWorld v
  world_centre_pos : 0 < normSq c.1.2
  scale_pos : 0 < (paperDesignP 12225).tau0 c
  centre_eq : (paperDesignP 12225).bA c.1 c.2.1.1 = hiddenCentre (J := J)
    c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP 12225).tau0 c)
  lower_pos : 0 < lowerEnergy
  full_nonneg : 0 ≤ centreTable (centreGroup i)
  MP_nonneg : 0 ≤ MP
  window : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ Icc thetaLo thetaHi
  world_cap : 1 - BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ≤ qWorld
  signal_domain : 1 - BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
    Icc (0 : ℝ) (27 / 50)
  full_scalar : fullFormula 12225 J delta k k3 thetaLo thetaHi S MP ≤ centreTable (centreGroup i)
  parallel_scalar : parallelFormula 12225 J delta
    (momentAllowance 12225 BstLean.Part154.csC delta k k3 thetaHi S)
    (BstLean.Part154.bN 12225 BstLean.Part154.csC thetaHi)
    (√(momentAllowance 12225 BstLean.Part154.csC delta k k3 thetaHi S) +
      sharpDeviation 12225 BstLean.Part154.csC delta thetaLo thetaHi) thetaHi MP ≤ parallelCap
  lower_scalar : lowerEnergy ≤ energyLower 12225 (gMinus 12225) (gPlus 12225)
    (finiteEnergy 12225 J delta)
    (BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c))
  upper_scalar : BstLean.Part206.energyUpper 12225 (gMinus 12225) (gPlus 12225)
    (finiteEnergy 12225 J delta) qWorld ≤ energyTable i
  operator_scalar : BstLean.Part219.operatorAllowance c.1.2 ((paperDesignP 12225).tau0 c)
    eta (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ MP
  direction_scalar : BstLean.Part219.paperDirectionBudget c.1.2
    ((paperDesignP 12225).tau0 c) lowerEnergy (centreTable (centreGroup i)) eta
    (ENNReal.ofReal (1 / 20000)) ≤ directionCap
  base_event : c.2.1.1 ∈ BstLean.Part222.centreBase 12225 J c.1.2 ((paperDesignP 12225).tau0 c)
  error_event : c.2.1.1 ∈ BstLean.Part215.sharpErrorEvent c.1.2 ((paperDesignP 12225).tau0 c)
  operator_event : c.2.1.1 ∈ BstLean.Part215.operatorEvent c.1.2
    ((paperDesignP 12225).tau0 c) eta (ENNReal.ofReal (1 / 20000))
  energy_event : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2 ((paperDesignP 12225).tau0 c)

structure NetworkInputs (c : Ret 12225) (i : Fin 60) : Prop where
  scale_pos : 0 < (paperDesignP 12225).tau0 c
  centre_pos : 0 < normSq ((paperDesignP 12225).bA c.1 c.2.1.1)
  centre_nonneg : ∀ j, 0 ≤ (paperDesignP 12225).bA c.1 c.2.1.1 j
  interfaces : WFInterfaces (paperDesignP 12225) c directionCap energyCap parallelCap
  centre_energy : centreEnergy (paperDesignP 12225) c ≤ energyTable i
  full_centre : BstLean.Part160.CENTRE_at (paperDesignP 12225) c (centreTable (centreGroup i))

theorem network_from_source {c : Ret 12225} {i : Fin 60} (F : SourceInputs c i) :
    NetworkInputs c i := by
  have hδ : ENNReal.ofReal (1 / 20000 : ℝ) ≠ 0 := by norm_num
  have hSource := BstLean.Part222.centreSource_on_operator_event c.1.2
    ((paperDesignP 12225).tau0 c) F.eta F.MP hδ F.base_event F.operator_event
    (BstLean.Part222.operatorXiAllowance_le c.1.2 ((paperDesignP 12225).tau0 c)
      F.eta F.MP _ F.operator_scalar)
  have hC := centre_formula_junction (by norm_num) (by norm_num) F.J_pos c.1.2
    F.world_centre_pos F.scale_pos F.MP_nonneg F.v F.certificate F.window F.world_cap hSource
  have hF := hC.1.trans F.full_scalar
  rw [BstLean.Part222.fullError_normalization (by norm_num) (paperDesignP 12225) c
    F.centre_eq] at hF
  have hP := hC.2.1.trans F.parallel_scalar
  have hEL : F.lowerEnergy ≤ centreEnergy (paperDesignP 12225) c := by
    rw [BstLean.Part222.energy_normalization (by norm_num) (paperDesignP 12225) c
      F.scale_pos F.centre_eq]
    exact F.lower_scalar.trans hC.2.2.1
  have hEU : centreEnergy (paperDesignP 12225) c ≤ energyTable i := by
    rw [BstLean.Part222.energy_normalization (by norm_num) (paperDesignP 12225) c
      F.scale_pos F.centre_eq]
    exact hC.2.2.2.1.trans F.upper_scalar
  have hbn : (12225 : ℝ) * F.lowerEnergy ≤ normSq ((paperDesignP 12225).bA c.1 c.2.1.1) := by
    unfold centreEnergy at hEL
    linarith [(le_div_iff₀ (by norm_num : (0 : ℝ) < 12225)).mp hEL]
  have hbpos : 0 < normSq ((paperDesignP 12225).bA c.1 c.2.1.1) :=
    (mul_pos (by norm_num) F.lower_pos).trans_le hbn
  refine ⟨F.scale_pos, hbpos, ?_, ?_, hEU,
    BstLean.Part222.centre_at_of_raw_bound (paperDesignP 12225) c hF⟩
  · intro j
    rw [F.centre_eq]
    exact BstLean.Part222.hiddenCentre_nonneg _ _ _ _ j
  · exact ⟨BstLean.Part219.directionMoment_mono
      (BstLean.Part219.directionMoment_paper (by norm_num) (paperDesignP 12225) c
        F.scale_pos F.lower_pos F.full_nonneg hδ F.signal_domain hbn hF
        F.error_event F.operator_event) F.direction_scalar,
      energy_on_event c F.energy_event,
      BstLean.Part222.parallelCentre_of_s12 (by norm_num) (paperDesignP 12225) c
        F.centre_eq hbpos (by norm_num [parallelCap]) hP⟩

/-- The rational cell proofs supply every cutoff and mass field. -/
noncomputable def frameInputs_from_network (C : LocalCovariance cell capTable)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (F : NetworkInputs c i) :
    LocalFrameInputs cell capTable c BstLean.Part249.optionBAgentFrame := by
  have S := scalar_on_needed hi
  exact {
    cov_le := C
    index := i
    index_needed := hi
    member := hm
    cutoff := cutoffTable
    centreAllowance := centreTable
    massAllowance := massTable
    M := directionCap
    H := energyCap
    xiP := parallelCap
    E := energyTable i
    u := radiusCutoff
    order := 12
    order_pos := by norm_num
    order_le := by norm_num
    scale_pos := F.scale_pos
    centre_pos := F.centre_pos
    centre_nonneg := F.centre_nonneg
    interfaces := F.interfaces
    centre_energy := F.centre_energy
    u_pos := by norm_num [radiusCutoff]
    u_lt := by norm_num [radiusCutoff]
    cutoff_pos := S.cutoff_pos
    cutoff_lt := S.cutoff_lt
    gap_pos := S.gap_pos
    covariance_nonneg := S.covariance_nonneg
    full_centre := F.full_centre
    mass_scalar := S.mass_scalar
    frame_scalar := S.frame_scalar }

noncomputable def frameInputs_from_source (C : LocalCovariance cell capTable)
    {c : Ret 12225} {i : Fin 60} (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ cell i)
    (F : SourceInputs c i) : LocalFrameInputs cell capTable c BstLean.Part249.optionBAgentFrame :=
  frameInputs_from_network C hi hm (network_from_source F)

end BstLean.Part253
