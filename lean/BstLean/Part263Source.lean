import BstLean.Part263Frame
import BstLean.Part253Supply

/-! Actual source events and explicit analytic certificates supply local fields. -/
namespace BstLean.Part263
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part188
open BstLean.Part169 (paperDesignP)
open BstLean.Part211

theorem energy_on_event {n : ℕ} (hn : 2 ≤ n) (c : Ret n)
    (hc : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2 ((paperDesignP n).tau0 c))
    {H : ℝ} (hH : BstLean.Part222.energyAllowance n ≤ H) :
    EnergyMoment (paperDesignP n) c H := by
  have h := BstLean.Part222.energyMoment_on_event (by omega : 1 ≤ n) (paperDesignP n) c hc
  exact ⟨h.1.trans hH, h.2.1, h.2.2.trans (pow_le_pow_left₀ h.1 hH 32)⟩

structure SourceInputs (n : ℕ) (c : Ret n) (r : CellData) (M H xi : ℝ) where
  energy_allowance : BstLean.Part222.energyAllowance n ≤ H
  parallel_nonneg : 0 ≤ xi
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
  certificate : CentreCertificate n J delta k k3 thetaLo thetaHi S MP qWorld v
  world_centre_pos : 0 < normSq c.1.2
  scale_pos : 0 < (paperDesignP n).tau0 c
  centre_eq : (paperDesignP n).bA c.1 c.2.1.1 = hiddenCentre (J := J)
    c.2.1.1.1 c.2.1.1.2 c.1.2 ((paperDesignP n).tau0 c)
  lower_pos : 0 < lowerEnergy
  full_nonneg : 0 ≤ r.centre
  MP_nonneg : 0 ≤ MP
  window : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc thetaLo thetaHi
  world_cap : 1 - BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ≤ qWorld
  signal_domain : 1 - BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
    Icc (0 : ℝ) (27 / 50)
  full_scalar : fullFormula n J delta k k3 thetaLo thetaHi S MP ≤ r.centre
  parallel_scalar : parallelFormula n J delta
    (momentAllowance n BstLean.Part154.csC delta k k3 thetaHi S)
    (BstLean.Part154.bN n BstLean.Part154.csC thetaHi)
    (√(momentAllowance n BstLean.Part154.csC delta k k3 thetaHi S) +
      sharpDeviation n BstLean.Part154.csC delta thetaLo thetaHi) thetaHi MP ≤ xi
  lower_scalar : lowerEnergy ≤ energyLower n (gMinus n) (gPlus n)
    (finiteEnergy n J delta)
    (BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c))
  upper_scalar : BstLean.Part206.energyUpper n (gMinus n) (gPlus n)
    (finiteEnergy n J delta) qWorld ≤ r.energy
  operator_scalar : BstLean.Part219.operatorAllowance c.1.2 ((paperDesignP n).tau0 c)
    eta (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ MP
  direction_scalar : BstLean.Part219.paperDirectionBudget c.1.2
    ((paperDesignP n).tau0 c) lowerEnergy (r.centre) eta
    (ENNReal.ofReal (1 / 20000)) ≤ M
  base_event : c.2.1.1 ∈ BstLean.Part222.centreBase n J c.1.2 ((paperDesignP n).tau0 c)
  error_event : c.2.1.1 ∈ BstLean.Part215.sharpErrorEvent c.1.2 ((paperDesignP n).tau0 c)
  operator_event : c.2.1.1 ∈ BstLean.Part215.operatorEvent c.1.2
    ((paperDesignP n).tau0 c) eta (ENNReal.ofReal (1 / 20000))
  energy_event : c.2.1.1 ∈ BstLean.Part222.energyEvent c.1.2 ((paperDesignP n).tau0 c)

theorem network_from_source {n : ℕ} (hn : 4096 ≤ n) (hnhi : n ≤ 16384) {c : Ret n}
    {r : CellData} {M H xi : ℝ} (F : SourceInputs n c r M H xi) :
    NetworkInputs n c r M H xi := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ : ENNReal.ofReal (1 / 20000 : ℝ) ≠ 0 := by norm_num
  have hSource := BstLean.Part222.centreSource_on_operator_event c.1.2
    ((paperDesignP n).tau0 c) F.eta F.MP hδ F.base_event F.operator_event
    (BstLean.Part222.operatorXiAllowance_le c.1.2 ((paperDesignP n).tau0 c)
      F.eta F.MP _ F.operator_scalar)
  have hC := centre_formula_junction (by omega) (by omega) F.J_pos c.1.2
    F.world_centre_pos F.scale_pos F.MP_nonneg F.v F.certificate F.window F.world_cap hSource
  have hF := hC.1.trans F.full_scalar
  rw [BstLean.Part222.fullError_normalization (by omega) (paperDesignP n) c
    F.centre_eq] at hF
  have hP := hC.2.1.trans F.parallel_scalar
  have hEL : F.lowerEnergy ≤ centreEnergy (paperDesignP n) c := by
    rw [BstLean.Part222.energy_normalization (by omega) (paperDesignP n) c
      F.scale_pos F.centre_eq]
    exact F.lower_scalar.trans hC.2.2.1
  have hEU : centreEnergy (paperDesignP n) c ≤ r.energy := by
    rw [BstLean.Part222.energy_normalization (by omega) (paperDesignP n) c
      F.scale_pos F.centre_eq]
    exact hC.2.2.2.1.trans F.upper_scalar
  have hbn : (n : ℝ) * F.lowerEnergy ≤ normSq ((paperDesignP n).bA c.1 c.2.1.1) := by
    unfold centreEnergy at hEL
    linarith [(le_div_iff₀ hnpos).mp hEL]
  have hbpos : 0 < normSq ((paperDesignP n).bA c.1 c.2.1.1) :=
    (mul_pos hnpos F.lower_pos).trans_le hbn
  refine ⟨F.scale_pos, hbpos, ?_, hEU,
    BstLean.Part222.centre_at_of_raw_bound (paperDesignP n) c hF⟩
  · exact ⟨BstLean.Part219.directionMoment_mono
      (BstLean.Part219.directionMoment_paper (by omega) (paperDesignP n) c
        F.scale_pos F.lower_pos F.full_nonneg hδ F.signal_domain hbn hF
        F.error_event F.operator_event) F.direction_scalar,
      energy_on_event (by omega) c F.energy_event F.energy_allowance,
      BstLean.Part222.parallelCentre_of_s12 (by omega) (paperDesignP n) c
        F.centre_eq hbpos F.parallel_nonneg hP⟩

end BstLean.Part263
