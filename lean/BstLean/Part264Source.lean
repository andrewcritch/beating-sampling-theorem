import BstLean.Part264Operator
import BstLean.Part264Direction
import BstLean.Part264EnergyLower
import BstLean.Part264WorldSource
import BstLean.Part263Source

/-! The remaining local analytic certificates are separate from paid events. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188 BstLean.Part211
open BstLean.Part263 (CellData)

structure CellSourceNumerics (n : ℕ) (r : CellData) (M H xi : ℝ) where
  thetaHi : ℝ
  S : ℝ
  certificate : CentreCertificate n n 0.011 1.22 1.12 (0.46)
    thetaHi S 1.22 (1 - r.lower) (fun _ => 0.006)
  energy_allowance : BstLean.Part222.energyAllowance n ≤ H
  parallel_nonneg : 0 ≤ xi
  centre_nonneg : 0 ≤ r.centre
  centre_upper : r.centre ≤ 0.1
  direction_allowance : 0.08955 ≤ M
  source_lower : 0.46 ≤ r.lower
  source_upper : r.upper ≤ thetaHi
  source_upper532 : r.upper ≤ 0.532
  full_scalar : fullFormula n n 0.011 1.22 1.12 (0.46) thetaHi S 1.22 ≤ r.centre
  parallel_scalar : parallelFormula n n 0.011
    (momentAllowance n BstLean.Part154.csC 0.011 1.22 1.12 thetaHi S)
    (BstLean.Part154.bN n BstLean.Part154.csC thetaHi)
    (√(momentAllowance n BstLean.Part154.csC 0.011 1.22 1.12 thetaHi S) +
      sharpDeviation n BstLean.Part154.csC 0.011 (0.46) thetaHi) thetaHi 1.22 ≤ xi
  upper_scalar : BstLean.Part206.energyUpper n (gMinus n) (gPlus n)
    (finiteEnergy n n 0.011) (1 - r.lower) ≤ r.energy

noncomputable def sourceInputs_of_numerics {n : ℕ} (hn : 12225 ≤ n)
    {c : Ret n} {r : CellData} {M H xi : ℝ}
    (N : CellSourceNumerics n r M H xi)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc r.lower r.upper)
    (hDir : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (0.47199 : ℝ) 0.52358)
    (F : BstLean.Part262.SourceEvents c) : BstLean.Part263.SourceInputs n c r M H xi where
  energy_allowance := N.energy_allowance
  parallel_nonneg := N.parallel_nonneg
  J := n
  J_pos := by omega
  delta := 0.011
  k := 1.22
  k3 := 1.12
  thetaLo := 0.46
  thetaHi := N.thetaHi
  S := N.S
  MP := 1.22
  qWorld := 1 - r.lower
  lowerEnergy := 0.665
  eta := 0.006
  v := fun _ => 0.006
  certificate := N.certificate
  world_centre_pos := F.world_centre_pos
  scale_pos := F.scale_pos
  centre_eq := BstLean.Part263.paper_centre_eq c
  lower_pos := by norm_num
  full_nonneg := N.centre_nonneg
  MP_nonneg := by norm_num
  window := ⟨N.source_lower.trans hm.1, hm.2.trans N.source_upper⟩
  world_cap := sub_le_sub_left hm.1 1
  signal_domain := by
    have hl := N.source_lower.trans hm.1
    have hu := hm.2.trans N.source_upper532
    constructor <;> linarith
  full_scalar := N.full_scalar
  parallel_scalar := N.parallel_scalar
  lower_scalar := by
    have h := (energy_lower_data hn
      ⟨N.source_lower.trans hm.1,hm.2.trans N.source_upper532⟩).2.2
    convert h using 1 <;> norm_num
  upper_scalar := N.upper_scalar
  operator_scalar := operator_allowance_le hn _ F.scale_pos
  direction_scalar := (direction_budget_le hn _ _ _ _ _ _ hDir (by norm_num)
    N.centre_nonneg N.centre_upper (operator_allowance_le hn _ F.scale_pos)).trans
      N.direction_allowance
  base_event := F.base_event
  error_event := F.error_event
  operator_event := F.operator_event
  energy_event := F.energy_event

theorem network_from_numerics {n : ℕ} (hn : n ∈ Icc 12225 12349)
    {c : Ret n} {r : CellData} {M H xi : ℝ}
    (N : CellSourceNumerics n r M H xi)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc r.lower r.upper)
    (hw : c ∈ BstLean.Part159.Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) : BstLean.Part263.NetworkInputs n c r M H xi :=
  BstLean.Part263.network_from_source (by have := hn.1; omega) (by have := hn.2; omega)
    (sourceInputs_of_numerics hn.1 N hm (direction_window hn hw hc) (source_events hn hw hc))

end BstLean.Part264
