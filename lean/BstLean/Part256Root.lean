import BstLean.Part252RetunedMass

namespace BstLean.Part256
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part195 BstLean.Part222
open BstLean.Part252

theorem low_mass_from_source {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (Fsource : BstLean.Part253.SourceEvents c)
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part253.worldInterval) : LowResidualMass c := by
  obtain ⟨i, hi, hm⟩ := BstLean.Part253.needed_cells_cover hθ
  have F := BstLean.Part253.retuned_network_from_events hi hm
    Fsource
  have he : 0 < eR c := by linarith [(centre_energy_range hw ha).1]
  have hp := analyticBaseCertificate.pass_fields ha
  have hE := energyMoment_on_event (by norm_num) (paperDesignP 12225) c
    (hp.1.1.1.1 hw.2.1)
  have hE' : EnergyMoment (paperDesignP 12225) c ((2101 / 100) / 12225) :=
    ⟨by norm_num, hE.2.1, hE.2.2.trans
      (pow_le_pow_left₀ hE.1 energy_allowance_sharp_row 32)⟩
  have hD := BstLean.Part219.directionMoment_mono F.interfaces.direction
    (by norm_num [BstLean.Part253.directionCap] :
      BstLean.Part253.directionCap ≤ (91 / 1000 : ℝ))
  have hP : ParallelCentre (paperDesignP 12225) c (4 / 100) := by
    refine ⟨by norm_num, ?_⟩
    exact F.interfaces.parallel.2.trans (by
      gcongr
      norm_num [BstLean.Part253.parallelCap])
  exact low_mass_of_interfaces hw he (BstLean.Part253.paper_centre_nonneg c)
    ⟨hD, hE', hP⟩ (F.centre_energy.trans (retuned_energy_cap hi))
    (by norm_num : (0 : ℝ) < 42 / 10000) (by norm_num)
    (by norm_num [mixtureFloor]) (by linarith [retuned_low_mass_gap]) retuned_low_mass_price

noncomputable def rootInputs_from_source {c : Ret 12225} (t : ℝ)
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ hqBaseEvent)
    (F : BstLean.Part253.SourceEvents c)
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part253.worldInterval) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot :=
  hqRootInputs_on_base t hw hc (low_mass_from_source hw hc.1.1 F hθ)

end BstLean.Part256
