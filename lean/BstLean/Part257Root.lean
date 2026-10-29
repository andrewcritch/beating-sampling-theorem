import BstLean.Part257Events

/-! The paid source event supplies root inputs on the actual World interval. -/
namespace BstLean.Part257
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part195 BstLean.Part222
open BstLean.Part252

theorem low_mass_on_source_cell {c : Ret 12225} {i : Fin 60}
    (hi : BstLean.Part253.needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ BstLean.Part253.cell i)
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (Fsource : BstLean.Part253.SourceEvents c) : LowResidualMass c := by
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

noncomputable def rootInputs_of_base {c : Ret 12225} (t : ℝ)
    (hw : c ∈ BstLean.Part159.Hof BstLean.Part250.worldPackage.hidden)
    (hc : c ∈ sourceBase) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot := by
  have ha := hc.1.1.1
  have hwin := actual_world_window hw ha
  have hmass : LowResidualMass c := by
    obtain ⟨i, hi, hm⟩ := rootWorldInterval_cover (actual_world_interval hw ha)
    exact low_mass_on_source_cell hi hm hwin ha (sourceEvents_of_base hw hc)
  exact hqRootInputs_on_base t hwin hc.1 hmass

end BstLean.Part257
