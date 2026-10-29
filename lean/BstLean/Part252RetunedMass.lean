import BstLean.Part252LowMassNum
import BstLean.Part252GuardedTable
import BstLean.Part253RetunedSupply

/-! The narrower World window and the existing common source event supply the
low-residual-mass bound. No additional event payment occurs here. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part195 BstLean.Part222

theorem retuned_energy_cap {i : Fin 60} (hi : BstLean.Part253.needed i) :
    BstLean.Part253.retunedEnergy i ≤ (702 / 1000 : ℝ) := by
  fin_cases i <;> norm_num [BstLean.Part253.needed] at hi <;>
    norm_num [BstLean.Part253.retunedEnergy, BstLean.Part253.energyTable]

theorem retuned_low_mass_gap :
    (4 / 100 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - mixtureFloor) -
      (√(702 / 1000) + √((4 / 100 : ℝ) / 12225)) := by
  have h1 : (880019 / 10 ^ 6 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - mixtureFloor) :=
    le_sqrt_of_sq_le (by norm_num [mixtureFloor])
  have h2 : √(702 / 1000 : ℝ) ≤ 837855 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √((4 / 100 : ℝ) / 12225) ≤ 181 / 10 ^ 5 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem retuned_low_mass_price :
    massBound 12225 (91 / 1000) ((2101 / 100) / 12225) (4 / 100) (702 / 1000)
      (42 / 10000) mixtureFloor ≤ 12225 * lowMassBudget := by
  have hg := retuned_low_mass_gap
  have hg0 : 0 < √((1 - 42 / 10000) ^ 2 - mixtureFloor) -
      (√(702 / 1000) + √((4 / 100 : ℝ) / 12225)) := by linarith
  have hr := rotation_twelve
  have hr0 := rotationConstant_nonneg 12
  unfold massBound
  simp only [Nat.cast_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 12225)
  calc
    _ ≤ (((2101 / 100 : ℝ) / 12225) / (42 / 10000)) ^ 32 +
        ((48 / 10 : ℝ) ^ 24 * ((91 / 1000) / 12225) ^ 12) /
          (4 / 100) ^ 24 := by
      have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 100) hg 24
      have hn := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hr0 hr 24)
        (by positivity : (0 : ℝ) ≤ ((91 / 1000) / 12225) ^ 12)
      exact add_le_add_right (div_le_div₀ (by positivity) hn (by positivity) hd)
        ((((2101 / 100 : ℝ) / 12225) / (42 / 10000)) ^ 32)
    _ ≤ lowMassBudget := by norm_num [lowMassBudget]

theorem sourceEvents_on_common {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (hs : c ∈ sharedGood (paperDesignP 12225)) : BstLean.Part253.SourceEvents c := by
  have hsrc := analyticBaseCertificate.centre_sources ha hw.2.1
  have hc : 0 < normSq c.1.2 :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm fun h => hw.1 (normSq_eq_zero h))
  refine { world_centre_pos := hc
           scale_pos := hw.2.1
           base_event := ?_
           error_event := ?_
           operator_event := ?_
           energy_event := ?_ }
  · exact ⟨2, by norm_num, hsrc⟩
  · exact analyticBaseCertificate.direction ha hw.2.1
  · have hη : (6 / 1000 : ℝ) = 0.006 := by norm_num
    rw [← hη]
    exact hs.2 hw.2.1
  · exact (analyticBaseCertificate.pass_fields ha).1.1.1.1 hw.2.1

theorem low_mass_on_cell {c : Ret 12225} {i : Fin 60}
    (hi : BstLean.Part253.needed i)
    (hm : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ BstLean.Part253.cell i)
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (hs : c ∈ sharedGood (paperDesignP 12225)) : LowResidualMass c := by
  have F := BstLean.Part253.retuned_network_from_events hi hm
    (sourceEvents_on_common hw ha hs)
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

theorem low_mass_on_common {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (ha : c ∈ analyticBase)
    (hs : c ∈ sharedGood (paperDesignP 12225))
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part253.worldInterval) : LowResidualMass c := by
  obtain ⟨i, hi, hm⟩ := BstLean.Part253.needed_cells_cover hθ
  exact low_mass_on_cell hi hm hw ha hs

noncomputable def rootInputs_on_common {c : Ret 12225} (t : ℝ)
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ hqBaseEvent)
    (hs : c ∈ sharedGood (paperDesignP 12225))
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part253.worldInterval) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot :=
  hqRootInputs_on_base t hw hc (low_mass_on_common hw hc.1.1 hs hθ)

theorem replacement_on_common {c : Ret 12225} (t : ℝ)
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ hqBaseEvent)
    (hs : c ∈ sharedGood (paperDesignP 12225))
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
      BstLean.Part253.worldInterval) :
    |√(QStand (paperDesignP 12225) t c) - √(qTilde (paperDesignP 12225) t c)| ≤
      BstLean.Part243.rowRoot := by
  let R := rootInputs_on_common t hw hc hs hθ
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c R.split R.window
    R.passes R.fluctuation).trans R.scalar

/-- The common source events and narrower World window discharge the mass
premise. Table payment and the local frame remain explicit inputs. -/
noncomputable def retunedAgentPackage {H : Set (Ret 12225)}
    (h : TablePayment H) (t : ℝ)
    (hframe : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame))
    (hwindow : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
        BstLean.Part253.worldInterval) :
    BstLean.Part243.AgentPackage 12225 H BstLean.Part243.rowRadius
      BstLean.Part249.optionBAgentFrame BstLean.Part243.rowRoot
      BstLean.Part243.proposedRetainedCharge t := by
  apply hqAgentPackage h t hframe
  intro c hc
  obtain ⟨F⟩ := hframe c hc
  exact low_mass_on_common (window_of_frame F) hc.2.1.1.1 hc.2.2 (hwindow c hc)

/-- The guarded table charge pays only failures inside the analytic base. -/
noncomputable def retunedAgentPackage_of_guarded {H : Set (Ret 12225)}
    (h : GuardedTablePayment H) (t : ℝ)
    (hframe : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame))
    (hwindow : ∀ c ∈ goodSet H (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈
        BstLean.Part253.worldInterval) :
    BstLean.Part243.AgentPackage 12225 H BstLean.Part243.rowRadius
      BstLean.Part249.optionBAgentFrame BstLean.Part243.rowRoot
      BstLean.Part243.proposedRetainedCharge t := by
  apply hqAgentPackage_of_base_charge (hqBaseEvent_charge_of_guarded h) t hframe
  intro c hc
  obtain ⟨F⟩ := hframe c hc
  exact low_mass_on_common (window_of_frame F) hc.2.1.1.1 hc.2.2 (hwindow c hc)

end BstLean.Part252
