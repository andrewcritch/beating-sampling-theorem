import BstLean.Part252RetunedMass
import BstLean.Part252TablePayment
import BstLean.Part250World

/-! The supplied World window and the charged common event populate the
dimension-12225 root inputs without a table-payment or mass premise. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part161 BstLean.Part169

noncomputable def rootWorldInterval : Set ℝ :=
  Icc (BstLean.Part253.noiseNode 10) (BstLean.Part253.noiseNode 53)

theorem rootWorldInterval_cover {θ : ℝ} (hw : θ ∈ rootWorldInterval) :
    ∃ i : Fin 60, BstLean.Part253.needed i ∧ θ ∈ BstLean.Part253.cell i := by
  obtain ⟨j, hj, hc⟩ := BstLean.Part193.chain_coverage
    (fun j => BstLean.Part253.noiseNode (j + 10)) (by norm_num : 0 < 43)
    (fun j _ => BstLean.Part253.noiseNode_mono (by omega)) hw
  have hj' := Finset.mem_range.mp hj
  let i : Fin 60 := ⟨j + 10, by omega⟩
  refine ⟨i, ⟨by dsimp [i]; omega, by dsimp [i]; omega⟩, ?_⟩
  change θ ∈ Icc (BstLean.Part253.noiseNode (j + 10))
    (BstLean.Part253.noiseNode (j + 10 + 1))
  have he : j + 1 + 10 = j + 10 + 1 := by omega
  have he' : j + (10 + 1) = j + 10 + 1 := by omega
  simpa only [Set.mem_Icc, he, he'] using hc

theorem actual_world_interval {c : Ret 12225}
    (hc : c ∈ Hof BstLean.Part250.worldPackage.hidden) (ha : c ∈ analyticBase) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP 12225).tau0 c) ∈ rootWorldInterval := by
  have hang := analyticBaseCertificate.angles ha
  have hw := BstLean.Part250.internalWorld.noise_window c ⟨hc, hang⟩
  have hlo : BstLean.Part253.noiseNode 10 ≤
      BstLean.Part227.noiseLower (202225 / 100000) :=
    (le_trans (by norm_num [BstLean.Part253.noiseNode]) BstLean.Part250.noiselo.1)
  have hhi : BstLean.Part227.noiseUpper 12225 (202831 / 100000) ≤
      BstLean.Part253.noiseNode 53 :=
    BstLean.Part250.noisehi.2.trans (by norm_num [BstLean.Part253.noiseNode])
  exact ⟨hlo.trans hw.1, hw.2.trans hhi⟩

theorem actual_world_window {c : Ret 12225}
    (hc : c ∈ Hof BstLean.Part250.worldPackage.hidden) (ha : c ∈ analyticBase) :
    WINDOW (paperDesignP 12225) c := by
  have hi := actual_world_interval hc ha
  have hτ := (BstLean.Part250.internalWorld.scale_identity c.1.1 hc).1
  rw [← BstLean.Part250.internalWorld.scale_eq c] at hτ
  apply window_of_theta (by norm_num) _ c hτ
  exact ⟨(le_trans (by norm_num [rootWorldInterval, BstLean.Part253.noiseNode]) hi.1),
    hi.2.trans (by norm_num [rootWorldInterval, BstLean.Part253.noiseNode])⟩

noncomputable def completedRootInputs {c : Ret 12225} (t : ℝ)
    (hw : c ∈ Hof BstLean.Part250.worldPackage.hidden)
    (hc : c ∈ hqBaseEvent) (hs : c ∈ sharedGood (paperDesignP 12225)) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot := by
  have ha := hc.1.1
  have hwin := actual_world_window hw ha
  have hmass : LowResidualMass c := by
    obtain ⟨i, hi, hm⟩ := rootWorldInterval_cover (actual_world_interval hw ha)
    exact low_mass_on_cell hi hm hwin ha hs
  exact hqRootInputs_on_base t hwin hc hmass

structure CompletedRootCertificate where
  base_measurable : MeasurableSet hqBaseEvent
  base_charge : (retDist (paperCentres 12225)).real
    (Hof BstLean.Part250.worldPackage.hidden ∩ hqBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance
  inputs : ∀ (t : ℝ) (c : Ret 12225), c ∈ Hof BstLean.Part250.worldPackage.hidden →
    c ∈ hqBaseEvent → c ∈ sharedGood (paperDesignP 12225) →
      BstLean.Part243.RootInputs 12225 t c BstLean.Part243.rowRoot

noncomputable def completedRootCertificate : CompletedRootCertificate where
  base_measurable := hqBaseEvent_measurable
  base_charge := hqBaseEvent_charge (certifiedTablePayment _)
  inputs := fun t _ hw hc hs => completedRootInputs t hw hc hs

theorem completed_replacement {c : Ret 12225} (t : ℝ)
    (hw : c ∈ Hof BstLean.Part250.worldPackage.hidden)
    (hc : c ∈ hqBaseEvent) (hs : c ∈ sharedGood (paperDesignP 12225)) :
    |√(QStand (paperDesignP 12225) t c) - √(qTilde (paperDesignP 12225) t c)| ≤
      BstLean.Part243.rowRoot := by
  let R := completedRootInputs t hw hc hs
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c R.split R.window
    R.passes R.fluctuation).trans R.scalar

noncomputable def completedAgentPackage (t : ℝ)
    (hframe : ∀ c ∈ goodSet (Hof BstLean.Part250.worldPackage.hidden)
      (hqBaseEvent ∩ sharedGood (paperDesignP 12225))
      (HbarW (paperDesignP 12225)) BstLean.Part243.rowRadius,
      Nonempty (BstLean.Part249.FrameInputs 12225 c BstLean.Part249.optionBAgentFrame)) :
    BstLean.Part243.AgentPackage 12225 (Hof BstLean.Part250.worldPackage.hidden)
      BstLean.Part243.rowRadius BstLean.Part249.optionBAgentFrame BstLean.Part243.rowRoot
      BstLean.Part243.proposedRetainedCharge t := by
  apply hqAgentPackage (certifiedTablePayment _) t hframe
  intro c hc
  have ha := hc.2.1.1.1
  have hw := actual_world_window hc.1.1 ha
  obtain ⟨i, hi, hm⟩ := rootWorldInterval_cover (actual_world_interval hc.1.1 ha)
  exact low_mass_on_cell hi hm hw ha hc.2.2

end BstLean.Part252
