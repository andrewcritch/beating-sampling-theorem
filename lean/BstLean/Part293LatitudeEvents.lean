import BstLean.Part293SourceEvents
import BstLean.Part291LatitudeSource
import BstLean.Part252PositiveOutput

/-! The latitude allowance includes the output-centre tail and its null event. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part166 BstLean.Part212 BstLean.Part252 BstLean.Part289

def latitudeFamily (n : ℕ) : Set (AgFam n) :=
  {k | winC k.1.1 k.1.2 ∧ BstLean.Part150.thetaC k.1.1 k.1.2 ≤ 0.528 →
    k ∈ latitudeEvent n (ENNReal.ofReal (3.042 / n))}

theorem latitudeFamily_measurable (n : ℕ) : MeasurableSet (latitudeFamily n) := by
  have hw : MeasurableSet {k : AgFam n | winC k.1.1 k.1.2} :=
    (measurableSet_lt measurable_const (measurable_snd.comp measurable_fst)).inter
      ((measurableSet_le measurable_const measurable_thetaC_key).inter
        (measurableSet_le measurable_thetaC_key measurable_const))
  have he : latitudeFamily n =
      ({k : AgFam n | winC k.1.1 k.1.2} ∩
        {k | BstLean.Part150.thetaC k.1.1 k.1.2 ≤ 0.528})ᶜ ∪
        latitudeEvent n (ENNReal.ofReal (3.042 / n)) := by
    ext k
    exact imp_iff_not_or
  rw [he]
  exact (hw.inter (measurableSet_le measurable_thetaC_key measurable_const)).compl.union
    (measurableSet_latitudeEvent n _)

theorem latitudeFamily_ret_charge {n : ℕ} (hn : BstLean.BlueprintLow.LowBand n) :
    (retDist (statedDesign2 n).toCentres).real
      (agentEv (statedDesign2 n) (latitudeFamily n))ᶜ ≤ (1 / 10000 : ℝ) := by
  rw [agentEv_compl]
  apply retDist_agent_charge (statedDesign2 n)
    (paperDesign_tauWorld passF passW measurable_passF measurable_passW)
    (latitudeFamily_measurable n) (by norm_num)
  intro c tau htau
  by_cases hw : winC c tau ∧ BstLean.Part150.thetaC c tau ≤ 0.528
  · simpa [latitudeFamily, BstLean.BlueprintLow.agentLatitudeEvent, hw.1, hw.2,
      Set.compl_setOf] using
      BstLean.BlueprintLow.agentLatitudeEvent_charge hn c hw.1 hw.2
  · have hempty : {A | ((c, tau), A) ∉ latitudeFamily n} = ∅ := by
      ext A
      simp only [latitudeFamily, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro hwin
      exact (hw hwin).elim
    rw [hempty, measureReal_empty]
    norm_num

noncomputable def latitudeCharge_of_band {n : ℕ} (hn : BstLean.BlueprintLow.LowBand n) :
    NetworkCharge (retDist (statedDesign2 n).toCentres) latitudeCharge where
  event := (agentEv (statedDesign2 n) (latitudeFamily n) ∩
    outputCentreEvent (statedDesign2 n).toCentres) ∩
      positiveOutputEvent (statedDesign2 n).toCentres
  measurable := ((measurableSet_agentEv _ (latitudeFamily_measurable n)).inter
    (outputCentreEvent_measurable _)).inter (positiveOutputEvent_measurable _)
  nonneg := by norm_num [latitudeCharge]
  complement := by
    rw [compl_inter, compl_inter]
    have hL := latitudeFamily_ret_charge hn
    have hO := (outputCentreEvent_charge (by have := hn.1; omega)
      (statedDesign2 n).toCentres).trans exp_neg12_row
    have hP := positiveOutputEvent_charge (by have := hn.1; omega)
      (statedDesign2 n).toCentres
    apply ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans (add_le_add hL hO)) hP)).trans
    norm_num [latitudeCharge]

end BstLean.Part293
