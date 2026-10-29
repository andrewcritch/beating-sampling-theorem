import BstLean.Part291SelectedEvents
import BstLean.Part291TICells
import BstLean.Part289Design

namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169 BstLean.Part182
open BstLean.Part215 (AgentPair)

def lowNoiseCells (n : ℕ) (j : Fin 160) : Set ((Fin n → ℝ) × ℝ) :=
  {x | BstLean.Part150.thetaC x.1 x.2 ∈ Icc (frameNoiseLower j) (frameNoiseUpper j)}

def lowSchurBandEvent (n : ℕ) : Set (AgFam n) :=
  selectedEvent (lowNoiseCells n)
    (fun j => lowSchurEvent n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j))

theorem lowSchurBandEvent_measurable (n : ℕ) : MeasurableSet (lowSchurBandEvent n) := by
  apply selectedEvent_measurable
  · intro j
    have hm : Measurable (fun x : (Fin n → ℝ) × ℝ => BstLean.Part150.thetaC x.1 x.2) := by
      unfold BstLean.Part150.thetaC BstLean.Part150.rhoC normSq
      fun_prop
    exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  · intro j
    exact lowSchurEvent_measurable _ _ _ _

theorem lowSchurBandEvent_select {n : ℕ} {x : (Fin n → ℝ) × ℝ} {a : AgentPair n}
    (hw : BstLean.Part150.thetaC x.1 x.2 ∈ Icc (0.46 : ℝ) 0.54)
    (h : (x,a) ∈ lowSchurBandEvent n) :
    ∃ j : Fin 160, BstLean.Part150.thetaC x.1 x.2 ∈ Icc (frameNoiseLower j) (frameNoiseUpper j) ∧
      (x,a) ∈ lowSchurEvent n (lowTIParameters j) (frameNoiseLower j) (frameNoiseUpper j) := by
  have hw' : BstLean.Part150.thetaC x.1 x.2 ∈ Icc (46 / 100 : ℝ) (54 / 100) := by
    norm_num at hw ⊢
    exact hw
  obtain ⟨j,hj⟩ := selectedCell_exists (lowNoiseCells n) (frame_noise_cover hw')
  refine ⟨j,hj.1,?_⟩
  have hh := mem_iInter.mp h j
  exact hh.resolve_left (fun hno => hno.1 hj)

theorem lowSchurBandEvent_charge {n : ℕ} (hn : 8000 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {a | ((c,τ),a) ∉ lowSchurBandEvent n} ≤ (0.00025 : ℝ) := by
  by_cases hw : ∃ j, (c,τ) ∈ lowNoiseCells n j
  · exact selectedEvent_charge (nuA n) (lowNoiseCells n) _ hw
      (fun j _ => lowSchurEvent_charge hn (lowTISupplyBand hn j) c hτ)
  · have he : {a | ((c,τ),a) ∉ lowSchurBandEvent n} = ∅ := by
      ext a
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      apply mem_iInter.mpr
      intro j
      exact Or.inl ⟨fun hj => hw ⟨j,hj.1⟩,mem_univ _⟩
    rw [he,measureReal_empty]
    norm_num

def lowSchurRetained (n : ℕ) : Set (Ret n) := agentEv (paperDesignP n) (lowSchurBandEvent n)

theorem lowSchurRetained_measurable (n : ℕ) : MeasurableSet (lowSchurRetained n) :=
  measurableSet_agentEv _ (lowSchurBandEvent_measurable n)

theorem lowSchurRetained_charge {n : ℕ} (hn : 8000 ≤ n) :
    (retDist (BstLean.Part289.statedDesign2 n).toCentres).real (lowSchurRetained n)ᶜ ≤ 0.00025 := by
  change (retDist (paperDesignP n).toCentres).real (agentEv (paperDesignP n) (lowSchurBandEvent n))ᶜ ≤ _
  rw [agentEv_compl]
  exact retDist_agent_charge _ (paperDesign_tauWorld passF passW measurable_passF measurable_passW)
    (lowSchurBandEvent_measurable n) (by norm_num) (fun c τ hτ => lowSchurBandEvent_charge hn c hτ)

end BstLean.BlueprintLow
