import BstLean.Part293AgentMix
import BstLean.Part293BiasModel
import BstLean.Part293OutputNorm
import BstLean.Part293DesignAdapter
import BstLean.Part293CappedPass
import BstLean.Part293TableEventFields
import BstLean.Part293TableStored

/-! One retained-data adapter combines the actual Agent, World and table supplies. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part161 BstLean.Part169
open BstLean.Part289 BstLean.BlueprintLow

noncomputable def cappedPass_of_agent_table {n : ℕ} (hn : LowBand n) (t : ℝ) (c : Ret n)
    (hw : c ∈ Hof (BstLean.Part290.worldHidden n) ∩
      (Ethm (statedDesign2 n).toCentres ∩ Ethp (statedDesign2 n).toCentres))
    (S : AgentSupplyInputs c)
    (hL : c.2.1.1 ∈ agentLatitudeEvent c.1.2 ((paperDesignP n).tau0 c))
    (hO : c ∈ BstLean.Part252.outputCentreEvent (paperDesignP n).toCentres)
    (hT : c ∈ BstLean.Part292.tableEvent n) : CappedPassInputs t c := by
  have W := worldSupplyBand hn.1 hn.2
  have hwindow := window_of_supply hn.1 W c hw
  have hguard := tableWorldGuard_of_supply hn.1 W c hw
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hb : 0 < normSq (bR c) := S.centre_pos
  have he : 0 < eR c := div_pos hb (by linarith)
  have hout := output_norm_capped hn.1 c he.le hO
  have hc : c.1.2 ≠ 0 := BstLean.Part172.sg_wr_ne
    (by have := hn.1; omega : 1 ≤ n) hguard.1
  have hτ : 0 < (paperDesignP n).tau0 c := hguard.1.1
  have hsplit : biasSplit c = lowPaperSplit (paperDesignP n) c := rfl
  let K := keptIx (paperDesignP n) c (biasSplit c)
  have hK : MeasurableSet K :=
    measurableSet_keptSet _ (biasSplit c).mgood (measurableSet_bulkIx _ c) _
  have hstored := storedInputs_of_table hn.1 c hT hguard hK (fun _ h => h.1)
  have hbias := biasInputs_of_model hn.1 hn.2 c hc hτ hb
    S.interfaces S.energy hL hout
    (fun a _ => table_variance_max hn.1 c hT hguard hb.ne' a) hstored
  rw [hsplit] at hbias
  refine {
    split := lowPaperSplit (paperDesignP n) c
    window := hwindow
    eta := rfl
    bias := hbias
    removed := removal_of_agentSupply hn.1 c S
    mixture := mixture_of_agentSupply hn.1 t c S
    displacement := displacement_of_agentSupply hn.1 c S
    arithmetic := arithmetic_comparison hn.1 t c
      (fun ho => arithmeticInputs_of_table hn.1 ho c hT hguard he hout) }

end BstLean.Part293
