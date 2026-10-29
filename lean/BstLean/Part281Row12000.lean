import BstLean.Part281Frame12000
import BstLean.Part280Rows11998
import BstLean.Part281RowBridge
import BstLean.Part281Odd
namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188
open BstLean.Part192 BstLean.Part196 BstLean.Part280

theorem energyCap12000 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (scalarRow12000.table i).energy ≤ m2Caps.Ecap := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [scalarRow12000,cell12000,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]

noncomputable def localRoot12000 : SharpLocalSupply 12000 m2Caps (sharpTableN 12000)
    (m2Guard 12000) (BstLean.Part159.Hof WorldRow12000.worldPackage.hidden) :=
  localRoot_from_numerics (by norm_num) (by norm_num) WorldRow12000.worldPackage rfl
    WorldRow12000.product_lower (WorldRow12000.producthi.2.trans (by norm_num))
    scalarRow12000 (fun _ hi => N12000.sourceNumerics12000 hi)
    (by norm_num [scalarRow12000,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow12000,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow12000,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    energyCap12000

theorem compatible12000 : agent12000.charge ≤ master12000.retainedCharge := by
  rw [show master12000.retainedCharge = scalar12000.retainedCharge from
    congrArg (fun C => C.retainedCharge) preserves12000]
  norm_num [agent12000,scalar12000]

noncomputable def row12000 : BstLean.Part259.RowInputs 12000 :=
  row_from_sharp (by norm_num) (by norm_num) N12000.frameData12000 agent12000 master12000
    BstLean.Part280.m2Certificate12000 localRoot12000 (by norm_num [BstLean.Part280.Sharp.Row12000.rootTarget,agent12000])
    rfl rfl (by norm_num [agent12000]) compatible12000

theorem classifier_stated_12000 (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 12000).prod (sampMeas (10^12) 12000)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12000) t
        BstLean.Part156.aL (10^12) x.1 x.2)} :=
  classifier_from_sharp_row row12000 (fun _ hc => hc.1) t
end BstLean.Part281
