import BstLean.Part281Frame11883
import BstLean.Part280Rows11883
import BstLean.Part281RowBridge
import BstLean.Part281Odd
namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188
open BstLean.Part192 BstLean.Part196 BstLean.Part280

theorem energyCap11883 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (scalarRow11883.table i).energy ≤ m2Caps.Ecap := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [scalarRow11883,cell11883,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]

noncomputable def localRoot11883 : SharpLocalSupply 11883 m2Caps (sharpTableN 11883)
    (m2Guard 11883) (BstLean.Part159.Hof WorldRow11883.worldPackage.hidden) :=
  localRoot_from_numerics (by norm_num) (by norm_num) WorldRow11883.worldPackage rfl
    WorldRow11883.product_lower (WorldRow11883.producthi.2.trans (by norm_num))
    scalarRow11883 (fun _ hi => N11883.sourceNumerics11883 hi)
    (by norm_num [scalarRow11883,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow11883,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow11883,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    energyCap11883

theorem compatible11883 : agent11883.charge ≤ master11883.retainedCharge := by
  rw [show master11883.retainedCharge = scalar11883.retainedCharge from
    congrArg (fun C => C.retainedCharge) preserves11883]
  norm_num [agent11883,scalar11883]

noncomputable def row11883 : BstLean.Part259.RowInputs 11883 :=
  row_from_sharp (by norm_num) (by norm_num) N11883.frameData11883 agent11883 master11883
    BstLean.Part280.m2Certificate11883 localRoot11883 (by norm_num [BstLean.Part280.Sharp.Row11883.rootTarget,agent11883])
    rfl rfl (by norm_num [agent11883]) compatible11883

theorem classifier_stated_11883 (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 11883).prod (sampMeas (10^12) 11883)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 11883) t
        BstLean.Part156.aL (10^12) x.1 x.2)} :=
  classifier_from_sharp_row row11883 (fun _ hc => hc.1) t
end BstLean.Part281
