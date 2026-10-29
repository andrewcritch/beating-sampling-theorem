import BstLean.Part281Frame12224
import BstLean.Part280Cert12224
import BstLean.Part281RowBridge
import BstLean.Part281Odd
namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188
open BstLean.Part192 BstLean.Part196 BstLean.Part280

theorem energyCap12224 (i : Fin 60) (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (scalarRow12224.table i).energy ≤ m2Caps.Ecap := by
  fin_cases i
  all_goals norm_num at hi
  all_goals norm_num [scalarRow12224,cell12224,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps]

noncomputable def localRoot12224 : SharpLocalSupply 12224 m2Caps (sharpTableN 12224)
    (m2Guard 12224) (BstLean.Part159.Hof WorldRow12224.worldPackage.hidden) :=
  localRoot_from_numerics (by norm_num) (by norm_num) WorldRow12224.worldPackage rfl
    WorldRow12224.product_lower (WorldRow12224.producthi.2.trans (by norm_num))
    scalarRow12224 (fun _ hi => N12224.sourceNumerics12224 hi)
    (by norm_num [scalarRow12224,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow12224,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    (by norm_num [scalarRow12224,m2Caps,BstLean.Part275.pilotCaps,BstLean.Part275.part262Caps])
    energyCap12224

theorem compatible12224 : agent12224.charge ≤ master12224.retainedCharge := by
  rw [show master12224.retainedCharge = scalar12224.retainedCharge from
    congrArg (fun C => C.retainedCharge) preserves12224]
  norm_num [agent12224,scalar12224]

noncomputable def row12224 : BstLean.Part259.RowInputs 12224 :=
  row_from_sharp (by norm_num) (by norm_num) N12224.frameData12224 agent12224 master12224
    BstLean.Part280.m2Certificate12224' localRoot12224 (by norm_num [BstLean.Part280.Row12224.rootTarget,agent12224])
    rfl rfl (by norm_num [agent12224]) compatible12224

theorem classifier_stated_12224 (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 12224).prod (sampMeas (10^12) 12224)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign 12224) t
        BstLean.Part156.aL (10^12) x.1 x.2)} :=
  classifier_from_sharp_row row12224 (fun _ hc => hc.1) t
end BstLean.Part281
