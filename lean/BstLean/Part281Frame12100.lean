import BstLean.Part281Repair12100
import BstLean.Part281N12100Source
import BstLean.Part281BlockSupplies
namespace BstLean.Part281.N12100
open Real Set MeasureTheory BstLean.Part281 BstLean.Part263
noncomputable def covarianceInputs12100 : BstLean.Part277.CovarianceInputsP (528/1000) 12100
    scalarRow12100.grid BstLean.Part281.TI.parameters (caps repair12100) :=
  Geometry.covarianceInputs (by constructor <;> norm_num) scalarRow12100
    (by norm_num [scalarRow12100,grid12100,BstLean.Part277.worldGridP]) repair12100

noncomputable def frameData12100 : BstLean.Part264b.FrameData 12100 :=
  frameData_from_paid_numerics (by norm_num : 8000 ≤ 11883) (by norm_num) (by norm_num)
    WorldRow12100.worldPackage rfl WorldRow12100.product_lower
    (WorldRow12100.producthi.2.trans (by norm_num))
    (BstLean.Part277.world_upper_11883 (by norm_num : 11883 ≤ 12100)) (by norm_num)
    (by norm_num) (by norm_num)
    (BstLean.Part280.sharpSourceBase 12100 (BstLean.Part280.sharpTableN 12100))
    (BstLean.Part280.sharpSourceBase_measurable (by norm_num) BstLean.Part280.sharpTableN_measurable)
    (fun _ hc => hc.1) scalarRow12100 repair12100 covarianceInputs12100
    (fun _ hi => sourceNumerics12100 hi) agent12100.frame (by norm_num [scalarRow12100,agent12100])
end BstLean.Part281.N12100
