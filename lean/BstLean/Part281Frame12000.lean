import BstLean.Part281Repair12000
import BstLean.Part281N12000Source
import BstLean.Part281BlockSupplies
namespace BstLean.Part281.N12000
open Real Set MeasureTheory BstLean.Part281 BstLean.Part263
noncomputable def covarianceInputs12000 : BstLean.Part277.CovarianceInputsP (528/1000) 12000
    scalarRow12000.grid BstLean.Part281.TI.parameters (caps repair12000) :=
  Geometry.covarianceInputs (by constructor <;> norm_num) scalarRow12000
    (by norm_num [scalarRow12000,grid12000,BstLean.Part277.worldGridP]) repair12000

noncomputable def frameData12000 : BstLean.Part264b.FrameData 12000 :=
  frameData_from_paid_numerics (by norm_num : 8000 ≤ 11883) (by norm_num) (by norm_num)
    WorldRow12000.worldPackage rfl WorldRow12000.product_lower
    (WorldRow12000.producthi.2.trans (by norm_num))
    (BstLean.Part277.world_upper_11883 (by norm_num : 11883 ≤ 12000)) (by norm_num)
    (by norm_num) (by norm_num)
    (BstLean.Part280.sharpSourceBase 12000 (BstLean.Part280.sharpTableN 12000))
    (BstLean.Part280.sharpSourceBase_measurable (by norm_num) BstLean.Part280.sharpTableN_measurable)
    (fun _ hc => hc.1) scalarRow12000 repair12000 covarianceInputs12000
    (fun _ hi => sourceNumerics12000 hi) agent12000.frame (by norm_num [scalarRow12000,agent12000])
end BstLean.Part281.N12000
