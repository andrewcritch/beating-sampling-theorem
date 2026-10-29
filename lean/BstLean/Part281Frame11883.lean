import BstLean.Part281Repair11883
import BstLean.Part281N11883Source
import BstLean.Part281BlockSupplies
namespace BstLean.Part281.N11883
open Real Set MeasureTheory BstLean.Part281 BstLean.Part263
noncomputable def covarianceInputs11883 : BstLean.Part277.CovarianceInputsP (528/1000) 11883
    scalarRow11883.grid BstLean.Part281.TI.parameters (caps repair11883) :=
  Geometry.covarianceInputs (by constructor <;> norm_num) scalarRow11883
    (by norm_num [scalarRow11883,grid11883,BstLean.Part277.worldGridP]) repair11883

noncomputable def frameData11883 : BstLean.Part264b.FrameData 11883 :=
  frameData_from_paid_numerics (by norm_num : 8000 ≤ 11883) (by norm_num) (by norm_num)
    WorldRow11883.worldPackage rfl WorldRow11883.product_lower
    (WorldRow11883.producthi.2.trans (by norm_num))
    (BstLean.Part277.world_upper_11883 (by norm_num : 11883 ≤ 11883)) (by norm_num)
    (by norm_num) (by norm_num)
    (BstLean.Part280.sharpSourceBase 11883 (BstLean.Part280.sharpTableN 11883))
    (BstLean.Part280.sharpSourceBase_measurable (by norm_num) BstLean.Part280.sharpTableN_measurable)
    (fun _ hc => hc.1) scalarRow11883 repair11883 covarianceInputs11883
    (fun _ hi => sourceNumerics11883 hi) agent11883.frame (by norm_num [scalarRow11883,agent11883])
end BstLean.Part281.N11883
