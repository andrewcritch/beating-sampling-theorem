import BstLean.Part281Repair12224
import BstLean.Part281N12224Source
import BstLean.Part281BlockSupplies
namespace BstLean.Part281.N12224
open Real Set MeasureTheory BstLean.Part281 BstLean.Part263
noncomputable def covarianceInputs12224 : BstLean.Part277.CovarianceInputsP (528/1000) 12224
    scalarRow12224.grid BstLean.Part281.TI.parameters (caps repair12224) :=
  Geometry.covarianceInputs (by constructor <;> norm_num) scalarRow12224
    (by norm_num [scalarRow12224,grid12224,BstLean.Part277.worldGridP]) repair12224

noncomputable def frameData12224 : BstLean.Part264b.FrameData 12224 :=
  frameData_from_paid_numerics (by norm_num : 8000 ≤ 11883) (by norm_num) (by norm_num)
    WorldRow12224.worldPackage rfl WorldRow12224.product_lower
    (WorldRow12224.producthi.2.trans (by norm_num))
    (BstLean.Part277.world_upper_11883 (by norm_num : 11883 ≤ 12224)) (by norm_num)
    (by norm_num) (by norm_num)
    (BstLean.Part280.sharpSourceBase 12224 (BstLean.Part280.sharpTableN 12224))
    (BstLean.Part280.sharpSourceBase_measurable (by norm_num) BstLean.Part280.sharpTableN_measurable)
    (fun _ hc => hc.1) scalarRow12224 repair12224 covarianceInputs12224
    (fun _ hi => sourceNumerics12224 hi) agent12224.frame (by norm_num [scalarRow12224,agent12224])
end BstLean.Part281.N12224
