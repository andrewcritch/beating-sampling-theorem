import BstLean.Part264bFrameData
import BstLean.Part264bN12227Frame12227
namespace BstLean.Part264b
open Real Set

noncomputable def frameData12227 : FrameData 12227 where
  worldParameters := BstLean.Part260.worldParameters 12227
  world := BstLean.Part260.worldPackage 12227 (by constructor <;> norm_num)
  covarianceEvent := N12227.covarianceEvent12227
  cell := BstLean.Part263.cell BstLean.Part263.scalarRow12227.grid
  caps := BstLean.Part264.caps BstLean.Part264.repair12227
  covariance_measurable := N12227.covarianceEvent12227_measurable
  covariance_payment := N12227.covarianceEvent12227_payment
  baseEvent := BstLean.Part262.sourceBase 12227
  base_measurable := BstLean.Part262.sourceBase_measurable (by norm_num)
  frameAllowance := BstLean.Part259.agent12227.frame
  frame := N12227.frame12227

end BstLean.Part264b
