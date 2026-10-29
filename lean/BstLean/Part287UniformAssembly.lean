import BstLean.Part271R4Family
import BstLean.Part287R4

/-! The accepted Part271 block supply instantiates the Part287 band interface. -/
namespace BstLean.Part287

open Real Set BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part192
open BstLean.Part271

/-- The root selector changes bands; the World, scalar table and frame are shared. -/
noncomputable def uniformBandInputs : BandInputs 13225 16199 :=
  bandInputs_of_R4 (le_refl _) (le_refl _)
    (fun n hn => BstLean.Part271.R4.Family.supplies n hn.1 hn.2)

noncomputable def uniformIntervalInputs : IntervalInputs 13484 16199 :=
  uniformBandInputs.interval.restrict (by norm_num) (le_refl _)

end BstLean.Part287
