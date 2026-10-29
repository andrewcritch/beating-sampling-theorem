import BstLean.Part289Design
import BstLean.Part188Interfaces
import BstLean.Part169Pass

/-! Transfer the three geometric fields, which do not use the design's mixture table. -/
namespace BstLean.Part293
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part188 BstLean.Part289

theorem interfaces_stated2_to_paper {n : ℕ} {c : Ret n} {M H xi : ℝ}
    (I : WFInterfaces (statedDesign2 n) c M H xi) :
    WFInterfaces (paperDesignP n) c M H xi :=
  ⟨I.direction, I.energy, I.parallel⟩

end BstLean.Part293

/-- info: 'BstLean.Part293.interfaces_stated2_to_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.interfaces_stated2_to_paper
