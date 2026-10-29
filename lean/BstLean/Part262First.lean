import BstLean.Part262Root
import BstLean.Part257Root
import BstLean.Part259Data0

/-! The existing complete first row enters the parameterized root interface. -/
namespace BstLean.Part262
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part159 BstLean.Part169

theorem tableEvent_charge12225 :
    (retDist (paperCentres 12225)).real (tableEvent 12225)ᶜ ≤ (9 / 10000 : ℝ) :=
  BstLean.Part252.tableEvent_ret_charge

noncomputable def baseRootSupply12225 :
    BaseRootSupply 12225 (Hof BstLean.Part250.worldPackage.hidden)
      BstLean.Part259.agent12225.root (1499145 / 10 ^ 9) where
  event := sourceBase 12225
  measurable := sourceBase_measurable (by norm_num)
  payment := by
    exact (sourceBase_charge (by norm_num) tableEvent_charge12225 _).trans (by norm_num)
  inputs := by
    intro t c hw hc
    have hroot : BstLean.Part243.rowRoot = BstLean.Part259.agent12225.root := by
      norm_num [BstLean.Part243.rowRoot, BstLean.Part259.agent12225]
    rw [← hroot]
    exact BstLean.Part257.rootInputs_of_base t hw hc

end BstLean.Part262
