import BstLean.Part262Root
import BstLean.Part259Data0
namespace BstLean.Part262
open Real

/-- The root is the outward-rounded prescribed chain value. -/
theorem root_source12226 : (4424547329004687392087 / 500000000000000000000000 : ℝ) ≤ BstLean.Part259.agent12226.root ∧
    BstLean.Part259.agent12226.root = (8849094659 / 1000000000000 : ℝ) := by
  norm_num [BstLean.Part259.agent12226]

def numerics12226 : RootNumerics 12226 BstLean.Part259.agent12226.root where
  dimension := by norm_num
  price := by norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice, BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, BstLean.Part252.chi, BstLean.Part252.biasFloor, BstLean.Part252.epsilon, BstLean.Part252.varianceMax, BstLean.Part252.energyError, BstLean.Part252.locationError, BstLean.Part252.locationNorm, BstLean.Part252.varianceNorm, BstLean.Part252.biasRootCap, BstLean.Part252.eta, BstLean.Part252.mixtureFloor]
  reserve := by norm_num [BstLean.Part252.biasRootCap, BstLean.Part259.agent12226]

/-- This allocation has a proved table price only in the pilot dimension. -/
theorem allocation12226 : (1499145 / 10 ^ 9 : ℝ) + 3 / 10000 ≤ BstLean.Part259.agent12226.charge := by
  norm_num [BstLean.Part259.agent12226]

noncomputable def inputs12226 {t : ℝ} {c : BstLean.Part157.Ret 12226}
    (E : RootEvidence t c) : BstLean.Part243.RootInputs 12226 t c BstLean.Part259.agent12226.root :=
  rootInputs numerics12226 E

end BstLean.Part262
