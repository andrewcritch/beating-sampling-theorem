import BstLean.Part287World
import BstLean.Part286Bridge
import BstLean.Part271R4SupplyCore

/-! The scalar supply record, with no dependency on the exact World row family. -/
namespace BstLean.Part287

open Real Set BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part192

abbrev LocalSupplies (n : ℕ) := BstLean.Part271.R4.Supplies n

noncomputable def LocalSupplies.frameData {n : ℕ} (S : LocalSupplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) : BstLean.Part264b.FrameData n :=
  BstLean.Part269.frameData_from_numerics (by omega) (by omega)
    (World.worldPackage n ha hb) rfl (World.product_lower ha hb) (World.product_upper ha hb)
    S.scalar S.repair S.covariance S.numerics S.scalar.targetFrame rfl

theorem LocalSupplies.localRootSupply {n : ℕ} (S : LocalSupplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    BstLean.Part262.LocalRootSupply n (Hof (World.worldPackage n ha hb).hidden) :=
  BstLean.Part286.localRoot_from_numerics (by omega) (by omega)
    (World.worldPackage n ha hb) rfl (World.product_lower ha hb) (World.product_upper ha hb)
    S.scalar S.numerics S.direction_cap S.energy_cap S.parallel_cap S.centre_energy_cap

theorem LocalSupplies.grid_top_guard {n : ℕ} (S : LocalSupplies n) :
    S.scalar.grid.worldUpper < S.scalar.top := by
  have hnode : BstLean.Part263.noiseNode S.scalar.grid.top 53 ≤ S.scalar.grid.top := by
    have hp := S.scalar.grid.top_pos
    unfold BstLean.Part263.noiseNode
    norm_num
    linarith only [hp]
  exact S.scalar.grid.upper_node.trans_le (hnode.trans_eq S.scalar.grid_top)

end BstLean.Part287
