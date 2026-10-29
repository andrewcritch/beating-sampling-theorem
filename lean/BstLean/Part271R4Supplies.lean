import BstLean.Part271R4SupplyCore
import BstLean.Part271WorldBridge
import BstLean.Part286Bridge
import BstLean.Part271GlobalMaster

/-! Dimension-indexed scalar supplies for selection across R4 blocks. -/
namespace BstLean.Part271.R4

open Real Set BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part192

theorem GridCertificate.world_upper_lt_top {lo n : ℕ} (G : GridCertificate lo)
    (hn : lo ≤ n) : (G.grid hn).worldUpper < G.top :=
  (G.grid hn).upper_node.trans_le (G.node_le_top (by norm_num : 53 ≤ 60))

theorem scalar_top_guard {n : ℕ} (R : BstLean.Part263.ScalarRow n) :
    R.grid.worldUpper < R.top := by
  have hnode : BstLean.Part263.noiseNode R.grid.top 53 ≤ R.grid.top := by
    have hp := R.grid.top_pos
    unfold BstLean.Part263.noiseNode
    norm_num
    linarith only [hp]
  exact R.grid.upper_node.trans_le (hnode.trans_eq R.grid_top)

theorem Supplies.world_noise_lt_top {n : ℕ} (S : Supplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part271.R3.Family.worldPackage n ha hb).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) < S.scalar.top := by
  have hu := (BstLean.Part271.R3.Family.exact_world_window ha hb hw hc).2
  rw [← S.scalar.grid_upper] at hu
  exact hu.trans_lt (scalar_top_guard S.scalar)

noncomputable def Supplies.frameData {n : ℕ} (S : Supplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) : BstLean.Part264b.FrameData n :=
  BstLean.Part269.frameData_from_numerics (by omega) (by omega)
    (BstLean.Part271.R3.Family.worldPackage n ha hb) rfl
    (BstLean.Part271.R3.Family.product_lower ha hb)
    (BstLean.Part271.R3.Family.product_upper ha hb)
    S.scalar S.repair S.covariance S.numerics S.scalar.targetFrame rfl

noncomputable def Supplies.localRootSupply {n : ℕ} (S : Supplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    BstLean.Part262.LocalRootSupply n
      (Hof (BstLean.Part271.R3.Family.worldPackage n ha hb).hidden) :=
  BstLean.Part286.localRoot_from_numerics (by omega) (by omega)
    (BstLean.Part271.R3.Family.worldPackage n ha hb) rfl
    (BstLean.Part271.R3.Family.product_lower ha hb)
    (BstLean.Part271.R3.Family.product_upper ha hb)
    S.scalar S.numerics S.direction_cap S.energy_cap S.parallel_cap S.centre_energy_cap

theorem Supplies.frameData_world {n : ℕ} (S : Supplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (S.frameData ha hb).world = BstLean.Part271.R3.Family.worldPackage n ha hb := rfl

theorem Supplies.frameData_base {n : ℕ} (S : Supplies n)
    (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (S.frameData ha hb).baseEvent = BstLean.Part262.sourceBase n := rfl

noncomputable def enlargeFrame {n : ℕ} {event : Set (BstLean.Part160.AgFam n)}
    {cell : Fin 60 → Set ℝ} {caps : Fin 60 → ℝ} {c : Ret n} {a b : ℝ}
    (F : BstLean.Part259.LocalFrameInputs n event cell caps c a) (hab : a ≤ b) :
    BstLean.Part259.LocalFrameInputs n event cell caps c b :=
  { F with frame_scalar := F.frame_scalar.trans hab }

end BstLean.Part271.R4
