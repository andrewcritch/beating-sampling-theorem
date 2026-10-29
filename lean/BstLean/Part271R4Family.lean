import BstLean.Part271R4Supplies
import BstLean.Part271R4CommonSupplies
import BstLean.Part287Diagonal

/-! The shared short-block certificate instantiated on [n,n].
The bottom grid remains valid at every larger dimension. No per-row arithmetic
or new network root is introduced by this selection. -/
namespace BstLean.Part271.R4.Family
open Real Set

noncomputable def supplies (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) : Supplies n :=
  CommonSupplies.supplies (lo := n) (hi := n) ha hb (by omega)
    (BstLean.Part287.Diagonal.promoteGrid SharedTable.gridCertificate ha)
    (by
      change SharedTable.gridCertificate.top ∈
        Icc (105958839397/200000000000) (21253017353/40000000000)
      norm_num [SharedTable.gridCertificate])
    ⟨le_rfl,le_rfl⟩

noncomputable def frameData (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    BstLean.Part264b.FrameData n := (supplies n ha hb).frameData ha hb

noncomputable def localRootSupply (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    BstLean.Part262.LocalRootSupply n
      (BstLean.Part159.Hof (BstLean.Part271.R3.Family.worldPackage n ha hb).hidden) :=
  (supplies n ha hb).localRootSupply ha hb

theorem frameData_world (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (frameData n ha hb).world = BstLean.Part271.R3.Family.worldPackage n ha hb := rfl

theorem frameData_base (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (frameData n ha hb).baseEvent = BstLean.Part262.sourceBase n := rfl

theorem grid_top_guard (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (supplies n ha hb).scalar.grid.worldUpper < (supplies n ha hb).scalar.top :=
  scalar_top_guard (supplies n ha hb).scalar

theorem world_noise_lt_top (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199)
    {c : BstLean.Part157.Ret n}
    (hw : c ∈ BstLean.Part159.Hof (BstLean.Part271.R3.Family.worldPackage n ha hb).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((BstLean.Part169.paperDesignP n).tau0 c) <
      (supplies n ha hb).scalar.top :=
  (supplies n ha hb).world_noise_lt_top ha hb hw hc

end BstLean.Part271.R4.Family
