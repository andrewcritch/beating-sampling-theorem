import BstLean.Part287Assembly
import BstLean.Part287LocalSupplies

/-! Adapters for the concrete Part271 R4 supply and Part285 interval root shapes. -/
namespace BstLean.Part287

open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part192
open BstLean.Part271

/-- The R4 record supplies the block frame and all local analytic interfaces. -/
noncomputable def blockFrame_of_R4 {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199)
    (S : R4.Supplies n) :
    BlockFrameInputs n (World.worldPackage n ha hb) GlobalMaster.agent where
  event := (LocalSupplies.frameData S ha hb).covarianceEvent
  cell := (LocalSupplies.frameData S ha hb).cell
  caps := (LocalSupplies.frameData S ha hb).caps
  measurable := (LocalSupplies.frameData S ha hb).covariance_measurable
  payment := (LocalSupplies.frameData S ha hb).covariance_payment
  frame := by
    intro hW c hc
    obtain ⟨F⟩ := (LocalSupplies.frameData S ha hb).frame c hc
    exact ⟨{ F with frame_scalar := F.frame_scalar.trans S.frame_cap }⟩
  localRoot := LocalSupplies.localRootSupply S ha hb
  paidWindow := BstLean.Part285.Downstream.paidWindow_of_world ha
    (World.worldPackage n ha hb) (fun _ hc => hc)
    (World.product_lower ha hb) (World.product_upper ha hb)

theorem root_le_global {n : ℕ} (ha : 13225 ≤ n) :
    BstLean.Part285.Interval.rootOnBand n ≤ GlobalMaster.agent.root :=
  (BstLean.Part285.Downstream.rootOnBand_le_first ha).trans
    (by norm_num [BstLean.Part285.Interval.Band13225.root, GlobalMaster.agent])

theorem payment_le_global {n : ℕ} (ha : 13225 ≤ n) :
    (601 / 10 ^ 6 : ℝ) + BstLean.Part285.Interval.smallerTablePrice n +
      3 / 10000 ≤ GlobalMaster.agent.charge :=
  BstLean.Part285.Downstream.retainedCharge_le_1500 ha

/-- A whole R4 block or a union of blocks consumes the selected root certificates.
The World and master proofs are shared across the full interval. -/
noncomputable def bandInputs_of_R4 {lo hi : ℕ} (ha : 13225 ≤ lo) (hb : hi ≤ 16199)
    (S : ∀ n ∈ Icc lo hi, R4.Supplies n) : BandInputs lo hi where
  dimension := ha
  worldParameters := fun _ => GlobalMaster.world
  agentParameters := fun _ => GlobalMaster.agent
  world := fun n hn => World.worldPackage n (ha.trans hn.1) (hn.2.trans hb)
  master := fun n hn => GlobalMaster.certificate n (ha.trans hn.1) (hn.2.trans hb)
  rootAllowance := BstLean.Part285.Interval.rootOnBand
  tableAllowance := BstLean.Part285.Interval.smallerTablePrice
  root := fun _ hn => BstLean.Part285.Interval.sharpCertificate_per_n
    (by have := ha.trans hn.1; omega) (hn.2.trans hb)
  root_le := fun _ hn => root_le_global (ha.trans hn.1)
  block := fun _ hn => blockFrame_of_R4 (ha.trans hn.1) (hn.2.trans hb) (S _ hn)
  payment := fun _ hn => payment_le_global (ha.trans hn.1)
  compatible := fun n hn => GlobalMaster.compatible n (ha.trans hn.1) (hn.2.trans hb)

/-- Conditional interface theorem. Its name records the outstanding supply argument. -/
theorem classifier_stated_13484_16199_of_supplies
    (S : ∀ n ∈ Icc (13484 : ℕ) 16199, R4.Supplies n) :
    ∀ n ∈ Icc (13484 : ℕ) 16199, ∀ t : ℝ,
      99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
        {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
          BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  (bandInputs_of_R4 (by norm_num) (le_refl _) S).classifier

end BstLean.Part287
