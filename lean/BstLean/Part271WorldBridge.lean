import BstLean.Part271R3Family
import BstLean.Part269WorldSource

/-! The hidden-event and product-window interface for downstream row supplies. -/
namespace BstLean.Part271.R3.Family

open Real Set BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part169 BstLean.Part192

theorem world_hidden (n : ℕ) (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (worldPackage n ha hb).hidden =
      BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
        (178/10^8) (1232/10^7) := rfl

theorem product_lower {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7) := by
  have h := (BstLean.Part271.R3.FrameBand.productlo ha hb).1
  linarith only [h]

theorem product_upper {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) :
    BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ) :=
  (BstLean.Part271.R3.FrameBand.producthi ha hb).2.trans (by norm_num)

theorem exact_world_window {n : ℕ} (ha : 13225 ≤ n) (hb : n ≤ 16199) {c : Ret n}
    (hw : c ∈ Hof (worldPackage n ha hb).hidden) (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225/100000))
        (BstLean.Part227.noiseUpper n (202831/100000)) :=
  BstLean.Part269.exact_world_window (by omega) (worldPackage n ha hb)
    (world_hidden n ha hb) (product_lower ha hb) (product_upper ha hb) hw hc

end BstLean.Part271.R3.Family
