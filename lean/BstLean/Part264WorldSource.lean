import BstLean.Part260Family
import BstLean.Part262Sources
import BstLean.Part263ScalarSupply

/-! The paid source event supplies the exact World window and source memberships. -/
namespace BstLean.Part264
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part161
open BstLean.Part169 (paperDesignP)

theorem sourceBase_angles {n : ℕ} {c : Ret n} (hc : c ∈ BstLean.Part262.sourceBase n) :
    c ∈ BstLean.Part262.worldAngles n := hc.1.1.1.2

theorem actual_world_window {n : ℕ} (hn : n ∈ Icc 12225 12349) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (BstLean.Part227.noiseLower (202225 / 100000))
        (BstLean.Part227.noiseUpper n (202831 / 100000)) := by
  have ha := sourceBase_angles hc
  apply BstLean.Part260.actual_noise_window n hn c
  refine ⟨hw, ?_⟩
  rw [(BstLean.Part260.angle_events n hn).1, (BstLean.Part260.angle_events n hn).2]
  exact ha

theorem scale_pos {n : ℕ} (hn : n ∈ Icc 12225 12349) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part260.worldPackage n hn).hidden) :
    0 < (paperDesignP n).tau0 c := by
  change 0 < (BstLean.Part192.paperProgram n).design.tau0 c
  rw [(BstLean.Part260.worldPackage n hn).scale_eq c]
  exact ((BstLean.Part260.worldPackage n hn).scale_identity c.1.1 hw).1

theorem source_window {n : ℕ} (hn : n ∈ Icc 12225 12349) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) : WINDOW (paperDesignP n) c := by
  have hdim : 1 ≤ n := by have := hn.1; omega
  exact BstLean.Part252.window_of_theta hdim _ c (scale_pos hn hw)
    (BstLean.Part260.actual_noise_enclosure n hn (actual_world_window hn hw hc))

theorem source_events {n : ℕ} (hn : n ∈ Icc 12225 12349) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) : BstLean.Part262.SourceEvents c :=
  BstLean.Part262.sourceEvents_of_base (source_window hn hw hc) hc

theorem direction_window {n : ℕ} (hn : n ∈ Icc 12225 12349) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ Icc (0.47199 : ℝ) 0.52358 := by
  have hθ := actual_world_window hn hw hc
  exact ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
    hθ.2.trans ((BstLean.Part263.world_upper_le hn.1).trans (by norm_num))⟩

theorem local_cell {n : ℕ} (hn : n ∈ Icc 12225 12349)
    (R : BstLean.Part263.ScalarRow n) {c : Ret n}
    (hw : c ∈ Hof (BstLean.Part260.worldPackage n hn).hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n) :
    ∃ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) ∧
      BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈ BstLean.Part263.cell R.grid i :=
  BstLean.Part263.scalarRow_world_cover R (actual_world_window hn hw hc)

end BstLean.Part264
