import BstLean.Part269Source
import BstLean.Part264bFrameData

namespace BstLean.Part269
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part192 BstLean.Part227

theorem exact_world_window {n : ℕ} (hn : 4096 ≤ n)
    {wp : WorldParameters} (W : WorldPackage (paperProgram n) wp)
    (hidden_eq : W.hidden = hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ productLower n (1232/10^7))
    (upper : productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    {c : Ret n} (hw : c ∈ Hof W.hidden) (hc : c ∈ BstLean.Part262.sourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (noiseLower (202225/100000)) (noiseUpper n (202831/100000)) := by
  have ha := BstLean.Part264.sourceBase_angles hc
  have hg : c.1.1 ∈ hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7) := by
    change c.1.1 ∈ W.hidden at hw
    simpa only [hidden_eq] using hw
  exact noise_window (n := n) hn (paperProgram n).design rfl (fun _ => rfl)
    (c := c) (eB := 1232/10^7) (Alo := 202225/100000) (Ahi := 202831/100000)
    hg.2 hg.1.1.2 hg.1.2
    (window_guards (eB := 1232/10^7) hn (by norm_num)).1
    (window_guards (eB := 1232/10^7) hn (by norm_num)).2.1.le
    (window_guards (eB := 1232/10^7) hn (by norm_num)).2.2
    (by norm_num) lower upper ha.1 ha.2

theorem world_scale_pos {n : ℕ} {wp : WorldParameters}
    (W : WorldPackage (paperProgram n) wp) {c : Ret n} (hw : c ∈ Hof W.hidden) :
    0 < (paperDesignP n).tau0 c := by
  change 0 < (paperProgram n).design.tau0 c
  rw [W.scale_eq c]
  exact (W.scale_identity c.1.1 hw).1

theorem events_from_exact_window {n : ℕ} (hn : 12225 ≤ n) {wp : WorldParameters}
    (W : WorldPackage (paperProgram n) wp) {c : Ret n} (hw : c ∈ Hof W.hidden)
    (hc : c ∈ BstLean.Part262.sourceBase n)
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (noiseLower (202225/100000)) (noiseUpper n (202831/100000))) :
    BstLean.Part262.SourceEvents c := by
  have hwin := BstLean.Part252.window_of_theta (by omega : 1 ≤ n)
    (paperDesignP n) c (world_scale_pos W hw)
    (show BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (46/100 : ℝ) (54/100) from
      ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
       hθ.2.trans ((BstLean.Part263.world_upper_le hn).trans (by norm_num))⟩)
  exact BstLean.Part262.sourceEvents_of_base hwin hc

theorem direction_from_exact_window {n : ℕ} (hn : 12225 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Icc (noiseLower (202225/100000)) (noiseUpper n (202831/100000))) :
    θ ∈ Icc (0.47199 : ℝ) 0.52358 :=
  ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
   hθ.2.trans ((BstLean.Part263.world_upper_le hn).trans (by norm_num))⟩

end BstLean.Part269
