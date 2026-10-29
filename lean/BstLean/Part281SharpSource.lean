import BstLean.Part280World
import BstLean.Part280Interface
import BstLean.Part277Frame

namespace BstLean.Part281
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part192 BstLean.Part227 BstLean.Part280

theorem sharp_world_charge (hn : 11883 ≤ n) (hu : n ≤ 12224) (wr : WRet n) :
    (BstLean.Part153.nuA n).real (sharpBadPairN n wr) ≤ (843145 / 10^9 : ℝ) := by
  by_cases hw : tightG wr
  · exact (BstLean.Part252.product_charge_ae _ _
      (sharpFirstEventN_measurable (by omega) wr) (sharpBadPairN_measurable wr)
      (by norm_num) (by norm_num) (sharpFirstEventN_charge hn hu hw)
      (sharp_conditional_chargeN hn hu hw)).trans (by norm_num)
  · have he : sharpBadPairN n wr = ∅ := by
      ext θ
      simp only [sharpBadPairN, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    norm_num

theorem sharp_table_charge (hn : 11883 ≤ n) (hu : n ≤ 12224) :
    (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ (843145 / 10^9 : ℝ) := by
  have h := BstLean.Part170.retDist_pair_charge (paperCentres n) sharpPairEventN_measurable
    (by norm_num : (0 : ℝ) ≤ 843145 / 10^9) (sharp_world_charge hn hu)
  convert h using 1
  congr 1

theorem sharp_base_payment (hn : 11883 ≤ n) (hu : n ≤ 12224) (H : Set (Ret n)) :
    (retDist (paperCentres n)).real (H ∩ (sharpSourceBase n (sharpTableN n))ᶜ) ≤
      (1444145 / 10^9 : ℝ) := by
  exact (sharpSourceBase_charge (by omega) (sharp_table_charge hn hu) H).trans
    (by linarith [sourceChargeFn_le_m2 hn])

theorem paid_world_window {n : ℕ} (hn : 4096 ≤ n)
    {wp : WorldParameters} (W : WorldPackage (paperProgram n) wp)
    (hidden_eq : W.hidden = hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ productLower n (1232/10^7))
    (upper : productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    {c : Ret n} (hw : c ∈ Hof W.hidden) (hc : c ∈ BstLean.Part262.paidSourceBase n) :
    BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (noiseLower (202225/100000)) (noiseUpper n (202831/100000)) := by
  have ha : c ∈ BstLean.Part262.worldAngles n := hc.1.1.2
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

theorem paid_events_from_window {n : ℕ} (hn : 8000 ≤ n) {wp : WorldParameters}
    (W : WorldPackage (paperProgram n) wp) {c : Ret n} (hw : c ∈ Hof W.hidden)
    (hc : c ∈ BstLean.Part262.paidSourceBase n) {a : ℝ}
    (hup : noiseUpper n (202831/100000) ≤ a) (ha : a ≤ 54/100)
    (hθ : BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (noiseLower (202225/100000)) (noiseUpper n (202831/100000))) :
    BstLean.Part262.SourceEvents c := by
  have hw' := BstLean.Part252.window_of_theta (by omega : 1 ≤ n) (paperDesignP n) c
    (BstLean.Part269.world_scale_pos W hw)
    (show BstLean.Part150.thetaC c.1.2 ((paperDesignP n).tau0 c) ∈
      Icc (46/100 : ℝ) (54/100) from
      ⟨(le_trans (by norm_num) BstLean.Part250.noiselo.1).trans hθ.1,
       hθ.2.trans (hup.trans ha)⟩)
  exact BstLean.Part262.sourceEvents_of_paid hw' hc

end BstLean.Part281
