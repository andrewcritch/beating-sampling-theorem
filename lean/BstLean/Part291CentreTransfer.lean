import BstLean.Part291CentreMoment
import BstLean.Part291Energy
import BstLean.Part277Moment

namespace BstLean.BlueprintLow
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem centreRootN {n : ℕ} (hn : 8000 ≤ n) : (89.442719 : ℝ) ≤ √(n : ℝ) := by
  have h : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  exact le_sqrt_of_sq_le (by linarith)

theorem centreDeviationBand {n : ℕ} (hn : 8000 ≤ n) :
    sharpDeviation n csC 0.011 0.46 0.528 ≤ 0.066322 := by
  have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := BstLean.Part253.cs_lower
  have hw := (centreWnBand hn).2
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc2 : csC ≤ 2 := by linarith [BstLean.Part253.cs_upper]
  have hnum : 0 ≤ 2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) := by linarith
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / n) ≤ 0.013351983 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ 2 * (1 + (0.011 : ℝ) - 1.29521 * 0.46 / 2) / 8000 := by gcongr
      _ ≤ (0.013351983 : ℝ) ^ 2 := by norm_num
  have h2 : √(wn n * 0.528) ≤ 0.742885 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold sharpDeviation
  calc
    _ ≤ 4.89898 * ((0.013351983 : ℝ) + 2 * 0.742885 / 8000) := by gcongr
    _ ≤ (0.066322 : ℝ) := by norm_num

theorem centreN22Band {n : ℕ} (hn : 8000 ≤ n) : N22bar n 12 ≤ 0.002293 :=
  BstLean.Part277.n22_upperP (n0 := 8000) (by norm_num) hn
    (t := 3.464102) (c := 0.001145534)
    (sqrt_le_iff.mpr (by norm_num)) (by norm_num) (by norm_num) (by norm_num)

theorem centreRadialBand {n : ℕ} (hn : 8000 ≤ n) : xiNr n 0.528 1.269 ≤ 0.015069 := by
  have hs : √((1.269 : ℝ) * 0.528) ≤ 0.818555 := sqrt_le_iff.mpr (by norm_num)
  have hnR := centreRootN hn
  have hN := centreN22Band hn
  have hN0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
  unfold xiNr
  calc
    _ ≤ ((0.528 : ℝ) * (1 + 0.002293) + 0.818555) / 89.442719 := by gcongr
    _ ≤ (0.015069 : ℝ) := by norm_num

theorem centreEMpBand {n : ℕ} (hn : 8000 ≤ n) {xi bn : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0762) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.002245) :
    eMP n 0.011 xi bn ≤ 0.001919 := by
  have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((n : ℝ) * (1 - 0.011))) ≤ 0.000944148 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.002245 / (8000 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000944148 : ℝ) ^ 2 := by norm_num
  unfold eMP
  calc
    _ ≤ 2 * (0.000944148 : ℝ) + 3.141593 * 0.0762 / (8000 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001919 : ℝ) := by norm_num

theorem centrePiBarMPBand {n : ℕ} (hn : 8000 ≤ n) {xi bn : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0762) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.002245) :
    PiBarMP n 12 0.011 xi bn ≤ 0.204015 := by
  have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have he := centreEMpBand hn hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP n 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.047381431 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hns : (88.949423 : ℝ) ≤ √((n : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by linarith)
  have hn' := centreRootN hn
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / n) ≤ 0.155769060 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (16 : ℝ) * 12 * (1 + 0.011) / 8000 := by gcongr
      _ ≤ (0.155769060 : ℝ) ^ 2 := by norm_num
  unfold PiBarMP
  calc
    _ ≤ (0.047381431 + 0.0762 * 1.772454 / (2 * (88.949423 : ℝ))) * (1 + 0.001919) +
        8 / (8000 * 89.442719) + 0.155769060 := by gcongr
    _ ≤ (0.204015 : ℝ) := by norm_num

theorem centreParallelBand {n : ℕ} (hn : 8000 ≤ n) {xi bn cd : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0762) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.002245)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.342366) :
    parallelFormula n n 0.011 xi bn cd 0.528 1.269 ≤ agentParallelCap := by
  have hpp := centrePiBarMPBand hn hxi hxi1 hbn hbn1
  have hpl := BstLean.Part277.plow_lower_8000 hn
  have hpl0 : 0 ≤ plow n (11 / 1000) := by
    convert le_trans (by norm_num : (0 : ℝ) ≤ 0.56) hpl using 1 <;> norm_num
  have hpl' : (0.56 : ℝ) ≤ plow n (11 / 1000) := by convert hpl using 1 <;> norm_num
  have hns := centreRootN hn
  have he0 : 0 ≤ eMP n 0.011 xi bn := by unfold eMP; positivity
  have hpp0 : 0 ≤ PiBarMP n 12 0.011 xi bn := by unfold PiBarMP; positivity
  have hpo : parallelOracle n 0.011 xi bn cd ≤ 0.205884 := by
    unfold parallelOracle
    calc
      _ ≤ (1 + (0.342366 : ℝ) / (2 * 0.56 * 89.442719)) * 0.204015 +
          0.342366 ^ 2 / (2 * 0.56 * 89.442719) := by gcongr
      _ ≤ (0.205884 : ℝ) := by norm_num
  have hpo0 : 0 ≤ parallelOracle n 0.011 xi bn cd := by unfold parallelOracle; positivity
  have hr := centreRadialBand hn
  have hr0 : 0 ≤ xiNr n 0.528 1.269 := by
    have hN0 : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
    unfold xiNr
    positivity
  have hf : finiteEnergy n n 0.011 ≤ 0.010727 := by
    convert BstLean.Part277.finite_centre_8000 hn using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold parallelFormula BstLean.Part206.parallelAllowance
  calc
    _ ≤ ((0.205884 : ℝ) + 0.015069 +
        0.010727 * (1 + 2 * (0.342366 + 0.015069) / (0.56 * 89.442719))) ^ 2 := by gcongr
    _ ≤ agentParallelCap := by norm_num [agentParallelCap]

theorem centreMoment_nonneg {n : ℕ} (hn : LowBand n) :
    0 ≤ momentAllowance n csC 0.011 1.25 1.14 0.528 0.1826 ∧ 0 ≤ bN n csC 0.528 := by
  have hρ : 0 ≤ rhoBar n csC := by have h := centreRhoBand hn; linarith [h.1]
  have hw : 0 ≤ wn n := by have h := centreWnBand hn.1; linarith [h.1]
  have hp := piBar_nonneg (rhoBar n csC)
  have hv : 0 ≤ nuR (rhoBar n csC) := by unfold nuR; positivity
  have hz := (phiG_pos 0).le
  have ho := (phiG_pos 1).le
  have hc := BstLean.Part253.cs_lower
  have hk : 0 ≤ K0 := by unfold K0; exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb : 0 ≤ bN n csC 0.528 := by unfold bN QB cc0 cc1 cc2; positivity
  refine ⟨?_, hb⟩
  unfold momentAllowance restAllowance linearAllowance badAllowance tail
  positivity

theorem centreSourceScalarBand {n : ℕ} (hn : LowBand n) :
    fullFormula n n 0.011 1.25 1.14 0.46 0.528 0.1826 1.269 ≤ 0.14 ∧
    parallelFormula n n 0.011 (momentAllowance n csC 0.011 1.25 1.14 0.528 0.1826)
      (bN n csC 0.528) (√(momentAllowance n csC 0.011 1.25 1.14 0.528 0.1826) +
        sharpDeviation n csC 0.011 0.46 0.528) 0.528 1.269 ≤ agentParallelCap := by
  have hm := centreMomentBand hn
  have hnns := centreMoment_nonneg hn
  have hroot : √(momentAllowance n csC 0.011 1.25 1.14 0.528 0.1826) ≤ 0.276044 :=
    sqrt_le_iff.mpr ⟨by norm_num, hm.trans (by norm_num)⟩
  have hd := centreDeviationBand hn.1
  have hd0 : 0 ≤ sharpDeviation n csC 0.011 0.46 0.528 := by unfold sharpDeviation; positivity
  have hr := centreRadialBand hn.1
  have hr0 : 0 ≤ xiNr n 0.528 1.269 := by
    have hN : 0 ≤ N22bar n 12 := by unfold N22bar N12bar; positivity
    unfold xiNr
    positivity
  have hf : finiteEnergy n n 0.011 ≤ 0.010727 := by
    convert BstLean.Part277.finite_centre_8000 hn.1 using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg n n (by norm_num : (0 : ℝ) ≤ 0.011)
  constructor
  · unfold fullFormula
    calc
      _ ≤ ((0.276044 : ℝ) + 0.066322 + 0.015069 + 0.010727) ^ 2 := by gcongr
      _ ≤ (0.14 : ℝ) := by norm_num
  · exact centreParallelBand hn.1 hnns.1 hm hnns.2 (centreBnBand hn)
      (add_nonneg (sqrt_nonneg _) hd0) (by linarith)

end BstLean.BlueprintLow
