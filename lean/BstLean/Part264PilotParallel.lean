import BstLean.Part264PilotCentreFormula
import BstLean.Part253CentreFormula
import BstLean.Part211Parallel
import BstLean.Part253Data

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.56048 : ℝ) ≤ plow 12226 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12226) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0535)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001438) : eMP 12226 0.011 xi bn ≤ 0.001237 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12226 : ℝ) * (1 - 0.011))) ≤ 0.000611269 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001438 / (12226 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000611269 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000611269 : ℝ) + 3.141593 * 0.0535 / (12226 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001237 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0535)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001438) : PiBarMP 12226 12 0.011 xi bn ≤ 0.164415 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12226 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037921 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.956923 : ℝ) ≤ √((12226 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.566721 : ℝ) ≤ √12226 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12226) ≤ 0.126009057 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037921 + 0.0535 * 1.772454 / (2 * (109.956923 : ℝ))) * (1 + 0.001237) +
        8 / (12226 * 110.566721) + 0.126009057 := by gcongr
    _ ≤ (0.164415 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0535)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001438) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284807) :
    parallelOracle 12226 0.011 xi bn cd ≤ 0.165448 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12226 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12226 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.56048 : ℝ) ≤ plow 12226 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.566721 : ℝ) ≤ √12226 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284807 : ℝ) / (2 * 0.56048 * 110.566721)) * 0.164415 +
        0.284807 ^ 2 / (2 * 0.56048 * 110.566721) := by gcongr
    _ ≤ (0.165448 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.0535) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001438)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284807) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12226 12226 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.56048 : ℝ) ≤ plow 12226 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.566721 : ℝ) ≤ √12226 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12226 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12226 Θ 1.22 ≤ 0.011995 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.566721 := by gcongr <;> linarith
      _ ≤ (0.011995 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12226 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12226 12226 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12226 12226 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12226 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12226 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12226 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12226 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165448 + 0.011995 + (0.008646 : ℝ) *
        (1 + 2 * (0.284807 + 0.011995) / (0.56048 * 110.566721))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12226]

end BstLean.Part264
