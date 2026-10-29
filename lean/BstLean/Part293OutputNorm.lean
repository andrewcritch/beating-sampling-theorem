import BstLean.Part293LowNormalization
import BstLean.Part252Centre
import BstLean.Part289Design

/-! Output-centre normalization from the actual paid event, independent of node 39. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part293.Model

theorem output_chi_normalized {n : ℕ} (hn : 0 < n) :
    BstLean.Part164.chiUp n / n = lowMixtureChi n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : √((n : ℝ) * 12) / n = √(12 / (n : ℝ)) := by
    have hsq : (√((n : ℝ) * 12) / n) ^ 2 = 12 / (n : ℝ) := by
      rw [div_pow, sq_sqrt (by positivity)]
      field_simp
    rw [← hsq, sqrt_sq (by positivity)]
  unfold BstLean.Part164.chiUp lowMixtureChi
  rw [add_div, add_div, div_self hnR.ne']
  rw [show 2 * √((n : ℝ) * 12) / n = 2 * (√((n : ℝ) * 12) / n) by ring, he]
  norm_num

theorem outputCentre_model_normalized {n : ℕ} (hn : 0 < n) {c : Ret n}
    (hc : c ∈ BstLean.Part252.outputCentreEvent (paperDesignP n).toCentres) :
    normSq c.2.1.2 ≤ 2 * eR c * lowMixtureChi n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change normSq c.2.1.2 ≤ 2 / (mA n : ℝ) * normSq (bR c) * BstLean.Part164.chiUp n at hc
  refine hc.trans_eq ?_
  rw [← output_chi_normalized hn]
  unfold eR mA
  push_cast
  ring

theorem output_norm_capped {n : ℕ} (hn : 8000 ≤ n) (c : Ret n) (he : 0 ≤ eR c)
    (hO : c ∈ BstLean.Part252.outputCentreEvent (paperDesignP n).toCentres) :
    normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * 1.081 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have h := outputCentre_model_normalized (by omega) hO
  rw [lowChi_normalized] at h
  have hchi : Envelope.chi (1 / (n : ℝ)) ≤ (1.081 : ℝ) :=
    (Envelope.chi_bounds _ (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR)).2.trans (by norm_num)
  apply (h.trans (mul_le_mul_of_nonneg_left hchi (by positivity))).trans_eq
  field_simp

end BstLean.Part293
