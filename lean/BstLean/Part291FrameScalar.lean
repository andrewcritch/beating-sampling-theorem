import BstLean.Part291FrameInputs
import BstLean.Part291WindowTails
import BstLean.Part291Arithmetic
import BstLean.Part291RadiusWeights

namespace BstLean.BlueprintLow
open Real Set
open BstLean.Part188 BstLean.Part222 BstLean.Part255 BstLean.Part215

noncomputable def lowFrameMean (n : ℕ) (E : ℝ) : ℝ :=
  √E + √(agentParallelCap / n)

noncomputable def lowFrameShell (θ : ℝ) (p : Parameters) : ℝ :=
  θ * p.wLam / (1 - p.cRadius) * BstLean.Part254.gaussianPair lowCoreWindow +
  θ * p.wLam / (1 - p.wRadius) * BstLean.Part254.gaussianOutside lowCoreWindow

noncomputable def lowFrameBad : ℝ :=
  1.269 * (2 * √(√(BstLean.Part254.gaussianTail lowWideWindow.pair +
    2 * (BstLean.Part255.delta / 0.00025))) + √(BstLean.Part254.gaussianOutside lowWideWindow))

noncomputable def lowFrameCov (n : ℕ) (θ : ℝ) (p : Parameters) : ℝ :=
  radiusCoefficient n 1 θ * p.cLam + lowFrameShell θ p + lowFrameBad

noncomputable def lowFrameSchur (n : ℕ) (θ : ℝ) (p : Parameters) (E : ℝ) : ℝ :=
  p.cLam * (radiusCoefficient n 1 θ / ((1 - 0.0045) ^ 2 - lowFrameMean n E ^ 2) +
    rwDelta ((1 - 0.0045) ^ 2) 0.216 (lowFrameMean n E) (√(agentDirectionCap / n)) *
      radiusCoefficient n 2 θ) + (lowFrameShell θ p + lowFrameBad) / 0.216

/-- Cancel the dimension powers before bounding a continuum dimension interval. -/
theorem frameGB_dimension_normalized {n : ℕ} (hn : 0 < n)
    {a d M H N xi : ℝ} (hd : 0 < d) (hU : 0 ≤ N + xi) :
    frameGB n a d M H N xi =
      ((N + xi) / (d * n)) ^ (41 / 45 : ℝ) * (1 / d) ^ (4 / 45 : ℝ) *
        (1 + H) ^ (8 / 45 : ℝ) * ((a - d) / d ^ 2) * M := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (n : ℝ) ^ (41 / 45 : ℝ) * (n : ℝ) ^ (4 / 45 : ℝ) = n := by
    rw [← rpow_add hn0]
    norm_num
  have hz : (n : ℝ) ^ (41 / 45 : ℝ) ≠ 0 := ne_of_gt (rpow_pos_of_pos hn0 _)
  have hratio : (n : ℝ) ^ (4 / 45 : ℝ) / n = 1 / (n : ℝ) ^ (41 / 45 : ℝ) := by
    apply (div_eq_div_iff hn0.ne' hz).mpr
    nlinarith only [hp]
  have hx : 0 ≤ (N + xi) / d := div_nonneg hU hd.le
  rw [show (N + xi) / (d * n) = ((N + xi) / d) / n by ring,
    div_rpow hx hn0.le, div_rpow (by norm_num : (0 : ℝ) ≤ 1) hd.le]
  unfold frameGB
  rw [div_rpow hn0.le hd.le]
  calc
    _ = ((N + xi) / d) ^ (41 / 45 : ℝ) *
      ((n : ℝ) ^ (4 / 45 : ℝ) / n) / d ^ (4 / 45 : ℝ) *
      (1 + H) ^ (8 / 45 : ℝ) * ((a - d) / d ^ 2) * M := by ring
    _ = _ := by rw [hratio]; simp only [one_rpow]; ring

theorem rpow_fraction_bound {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B)
    {k m : ℕ} (hm : m ≠ 0) (hpow : x ^ k ≤ B ^ m) :
    x ^ ((k : ℝ) / m) ≤ B := by
  apply le_of_pow_le_pow_left₀ hm hB
  rw [← rpow_natCast, ← rpow_mul hx]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [div_mul_cancel₀ _ hm0, rpow_natCast]
  exact hpow

end BstLean.BlueprintLow
