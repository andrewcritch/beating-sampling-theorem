import BstLean.Part227Noise

/-! Part 280, task 2 (window decision): the World window of the Lean World packages
gives `θ ≤ .524` on M2.

The Part 260 World package of a row gives `θ ∈ [noiseLower 2.02225, noiseUpper n 2.02831]`
(`Part260.actual_noise_window`). The M2 World data (full-run65, rows 11883–12224) have
energy-ratio window `[2.0222557, 2.0283015] ⊆ [2.02225, 2.02831]`, so the same
interval form holds on M2. Its upper end is at most .5234 from 11883. -/
namespace BstLean.Part280
open Real Set

theorem noiseUpper_le_524 {n : ℕ} (hn : 11883 ≤ n) :
    BstLean.Part227.noiseUpper n (202831 / 100000) ≤ 524 / 1000 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : √(12 / (n : ℝ)) ≤ 3178 / 100000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hx0]
    nlinarith
  unfold BstLean.Part227.noiseUpper
  have hd : (0 : ℝ) < 1 - 2 * √(12 / (n : ℝ)) + (202831 / 100000 - 1) := by linarith
  rw [div_le_iff₀ hd]
  linarith

/-- Every angle in the World-package interval at an M2 dimension is at most .524. -/
theorem theta_le_of_noise {n : ℕ} (hn : 11883 ≤ n) {θ : ℝ}
    (h : θ ∈ Icc (BstLean.Part227.noiseLower (202225 / 100000))
      (BstLean.Part227.noiseUpper n (202831 / 100000))) : θ ≤ 524 / 1000 :=
  h.2.trans (noiseUpper_le_524 hn)

/-- The core window of the frame chain (`θ ≤ .528`, Part 263) is weaker than the
M2 bound; the M2 bound is the one the table event uses. -/
theorem m2_window_inside_core : (524 / 1000 : ℝ) ≤ 528 / 1000 := by norm_num

end BstLean.Part280
