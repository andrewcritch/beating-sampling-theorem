import BstLean.Part253Fallback

/-! Cutoff-independent obstructions for the supplied covariance caps.
These concern the order-twenty-four certificate, not the actual network frame. -/
namespace BstLean.Part253
open Real

noncomputable def rotationPowerFloor : ℝ :=
  (3.14159265358979323846 / 2) ^ 24 * 316234143225

theorem rotation_power_lower : rotationPowerFloor ≤
    BstLean.Part195.rotationConstant 12 ^ 24 := by
  have h := BstLean.Part195.rotationConstant_pow (by norm_num : 1 ≤ 12) (by norm_num)
  have hg : BstLean.Part162.gmom (2 * 12) = 316234143225 := by
    rw [BstLean.Part162.gmom_even]
    norm_num [Finset.prod_range_succ]
  rw [hg] at h
  rw [h]
  unfold rotationPowerFloor
  gcongr
  exact pi_gt_d20.le

/-- Lower rational square-root enclosures give an upper bound on the gap. -/
theorem mass_lower_rational {M H xi E u d a b w q beta : ℝ}
    (hM : 0 ≤ M) (ha : 0 ≤ a) (hE : a ^ 2 ≤ E)
    (hb : 0 ≤ b) (hxi : b ^ 2 ≤ xi / 12225)
    (hw : 0 ≤ w) (hs : (1 - u) ^ 2 - d ≤ w ^ 2)
    (hq : 0 < q) (hsub : w - (a + b) ≤ q)
    (hgap : 0 < √((1 - u) ^ 2 - d) - (√E + √(xi / 12225)))
    (hscalar : beta ≤ (12225 : ℝ) *
      ((H / u) ^ 32 + rotationPowerFloor * (M / 12225) ^ 12 / q ^ 24)) :
    beta ≤ BstLean.Part222.massBoundOrder 12225 12 M H xi E u d := by
  have h1 : a ≤ √E := le_sqrt_of_sq_le hE
  have h2 : b ≤ √(xi / 12225) := le_sqrt_of_sq_le hxi
  have h3 : √((1 - u) ^ 2 - d) ≤ w := sqrt_le_iff.mpr ⟨hw, hs⟩
  have hg : √((1 - u) ^ 2 - d) - (√E + √(xi / 12225)) ≤ q := by
    linarith
  have hr0 : 0 ≤ rotationPowerFloor := by unfold rotationPowerFloor; positivity
  have hr := rotation_power_lower
  apply hscalar.trans
  unfold BstLean.Part222.massBoundOrder
  norm_num only [Nat.cast_ofNat, Nat.reduceMul]
  gcongr

/-- Two mass tests and two quotient tests exclude every positive cutoff. -/
theorem cutoff_split_obstruction {N E d d0 d1 : ℝ}
    (hN : 0 < N) (hd : 0 < d) (h0 : 0 < d0) (h1 : 0 < d1)
    (h01 : d0 ≤ d1)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√E + √(parallelCap / 12225)))
    (hnum0 : (1.4601 : ℝ) * d0 ≤ N)
    (hnum1 : (1.4101 : ℝ) * d1 ≤ N)
    (hm0 : ∀ z, d0 ≤ z →
      0 < √((1 - radiusCutoff) ^ 2 - z) - (√E + √(parallelCap / 12225)) →
      (0.05 : ℝ) ≤ BstLean.Part222.massBoundOrder 12225 12
        directionCap energyCap parallelCap E radiusCutoff z)
    (hm1 : ∀ z, d1 ≤ z →
      0 < √((1 - radiusCutoff) ^ 2 - z) - (√E + √(parallelCap / 12225)) →
      (1.4601 : ℝ) ≤ BstLean.Part222.massBoundOrder 12225 12
        directionCap energyCap parallelCap E radiusCutoff z) :
    (1.4601 : ℝ) ≤ N / d + BstLean.Part222.massBoundOrder 12225 12
      directionCap energyCap parallelCap E radiusCutoff d := by
  have hm : 0 ≤ BstLean.Part222.massBoundOrder 12225 12
      directionCap energyCap parallelCap E radiusCutoff d := by
    unfold BstLean.Part222.massBoundOrder
    norm_num only [Nat.cast_ofNat, Nat.reduceMul]
    positivity
  rcases le_total d d0 with h | h
  · have hn : (1.4601 : ℝ) ≤ N / d := (le_div_iff₀ hd).mpr (by nlinarith)
    linarith
  · rcases le_total d d1 with hh | hh
    · have hn : (1.4101 : ℝ) ≤ N / d := (le_div_iff₀ hd).mpr (by nlinarith)
      have hm := hm0 d h hgap
      linarith
    · have hm := hm1 d hh hgap
      have hn : 0 ≤ N / d := div_nonneg hN.le hd.le
      linarith

end BstLean.Part253
