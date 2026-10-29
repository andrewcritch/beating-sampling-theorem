import BstLean.Part253Mass
import BstLean.Part259Local

namespace BstLean.Part263
open Real

theorem gap_lower {n : ℕ} {E xi u d a b q : ℝ}
    (ha : 0 ≤ a) (hE : E ≤ a ^ 2) (hb : 0 ≤ b) (hxi : xi / n ≤ b ^ 2)
    (_hq : 0 ≤ q) (hs : (q + a + b) ^ 2 ≤ (1 - u) ^ 2 - d) :
    q ≤ √((1 - u) ^ 2 - d) - (√E + √(xi / n)) := by
  have h1 : √E ≤ a := sqrt_le_iff.mpr ⟨ha, hE⟩
  have h2 : √(xi / n) ≤ b := sqrt_le_iff.mpr ⟨hb, hxi⟩
  have h3 : q + a + b ≤ √((1 - u) ^ 2 - d) := le_sqrt_of_sq_le hs
  linarith

theorem mass_bound_rational {n : ℕ} {M H xi E u d a b q beta : ℝ}
    (_hM : 0 ≤ M) (ha : 0 ≤ a) (hE : E ≤ a ^ 2)
    (hb : 0 ≤ b) (hxi : xi / n ≤ b ^ 2) (hq : 0 < q)
    (hs : (q + a + b) ^ 2 ≤ (1 - u) ^ 2 - d)
    (hscalar : (n : ℝ) * ((H / u) ^ 32 +
      BstLean.Part253.rotationPowerCap * (M / n) ^ 12 / q ^ 24) ≤ beta) :
    BstLean.Part222.massBoundOrder n 12 M H xi E u d ≤ beta := by
  have hg := gap_lower ha hE hb hxi hq.le hs
  apply le_trans ?_ hscalar
  unfold BstLean.Part222.massBoundOrder
  norm_num only [Nat.cast_ofNat, Nat.reduceMul]
  gcongr
  · unfold BstLean.Part253.rotationPowerCap
    positivity
  · exact BstLean.Part253.rotation_power_le

structure CellData where
  lower : ℝ
  upper : ℝ
  covariance : ℝ
  centre : ℝ
  energy : ℝ
  cutoff : ℝ
  frame : ℝ

/-- This certificate checks scalar data. It supplies no network event. -/
structure CellCertificate (n : ℕ) (M H xi : ℝ) (r : CellData) : Prop where
  window : r.lower ≤ r.upper
  covariance_nonneg : 0 ≤ r.covariance
  centre_nonneg : 0 ≤ r.centre
  energy_nonneg : 0 ≤ r.energy
  cutoff_pos : 0 < r.cutoff
  cutoff_lt : r.cutoff < (1 - (286 / 100000 : ℝ)) ^ 2
  gap_pos : 0 < √((1 - (286 / 100000 : ℝ)) ^ 2 - r.cutoff) -
    (√r.energy + √(xi / n))
  mass_scalar : BstLean.Part222.massBoundOrder n 12 M H xi r.energy
    (286 / 100000) r.cutoff ≤ (11 / 1000 : ℝ)
  frame_scalar : (r.covariance + r.centre) / r.cutoff + 11 / 1000 ≤ r.frame

end BstLean.Part263
