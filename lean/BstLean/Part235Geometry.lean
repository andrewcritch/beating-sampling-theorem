import BstLean.Part199Examples

/-! Part 235: scalar geometry certificates and actual pair containment. -/
namespace BstLean.Part235
open Real BstLean.Part199

/-- Rational summaries suffice to check the exact overlap formulas. -/
structure GeometryBounds (n : ℕ) (a b : ℝ) (w : Window) where
  plane : ℝ
  radius : ℝ
  radiusPlusBound : ℝ
  cross : ℝ
  a_nonneg : 0 ≤ a
  b_lt_one : b < 1
  plane_nonneg : 0 ≤ plane
  plane_lt_one : plane < 1
  radius_lt_one : radius < 1
  plane_bound : ∀ θ ∈ Set.Icc a b, planeRatio n θ w ≤ plane
  radius_bound : ∀ θ ∈ Set.Icc a b, radiusMinus n θ w ≤ radius
  radiusPlus_bound : ∀ θ ∈ Set.Icc a b, radiusPlus n θ w ≤ radiusPlusBound
  cross_bound : ∀ θ ∈ Set.Icc a b,
    θ / n * w.pair * BstLean.Part182.gPlus n w.z ≤ cross

theorem GeometryBounds.guard {n : ℕ} {a b lo hi : ℝ} {w : Window}
    (G : GeometryBounds n a b w) (hl : 0 ≤ lo) (hh : 0 ≤ hi)
    (hL : lo * (1 + G.radiusPlusBound) ≤ (1 - b) * (1 - G.plane) ^ 2 - G.cross)
    (hU : (1 - a) * (1 + G.plane) ^ 2 + G.cross ≤ hi * (1 - G.radius))
    {θ : ℝ} (hθ : θ ∈ Set.Icc a b) : OverlapGuard n θ w lo hi := by
  have hθ0 := G.a_nonneg.trans hθ.1
  have hθ1 := hθ.2.trans_lt G.b_lt_one
  have hp := G.plane_bound θ hθ
  have hr := G.radius_bound θ hθ
  have hrp := G.radiusPlus_bound θ hθ
  have hc := G.cross_bound θ hθ
  have hp0 : 0 ≤ planeRatio n θ w := by
    unfold planeRatio
    exact mul_nonneg w.t_nonneg (sqrt_nonneg _)
  have hlow : (1 - b) * (1 - G.plane) ^ 2 ≤
      (1 - θ) * (1 - planeRatio n θ w) ^ 2 := by
    apply mul_le_mul (sub_le_sub_left hθ.2 1)
      (pow_le_pow_left₀ (sub_nonneg.mpr G.plane_lt_one.le)
        (sub_le_sub_left hp 1) 2)
      (sq_nonneg _) (sub_nonneg.mpr hθ1.le)
  have hupp : (1 - θ) * (1 + planeRatio n θ w) ^ 2 ≤
      (1 - a) * (1 + G.plane) ^ 2 := by
    apply mul_le_mul (sub_le_sub_left hθ.1 1)
      (pow_le_pow_left₀ (add_nonneg zero_le_one hp0) (add_le_add le_rfl hp) 2)
      (sq_nonneg _) (sub_nonneg.mpr (hθ.1.trans hθ1.le))
  refine ⟨hθ0, hθ1, hp.trans_lt G.plane_lt_one, hr.trans_lt G.radius_lt_one, hl, ?_, ?_⟩
  · simpa only [overlapNumerator, neg_one_mul, ← sub_eq_add_neg] using
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hrp) hl).trans
        (hL.trans (sub_le_sub hlow hc))
  · simpa only [overlapNumerator, one_mul] using
      (add_le_add hupp hc).trans (hU.trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_left hr 1) hh))

/-- A certificate proves containment for the actual normalized pair. -/
theorem GeometryBounds.contains {n : ℕ} (hn : 0 < n) {a b lo hi : ℝ} {w : Window}
    (G : GeometryBounds n a b w) (hl : 0 ≤ lo) (hh : 0 ≤ hi)
    (hL : lo * (1 + G.radiusPlusBound) ≤ (1 - b) * (1 - G.plane) ^ 2 - G.cross)
    (hU : (1 - a) * (1 + G.plane) ^ 2 + G.cross ≤ hi * (1 - G.radius))
    {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ : BstLean.Part150.thetaC c τ ∈ Set.Icc a b)
    {p : (Fin n → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ BstLean.Part182.GammaS c w.t w.z w.pair) :
    lo ≤ dotProduct (BstLean.Part130.sphPt (c + τ • p.1))
      (BstLean.Part130.sphPt (c + τ • p.2)) ∧
    dotProduct (BstLean.Part130.sphPt (c + τ • p.1))
      (BstLean.Part130.sphPt (c + τ • p.2)) ≤ hi :=
  overlap_of_guard hn hτ w (G.guard hl hh hL hU hθ) hp

end BstLean.Part235
