import BstLean.Part228Cancellation

/-! Small proof rules for exact rational interval certificates. -/
namespace BstLean.Part228
open Real

def Bounds (x l u : ℝ) : Prop := l ≤ x ∧ x ≤ u

namespace Bounds
theorem point (x : ℝ) : Bounds x x x := ⟨le_rfl, le_rfl⟩

theorem add {x y l u a b L U : ℝ} (hx : Bounds x l u) (hy : Bounds y a b)
    (h : L ≤ l+a ∧ u+b ≤ U) : Bounds (x+y) L U := by
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, h.1, h.2]

theorem neg {x l u : ℝ} (hx : Bounds x l u) : Bounds (-x) (-u) (-l) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem mul {x y l u a b L U : ℝ} (hx : Bounds x l u) (hy : Bounds y a b)
    (h : L ≤ l*a ∧ L ≤ l*b ∧ L ≤ u*a ∧ L ≤ u*b ∧
      l*a ≤ U ∧ l*b ≤ U ∧ u*a ≤ U ∧ u*b ≤ U) : Bounds (x*y) L U := by
  have hm := BstLean.Part193.Interval.mem_mul
    (I := ⟨l,u,hx.1.trans hx.2⟩) (J := ⟨a,b,hy.1.trans hy.2⟩) hx hy
  exact ⟨(le_min (le_min h.1 h.2.1) (le_min h.2.2.1 h.2.2.2.1)).trans hm.1,
    hm.2.trans (max_le (max_le h.2.2.2.2.1 h.2.2.2.2.2.1)
      (max_le h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2))⟩

theorem inv {x l u L U : ℝ} (hx : Bounds x l u)
    (h : 0 < l ∧ L ≤ 1/u ∧ 1/l ≤ U) : Bounds (1/x) L U := by
  exact ⟨h.2.1.trans (one_div_le_one_div_of_le (h.1.trans_le hx.1) hx.2),
    (one_div_le_one_div_of_le h.1 hx.1).trans h.2.2⟩

theorem sqrt {x l u L U : ℝ} (hx : Bounds x l u)
    (h : 0 ≤ L ∧ 0 ≤ U ∧ L^2 ≤ l ∧ u ≤ U^2) : Bounds (√x) L U :=
  BstLean.Part193.Interval.sqrt_bounds h.1 h.2.1 (h.2.2.1.trans hx.1)
    (hx.2.trans h.2.2.2)

theorem pow {x l u L U : ℝ} (hx : Bounds x l u) (k : ℕ)
    (h : 0 ≤ l ∧ L ≤ l^k ∧ u^k ≤ U) : Bounds (x^k) L U := by
  exact ⟨h.2.1.trans (pow_le_pow_left₀ h.1 hx.1 k),
    (pow_le_pow_left₀ (h.1.trans hx.1) hx.2 k).trans h.2.2⟩

theorem pow_even_neg {x l u L U : ℝ} (hx : Bounds x l u) (k : ℕ)
    (hk : Even k) (h : u ≤ 0 ∧ L ≤ (-u)^k ∧ (-l)^k ≤ U) : Bounds (x^k) L U := by
  have hp := pow (neg hx) k ⟨by linarith [h.1], h.2⟩
  simpa only [hk.neg_pow] using hp

theorem pow_odd_neg {x l u L U : ℝ} (hx : Bounds x l u) (k : ℕ)
    (hk : Odd k) (h : u ≤ 0 ∧ -U ≤ (-u)^k ∧ (-l)^k ≤ -L) : Bounds (x^k) L U := by
  have hp := pow (neg hx) k ⟨by linarith [h.1], h.2⟩
  simpa only [hk.neg_pow, neg_neg] using neg hp

theorem abs {x l u L U : ℝ} (hx : Bounds x l u)
    (h : L ≤ 0 ∧ -U ≤ l ∧ u ≤ U) : Bounds |x| L U :=
  ⟨h.1.trans (abs_nonneg _), abs_le.mpr ⟨h.2.1.trans hx.1, hx.2.trans h.2.2⟩⟩

theorem abs_pos {x l u : ℝ} (hx : Bounds x l u) (h : 0 ≤ l) : Bounds |x| l u := by
  rw [abs_of_nonneg (h.trans hx.1)]; exact hx

theorem abs_neg {x l u : ℝ} (hx : Bounds x l u) (h : u ≤ 0) : Bounds |x| (-u) (-l) := by
  rw [abs_of_nonpos (hx.2.trans h)]; exact neg hx
end Bounds

noncomputable def endpointAt (θ x σ : ℝ) : ℝ := √(1-θ) + σ*6*√θ*x
noncomputable def endpointDrift (θ x σ : ℝ) : ℝ :=
  (σ*12*√(1-θ)*√θ + 36*θ*x) / (θ*(1-(endpointAt θ x σ)^2))

def ScaledCell (θ x σ E : ℝ) : Prop :=
  0 < 1-(σ*8)*x ∧ |endpointRatio (endpointAt θ x σ)*(σ*8)*x| < 1 ∧
    scaledExponentBound θ (endpointRatio (endpointAt θ x σ)) x (σ*8)
      (endpointDrift θ x σ) ≤ E

theorem endpointAt_drift {θ x σ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hσ : σ = -1 ∨ σ = 1) (hb : 1 - (endpointAt θ x σ)^2 ≠ 0) :
    endpointRatio (endpointAt θ x σ) - (1-θ)/θ = x * endpointDrift θ x σ := by
  rw [endpointRatio_sub hθ.ne' hb]
  have hc : (√(1-θ))^2 = 1-θ := sq_sqrt (by linarith)
  have hq : (√θ)^2 = θ := sq_sqrt hθ.le
  have he : (endpointAt θ x σ)^2 - (1-θ) =
      x*(σ*12*√(1-θ)*√θ + 36*θ*x) := by
    unfold endpointAt
    rcases hσ with rfl | rfl <;> linear_combination hc + 36*x^2*hq
  rw [he]
  unfold endpointDrift
  ring

end BstLean.Part228
