import BstLean.Part182Cov
import BstLean.Part193Cover

/-! Part 199: variable input windows and overlap intervals.
All averages use the same Gaussian stand-in input distribution. -/
namespace BstLean.Part199
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part150 BstLean.Part182

/-- Parameters of one input and pair window. -/
structure Window where
  t : ℝ
  z : ℝ
  pair : ℝ
  t_nonneg : 0 ≤ t
  z_nonneg : 0 ≤ z
  pair_nonneg : 0 ≤ pair

noncomputable def radiusMinus (n : ℕ) (θ : ℝ) (w : Window) : ℝ :=
  2 * w.t * √(θ * (1 - θ) / n) + 2 * θ * √(w.z / n)

noncomputable def radiusPlus (n : ℕ) (θ : ℝ) (w : Window) : ℝ :=
  radiusMinus n θ w + 2 * θ * w.z / n

noncomputable def planeRatio (n : ℕ) (θ : ℝ) (w : Window) : ℝ :=
  w.t * √(θ / ((1 - θ) * n))

noncomputable def overlapNumerator (n : ℕ) (θ : ℝ) (w : Window) (s : ℝ) : ℝ :=
  (1 - θ) * (1 + s * planeRatio n θ w) ^ 2 + s * (θ / n * w.pair * gPlus n w.z)

/-- Scalar premises for a variable overlap interval. -/
structure OverlapGuard (n : ℕ) (θ : ℝ) (w : Window) (lo hi : ℝ) : Prop where
  theta_nonneg : 0 ≤ θ
  theta_lt_one : θ < 1
  plane_lt_one : planeRatio n θ w < 1
  radius_lt_one : radiusMinus n θ w < 1
  lo_nonneg : 0 ≤ lo
  lower : lo * (1 + radiusPlus n θ w) ≤ overlapNumerator n θ w (-1)
  upper : overlapNumerator n θ w 1 ≤ hi * (1 - radiusMinus n θ w)

theorem radiusMinus_nonneg {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (w : Window) :
    0 ≤ radiusMinus n θ w := by
  unfold radiusMinus
  have := w.t_nonneg
  positivity

theorem radiusPlus_nonneg {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (w : Window) :
    0 ≤ radiusPlus n θ w := by
  have := radiusMinus_nonneg (n := n) hθ w
  have := w.z_nonneg
  unfold radiusPlus
  positivity

/-- Exact scalar guards imply actual pair containment, with no fixed dimension floor. -/
theorem overlap_of_guard {n : ℕ} (hn : 0 < n) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) (w : Window) {lo hi : ℝ}
    (h : OverlapGuard n (thetaC c τ) w lo hi)
    {a b : Fin n → ℝ} (hp : (a, b) ∈ GammaS c w.t w.z w.pair) :
    lo ≤ sphPt (c + τ • a) ⬝ᵥ sphPt (c + τ • b) ∧
      sphPt (c + τ • a) ⬝ᵥ sphPt (c + τ • b) ≤ hi := by
  have hc := ne_zero_of_thetaC_lt hn hτ h.theta_lt_one
  have hg := gamma_dot hn hc hτ w.t_nonneg w.z_nonneg w.pair_nonneg
    h.theta_lt_one hp h.plane_lt_one h.radius_lt_one
  have hd : 0 < 1 - radiusMinus n (thetaC c τ) w := by linarith [h.radius_lt_one]
  have hd' : 0 < 1 + radiusPlus n (thetaC c τ) w := by
    have := radiusPlus_nonneg (n := n) h.theta_nonneg w
    linarith
  have hL : 0 ≤ overlapNumerator n (thetaC c τ) w (-1) :=
    (mul_nonneg h.lo_nonneg hd'.le).trans h.lower
  have hg' : sphPt (c + τ • a) ⬝ᵥ sphPt (c + τ • b) ≤
      overlapNumerator n (thetaC c τ) w 1 /
      (1 - radiusMinus n (thetaC c τ) w) ∧
    (0 ≤ overlapNumerator n (thetaC c τ) w (-1) →
      overlapNumerator n (thetaC c τ) w (-1) /
        (1 + radiusPlus n (thetaC c τ) w) ≤ sphPt (c + τ • a) ⬝ᵥ sphPt (c + τ • b)) := by
    simpa only [overlapNumerator, planeRatio, radiusMinus, radiusPlus,
      one_mul, neg_one_mul, sub_eq_add_neg] using hg
  exact ⟨((le_div_iff₀ hd').mpr h.lower).trans (hg'.2 hL),
    hg'.1.trans ((div_le_iff₀ hd).mpr h.upper)⟩

/-- Componentwise window order. -/
def Window.LE (a b : Window) : Prop := a.t ≤ b.t ∧ a.z ≤ b.z ∧ a.pair ≤ b.pair

theorem omega_subset {n : ℕ} (c : Fin n → ℝ) {a b : Window} (h : a.LE b) :
    OmegaS c a.t a.z ⊆ OmegaS c b.t b.z := by
  intro ξ hξ
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h.2.1 (Nat.cast_nonneg n))
  exact ⟨hξ.1.trans h.1, by linarith [hξ.2.1], by linarith [hξ.2.2, h.2.1]⟩

theorem gPlus_mono (n : ℕ) {a b : Window} (h : a.z ≤ b.z) : gPlus n a.z ≤ gPlus n b.z := by
  unfold gPlus
  apply Real.sqrt_le_sqrt
  have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n))
  linarith

theorem gamma_subset {n : ℕ} (c : Fin n → ℝ) {a b : Window} (h : a.LE b) :
    GammaS c a.t a.z a.pair ⊆ GammaS c b.t b.z b.pair := by
  intro p hp
  refine ⟨omega_subset c h hp.1, omega_subset c h hp.2.1, hp.2.2.trans ?_⟩
  exact mul_le_mul h.2.2 (gPlus_mono n h.2.1) (Real.sqrt_nonneg _) b.pair_nonneg

/-- Local overlap guards transfer through a checked cover without a cell charge. -/
theorem overlap_guards_of_cover {n : ℕ} {w : Window} {lo hi : ℝ} {ι : Type*}
    {domain : Set ℝ} (C : BstLean.Part193.FiniteCover ℝ ι domain)
    (h : ∀ i ∈ C.indices, ∀ θ ∈ domain, θ ∈ C.cell i → OverlapGuard n θ w lo hi) :
    ∀ θ ∈ domain, OverlapGuard n θ w lo hi :=
  BstLean.Part193.finite_cover_property C h

end BstLean.Part199
