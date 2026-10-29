import BstLean.Part203Stages
import BstLean.Part203Choice

/-! Part 203: Chernoff tails and complete END reduction for either exponent choice. -/
namespace BstLean.Part203
open MeasureTheory ProbabilityTheory Real BstLean.Part156

noncomputable def endpointPlus (m : LogChoice) (a h H c f τ v₀ b : ℝ) : ℝ :=
  -τ * (1 / 100) + m.rhs (worldC c τ v₀) (worldK c τ v₀)
    (1 + H / (b * (√(1 / 100 / a) + h)))
    (H * (b * (√(1 / 100 / a) + h)) + H ^ 2) ((√(1 / 100 / a) + h) ^ 2) f

noncomputable def endpointMinus (m : LogChoice) (a h H c f τ v₀ b : ℝ) : ℝ :=
  -τ * (1 / 1000) + m.rhs (worldC c τ v₀) (worldK c τ v₀)
    (1 - H / (b * (√(1 / 100 / a) - h)))
    (-H * (b * (√(1 / 100 / a) - h)) + H ^ 2) ((√(1 / 100 / a) - h) ^ 2) f

section Tails
variable {Ω : Type*} [MeasurableSpace Ω]

theorem choice_mgf_plus (μ : Measure Ω) {p : Ω → ℝ}
    {n c f H Q τ v₀ r : ℝ} (h : FreeCPR μ p n c f H Q)
    (m : LogChoice) (hm : m.Valid) (hn : 0 < n) (hf : 0 < f)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hτ : 0 < τ)
    (hv0 : 0 ≤ v₀) (hv1 : v₀ ≤ 1) (hr : 0 < r) :
    ∫ ω, exp (n * τ * p ω) ∂μ ≤ exp (n * m.rhs (worldC c τ v₀) (worldK c τ v₀)
      (1 + H / r) (H * r + H ^ 2) Q f) :=
  (h.1 τ v₀ r hτ hv0 hv1 hr).trans
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (m.exact_le hm hf hQ0 hQ1) hn.le))

theorem choice_mgf_minus (μ : Measure Ω) {p : Ω → ℝ}
    {n c f H Q τ v₀ r : ℝ} (h : FreeCPR μ p n c f H Q)
    (m : LogChoice) (hm : m.Valid) (hn : 0 < n) (hf : 0 < f)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hτ : τ < 0)
    (hv0 : 0 ≤ v₀) (hv1 : v₀ ≤ 1) (hr : H < r) :
    ∫ ω, exp (n * τ * p ω) ∂μ ≤ exp (n * m.rhs (worldC c τ v₀) (worldK c τ v₀)
      (1 - H / r) (-H * r + H ^ 2) Q f) :=
  (h.2 τ v₀ r hτ hv0 hv1 hr).trans
    (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (m.exact_le hm hf hQ0 hQ1) hn.le))

/-- The upper endpoint tail applies to every actual stand-in mean Q in [0,1]. -/
theorem tail_plus (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
    (m : LogChoice) (hm : m.Valid) {n c f H Q a h τ v₀ b : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hτ : 0 < τ) (hv0 : 0 ≤ v₀) (hv1 : v₀ ≤ 1) (hb : 0 < b)
    (hE : endpointPlus m a h H c f τ v₀ b ≤ 0) (hCP : FreeCPR μ p n c f H Q) :
    μ.real {ω | zplus a h Q < p ω} ≤ exp (n * endpointPlus m a h H c f τ v₀ b) := by
  set z := zplus a h Q
  have hz0 : (1 : ℝ) / 100 ≤ z := zplus_ge a h Q
  have hzpos : 0 < z := by linarith
  set x₀ := √(1 / 100 / a)
  set x := √(z / a)
  have hx₀ : 0 < x₀ := sqrt_pos.mpr (by positivity)
  have hxx : x₀ ≤ x := sqrt_le_sqrt (div_le_div_of_nonneg_right hz0 ha.le)
  have hx : 0 < x := hx₀.trans_le hxx
  set t := x / x₀
  have ht : 1 ≤ t := (one_le_div hx₀).mpr hxx
  have hxt : x = t * x₀ := by dsimp [t]; field_simp
  have hzt : z = t ^ 2 * (1 / 100) := by
    have hsx : x ^ 2 = z / a := sq_sqrt (by positivity)
    have hs0 : x₀ ^ 2 = 1 / 100 / a := sq_sqrt (by positivity)
    have he : t ^ 2 = x ^ 2 / x₀ ^ 2 := by dsimp [t]; ring
    rw [he, hsx, hs0]
    field_simp
  set C := worldC c τ v₀
  set K := worldK c τ v₀
  have hdom : 0 < 1 + v₀ * (exp (τ * c) - 1) := bernoulli_pos hv0 hv1
  have hC : 0 ≤ C := tangentC_nonneg (by linarith only [hdom]) hc
  have hK : 0 < K := worldK_pos hc hτ hdom
  have hr : 0 < b * (x + h) := mul_pos hb (by linarith)
  have hmgf := choice_mgf_plus μ hCP m hm hn hf hQ0 hQ1 hτ hv0 hv1 hr
  have hQw : Q ≤ (x + h) ^ 2 := le_wplus_zplus hQ0 ha
  have hX : 0 ≤ exp (f * K * (1 + H / (b * (x + h)))) - 1 := by
    have hα : 0 ≤ 1 + H / (b * (x + h)) := by positivity
    have := Real.one_le_exp (mul_nonneg (mul_nonneg hf.le hK.le) hα)
    linarith
  have hsubQ := m.mono_Q (C := C) (β := H * (b * (x + h)) + H ^ 2)
    hm hf hQ0 hQ1 hQw hX
  have hscale := m.plus_END hm hC hK.le hf hH hb hh hx₀ ht
  have he : -τ * z + m.rhs C K (1 + H / (b * (x + h)))
      (H * (b * (x + h)) + H ^ 2) Q f ≤
      t ^ 2 * endpointPlus m a h H c f τ v₀ b := by
    rw [hxt] at hsubQ
    unfold endpointPlus
    rw [hzt, hxt]
    dsimp [C, K, x₀] at hsubQ hscale ⊢
    nlinarith only [hsubQ, hscale]
  have he2 : t ^ 2 * endpointPlus m a h H c f τ v₀ b ≤
      endpointPlus m a h H c f τ v₀ b := by
    have ht2 : 1 ≤ t ^ 2 := by nlinarith only [ht]
    nlinarith only [ht2, hE]
  have hi := integrable_exp_mul μ hp hp0 hp1 (n * τ)
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := p) z (mul_pos hn hτ).le hi
  calc
    _ ≤ μ.real {ω | z ≤ p ω} :=
      measureReal_mono (fun ω hω => le_of_lt (show z < p ω from hω))
    _ ≤ exp (-(n * τ) * z) * mgf p μ (n * τ) := hch
    _ ≤ exp (-(n * τ) * z) * exp (n * m.rhs C K (1 + H / (b * (x + h)))
        (H * (b * (x + h)) + H ^ 2) Q f) :=
      mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (n * (-τ * z + m.rhs C K (1 + H / (b * (x + h)))
        (H * (b * (x + h)) + H ^ 2) Q f)) := by rw [← exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonneg_left (he.trans he2) hn.le)

/-- The lower endpoint tail proves w(z) = Q ≤ 1 before END is applied. -/
theorem tail_minus (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → ℝ}
    (hp : Measurable p) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : ∀ ω, p ω ≤ 1)
    (m : LogChoice) (hm : m.Valid) {n c f H Q a h τ v₀ b : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hf : 0 < f) (hH : 0 ≤ H)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hτ : τ < 0) (hv0 : 0 ≤ v₀) (hv1 : v₀ ≤ 1) (hb : 0 < b)
    (hside : 2 * h + 2 * H / b < √(1 / 100 / a))
    (hE : endpointMinus m a h H c f τ v₀ b ≤ 0) (hCP : FreeCPR μ p n c f H Q)
    (hzQ : 1 / 1000 < zminus a h Q) :
    μ.real {ω | p ω < zminus a h Q} ≤ exp (n * endpointMinus m a h H c f τ v₀ b) := by
  set z := zminus a h Q
  set x₀ := √(1 / 100 / a)
  set x := √Q + h
  have hx₀ : 0 < x₀ := sqrt_pos.mpr (by positivity)
  have hxx : x₀ ≤ x := by
    have hz : (1 : ℝ) / 1000 ≤ z := hzQ.le
    have he : x = √(10 * z / a) := (sqrt_ten_zminus ha hh).symm
    rw [he]
    exact sqrt_le_sqrt ((div_le_div_iff_of_pos_right ha).mpr (by linarith))
  set t := x / x₀
  have ht : 1 ≤ t := (one_le_div hx₀).mpr hxx
  have hxt : x = t * x₀ := by dsimp [t]; field_simp
  have hzt : z = t ^ 2 * (1 / 1000) := by
    have hs0 : x₀ ^ 2 = 1 / 100 / a := sq_sqrt (by positivity)
    have hz : z = a / 10 * x ^ 2 := rfl
    rw [hz, hxt, mul_pow, hs0]
    field_simp
    ring
  have hsQ : √Q = t * x₀ - h := by rw [← hxt]; dsimp [x]; ring
  have hQw : (t * x₀ - h) ^ 2 = Q := by rw [← hsQ, sq_sqrt hQ0]
  have hinterval := negative_admissible ha hh hQ0 hQ1
    (z := z) (by dsimp [z, zminus]; ring) hzQ.le
  set C := worldC c τ v₀
  set K := worldK c τ v₀
  have hdom : 0 < 1 + v₀ * (exp (τ * c) - 1) := bernoulli_pos hv0 hv1
  have hC : 0 ≤ C := tangentC_nonneg (by linarith only [hdom]) hc
  have hK : K < 0 := worldK_neg hc hτ hdom
  have hg := minus_geometry hH hb hh hside ht
  have hr : H < b * (t * x₀ - h) := by
    have hrad : x₀ - h ≤ t * x₀ - h := by nlinarith only [ht, hx₀]
    exact hg.1.trans_le (mul_le_mul_of_nonneg_left hrad hb.le)
  have hmgf := choice_mgf_minus μ hCP m hm hn hf hQ0 hQ1 hτ hv0 hv1 hr
  have hscale := m.minus_END hm hC hK.le hf hH hb hh hside ht (by rwa [hQw])
  have he : -τ * z + m.rhs C K (1 - H / (b * (t * x₀ - h)))
      (-H * (b * (t * x₀ - h)) + H ^ 2) Q f ≤
      t ^ 2 * endpointMinus m a h H c f τ v₀ b := by
    unfold endpointMinus
    rw [hzt, ← hQw]
    dsimp [C, K, x₀] at hscale ⊢
    nlinarith only [hscale]
  have he2 : t ^ 2 * endpointMinus m a h H c f τ v₀ b ≤
      endpointMinus m a h H c f τ v₀ b := by
    have ht2 : 1 ≤ t ^ 2 := by nlinarith only [ht]
    nlinarith only [ht2, hE]
  have hi := integrable_exp_mul μ hp hp0 hp1 (n * τ)
  have hch := measure_le_le_exp_mul_mgf (μ := μ) (X := p) z
    (mul_neg_of_pos_of_neg hn hτ).le hi
  calc
    _ ≤ μ.real {ω | p ω ≤ z} :=
      measureReal_mono (fun ω hω => le_of_lt (show p ω < z from hω))
    _ ≤ exp (-(n * τ) * z) * mgf p μ (n * τ) := hch
    _ ≤ exp (-(n * τ) * z) * exp (n * m.rhs C K (1 - H / (b * (t * x₀ - h)))
        (-H * (b * (t * x₀ - h)) + H ^ 2) Q f) :=
      mul_le_mul_of_nonneg_left hmgf (exp_pos _).le
    _ = exp (n * (-τ * z + m.rhs C K (1 - H / (b * (t * x₀ - h)))
        (-H * (b * (t * x₀ - h)) + H ^ 2) Q f)) := by rw [← exp_add]; congr 1; ring
    _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonneg_left (he.trans he2) hn.le)

end Tails
end BstLean.Part203
