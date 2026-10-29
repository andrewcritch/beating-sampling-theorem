import BstLean.Part203FreeEnd

/-! Part 203: exact GP and TG are alternative completed exponents. -/
namespace BstLean.Part203
open Real

inductive LogChoice where
  | exact
  | tangent (u₀ : ℝ)

def LogChoice.Valid : LogChoice → Prop
  | .exact => True
  | .tangent u₀ => -1 < u₀

noncomputable def LogChoice.rhs (m : LogChoice) (C K α β Q L : ℝ) : ℝ :=
  match m with
  | .exact => exactRhs C K α β Q L
  | .tangent u₀ => tgRhs C K α β Q L u₀

lemma LogChoice.exact_le (m : LogChoice) (hm : m.Valid)
    {C K α β Q L : ℝ} (hL : 0 < L) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    exactRhs C K α β Q L ≤ m.rhs C K α β Q L := by
  cases m with
  | exact => exact le_rfl
  | tangent u₀ => exact exact_le_tg hL hQ0 hQ1 hm

lemma LogChoice.mono_Q (m : LogChoice) (hm : m.Valid)
    {C K α β Q W L : ℝ} (hL : 0 < L)
    (hQ : 0 ≤ Q) (hQ1 : Q ≤ 1) (hQW : Q ≤ W)
    (hX : 0 ≤ exp (L * K * α) - 1) :
    m.rhs C K α β Q L ≤ m.rhs C K α β W L := by
  have hmul := mul_le_mul_of_nonneg_right hQW hX
  cases m with
  | exact =>
    have hl := log_le_log (bernoulli_pos hQ hQ1) (by linarith :
      1 + Q * (exp (L * K * α) - 1) ≤ 1 + W * (exp (L * K * α) - 1))
    have := div_le_div_of_nonneg_right hl hL.le
    dsimp [LogChoice.rhs, exactRhs]
    linarith
  | tangent u₀ =>
    have := div_le_div_of_nonneg_right hmul
      (mul_nonneg hL.le (by change -1 < u₀ at hm; linarith : 0 ≤ 1 + u₀))
    dsimp [LogChoice.rhs, tgRhs]
    linarith

lemma LogChoice.plus_END (m : LogChoice) (hm : m.Valid)
    {C K L H b h x t : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 0 < L)
    (hH : 0 ≤ H) (hb : 0 < b) (hh : 0 ≤ h) (hx : 0 < x) (ht : 1 ≤ t) :
    m.rhs C K (1 + H / (b * (t * x + h)))
      (H * (b * (t * x + h)) + H ^ 2) ((t * x + h) ^ 2) L ≤
      t ^ 2 * m.rhs C K (1 + H / (b * (x + h)))
        (H * (b * (x + h)) + H ^ 2) ((x + h) ^ 2) L := by
  cases m with
  | exact => exact exact_plus_END hC hK hL hH hb hh hx ht
  | tangent u₀ => exact tg_plus_END hC hK hL hH hb hh hx ht hm

lemma LogChoice.minus_END (m : LogChoice) (hm : m.Valid)
    {C K L H b h x t : ℝ} (hC : 0 ≤ C) (hK : K ≤ 0) (hL : 0 < L)
    (hH : 0 ≤ H) (hb : 0 < b) (hh : 0 ≤ h)
    (hx : 2 * h + 2 * H / b < x) (ht : 1 ≤ t) (hw : (t * x - h) ^ 2 ≤ 1) :
    m.rhs C K (1 - H / (b * (t * x - h)))
      (-H * (b * (t * x - h)) + H ^ 2) ((t * x - h) ^ 2) L ≤
      t ^ 2 * m.rhs C K (1 - H / (b * (x - h)))
        (-H * (b * (x - h)) + H ^ 2) ((x - h) ^ 2) L := by
  cases m with
  | exact => exact exact_minus_END hC hK hL hH hb hh hx ht hw
  | tangent u₀ => exact tg_minus_END hC hK hL hH hb hh hx ht hm

end BstLean.Part203
