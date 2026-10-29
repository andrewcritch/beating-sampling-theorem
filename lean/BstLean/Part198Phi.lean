import BstLean.Part160MFU

/-! The sharp Gaussian distribution-function inequality used by the HS estimate. -/
namespace BstLean.Part198
open MeasureTheory Real Set Filter Topology
open BstLean.Part153 (phiG PhiG hasDerivAt_phiG hasDerivAt_PhiG phiG_pos)
open BstLean.Part154 BstLean.Part160

private def DownCross (f : ℝ → ℝ) : Prop :=
  ∀ x y, 0 ≤ x → x ≤ y → f x < 0 → f y ≤ 0

/-- A derivative with one downward sign change gives the same property to its primitive. -/
private lemma downCross_primitive {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hdown : DownCross f') : DownCross f := by
  intro x y hx hxy hfx
  by_contra hy
  have hfy : 0 < f y := lt_of_not_ge hy
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with e | h
    · rw [← e, h0] at hfx; exact False.elim (lt_irrefl _ hfx)
    · exact h
  have hxy' : x < y := by
    rcases hxy.eq_or_lt with e | h
    · subst y; linarith
    · exact h
  obtain ⟨u, hu, hdu⟩ := exists_deriv_neg hd hx0 (by simpa [h0] using hfx)
  obtain ⟨v, hv, hdv⟩ := exists_deriv_pos hd hxy' (lt_trans hfx hfy)
  have := hdown u v hu.1.le (hu.2.le.trans hv.1.le) hdu
  linarith

private noncomputable def bPhi : ℝ := 2 / π - 1 / 2
private noncomputable def dPhi : ℝ := 1 - 2 / π

private lemma bPhi_pos : 0 < bPhi := by
  unfold bPhi
  have := pi_lt_four
  have := pi_pos
  apply sub_pos.mpr
  apply (lt_div_iff₀ Real.pi_pos).mpr
  linarith

private lemma dPhi_pos : 0 < dPhi := by
  unfold dPhi
  have := pi_gt_three
  have : 2 / π < (1 : ℝ) := (div_lt_one pi_pos).mpr (by linarith)
  linarith

private noncomputable def fPhi (y : ℝ) : ℝ :=
  exp (dPhi * y) * (1 - 2 * bPhi * y) - 1

private lemma deriv_fPhi (y : ℝ) : HasDerivAt fPhi
    (exp (dPhi * y) * (dPhi - 2 * bPhi - 2 * bPhi * dPhi * y)) y := by
  have h := ((((hasDerivAt_id y).const_mul dPhi).exp).mul
    (((hasDerivAt_id y).const_mul (2 * bPhi)).const_sub 1)).sub_const 1
  refine HasDerivAt.congr_deriv (show HasDerivAt fPhi _ y from h) ?_
  simp only [id]
  ring

private lemma fPhi_down : DownCross fPhi := by
  apply downCross_primitive deriv_fPhi (by simp [fPhi])
  intro x y hx hxy hneg
  have hx' : dPhi - 2 * bPhi - 2 * bPhi * dPhi * x < 0 := by
    nlinarith only [hneg, exp_pos (dPhi * x)]
  have hxy' : 2 * bPhi * dPhi * x ≤ 2 * bPhi * dPhi * y := mul_le_mul_of_nonneg_left hxy
    (mul_nonneg (mul_nonneg (by norm_num) bPhi_pos.le) dPhi_pos.le)
  exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le (by linarith)

private noncomputable def ePhi (t : ℝ) : ℝ :=
  2 * phiG 0 * t * exp (-bPhi * t ^ 2) - (2 * PhiG t - 1)

private lemma deriv_ePhi (t : ℝ) : HasDerivAt ePhi
    (2 * phiG 0 * exp (-(t ^ 2) / 2) * fPhi (t ^ 2)) t := by
  have h := (((hasDerivAt_id t).const_mul (2 * phiG 0)).mul
    ((((hasDerivAt_id t).pow 2).const_mul (-bPhi)).exp)).sub
    (((hasDerivAt_PhiG t).const_mul 2).sub_const 1)
  have he : exp (-(t ^ 2) / 2) * exp (dPhi * t ^ 2) = exp (-bPhi * t ^ 2) := by
    rw [← exp_add]
    congr 1
    unfold bPhi dPhi
    ring
  have hp : phiG t = phiG 0 * exp (-(t ^ 2) / 2) := by
    simp [phiG, neg_div]
  refine HasDerivAt.congr_deriv (show HasDerivAt ePhi _ t from h) ?_
  unfold fPhi
  simp only [Pi.pow_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  rw [hp]
  linear_combination -2 * phiG 0 * (1 - 2 * bPhi * t ^ 2) * he

private lemma ePhi_down : DownCross ePhi := by
  apply downCross_primitive deriv_ePhi (by simp [ePhi, PhiG_zero])
  intro x y hx hxy hneg
  have hp : 0 < 2 * phiG 0 * exp (-(x ^ 2) / 2) :=
    mul_pos (mul_pos (by norm_num) (phiG_pos 0)) (exp_pos _)
  have hfx : fPhi (x ^ 2) < 0 := by nlinarith only [hp, hneg]
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx hxy 2
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num) (phiG_pos 0).le) (exp_pos _).le)
    (fPhi_down _ _ (sq_nonneg _) hsq hfx)

private noncomputable def squareGap (t : ℝ) : ℝ :=
  1 - exp (-(2 / π) * t ^ 2) - (2 * PhiG t - 1) ^ 2

private lemma deriv_squareGap (t : ℝ) : HasDerivAt squareGap
    (4 * phiG t * ePhi t) t := by
  have h := (((((hasDerivAt_id t).pow 2).const_mul (-(2 / π))).exp).const_sub 1).sub
    ((((hasDerivAt_PhiG t).const_mul 2).sub_const 1).pow 2)
  have hp : phiG t = phiG 0 * exp (-(t ^ 2) / 2) := by
    simp [phiG, neg_div]
  have hp0 : phiG 0 ^ 2 = 1 / (2 * π) := by
    unfold phiG
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
      zero_div, exp_zero, mul_one, inv_pow]
    rw [sq_sqrt (by positivity)]
    simp
  have he : exp (-(t ^ 2) / 2) * exp (-bPhi * t ^ 2) =
      exp (-(2 / π) * t ^ 2) := by
    rw [← exp_add]
    congr 1
    unfold bPhi
    ring
  refine HasDerivAt.congr_deriv (show HasDerivAt squareGap _ t from h) ?_
  symm
  simp only [Pi.pow_apply, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  unfold ePhi
  rw [hp]
  calc 4 * (phiG 0 * exp (-(t ^ 2) / 2)) *
        (2 * phiG 0 * t * exp (-bPhi * t ^ 2) - (2 * PhiG t - 1)) =
      8 * phiG 0 ^ 2 * t * (exp (-(t ^ 2) / 2) * exp (-bPhi * t ^ 2)) -
        8 * phiG 0 * exp (-(t ^ 2) / 2) * PhiG t +
        4 * phiG 0 * exp (-(t ^ 2) / 2) := by ring
    _ = _ := by rw [hp0, he]; ring

private lemma squareGap_limit : Tendsto squareGap atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => exp (-(2 / π) * t ^ 2)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
      (neg_lt_zero.mpr (div_pos (by norm_num) pi_pos))
  have h := (he.const_sub 1).sub (((tendsto_PhiG.const_mul 2).sub_const 1).pow 2)
  norm_num at h
  change Tendsto (fun t : ℝ => 1 - exp (-(2 / π) * t ^ 2) -
    (2 * PhiG t - 1) ^ 2) atTop (𝓝 0)
  simpa only [neg_mul] using h

/-- The square-versus-disc bound follows from a one-change derivative argument. -/
theorem PhiG_square_bound (t : ℝ) :
    (2 * PhiG t - 1) ^ 2 ≤ 1 - exp (-(2 / π) * t ^ 2) := by
  have hpos : ∀ x : ℝ, 0 ≤ x → 0 ≤ squareGap x := by
    intro x hx
    by_contra h
    have hneg : squareGap x < 0 := lt_of_not_ge h
    have hzero : squareGap 0 = 0 := by simp [squareGap, PhiG_zero]
    have hx0 : 0 < x := by
      rcases hx.eq_or_lt with e | h
      · rw [← e, hzero] at hneg; exact False.elim (lt_irrefl _ hneg)
      · exact h
    obtain ⟨u, hu, hdu⟩ := exists_deriv_neg deriv_squareGap hx0
      (by simpa [hzero] using hneg)
    obtain ⟨v, hv, hdv⟩ := exists_deriv_pos_after deriv_squareGap squareGap_limit hneg
    have hu' : ePhi u < 0 := by nlinarith only [hdu, phiG_pos u]
    have hv' : 0 < ePhi v := by nlinarith only [hdv, phiG_pos v]
    have := ePhi_down u v hu.1.le (hu.2.le.trans hv.le) hu'
    linarith
  rcases le_total 0 t with ht | ht
  · have := hpos t ht
    unfold squareGap at this
    linarith
  · have := hpos (-t) (by linarith)
    unfold squareGap at this
    rw [PhiG_neg_eq, neg_sq] at this
    nlinarith only [this]

/-- The sharp exponential lower bound for the Gaussian Bernoulli variance. -/
theorem PhiG_variance_lower (t : ℝ) :
    exp (-(2 / π) * t ^ 2) / 4 ≤ PhiG t * (1 - PhiG t) := by
  nlinarith only [PhiG_square_bound t]

#print axioms PhiG_square_bound
#print axioms PhiG_variance_lower
end BstLean.Part198
