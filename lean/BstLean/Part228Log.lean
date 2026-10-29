import BstLean.Part197Log

/-! The logarithm remainder retains the reciprocal degree factor. -/
namespace BstLean.Part228
open Real
open BstLean.Part197 (logOneAddSum)

theorem log_one_add_remainder_sharp {x : ℝ} (hx : |x| < 1) (N : ℕ) :
    |log (1 + x) - logOneAddSum N x| ≤
      |x| ^ (N + 1) / (((N + 1 : ℕ) : ℝ) * (1 - |x|)) := by
  let f : ℕ → ℝ := fun j => (-x) ^ (j + 1) / ((j + 1 : ℕ) : ℝ)
  have hf := hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using hx)
  have hfs : Summable f := by simpa [f] using hf.summable
  let A := |x| ^ (N + 1) / ((N + 1 : ℕ) : ℝ)
  have hgeo : Summable (fun j : ℕ => A * |x| ^ j) :=
    (summable_geometric_of_lt_one (abs_nonneg x) hx).mul_left A
  have hb (j : ℕ) : ‖f (j + N)‖ ≤ A * |x| ^ j := by
    have hD : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hD' : (0 : ℝ) < ((j + N + 1 : ℕ) : ℝ) := by positivity
    have hDD : ((N + 1 : ℕ) : ℝ) ≤ ((j + N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show N + 1 ≤ j + N + 1 by omega)
    have hpow : |x| ^ (j + N + 1) = |x| ^ (N + 1) * |x| ^ j := by
      rw [show j + N + 1 = N + 1 + j by omega, pow_add]
    dsimp [f, A]
    rw [abs_div, abs_pow, abs_neg,
      abs_of_pos hD', hpow, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) hD hDD
  have hnorm : Summable (fun j => ‖f (j + N)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgeo
  have he : |log (1 + x) - logOneAddSum N x| = ‖∑' j, f (j + N)‖ := by
    have hs := hfs.sum_add_tsum_nat_add N
    have hv : (∑' j, f j) = -log (1 + x) := by simpa [f] using hf.tsum_eq
    rw [hv] at hs
    unfold logOneAddSum
    rw [Real.norm_eq_abs]
    have he' : log (1 + x) - -(∑ j ∈ Finset.range N, (-x) ^ (j + 1) / ((j + 1 : ℕ) : ℝ)) =
        -(∑' j, f (j + N)) := by
      change log (1 + x) - -(∑ j ∈ Finset.range N, f j) = _
      linarith
    rw [he', abs_neg]
  rw [he]
  calc ‖∑' j, f (j + N)‖ ≤ ∑' j, ‖f (j + N)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, A * |x| ^ j := hnorm.tsum_le_tsum hb hgeo
    _ = A * (1 - |x|)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg x) hx]
    _ = _ := by dsimp [A]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem cancellation_remainder30 {x : ℝ} (hx : |x| < 1) :
    |(x - log (1 + x)) - (x - logOneAddSum 30 x)| ≤
      |x| ^ 31 / (31 * (1 - |x|)) := by
  have he : (x - log (1 + x)) - (x - logOneAddSum 30 x) =
      -(log (1 + x) - logOneAddSum 30 x) := by ring
  rw [he, abs_neg]
  simpa using log_one_add_remainder_sharp hx 30

end BstLean.Part228
