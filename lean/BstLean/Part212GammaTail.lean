import Mathlib

/-! A finite gamma-tail polynomial gives an integral bound after the radial substitution. -/
namespace BstLean.Part212
open MeasureTheory Real Filter Topology Set
open scoped ENNReal

noncomputable def gammaTail (k : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), y ^ i / (i.factorial : ℝ)

lemma gammaTail_succ (k : ℕ) (y : ℝ) :
    gammaTail (k + 1) y = gammaTail k y + y ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  exact Finset.sum_range_succ _ _

lemma gammaTail_zero (k : ℕ) : gammaTail k 0 = 1 := by
  induction k with
  | zero => simp [gammaTail]
  | succ k ih => rw [gammaTail_succ, ih, zero_pow (by omega), zero_div, add_zero]

lemma gammaTail_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ gammaTail k y :=
  Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hy _) (Nat.cast_nonneg _)

theorem gammaTail_derivative (k : ℕ) (y : ℝ) :
    HasDerivAt (gammaTail k) (gammaTail k y - y ^ k / (k.factorial : ℝ)) y := by
  induction k with
  | zero =>
    have he : gammaTail 0 = fun _ : ℝ => 1 := by funext x; simp [gammaTail]
    rw [he]
    simpa using hasDerivAt_const y (1 : ℝ)
  | succ k ih =>
    have he : gammaTail (k + 1) = fun x =>
        gammaTail k x + x ^ (k + 1) / ((k + 1).factorial : ℝ) :=
      funext (gammaTail_succ k)
    rw [he]
    have h := ih.add (((hasDerivAt_id y).pow (k + 1)).div_const ((k + 1).factorial : ℝ))
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel, he, id_eq, mul_one]
    have hfac : (↑(k + 1) : ℝ) * y ^ k / ((k + 1).factorial : ℝ) =
        y ^ k / (k.factorial : ℝ) := by
      have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
      have hf0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp
    rw [hfac]
    ring

noncomputable def gammaPrimitive (k : ℕ) (B v : ℝ) : ℝ :=
  -(k.factorial : ℝ) / B ^ (k + 1) * (exp (-B * v) * gammaTail k (B * v))

theorem gammaPrimitive_derivative (k : ℕ) {B : ℝ} (hB : 0 < B) (v : ℝ) :
    HasDerivAt (gammaPrimitive k B) (v ^ k * exp (-B * v)) v := by
  have hV : HasDerivAt (fun x : ℝ => B * x) B v := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id v).const_mul B
  have hP := (gammaTail_derivative k (B * v)).comp v hV
  have hE : HasDerivAt (fun x : ℝ => exp (-B * x)) (-B * exp (-B * v)) v := by
    have hV' : HasDerivAt (fun x : ℝ => -B * x) (-B) v := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id v).const_mul (-B)
    convert hV'.exp using 1 <;> ring
  have h := (hE.mul hP).const_mul (-(k.factorial : ℝ) / B ^ (k + 1))
  unfold gammaPrimitive
  refine h.congr_deriv ?_
  dsimp only [Function.comp_apply, Pi.mul_apply]
  have hf0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [mul_pow, pow_succ]
  field_simp
  ring

noncomputable def gammaMobius (t : ℝ) : ℝ := t / (1 + 2 * t)

theorem gammaMobius_derivative {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt gammaMobius (1 / (1 + 2 * t) ^ 2) t := by
  have hA : 1 + 2 * t ≠ 0 := ne_of_gt (by positivity)
  have h := (hasDerivAt_id t).div (((hasDerivAt_id t).const_mul 2).const_add 1) hA
  exact h.congr_deriv (by simp only [id_eq, mul_one]; field_simp; ring)

theorem gammaMobius_tendsto : Tendsto gammaMobius atTop (𝓝 (1 / 2)) := by
  have hA : Tendsto (fun t : ℝ => 1 + 2 * t) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hi := tendsto_inv_atTop_zero.comp hA
  have hl : Tendsto (fun t : ℝ => 1 / 2 - (1 / 2) * (1 + 2 * t)⁻¹) atTop (𝓝 (1 / 2)) := by
    simpa only [Function.comp_apply, mul_zero, sub_zero] using
      tendsto_const_nhds.sub (hi.const_mul (1 / 2))
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hA0 : 1 + 2 * t ≠ 0 := ne_of_gt (by positivity)
  unfold gammaMobius
  field_simp
  ring

theorem mobius_gamma_bound (k : ℕ) {B : ℝ} (hB : 0 < B) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (gammaMobius t ^ k * exp (-B * gammaMobius t) / (1 + 2 * t) ^ 2) ≤
      ENNReal.ofReal ((k.factorial : ℝ) / B ^ (k + 1)) := by
  let F := fun t => gammaPrimitive k B (gammaMobius t)
  let H := fun t => gammaMobius t ^ k * exp (-B * gammaMobius t) / (1 + 2 * t) ^ 2
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F (H t) t := by
    intro t ht
    have h := (gammaPrimitive_derivative k hB (gammaMobius t)).comp t
      (gammaMobius_derivative ht)
    exact h.congr_deriv (by dsimp [H]; ring)
  have h0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ H t := by
    intro t ht
    have ht0 : 0 < t := ht
    exact div_nonneg (mul_nonneg (pow_nonneg
      (div_nonneg ht.le (by linarith : (0 : ℝ) ≤ 1 + 2 * t)) _) (exp_pos _).le)
      (sq_nonneg _)
  have hc : Continuous (gammaPrimitive k B) := by unfold gammaPrimitive gammaTail; fun_prop
  have hl : Tendsto F atTop (𝓝 (gammaPrimitive k B (1 / 2))) :=
    (hc.tendsto _).comp gammaMobius_tendsto
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd h0 hl
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd h0 hl
  have hlim : gammaPrimitive k B (1 / 2) ≤ 0 := by
    unfold gammaPrimitive
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg _)) (pow_nonneg hB.le _))
      (mul_nonneg (exp_pos _).le (gammaTail_nonneg k (by positivity)))
  have hstart : F 0 = -(k.factorial : ℝ) / B ^ (k + 1) := by
    simp [F, gammaPrimitive, gammaMobius, gammaTail_zero]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ h0)), he]
  apply ENNReal.ofReal_le_ofReal
  rw [hstart, neg_div]
  linarith
end BstLean.Part212
