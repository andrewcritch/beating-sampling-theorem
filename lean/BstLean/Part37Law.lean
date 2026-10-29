import BstLean.Part37Defs

/-!
# Part 37, wave 1: elementary bounds on `q_θ`, on `T_K` and on `exp`

Paper: Lemma `frob` (density in `[ρ⁻¹, ρ]`) and the remark on the disprover's moment route. Specification
§3. Real analysis only. `T_3(−1/4) = 299/384`. Useful Mathlib facts: `Real.exp_bound`,
`Real.add_one_le_exp`, `Real.exp_one_lt_d9`, `Real.sum_le_exp_of_nonneg`-type lemmas.

Provers: replace each `sorry` by a proof. Do not edit `Part37Defs.lean` or any statement in this file,
and do not use `native_decide` anywhere.
-/

namespace BstLean.Part37

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss qformι funF frobSq CoefIdx cOf LOf aOf Bof varOf unitOf qformC
  uniformSphere kappa eta)
open BstLean.Part33 (SphereProd floorY4 rawQ Dc)

variable {n : ℕ}

/-- On the unit sphere, `|q_θ| ≤ 1/4` over the ball. -/
theorem qth_abs_le (θ : Fin n → ℝ) (hθ : InBall θ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    |qth θ x| ≤ 1 / 4 := by
  calc
    |qth θ x| ≤ ∑ i, |θ i * x i ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (1 / 4 : ℝ) * x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]
      exact mul_le_mul_of_nonneg_right (hθ i) (sq_nonneg _)
    _ = 1 / 4 := by rw [← Finset.mul_sum, hx]; ring

/-- For `K ≥ 3` and `|s| ≤ 1/4`: `T_K(s) ≥ T_3(−1/4) = 299/384`. -/
theorem taylor_lower (K : ℕ) (hK : 3 ≤ K) (s : ℝ) (hs : |s| ≤ 1 / 4) : 299 / 384 ≤ taylorExp K s := by
  have hlo := (abs_le.mp hs).1
  have hbase : (299 / 384 : ℝ) ≤ taylorExp 3 s := by
    simp [taylorExp, Finset.sum_range_succ]
    nlinarith [sq_nonneg (s + 1 / 4), mul_nonneg (show 0 ≤ s + 1 / 4 by linarith)
      (sq_nonneg (s + 1 / 4))]
  have hsucc (k : ℕ) : taylorExp (k + 1) s = taylorExp k s + s ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    simp [taylorExp, Finset.sum_range_succ]
  have hpair (k : ℕ) (hk : Even k) :
      0 ≤ s ^ k / (k.factorial : ℝ) + s ^ (k + 1) / ((k + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hf : (0 : ℝ) < k.factorial := by positivity
    have hp := hk.pow_nonneg s
    have hc : 0 ≤ (k : ℝ) + 1 + s := by
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    apply (div_nonneg (mul_nonneg hp hc) (show 0 ≤ ((k : ℝ) + 1) * k.factorial by positivity)).trans_eq
    field_simp
  induction K using Nat.strong_induction_on with
  | h K ih =>
    by_cases he : Even K
    · obtain ⟨j, rfl⟩ := he
      have hi := ih (j + j - 1) (by omega) (by omega)
      have heq : j + j = (j + j - 1) + 1 := by omega
      rw [heq, hsucc]
      have hp : 0 ≤ s ^ (j + j) := (show Even (j + j) from ⟨j, rfl⟩).pow_nonneg s
      rw [← heq]
      exact le_trans hi (le_add_of_nonneg_right (div_nonneg hp (by positivity)))
    · by_cases h3 : K = 3
      · simpa [h3] using hbase
      have hmod : K % 2 ≠ 0 := by simpa [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] using he
      have hk : 3 ≤ K - 2 := by omega
      have hi := ih (K - 2) (by omega) hk
      have heven : Even (K - 1) := by
        rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
        omega
      have hp := hpair (K - 1) heven
      have e1 : K = (K - 1) + 1 := by omega
      have e2 : K - 1 = (K - 2) + 1 := by omega
      have eq : taylorExp K s = taylorExp (K - 2) s +
          (s ^ (K - 1) / ((K - 1).factorial : ℝ) + s ^ ((K - 1) + 1) / (((K - 1) + 1).factorial : ℝ)) := by
        conv_lhs => rw [e1, hsucc]
        rw [e2, hsucc]
        simp only [← e2]
        ring
      rw [eq]
      linarith

/-- For every `K` and `|s| ≤ 1/4`: `T_K(s) ≤ e^{1/4}`. -/
theorem taylor_upper (K : ℕ) (s : ℝ) (hs : |s| ≤ 1 / 4) : taylorExp K s ≤ Real.exp (1 / 4) := by
  calc
    taylorExp K s ≤ taylorExp K (1 / 4) := by
      apply Finset.sum_le_sum
      intro k _
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (le_abs_self (s ^ k)).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg s) hs k)
    _ ≤ Real.exp (1 / 4) := Real.sum_le_exp_of_nonneg (by norm_num) _

/-- For every `K` and `|s| ≤ 1/4`: `T_K(s) > 0`. -/
theorem taylor_pos (K : ℕ) (s : ℝ) (hs : |s| ≤ 1 / 4) : 0 < taylorExp K s := by
  by_cases hK : 3 ≤ K
  · exact lt_of_lt_of_le (by norm_num) (taylor_lower K hK s hs)
  have hlo := (abs_le.mp hs).1
  have hhi := (abs_le.mp hs).2
  interval_cases K <;> norm_num [taylorExp, Finset.sum_range_succ] <;> nlinarith [sq_nonneg s]

/-- `e^{1/4} ≤ ρ' · T_3(−1/4)`, so the density of `D_K` (`K ≥ 3`) lies in `[1/ρ', ρ']`. -/
theorem exp_quarter_le : Real.exp (1 / 4) ≤ (33 / 20) * (299 / 384) := by
  have h := Real.exp_bound' (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- `ρ = e^{1/2} ≤ ρ' = 33/20`. -/
theorem exp_half_le : Real.exp (1 / 2) ≤ 33 / 20 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- `Z_K > 0` over the ball. -/
theorem ZK_pos (hn : 1 ≤ n) (θ : Fin n → ℝ) (hθ : InBall θ) (K : ℕ) : 0 < ZK n K θ := by
  let := BstLean.Part29.uniformSphere_isProbability n hn
  have hp : ∀ᵐ x ∂uniformSphere n, 0 < taylorExp K (qth θ x) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    exact taylor_pos K _ (qth_abs_le θ hθ x hx)
  have hi : Integrable (fun x => taylorExp K (qth θ x)) (uniformSphere n) := by
    apply Integrable.of_bound (C := Real.exp (1 / 4))
    · exact (by unfold taylorExp qth; fun_prop : Continuous (fun x => taylorExp K (qth θ x))).aestronglyMeasurable
    · filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n, hp] with x hx hpx
      rw [Real.norm_eq_abs, abs_of_pos hpx]
      exact taylor_upper K _ (qth_abs_le θ hθ x hx)
  apply (integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h => h.le) hi).mpr
  have he : Function.support (fun x => taylorExp K (qth θ x)) =ᵐ[uniformSphere n] Set.univ := by
    filter_upwards [hp] with x hx
    simp [Function.mem_support, ne_of_gt hx]
  rw [measure_congr he]
  simp

/-- `Z_θ > 0`. -/
theorem Zth_pos (hn : 1 ≤ n) (θ : Fin n → ℝ) : 0 < Zth n θ := by
  let := BstLean.Part29.uniformSphere_isProbability n hn
  apply integral_exp_pos
  apply Integrable.of_bound (C := Real.exp (∑ i, |θ i|))
  · exact (by unfold qth; fun_prop : Continuous (fun x => Real.exp (qth θ x))).aestronglyMeasurable
  · filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (le_abs_self (θ i)) (sq_nonneg (x i)))
    apply Finset.sum_le_sum
    intro i _
    have hi : x i ^ 2 ≤ 1 := by
      rw [← hx]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    simpa using mul_le_mul_of_nonneg_left hi (abs_nonneg (θ i))

end BstLean.Part37
