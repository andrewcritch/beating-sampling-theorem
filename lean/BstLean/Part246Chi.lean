import BstLean.Part246Gamma
import BstLean.Part244Smin
import BstLean.Part221RadialDensity

/-! Part 246: the Gaussian norm mean `a_n = E|g_n| = √2 Γ((n+1)/2)/Γ(n/2)`, the recursion
`a_n a_{n+1} = n`, and the monotonicity `a_N - a_d ≥ √N - √d` (`√n - a_n` is nonincreasing). -/
namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part244 (gaussNormMean)

/-- **The Gaussian norm mean in closed form.** -/
theorem gaussNormMean_eq {n : ℕ} (hn : 1 ≤ n) : gaussNormMean n = √2 * phiG ((n : ℝ) / 2) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h := BstLean.Part53.RemezAux.gaussian_radius_integral (Fin n) (fun r => r)
  simp only [Fintype.card_fin] at h
  have hK := BstLean.Part221.gaussianRadialFactor_gamma hn
  have hI : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * exp (-r ^ 2 / 2) * r =
      (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) * (1 / 2) * Gamma (((n : ℝ) + 1) / 2) := by
    have e : ∀ r ∈ Ioi (0 : ℝ), r ^ (n - 1) * exp (-r ^ 2 / 2) * r =
        r ^ (n : ℝ) * exp (-(1 / 2) * r ^ (2 : ℝ)) := by
      intro r hr
      have h1 : r ^ (n - 1) * r = r ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.rpow_natCast,
        ← h1]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi e,
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
        (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 < (n : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2)]
  unfold gaussNormMean
  change ∫ Z, √(∑ i, Z i ^ 2) ∂stdGauss (Fin n) = _
  rw [h, hI, hK]
  unfold phiG
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have g1 := Gamma_pos_of_pos (show 0 < (n : ℝ) / 2 by positivity)
  have e1 : ((n : ℝ) + 1) / 2 = (n : ℝ) / 2 + 1 / 2 := by ring
  rw [e1]
  have e2 : (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) = (1 / 2 : ℝ) ^ (-(n : ℝ) / 2) * √2 := by
    rw [show -((n : ℝ) + 1) / 2 = -(n : ℝ) / 2 + (-(1 / 2)) by ring,
      Real.rpow_add (by norm_num)]
    congr 1
    rw [Real.rpow_neg (by norm_num), Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
      ← Real.sqrt_eq_rpow, one_div, inv_inv]
  rw [e2]
  have hp : 0 < (1 / 2 : ℝ) ^ (-(n : ℝ) / 2) := by positivity
  field_simp

lemma gaussNormMean_pos {n : ℕ} (hn : 1 ≤ n) : 0 < gaussNormMean n := by
  rw [gaussNormMean_eq hn]
  exact mul_pos (by positivity) (phiG_pos (by positivity))

/-- `a_n a_{n+1} = n`. -/
theorem gaussNormMean_mul {n : ℕ} (hn : 1 ≤ n) :
    gaussNormMean n * gaussNormMean (n + 1) = n := by
  rw [gaussNormMean_eq hn, gaussNormMean_eq (by omega)]
  have h := phiG_mul (show 0 < (n : ℝ) / 2 by positivity)
  have e : ((n + 1 : ℕ) : ℝ) / 2 = (n : ℝ) / 2 + 1 / 2 := by push_cast; ring
  rw [e]
  have h2 : √2 * phiG ((n : ℝ) / 2) * (√2 * phiG ((n : ℝ) / 2 + 1 / 2)) =
      2 * (phiG ((n : ℝ) / 2) * phiG ((n : ℝ) / 2 + 1 / 2)) := by
    rw [show √2 * phiG ((n : ℝ) / 2) * (√2 * phiG ((n : ℝ) / 2 + 1 / 2)) =
      (√2 * √2) * (phiG ((n : ℝ) / 2) * phiG ((n : ℝ) / 2 + 1 / 2)) by ring,
      Real.mul_self_sqrt (by norm_num)]
  rw [h2, h]; ring

/-- `a_n² ≤ n - 1/2 + 1/(8n) + 1/(8n²)`. -/
theorem gaussNormMean_sq_le {n : ℕ} (hn : 1 ≤ n) :
    gaussNormMean n ^ 2 ≤ (n : ℝ) - 1 / 2 + 1 / (8 * n) + 1 / (8 * n ^ 2) := by
  rw [gaussNormMean_eq hn, mul_pow, Real.sq_sqrt (by norm_num)]
  have h := phiG_sq_le_Uf (show 0 < (n : ℝ) / 2 by positivity)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e : 2 * Uf ((n : ℝ) / 2) = (n : ℝ) - 1 / 2 + 1 / (8 * n) + 1 / (8 * n ^ 2) := by
    unfold Uf; field_simp; ring
  linarith

/-- **The step** `a_{n+1} - a_n ≥ √(n+1) - √n` for `n ≥ 2`. -/
theorem gaussNormMean_step {n : ℕ} (hn : 2 ≤ n) :
    √((n : ℝ) + 1) - √(n : ℝ) ≤ gaussNormMean (n + 1) - gaussNormMean n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set a := gaussNormMean n with had
  have ha : 0 < a := gaussNormMean_pos hn1
  have hrec : gaussNormMean (n + 1) = n / a := by
    rw [eq_div_iff ha.ne', mul_comm]; exact gaussNormMean_mul hn1
  rw [hrec]
  set A2 := (n : ℝ) - 1 / 2 + 1 / (8 * n) + 1 / (8 * n ^ 2) with hA2
  have hsq : a ^ 2 ≤ A2 := gaussNormMean_sq_le hn1
  set D := (n : ℝ) - A2 with hD
  have hD0 : 0 < D := by
    rw [hD, hA2]
    have : 1 / (8 * (n : ℝ)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have : 1 / (8 * (n : ℝ) ^ 2) ≤ 1 / 32 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hA0 : 0 < A2 := by nlinarith [sq_nonneg a]
  set s := √(n : ℝ) with hs
  set t := √((n : ℝ) + 1) with ht
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by linarith)
  -- `t s ≥ n + 1/2 - 1/(8n)`
  have hts : (n : ℝ) + 1 / 2 - 1 / (8 * n) ≤ t * s := by
    have hl0 : 0 ≤ (n : ℝ) + 1 / 2 - 1 / (8 * n) := by
      have : 1 / (8 * (n : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      linarith
    have hsq' : ((n : ℝ) + 1 / 2 - 1 / (8 * n)) ^ 2 ≤ (t * s) ^ 2 := by
      rw [mul_pow, ht2, hs2]
      have e : ((n : ℝ) + 1 / 2 - 1 / (8 * n)) ^ 2 = n ^ 2 + n - 1 / (8 * n) + 1 / (64 * n ^ 2) := by
        field_simp; ring
      rw [e]
      have : 1 / (64 * (n : ℝ) ^ 2) ≤ 1 / (8 * n) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      nlinarith
    exact (pow_le_pow_iff_left₀ hl0 (by positivity) two_ne_zero).1 hsq'
  -- the polynomial inequality `D² (4n + 2 - 1/(4n)) ≥ A2`
  have hpoly : A2 ≤ D ^ 2 * (4 * n + 2 - 1 / (4 * n)) := by
    rw [hD, hA2]
    rw [← sub_nonneg]
    have e : ((n : ℝ) - ((n : ℝ) - 1 / 2 + 1 / (8 * n) + 1 / (8 * n ^ 2))) ^ 2 *
        (4 * n + 2 - 1 / (4 * n)) - ((n : ℝ) - 1 / 2 + 1 / (8 * n) + 1 / (8 * n ^ 2)) =
        (128 * n ^ 5 - 224 * n ^ 4 - 48 * n ^ 3 + 39 * n ^ 2 + 6 * n - 1) / (256 * n ^ 5) := by
      field_simp; ring
    rw [e]
    apply div_nonneg _ (by positivity)
    set m := (n : ℝ) - 2 with hm
    have hm0 : 0 ≤ m := by linarith
    have e2 : 128 * (n : ℝ) ^ 5 - 224 * n ^ 4 - 48 * n ^ 3 + 39 * n ^ 2 + 6 * n - 1 =
        128 * m ^ 5 + 1056 * m ^ 4 + 3280 * m ^ 3 + 4615 * m ^ 2 + 2658 * m + 295 := by
      rw [hm]; ring
    rw [e2]; positivity
  -- `D (t + s) ≥ √A2`
  have hmain : √A2 ≤ D * (t + s) := by
    have hsq2 : (√A2) ^ 2 ≤ (D * (t + s)) ^ 2 := by
      rw [Real.sq_sqrt hA0.le, mul_pow]
      have e : (t + s) ^ 2 = 2 * n + 1 + 2 * (t * s) := by nlinarith
      rw [e]
      have h4 : 4 * (n : ℝ) + 2 - 1 / (4 * n) ≤ 2 * n + 1 + 2 * (t * s) := by
        have : 2 * (1 / (8 * (n : ℝ))) = 1 / (4 * n) := by field_simp; ring
        linarith
      have := mul_le_mul_of_nonneg_left h4 (sq_nonneg D)
      linarith
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 hsq2
  -- conclude
  have hta : t - s = 1 / (t + s) := by
    rw [eq_div_iff (by positivity)]; nlinarith
  have haA : a ≤ √A2 := Real.le_sqrt_of_sq_le hsq
  rw [hta]
  have hlhs : (n : ℝ) / a - a = (n - a ^ 2) / a := by field_simp
  rw [hlhs, div_le_div_iff₀ (by positivity) ha]
  have h1 : D ≤ n - a ^ 2 := by rw [hD]; linarith
  calc 1 * a ≤ √A2 := by linarith
    _ ≤ D * (t + s) := hmain
    _ ≤ (n - a ^ 2) * (t + s) := mul_le_mul_of_nonneg_right h1 (by positivity)

lemma gaussNormMean_one : gaussNormMean 1 = √2 / √π := by
  rw [gaussNormMean_eq le_rfl]
  unfold phiG
  norm_num [Real.Gamma_one, Real.Gamma_one_half_eq]
  ring

lemma gaussNormMean_two : gaussNormMean 2 = √2 * √π / 2 := by
  rw [gaussNormMean_eq (by norm_num)]
  unfold phiG
  have e : ((2 : ℕ) : ℝ) / 2 + 1 / 2 = 1 / 2 + 1 := by norm_num
  rw [e, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  norm_num
  ring

/-- The first step `a_2 - a_1 ≥ √2 - 1`. -/
lemma gaussNormMean_step_one : √(2 : ℝ) - 1 ≤ gaussNormMean 2 - gaussNormMean 1 := by
  rw [gaussNormMean_one, gaussNormMean_two]
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hsp : (177 / 100 : ℝ) ≤ √π := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsp2 : √π ≤ 178 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hs2 : √(2 : ℝ) ≤ 1415 / 1000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs2' : (1414 / 1000 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hspp : 0 < √π := by linarith
  have hinv : (√π)⁻¹ ≤ 100 / 177 := by
    rw [inv_le_comm₀ hspp (by norm_num)]; linarith
  have h1 : √2 / √π = √2 * (√π)⁻¹ := div_eq_mul_inv _ _
  rw [h1]
  have hs0 : (0 : ℝ) ≤ √2 := by linarith
  have a1 := mul_le_mul_of_nonneg_left hinv hs0
  have a2 := mul_le_mul_of_nonneg_left hsp hs0
  nlinarith

/-- **Monotonicity of `√n - a_n`**: `a_N - a_d ≥ √N - √d` for `1 ≤ d ≤ N`. -/
theorem gaussNormMean_mono {d N : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    √(N : ℝ) - √(d : ℝ) ≤ gaussNormMean N - gaussNormMean d := by
  induction N, hdN using Nat.le_induction with
  | base => simp
  | succ k hdk ih =>
    have hstep : √((k : ℝ) + 1) - √(k : ℝ) ≤ gaussNormMean (k + 1) - gaussNormMean k := by
      rcases Nat.lt_or_ge k 2 with hk | hk
      · have hk1 : k = 1 := by omega
        subst hk1
        have := gaussNormMean_step_one
        norm_num at this ⊢
        exact this
      · exact gaussNormMean_step hk
    push_cast
    linarith

end BstLean.Part246
