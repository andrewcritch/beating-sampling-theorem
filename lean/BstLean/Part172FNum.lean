import BstLean.Part171All

/-!
# Part 172 (file `FNum`): the numerical frame constant

No proof is left open; no `native_decide` or `axiom` is used.

* `fr_two_rpow`: `2^{1/512} ≤ 736/735` (nine squarings with rational bounds).
* `fr_rpow_m`: `m^{1/(64q)} ≤ 1.0235` for `q = ⌊log₂ n⌋`, `n ≥ 80 000`.
* `fr_X`, `fr_X_pow`: the frame constant `X = ((d+128)/(d−1))·m^{1/(64q)}·(d+128q)·γ·B`.
* **`fr_X_num`**: `X ≤ 4.25/n²` for `B = t_A`, every `n ≥ 80 000`.
-/

namespace BstLean.Part172
open Real BstLean.Part130 BstLean.Part168

variable {n : ℕ}

lemma fr_sq_step {a x b : ℝ} (ha : 0 ≤ a) (hx : a ≤ x) (hb : b ≤ a ^ 2) : b ≤ x ^ 2 :=
  hb.trans (pow_le_pow_left₀ ha hx 2)

lemma fr_pow512 : (2 : ℝ) ≤ (736 / 735) ^ (512 : ℕ) := by
  have e : ((736 : ℝ) / 735) ^ (512 : ℕ) =
      ((((((((((736 : ℝ) / 735) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  rw [e]
  have h1 : (1002722939 / 1000000000 : ℝ) ≤ ((736 : ℝ) / 735) ^ 2 := by norm_num
  have h2 := fr_sq_step (by norm_num) h1 (show (251363323 / 250000000 : ℝ) ≤ _ by norm_num)
  have h3 := fr_sq_step (by norm_num) h2 (show (505468161 / 500000000 : ℝ) ≤ _ by norm_num)
  have h4 := fr_sq_step (by norm_num) h3 (show (1021992247 / 1000000000 : ℝ) ≤ _ by norm_num)
  have h5 := fr_sq_step (by norm_num) h4 (show (130558519 / 125000000 : ℝ) ≤ _ by norm_num)
  have h6 := fr_sq_step (by norm_num) h5 (show (27272843 / 25000000 : ℝ) ≤ _ by norm_num)
  have h7 := fr_sq_step (by norm_num) h6 (show (148761593 / 125000000 : ℝ) ≤ _ by norm_num)
  have h8 := fr_sq_step (by norm_num) h7 (show (1416320739 / 1000000000 : ℝ) ≤ _ by norm_num)
  have h9 := fr_sq_step (by norm_num) h8 (show (401192887 / 200000000 : ℝ) ≤ _ by norm_num)
  exact le_trans (by norm_num) h9

lemma fr_two_rpow : (2 : ℝ) ^ ((1 : ℝ) / 512) ≤ 736 / 735 := by
  have h := Real.rpow_le_rpow (by norm_num) fr_pow512 (by norm_num : (0 : ℝ) ≤ 1 / 512)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
  have e : ((512 : ℕ) : ℝ) * (1 / 512) = 1 := by norm_num
  rw [e, Real.rpow_one] at h
  exact h

/-- `m^{1/(64q)} ≤ 1.0235` for `q = ⌊log₂ n⌋`. -/
lemma fr_rpow_m (hn : 80000 ≤ n) :
    ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) ≤ 10235 / 10000 := by
  set q := qn n with hq
  have hq16 : (16 : ℝ) ≤ q := by exact_mod_cast q_ge hn
  have hq0 : (0 : ℝ) < q := by linarith
  have hm : ((mA n : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((2 * q + 2 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have h := lt_pow_q n
    have h2 : mA n ≤ 2 ^ (2 * q + 2) := by
      unfold mA
      rw [show 2 * q + 2 = (q + 1) * 2 by ring, pow_mul]
      exact Nat.pow_le_pow_left h.le 2
    exact_mod_cast h2
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hm
    (by positivity : (0 : ℝ) ≤ 1 / (64 * (q : ℝ)))
  rw [← Real.rpow_mul (by norm_num)] at h1
  refine h1.trans ?_
  have hexp : ((2 * q + 2 : ℕ) : ℝ) * (1 / (64 * (q : ℝ))) ≤ 17 * (1 / 512) := by
    push_cast
    rw [show (2 * (q : ℝ) + 2) * (1 / (64 * (q : ℝ))) = (2 * q + 2) / (64 * q) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans ?_
  rw [mul_comm, Real.rpow_mul (by norm_num)]
  have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 512)) ^ (17 : ℝ) ≤ (736 / 735 : ℝ) ^ (17 : ℝ) :=
    Real.rpow_le_rpow (by positivity) fr_two_rpow (by norm_num)
  refine h3.trans ?_
  rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The frame constant `X = ((d+128)/(d−1))·m^{1/(64q)}·(d+128q)·γ·B`. -/
noncomputable def fr_X (n q : ℕ) (B : ℝ) : ℝ :=
  (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) *
    ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * q))) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q)) *
    (2 / (n : ℝ) * B)

lemma fr_alg (a b R M e B : ℝ) (hr : R ^ 64 = M) :
    a ^ 64 / b ^ 64 * B ^ 64 * (M * e ^ 64) = (a / b * (R * e) * B) ^ 64 := by
  rw [← hr]; ring

lemma fr_X_pow {q : ℕ} (hq : 1 ≤ q) (B : ℝ) :
    (((n - 1 - 1 : ℕ) : ℝ) + 128) ^ 64 / (((n - 1 - 1 : ℕ) : ℝ) - 1) ^ 64 *
      (2 / (n : ℝ) * B) ^ 64 *
      ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) ^ 64)) =
      fr_X n q B ^ 64 := by
  have hm0 : (0 : ℝ) ≤ ((mA n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : (((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * q))) ^ (64 : ℕ) =
      ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    congr 1
    push_cast
    field_simp
  unfold fr_X
  exact fr_alg _ _ _ _ _ _ hr

/-- **`X ≤ 4.25/n²`** for `q = ⌊log₂ n⌋`, `B = t_A`, every `n ≥ 80 000`. -/
theorem fr_X_num (hn : 80000 ≤ n) :
    fr_X n (qn n) (2 / ((mA n : ℕ) : ℝ)) ≤ 425 / 100 / (n : ℝ) ^ 2 := by
  set q := qn n with hq
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [show n - 1 - 1 = n - 2 by omega]; push_cast [show 2 ≤ n by omega]; ring
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hqn : (4096 : ℝ) * q ≤ n := by exact_mod_cast q_lin hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hR := fr_rpow_m hn
  have hR0 : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) := Real.rpow_nonneg (by positivity) _
  have f1 : (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤ 10017 / 10000 := by
    rw [hd, div_le_iff₀ (by linarith)]; linarith
  have f1' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) := by
    rw [hd]; apply div_nonneg <;> linarith
  have f3 : (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) ≤ 2 * (33 / 32) := by
    rw [hd, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have f3' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) := by
    rw [hd]; apply mul_nonneg <;> [nlinarith; positivity]
  have e : fr_X n q (2 / ((mA n : ℕ) : ℝ)) =
      ((((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) *
      ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) *
      ((((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ))) * (2 / (n : ℝ) ^ 2) := by
    unfold fr_X; rw [hmR]; ring
  rw [e]
  have hn2 : (0 : ℝ) < 2 / (n : ℝ) ^ 2 := by positivity
  have h := mul_le_mul (mul_le_mul (mul_le_mul f1 hR hR0 (by norm_num)) f3 f3' (by norm_num))
    (le_refl (2 / (n : ℝ) ^ 2)) hn2.le (by norm_num)
  refine h.trans (le_of_eq_of_le rfl ?_)
  rw [show 425 / 100 / (n : ℝ) ^ 2 = 425 / 200 * (2 / (n : ℝ) ^ 2) by ring]
  exact mul_le_mul_of_nonneg_right (by norm_num) hn2.le

end BstLean.Part172
