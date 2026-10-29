import BstLean.Part167All

/-!
# Part 168 (file `Num`): the numerics `K2XY ≤ 4.7` (sub-lemma 7 of Lemma LJ)

No proof is left open; no `native_decide` or `axiom` is used.

Take `q = qn n = ⌊log₂ n⌋` in `max_mom`, so `q ≥ 16` and `4096 q ≤ 2^q ≤ n` for `n ≥ 80 000`.

* `rpow_m_le`: `m^{1/(64q)} ≤ (513/512)^{17} ≤ 1.034` (`m = n² ≤ 2^{2q+2}`, Bernoulli for `2^{1/512}`).
* **`X2_num`**: `X2q n (qn n) ≤ 2.2`.
* **`Y_num'`**: `t_A·Y2n ≤ 2.002`.
* **`Z_num`**: `Cg·√t_A·Zop n ≤ 0.1` (`Cg ≤ 11.1` from `127!! ≤ 7^{128}`).
* **`K2_num`**: `K2XY n (X2q n (qn n)) (Y2n n) ≤ 4.7` for every `n ≥ 80 000`.
-/

namespace BstLean.Part168

open Real
open BstLean.Part130
open BstLean.Part167

variable {n : ℕ}

/-- `X2` for a given `q`: `((d+128)/(d−1))·m^{1/(64q)}(d+128q)·γ_A·t_A·BL(m)`, `d = n − 2`,
`m = n²` (the paper's `X_ℓ²` in Lean's route). -/
noncomputable def X2q (n q : ℕ) : ℝ :=
  (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) *
    ((((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * q))) * (((n - 1 - 1 : ℕ) : ℝ) + 128 * q)) *
    (2 / (n : ℝ)) * (2 / ((mA n : ℕ) : ℝ)) * BL (mA n)

/-- The order parameter of `max_mom`: `q = ⌊log₂ n⌋`. -/
def qn (n : ℕ) : ℕ := Nat.log 2 n

lemma pow_q_le (hn : 1 ≤ n) : 2 ^ qn n ≤ n := Nat.pow_log_le_self 2 (by omega)

lemma lt_pow_q (n : ℕ) : n < 2 ^ (qn n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n

lemma q_ge (hn : 80000 ≤ n) : 16 ≤ qn n := by
  unfold qn
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

lemma lin_le_pow (k : ℕ) : 4096 * (16 + k) ≤ 2 ^ (16 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 16 + (k + 1) = (16 + k) + 1 by omega, pow_succ]
    omega

lemma q_lin (hn : 80000 ≤ n) : 4096 * qn n ≤ n := by
  obtain ⟨k, hk⟩ : ∃ k, qn n = 16 + k := ⟨qn n - 16, by have := q_ge hn; omega⟩
  have h1 := lin_le_pow k
  have h2 := pow_q_le (n := n) (by omega)
  rw [hk] at h2 ⊢
  omega

/-- `2^{1/512} ≤ 513/512` (Bernoulli). -/
lemma two_rpow_512 : (2 : ℝ) ^ ((1 : ℝ) / 512) ≤ 513 / 512 := by
  have hb : (2 : ℝ) ≤ (513 / 512) ^ (512 : ℕ) := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / 512 by norm_num) 512
    have e : (1 : ℝ) + ((512 : ℕ) : ℝ) * (1 / 512) = 2 := by norm_num
    have e2 : (1 : ℝ) + 1 / 512 = 513 / 512 := by norm_num
    rw [e, e2] at this
    exact this
  have h := Real.rpow_le_rpow (by norm_num) hb (by norm_num : (0 : ℝ) ≤ 1 / 512)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
  norm_num at h
  exact h

/-- `2^{1/64} ≤ 65/64` (Bernoulli). -/
lemma two_rpow_64 : (2 : ℝ) ^ ((1 : ℝ) / 64) ≤ 65 / 64 := by
  have hb : (2 : ℝ) ≤ (65 / 64) ^ (64 : ℕ) := by norm_num
  have h := Real.rpow_le_rpow (by norm_num) hb (by norm_num : (0 : ℝ) ≤ 1 / 64)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
  norm_num at h
  exact h

/-- **`m^{1/(64q)} ≤ 1.034`.** -/
lemma rpow_m_le (hn : 80000 ≤ n) :
    ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) ≤ 1034 / 1000 := by
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
  have h2 := two_rpow_512
  have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 512)) ^ (17 : ℝ) ≤ (513 / 512 : ℝ) ^ (17 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  refine h3.trans ?_
  rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- **`X2 ≤ 2.2`** for `q = ⌊log₂ n⌋`. -/
theorem X2_num (hn : 80000 ≤ n) : X2q n (qn n) ≤ 22 / 10 := by
  set q := qn n with hq
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [show n - 1 - 1 = n - 2 by omega]; push_cast [show 2 ≤ n by omega]; ring
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hqn : (4096 : ℝ) * q ≤ n := by exact_mod_cast q_lin hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hR := rpow_m_le hn
  have hR0 : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) := Real.rpow_nonneg (by positivity) _
  -- the four factors
  have f1 : (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) ≤ 1002 / 1000 := by
    rw [hd, div_le_iff₀ (by linarith)]; linarith
  have f1' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1) := by
    rw [hd]; apply div_nonneg <;> linarith
  have f3 : (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) ≤ 2 * (33 / 32) := by
    rw [hd, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have f3' : 0 ≤ (((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ)) := by
    rw [hd]; apply mul_nonneg <;> [nlinarith; positivity]
  have f4 : 2 / ((mA n : ℕ) : ℝ) * BL (mA n) ≤ 1016 / 1000 := by
    unfold BL
    rw [hmR]
    set N : ℝ := (n : ℝ) with hN
    have hN0 : 0 < N := by linarith
    have hsq : √(N ^ 2 / 2 + 128) ≤ N := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have h64 := two_rpow_64
    have h640 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 64) := by positivity
    have e : 2 / N ^ 2 * ((2 : ℝ) ^ ((1 : ℝ) / 64) * (N ^ 2 / 2 + 256) + 8 * √(N ^ 2 / 2 + 128)) =
        (2 : ℝ) ^ ((1 : ℝ) / 64) * (1 + 512 / N ^ 2) + 16 * √(N ^ 2 / 2 + 128) / N ^ 2 := by
      field_simp; ring
    rw [e]
    have hA : (2 : ℝ) ^ ((1 : ℝ) / 64) * (1 + 512 / N ^ 2) ≤ 65 / 64 * (1 + 512 / N ^ 2) :=
      mul_le_mul_of_nonneg_right h64 (by positivity)
    have hB : 512 / N ^ 2 ≤ 1 / 10000000 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hC : 16 * √(N ^ 2 / 2 + 128) / N ^ 2 ≤ 1 / 5000 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have f4' : 0 ≤ 2 / ((mA n : ℕ) : ℝ) * BL (mA n) := by
    unfold BL; positivity
  have e : X2q n q = ((((n - 1 - 1 : ℕ) : ℝ) + 128) / (((n - 1 - 1 : ℕ) : ℝ) - 1)) *
      ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (q : ℝ))) *
      ((((n - 1 - 1 : ℕ) : ℝ) + 128 * q) * (2 / (n : ℝ))) *
      (2 / ((mA n : ℕ) : ℝ) * BL (mA n)) := by
    unfold X2q; ring
  rw [e]
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul f1 hR hR0 (by norm_num)) f3 f3'
    (by norm_num)) f4 f4' (by norm_num)) (by norm_num)

/-- **`t_A·Y2n ≤ 2.002`.** -/
theorem Y_num' (hn : 2 ≤ n) : 2 / ((mA n : ℕ) : ℝ) * Y2n n ≤ 2002 / 1000 := by
  unfold Y2n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [show 1 ≤ n by omega]; ring
  rw [hmR, h1]
  have e : 2 / (n : ℝ) ^ 2 * (2 / (n : ℝ) * (1001 / 1000 * ((n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2))) =
      2002 / 1000 * (((n : ℝ) - 1) / n) := by
    field_simp; ring
  rw [e]
  have : ((n : ℝ) - 1) / n ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

/-- `127!! ≤ 7^{128}`, so `Cg ≤ 11.1`. -/
lemma Cg_le : Cg ≤ 111 / 10 := by
  unfold Cg
  have hg : BstLean.Part162.gmom 128 ≤ (7 : ℝ) ^ (128 : ℕ) := by
    rw [show (128 : ℕ) = 2 * 64 from rfl, BstLean.Part162.gmom_even]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num
  have h1 := Real.rpow_le_rpow (BstLean.Part162.gmom_nonneg 128) hg
    (by norm_num : (0 : ℝ) ≤ 1 / 128)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h1
  norm_num at h1
  have hpi := Real.pi_lt_d2
  have h0 : 0 ≤ BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) :=
    Real.rpow_nonneg (BstLean.Part162.gmom_nonneg 128) _
  have h7 : BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) ≤ 7 := by simpa using h1
  calc π / 2 * BstLean.Part162.gmom 128 ^ ((1 : ℝ) / 128) ≤ (315 / 100) / 2 * 7 :=
        mul_le_mul (by linarith) h7 h0 (by norm_num)
    _ ≤ 111 / 10 := by norm_num

/-- `gaussMomConst 64 ≤ 80`. -/
lemma G64_le : BstLean.Part152.gaussMomConst 64 ≤ 80 := by
  unfold BstLean.Part152.gaussMomConst
  have hb : (2 : ℝ) ^ 64 * ((Nat.factorial 64 : ℕ) : ℝ) ≤ (80 : ℝ) ^ (128 : ℕ) := by
    have : (2 : ℕ) ^ 64 * Nat.factorial 64 ≤ 80 ^ 128 := by
      norm_num [Nat.factorial]
    exact_mod_cast this
  have h1 := Real.rpow_le_rpow (by positivity) hb (by norm_num : (0 : ℝ) ≤ 1 / ((2 * 64 : ℕ) : ℝ))
  have e : ((80 : ℝ) ^ (128 : ℕ)) ^ (1 / ((2 * 64 : ℕ) : ℝ)) = 80 := by
    rw [show ((2 * 64 : ℕ) : ℝ) = ((128 : ℕ) : ℝ) by norm_num, one_div]
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  exact h1.trans (le_of_eq e)

/-- **`Cg·√t_A·Zop ≤ 0.1`.** -/
theorem Z_num (hn : 80000 ≤ n) : Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n ≤ 1 / 10 := by
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  unfold Zop
  rw [hmR, Real.sqrt_sq (by linarith)]
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 < N := by linarith
  set G := BstLean.Part152.gaussMomConst 64
  have hG := G64_le
  have hG0 : 0 ≤ G := BstLean.Part152.gaussMomConst_nonneg 64
  have hs : √N ≤ N / 100 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ √N := Real.sqrt_nonneg _
  have hC := Cg_le
  have hC0 := Cg_pos
  set T := Cg * √(2 / N ^ 2) * (√(2 / N) * (N + √N + G)) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hT2 : T ^ 2 = Cg ^ 2 * (2 / N ^ 2) * (2 / N) * (N + √N + G) ^ 2 := by
    rw [hT, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hS : N + √N + G ≤ 1011 / 1000 * N := by linarith
  have hS0 : 0 ≤ N + √N + G := by positivity
  have hb : T ^ 2 ≤ 1 / 100 := by
    rw [hT2]
    have h1 : Cg ^ 2 ≤ (111 / 10) ^ 2 := pow_le_pow_left₀ hC0.le hC 2
    have h2 : (N + √N + G) ^ 2 ≤ (1011 / 1000 * N) ^ 2 := pow_le_pow_left₀ hS0 hS 2
    have e : (111 / 10) ^ 2 * (2 / N ^ 2) * (2 / N) * (1011 / 1000 * N) ^ 2 =
        (111 / 10) ^ 2 * 4 * (1011 / 1000) ^ 2 / N := by
      field_simp; ring
    calc Cg ^ 2 * (2 / N ^ 2) * (2 / N) * (N + √N + G) ^ 2
        ≤ (111 / 10) ^ 2 * (2 / N ^ 2) * (2 / N) * (1011 / 1000 * N) ^ 2 := by gcongr
      _ = (111 / 10) ^ 2 * 4 * (1011 / 1000) ^ 2 / N := e
      _ ≤ 1 / 100 := by rw [div_le_iff₀ hN0]; nlinarith
  nlinarith

/-- **The numerics of Lemma LJ**: `K2XY n X2 Y2 ≤ 4.7` for every `n ≥ 80 000`, with
`X2 = X2q n ⌊log₂ n⌋` and `Y2 = Y2n n`. -/
theorem K2_num (hn : 80000 ≤ n) : K2XY n (X2q n (qn n)) (Y2n n) ≤ 47 / 10 := by
  unfold K2XY
  have hX := X2_num hn
  have hY := Y_num' (n := n) (by omega)
  have hZ := Z_num hn
  have hX0 : 0 ≤ X2q n (qn n) := by
    unfold X2q
    have hd : (2 : ℝ) ≤ ((n - 1 - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 - 1 by omega)
    have : 0 ≤ BL (mA n) := by unfold BL; positivity
    have : 0 ≤ ((mA n : ℕ) : ℝ) ^ ((1 : ℝ) / (64 * (qn n : ℝ))) := Real.rpow_nonneg (by positivity) _
    apply mul_nonneg; apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
    · apply div_nonneg <;> linarith
    · apply mul_nonneg this; positivity
    · positivity
    · positivity
    · assumption
  have hY0 : 0 ≤ 2 / ((mA n : ℕ) : ℝ) * Y2n n := by
    have := Y2n_pos (n := n) (by omega); positivity
  have hZ0 : 0 ≤ Cg * √(2 / ((mA n : ℕ) : ℝ)) * Zop n := by
    have := Cg_pos; have := Zop_pos (n := n) (by omega); positivity
  have hs : √(X2q n (qn n) + 2 / ((mA n : ℕ) : ℝ) * Y2n n) ≤ 205 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hs0 := Real.sqrt_nonneg (X2q n (qn n) + 2 / ((mA n : ℕ) : ℝ) * Y2n n)
  nlinarith

end BstLean.Part168
