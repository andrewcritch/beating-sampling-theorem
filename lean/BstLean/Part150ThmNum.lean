import BstLean.Part150Thm

/-!
# Part 150, item 5: numbers for the arithmetic program with `J = n²` atoms

* `xiN_poly`: the polynomial inequality behind the normalization constant.
* **`xiA_sq_le`**: `xiA n (n²) (√n/10) ≤ 26/(n√n) + 3852/n²` for `n ≥ 4096`.
* **`arithProg150_sq`**: the success bound of `fullProg150 k n (n²)` with explicit terms.
* **`arithProg150_16384`**: `≥ 7/10` for every `n ≥ 16 384`, `k ≥ 100n`.
* **`arithProg150_99`**: `≥ 99/100` for every `n ≥ 400 000`, `k ≥ n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Set Real
open BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part139 (gamK)
open BstLean.Part141 BstLean.Part145
open BstLean.Part149

variable {n : ℕ}

/-- The polynomial inequality behind the normalization constant (`t = 1/√n ≤ 1/64`). -/
lemma xiN_poly {t P ke : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 64) (_hP0 : 0 ≤ P) (hP : P ≤ 35 / 100)
    (_hke0 : 0 ≤ ke) (hke : ke ≤ 401 / 100) :
    (192 * (6 * t ^ 2) * P + ke * (5 * t)) * (534859 / 1000000 * t + 12510 / 1000 * t ^ 2) ^ 2 +
      (24 * (6 * t ^ 2) * (17 + 16 * (9 / 100)) * P + 2 * (6 * t ^ 2) * ke) * (5 * t ^ 4) +
      (96 * (1 + 9 / 100) * (6 * t ^ 2) ^ 2 * P + ke * (18 / 10 * t ^ 3 + 18 * t ^ 4)) ≤
    1296 / 100 * t ^ 3 + 1925 * t ^ 4 := by
  set B : ℝ := 192 * (6 * t ^ 2) * (534859 / 1000000 * t + 12510 / 1000 * t ^ 2) ^ 2 +
    24 * (6 * t ^ 2) * (17 + 16 * (9 / 100)) * (5 * t ^ 4) +
    96 * (1 + 9 / 100) * (6 * t ^ 2) ^ 2 with hB
  set C : ℝ := 5 * t * (534859 / 1000000 * t + 12510 / 1000 * t ^ 2) ^ 2 +
    2 * (6 * t ^ 2) * (5 * t ^ 4) + (18 / 10 * t ^ 3 + 18 * t ^ 4) with hC
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have e : (192 * (6 * t ^ 2) * P + ke * (5 * t)) *
        (534859 / 1000000 * t + 12510 / 1000 * t ^ 2) ^ 2 +
      (24 * (6 * t ^ 2) * (17 + 16 * (9 / 100)) * P + 2 * (6 * t ^ 2) * ke) * (5 * t ^ 4) +
      (96 * (1 + 9 / 100) * (6 * t ^ 2) ^ 2 * P + ke * (18 / 10 * t ^ 3 + 18 * t ^ 4)) =
      P * B + ke * C := by rw [hB, hC]; ring
  rw [e]
  have h1 : P * B ≤ 35 / 100 * B := mul_le_mul_of_nonneg_right hP hB0
  have h2 : ke * C ≤ 401 / 100 * C := mul_le_mul_of_nonneg_right hke hC0
  have p3 : 0 < t ^ 3 := by positivity
  have p4 : 0 < t ^ 4 := by positivity
  have h5 : t ^ 5 ≤ t ^ 4 / 64 := by
    have := mul_le_mul_of_nonneg_left ht p4.le
    calc t ^ 5 = t ^ 4 * t := by ring
      _ ≤ t ^ 4 * (1 / 64) := this
      _ = t ^ 4 / 64 := by ring
  have h6 : t ^ 6 ≤ t ^ 4 / 4096 := by
    have h := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ t ^ 5)
    calc t ^ 6 = t ^ 5 * t := by ring
      _ ≤ t ^ 5 * (1 / 64) := h
      _ ≤ t ^ 4 / 64 * (1 / 64) := mul_le_mul_of_nonneg_right h5 (by norm_num)
      _ = t ^ 4 / 4096 := by ring
  have h3 : 35 / 100 * B + 401 / 100 * C ≤ 1296 / 100 * t ^ 3 + 1925 * t ^ 4 := by
    rw [hB, hC]
    ring_nf
    nlinarith only [h5, h6, p3, p4]
  linarith only [h1, h2, h3]

lemma CQn_t {t : ℝ} (ht0 : 0 < t) (hst : √(n : ℝ) = 1 / t) (hnt : (n : ℝ) = 1 / t ^ 2) :
    CQn n (9 / 100) (1 / 10) (√(n : ℝ) / 10) =
      192 * (6 * t ^ 2) * (1 / (π * (1 - 9 / 100))) +
        (4 + 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) *
          (1 / (π * (1 - 9 / 100)))) * (5 * t) := by
  have hpi0 := Real.pi_pos
  unfold CQn
  rw [hst, hnt]
  field_simp
  ring

lemma CEn_t {t : ℝ} (ht0 : 0 < t) (hnt : (n : ℝ) = 1 / t ^ 2) :
    CEn n (9 / 100) (1 / 10) =
      24 * (6 * t ^ 2) * (17 + 16 * (9 / 100)) * (1 / (π * (1 - 9 / 100))) +
        2 * (6 * t ^ 2) * (4 + 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) *
          (1 / (π * (1 - 9 / 100)))) := by
  have hpi0 := Real.pi_pos
  unfold CEn
  rw [hnt]
  field_simp

lemma C0n_t {t : ℝ} (ht0 : 0 < t) (hst : √(n : ℝ) = 1 / t) (hnt : (n : ℝ) = 1 / t ^ 2) :
    C0n n (9 / 100) (1 / 10) (√(n : ℝ) / 10) =
      96 * (1 + 9 / 100) * (6 * t ^ 2) ^ 2 * (1 / (π * (1 - 9 / 100))) +
        (4 + 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) *
          (1 / (π * (1 - 9 / 100)))) * (18 / 10 * t ^ 3 + 18 * t ^ 4) := by
  have hpi0 := Real.pi_pos
  unfold C0n
  rw [hst, hnt]
  field_simp
  ring

/-- The binomial part with `J = n²` atoms: `xiBin (n²) ≤ 1/n²` (`t = 1/√n`). -/
lemma xiBin_sq_le (hn : 4096 ≤ n) {t : ℝ} (ht0 : 0 < t) (ht2 : t ^ 2 ≤ 1 / 4096)
    (hnt : (n : ℝ) = 1 / t ^ 2) : xiBin (n ^ 2) ≤ t ^ 4 := by
  have hJbig : 4096 ≤ n ^ 2 := by
    calc 4096 ≤ n := hn
      _ ≤ n ^ 2 := by nlinarith
  have hJR : ((n ^ 2 : ℕ) : ℝ) = 1 / t ^ 4 := by
    push_cast; rw [hnt]; field_simp
  have ha := alphaJ_le (J := n ^ 2) (by omega)
  have hb := betaJ_le (J := n ^ 2) hJbig
  have ha0 := alphaJ_nonneg (n ^ 2)
  have hb0 := betaJ_nonneg (n ^ 2)
  rw [hJR] at ha hb
  have ha' : alphaJ (n ^ 2) ≤ 1792 / 10000 * t ^ 4 := by
    refine ha.trans (le_of_eq ?_); field_simp
  have hb' : betaJ (n ^ 2) ≤ 81 / 1000 * t ^ 4 := by
    refine hb.trans (le_of_eq ?_); field_simp
  have p4 : 0 ≤ t ^ 4 := by positivity
  have ht4 : t ^ 4 ≤ 1 / 4096 := by
    have h0 : t ^ 4 = t ^ 2 * t ^ 2 := by ring
    have h1 := mul_le_mul ht2 ht2 (sq_nonneg t) (by norm_num : (0 : ℝ) ≤ 1 / 4096)
    rw [h0]; linarith only [h1]
  have hasmall : alphaJ (n ^ 2) ≤ 1 / 1000 := by linarith only [ha', ht4]
  have hsq : alphaJ (n ^ 2) ^ 2 ≤ 1 / 1000 * alphaJ (n ^ 2) := by
    have := mul_le_mul_of_nonneg_right hasmall ha0
    calc alphaJ (n ^ 2) ^ 2 = alphaJ (n ^ 2) * alphaJ (n ^ 2) := by ring
      _ ≤ 1 / 1000 * alphaJ (n ^ 2) := this
  have hpi := Real.pi_gt_three
  have hinv : 1 / π ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hpi.le
  have hsum0 : 0 ≤ 2 * betaJ (n ^ 2) + 4 * alphaJ (n ^ 2) + 2 * alphaJ (n ^ 2) ^ 2 := by
    positivity
  have h1 : (2 * betaJ (n ^ 2) + 4 * alphaJ (n ^ 2) + 2 * alphaJ (n ^ 2) ^ 2) / π ≤
      (2 * betaJ (n ^ 2) + 4 * alphaJ (n ^ 2) + 2 * alphaJ (n ^ 2) ^ 2) * (1 / 3) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hsum0
  unfold xiBin
  linarith only [h1, hsq, ha', hb', p4, ha0, hb0]

/-- **The displacement constant with `lam = √n/10`**: the binomial part and the normalization
part. -/
theorem xiA_le (hn : 4096 ≤ n) (J : ℕ) :
    xiA n J (√(n : ℝ) / 10) ≤
      2 * xiBin J + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have hs64 : (64 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht64 : t ≤ 1 / 64 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs64
  have hst : √(n : ℝ) = 1 / t := by rw [ht]; field_simp
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 ≤ 1 / 4096 := by
    have := pow_le_pow_left₀ ht0.le ht64 2
    norm_num at this ⊢; linarith
  have hpi := Real.pi_gt_d4
  have hpi0 := Real.pi_pos
  have eQ := CQn_t (n := n) ht0 hst hnt
  have eE := CEn_t (n := n) ht0 hnt
  have e0 := C0n_t (n := n) ht0 hst hnt
  have edQ : dQb149 n = 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    unfold dQb149
    rw [hst, hnt]
    field_simp
  have em : (5 : ℝ) / (mA n : ℝ) = 5 * t ^ 4 := by
    rw [mA_eqR, hnt]; field_simp
  have e26 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2 =
      2592 / 100 * t ^ 3 + 3850 * t ^ 4 := by
    rw [hst, hnt]; field_simp
  unfold xiA xiArith
  have e26' : 2 * xiBin J + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2 =
      2 * xiBin J + (2592 / 100 * t ^ 3 + 3850 * t ^ 4) := by rw [← e26]; ring
  rw [e26', eQ, eE, e0, edQ, em]
  have hP0 : (0 : ℝ) < 1 / (π * (1 - 9 / 100)) := by positivity
  have hP35 : 1 / (π * (1 - 9 / 100)) ≤ 35 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    norm_num at hpi ⊢; linarith
  have hke0 : 0 ≤ 4 + 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) *
      (1 / (π * (1 - 9 / 100))) := by positivity
  have hke1 : 4 + 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) *
      (1 / (π * (1 - 9 / 100))) ≤ 401 / 100 := by
    have h1 : 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) ≤ 1 / 100 := by
      nlinarith only [sq_nonneg t, ht2]
    have h0 : 0 ≤ 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) := by positivity
    have h2 : 24 * (6 * t ^ 2) * (1 / 10 + 2 * (9 / 100) ^ 2 + 6 * t ^ 2 / 2) *
        (1 / (π * (1 - 9 / 100))) ≤ 1 / 100 * 1 :=
      mul_le_mul h1 (hP35.trans (by norm_num)) hP0.le (by norm_num)
    linarith only [h2]
  have hpoly := xiN_poly ht0 ht64 hP0.le hP35 hke0 hke1
  linarith only [hpoly]


/-- `xiBin (n²) ≤ 1/n²`. -/
theorem xiBin_sq (hn : 4096 ≤ n) : xiBin (n ^ 2) ≤ 1 / (n : ℝ) ^ 2 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have hs64 : (64 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht64 : t ≤ 1 / 64 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs64
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 ≤ 1 / 4096 := by
    have := pow_le_pow_left₀ ht0.le ht64 2
    norm_num at this ⊢; linarith
  have h := xiBin_sq_le hn ht0 ht2 hnt
  refine h.trans (le_of_eq ?_)
  rw [hnt]; field_simp

/-- `xiBin n ≤ 1/n` (the paper's main form `J = n`). -/
theorem xiBin_n (hn : 4096 ≤ n) : xiBin n ≤ 1 / (n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have ha := alphaJ_le (J := n) (by omega)
  have hb := betaJ_le (J := n) hn
  have ha0 := alphaJ_nonneg n
  have hb0 := betaJ_nonneg n
  have hinvn : 1 / (n : ℝ) ≤ 1 / 4096 := one_div_le_one_div_of_le (by norm_num) hx
  have ha' : alphaJ n ≤ 1792 / 10000 * (1 / (n : ℝ)) := by
    refine ha.trans (le_of_eq ?_); ring
  have hb' : betaJ n ≤ 81 / 1000 * (1 / (n : ℝ)) := by
    refine hb.trans (le_of_eq ?_); ring
  have hasmall : alphaJ n ≤ 1 / 1000 := by linarith only [ha', hinvn]
  have hsq : alphaJ n ^ 2 ≤ 1 / 1000 * alphaJ n := by
    have := mul_le_mul_of_nonneg_right hasmall ha0
    calc alphaJ n ^ 2 = alphaJ n * alphaJ n := by ring
      _ ≤ 1 / 1000 * alphaJ n := this
  have hpi := Real.pi_gt_three
  have hinv : 1 / π ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hpi.le
  have hsum0 : 0 ≤ 2 * betaJ n + 4 * alphaJ n + 2 * alphaJ n ^ 2 := by positivity
  have h1 : (2 * betaJ n + 4 * alphaJ n + 2 * alphaJ n ^ 2) / π ≤
      (2 * betaJ n + 4 * alphaJ n + 2 * alphaJ n ^ 2) * (1 / 3) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hsum0
  have hn0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold xiBin
  linarith only [h1, hsq, ha', hb', hn0, ha0, hb0]

/-- **The arithmetic program with `J + 1` atoms**: explicit terms (`lam = √n/10`). -/
theorem arithProg150_gen (hn : 4096 ≤ n) {k : ℕ} (hk : 1 ≤ k) {J : ℕ} (hJ : 1 ≤ J) {η₄ η₅ : ℝ}
    (hη₄ : 0 < η₄) (hη₅ : 0 < η₅) :
    1 - ((1 + η₅) * ((1 + η₄) * p149 n +
          (2 * xiBin J + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2) *
            (625 + (1 + 1 / η₄) * 235)) +
        (1 + 1 / η₅) * (19 / k) + 1 / (n : ℝ)) ≤
      ((mlpTriple 2 n).prod (gamK k n)).real
        {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
            Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have h := arithProg150 hn hk hJ (lam := √(n : ℝ) / 10) (by positivity) hη₄ hη₅
  refine le_trans ?_ h
  have hxi := xiA_le hn J
  have hK : (0 : ℝ) ≤ 625 + (1 + 1 / η₄) * 235 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hxi hK
  have h2 := mul_le_mul_of_nonneg_left
    (add_le_add_left h1 ((1 + η₄) * p149 n)) (by positivity : (0 : ℝ) ≤ 1 + η₅)
  linarith only [h2]

lemma p149_le_16384 (hn : 16384 ≤ n) : p149 n ≤ 19413 / 100000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  unfold p149
  have h1 : (1835 : ℝ) / n ≤ 1835 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h2 : (130287 : ℝ) / ((n : ℝ) * √(n : ℝ)) ≤ 130287 / (16384 * 128) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3 : (5368347 : ℝ) / (n : ℝ) ^ 2 ≤ 5368347 / 16384 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  norm_num at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

/-- **`J = n²` atoms: success at least `7/10` for every `n ≥ 16 384`, `k ≥ 100n`.** -/
theorem arithProg150_16384 (hn : 16384 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    7 / 10 ≤ ((mlpTriple 2 n).prod (gamK k n)).real
      {p | |(fullProg150 k n (n ^ 2)).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (1638400 : ℝ) ≤ k := by
    have : (100 * n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := arithProg150_gen hn4 hk1 (J := n ^ 2) (Nat.one_le_pow _ _ (by omega))
    (η₄ := 1 / 4) (by norm_num) (η₅ := 1 / 100) (by norm_num)
  refine le_trans ?_ h
  have hp := p149_le_16384 hn
  have hb := xiBin_sq hn4
  have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (16384 * 128) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3 : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 16384 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  have h3' : (3850 : ℝ) / (n : ℝ) ^ 2 = 3850 * (1 / (n : ℝ) ^ 2) := by ring
  have h4 : (19 : ℝ) / k ≤ 19 / 1638400 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
  have h5 : (1 : ℝ) / n ≤ 1 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  rw [h3']
  norm_num at hp hb h2 h3 h4 h5 ⊢
  linarith only [hp, hb, h2, h3, h4, h5]

/-- **`J = n` atoms (the main form of the paper): success at least `1/2` for every
`n ≥ 16 384`, `k ≥ 100n`.** -/
theorem arithProg150_n_16384 (hn : 16384 ≤ n) {k : ℕ} (hk : 100 * n ≤ k) :
    1 / 2 ≤ ((mlpTriple 2 n).prod (gamK k n)).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (1638400 : ℝ) ≤ k := by
    have : (100 * n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := arithProg150_gen hn4 hk1 (J := n) (by omega)
    (η₄ := 2 / 5) (by norm_num) (η₅ := 1 / 100) (by norm_num)
  refine le_trans ?_ h
  have hp := p149_le_16384 hn
  have hb := xiBin_n hn4
  have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (16384 * 128) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3 : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 16384 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  have h3' : (3850 : ℝ) / (n : ℝ) ^ 2 = 3850 * (1 / (n : ℝ) ^ 2) := by ring
  have h4 : (19 : ℝ) / k ≤ 19 / 1638400 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
  have h5 : (1 : ℝ) / n ≤ 1 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  rw [h3']
  norm_num at hp hb h2 h3 h4 h5 ⊢
  linarith only [hp, hb, h2, h3, h4, h5]

/-- **`J = n²` atoms: success at least `99/100` for every `n ≥ 400 000`, `k ≥ n`.** -/
theorem arithProg150_99 (hn : 400000 ≤ n) {k : ℕ} (hk : n ≤ k) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (gamK k n)).real
      {p | |(fullProg150 k n (n ^ 2)).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Part130.Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hx : (400000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (632 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (400000 : ℝ) ≤ k := by
    have : (n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h := arithProg150_gen hn4 hk1 (J := n ^ 2) (Nat.one_le_pow _ _ (by omega))
    (η₄ := 1 / 2) (by norm_num) (η₅ := 1 / 10) (by norm_num)
  refine le_trans ?_ h
  have hb := xiBin_sq hn4
  have h1 : (1835 : ℝ) / n ≤ 1835 / 400000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h1b : (130287 : ℝ) / ((n : ℝ) * √(n : ℝ)) ≤ 130287 / (400000 * 632) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3 : (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 400000 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  have h1c : (5368347 : ℝ) / (n : ℝ) ^ 2 = 5368347 * (1 / (n : ℝ) ^ 2) := by ring
  have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (400000 * 632) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (mul_le_mul hx hs (by norm_num) hx0.le)
  have h3' : (3850 : ℝ) / (n : ℝ) ^ 2 = 3850 * (1 / (n : ℝ) ^ 2) := by ring
  have h4 : (19 : ℝ) / k ≤ 19 / 400000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hkR
  have h5 : (1 : ℝ) / n ≤ 1 / 400000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold p149
  rw [h3', h1c]
  norm_num at hb h1 h1b h2 h3 h4 h5 ⊢
  linarith only [hb, h1, h1b, h2, h3, h4, h5]

end BstLean.Part150

open BstLean.Part150 in
#print axioms xiA_le
open BstLean.Part150 in
#print axioms arithProg150_gen
open BstLean.Part150 in
#print axioms arithProg150_16384
open BstLean.Part150 in
#print axioms arithProg150_n_16384
open BstLean.Part150 in
#print axioms arithProg150_99
