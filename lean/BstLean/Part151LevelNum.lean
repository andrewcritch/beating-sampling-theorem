import BstLean.Part151Level

/-!
# Part 151, item 5: the numbers. Success `≥ 3/4` for every `n ≥ 16 384`

Role: `delegations/statements/p151-spec.md`, item 5.

* `pFail7_num`: at the parameters of `displaceSamp150` (Part 150), with `θ = 3/4`,
  `ε_W = 1/15`, `η₃ = 3/10`, `η₄ = 8/39`, `η₅ = 1/47`: `pFail7 κ ≤ 0.095516 + 0.352703·κ` for
  `n ≥ 16 384`, `k ≥ 100n`.
* `gaussLevel151_of_kap`: the level `1 − (0.095516 + 0.352703·κ)` for every constant `κ` of the
  Gaussian tail.
* **`gaussLevel151`**: the straight-line program `fullProg150 k n n` of Part 150 succeeds with
  probability at least `3/4` for every `n ≥ 16 384`, `k ≥ 100n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (cenA tauWA gA measurable_gA qA qA_cast)
open BstLean.Part145
open BstLean.Part149
open BstLean.Part150

/-- The Gaussian-step term of `pFail7` as a linear form. -/
lemma A_term_eq (a b ξ N k : ℝ) (hN : 0 < N) (hk : 0 < k) :
    ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * (2 / N * a) +
          (1 + 1 / (3 / 10)) * (2 / N * (2 / (1 - 8441 / 10000)) * b)) +
        (1 + 1 / (8 / 39)) * (2 / N * (2 / (1 - 9193 / 10000)) * ξ)) +
      (1 + 1 / (1 / 47)) * (4 / N / k)) /
      ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 / N * (222757 / 1000000)))) =
    ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * 2))) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * a +
      ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 1 / (3 / 10)) *
          (2 * (2 / (1 - 8441 / 10000)))))) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * b +
      ((1 + 1 / 47) * ((1 + 1 / (8 / 39)) * (2 * (2 / (1 - 9193 / 10000))))) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * ξ +
      ((1 + 1 / (1 / 47)) * 4) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * (1 / k) := by
  field_simp

lemma spread_term_eq (s : ℝ) (hs : 0 < s) :
    2 * (4 / s ^ 2 * (78728 / 100000 / s)) ^ 2 /
        ((1 - 3 / 4) * (4 / s ^ 2 * (222757 / 1000000))) ^ 2 =
      2 * (78728 / 100000) ^ 2 / ((1 / 4) * (222757 / 1000000)) ^ 2 * (1 / s ^ 2) := by
  field_simp
  ring

lemma W_term_eq (N : ℝ) (hN : 0 < N) :
    4849 / 20000 * (1 / N) * (4 / N) / ((1 / 15) ^ 2 * (3 / 4 * (4 / N * (222757 / 1000000)))) =
      4849 / 20000 / ((1 / 15) ^ 2 * (3 / 4 * (222757 / 1000000))) * (1 / N) := by
  field_simp

variable {k n : ℕ}

/-- **The numbers**: `pFail7 κ ≤ 0.095516 + 0.352703·κ` for `n ≥ 16 384`, `k ≥ 100n`, at the
parameters of `displaceSamp150`, `θ = 3/4`, `ε_W = 1/15`, `η₃ = 3/10`, `η₄ = 8/39`,
`η₅ = 1/47`. -/
theorem pFail7_num {κ : ℝ} (hκ0 : 0 ≤ κ) (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {ξ : ℝ}
    (hξ : ξ ≤ 20 / (n : ℝ) ^ 2 + 2592 / 100 / ((n : ℝ) * √(n : ℝ)) + 3850 / (n : ℝ) ^ 2) :
    pFail7 κ n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000) (273 / 1000)
      (251 / 1000) (51 / 10) (56 / 1000) (1 / 10)
      (393278 / 1000000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
      (16034 / 100000 * (1 / √(n : ℝ)) + 11363 / 1000 * (1 / √(n : ℝ)) ^ 2)
      (4728 / 1000 * (1 / √(n : ℝ)) ^ 2) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8441 / 10000) (9 / 100)
      (534859 / 1000000 * (1 / √(n : ℝ)) + 12510 / 1000 * (1 / √(n : ℝ)) ^ 2) ξ (1 / 25)
      (9193 / 10000) (3 / 10) (8 / 39) (1 / 47) (3 / 4) (1 / 15) ≤
      95516 / 1000000 + κ * (352703 / 1000000) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have hs0 : 0 < √(n : ℝ) := by linarith
  have hkR : (1638400 : ℝ) ≤ k := by
    have : (100 * n : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hx0.le
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 128 := by rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [ht, div_pow, one_pow, hsq]
  have hy : 1 / (n : ℝ) ≤ 1 / 16384 := one_div_le_one_div_of_le (by norm_num) hx
  have ht2' : t ^ 2 ≤ 1 / 16384 := by rw [ht2]; exact hy
  have ht20 : 0 ≤ t ^ 2 := sq_nonneg t
  have h1k : 1 / (k : ℝ) ≤ 1 / 1638400 := one_div_le_one_div_of_le (by norm_num) hkR
  set K : ℝ := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 with hKd
  set X : ℝ := 16034 / 100000 * t + 11363 / 1000 * t ^ 2 with hXd
  set δ : ℝ := 4728 / 1000 * t ^ 2 with hδd
  set Q : ℝ := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 with hQd
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hX0 : 0 ≤ X := by rw [hXd]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδd]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQd]; positivity
  have hK : K ≤ 3766027 / 1000000000 := by rw [hKd]; linarith
  have hX : X ≤ 1946199 / 1000000000 := by rw [hXd]; linarith
  have hδ : δ ≤ 288575 / 1000000000 := by rw [hδd]; linarith
  have hQ : Q ≤ 4942136 / 1000000000 := by rw [hQd]; linarith
  have hK2 : K ^ 2 ≤ (3766027 / 1000000000) ^ 2 := pow_le_pow_left₀ hK0 hK 2
  have hX2 : X ^ 2 ≤ (1946199 / 1000000000) ^ 2 := pow_le_pow_left₀ hX0 hX 2
  have hδ2 : δ ^ 2 ≤ (288575 / 1000000000) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have hQ2 : Q ^ 2 ≤ (4942136 / 1000000000) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  -- the constant of the stage of `A`
  set a : ℝ := EA2 (6662 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000)
    (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) K X δ with had
  have ha : a ≤ 8717411 / 1000000000 := by
    have cK : Part149.kK2 (6662 / 10000) (284 / 10000) (273 / 1000) (51 / 10) (1 / 10) ≤ 172 := by
      unfold Part149.kK2; norm_num
    have cX : Part149.kX2 (6662 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
        (1908 / 1000) (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) ≤ 1572 := by
      unfold Part149.kX2; norm_num
    have cD : Part149.kD2 (6662 / 10000) (284 / 10000) (1908 / 1000) (251 / 1000) (51 / 10)
        (56 / 1000) ≤ 3887 := by
      unfold Part149.kD2; norm_num
    rw [had]
    unfold EA2
    calc _ ≤ 172 * (3766027 / 1000000000) ^ 2 + 1572 * (1946199 / 1000000000) ^ 2 +
          3887 * (288575 / 1000000000) ^ 2 :=
          add_le_add (add_le_add (mul_le_mul cK hK2 (sq_nonneg _) (by norm_num))
            (mul_le_mul cX hX2 (sq_nonneg _) (by norm_num)))
            (mul_le_mul cD hδ2 (sq_nonneg _) (by norm_num))
      _ ≤ 8717411 / 1000000000 := by norm_num
  have hm5 : 5 / (mA n : ℝ) ≤ 5 / 16384 ^ 2 := by
    rw [mA_eqR]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hx 2)
  have hm50 : 0 ≤ 5 / (mA n : ℝ) := by rw [mA_eqR]; positivity
  set b : ℝ := xiB n (9 / 100) (88 / 100) (9 / 100) Q with hbd
  have hb : b ≤ 6053068 / 100000000000 := by
    have c1 : cQ3 (88 / 100) (9 / 100) ≤ 2304 / 1000 := by unfold cQ3 Kq; norm_num
    have c2 : cD3 (9 / 100) (88 / 100) (9 / 100) ≤ 2285 / 10 := by unfold cD3 Kq; norm_num
    rw [hbd]
    unfold xiB
    calc _ ≤ 2304 / 1000 * (4942136 / 1000000000) ^ 2 + 2285 / 10 * (5 / 16384 ^ 2) :=
          add_le_add (mul_le_mul c1 hQ2 (sq_nonneg _) (by norm_num))
            (mul_le_mul c2 hm5 hm50 (by norm_num))
      _ ≤ 6053068 / 100000000000 := by norm_num
  -- the displacement constant
  have hξ' : ξ ≤ 2677650 / 100000000000 := by
    have h1 : (20 : ℝ) / (n : ℝ) ^ 2 ≤ 20 / 16384 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
    have h2 : (2592 : ℝ) / 100 / ((n : ℝ) * √(n : ℝ)) ≤ 2592 / 100 / (16384 * 128) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (mul_le_mul hx hs (by norm_num) hx0.le)
    have h3 : (3850 : ℝ) / (n : ℝ) ^ 2 ≤ 3850 / 16384 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
    have h4 : (20 : ℝ) / 16384 ^ 2 + 2592 / 100 / (16384 * 128) + 3850 / 16384 ^ 2 ≤
        2677650 / 100000000000 := by norm_num
    linarith
  -- (1) the bad event
  have h1 : badT n (284 / 10000) (635 / 10000) K X (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (9 / 100) Q ξ (1 / 25) ≤ 51189 / 1000000 := by
    unfold badT
    rw [← hbd]
    have p1 : (1 : ℝ) / 50000 / (n : ℝ) ≤ 1 / 50000 / 16384 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    have p2 : (68000000 : ℝ) / (qA n : ℝ) ^ 2 ≤ 68000000 / (10000 * 16384) ^ 2 := by
      rw [qA_cast]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) (by linarith) 2)
    have p3 : K ^ 2 / (284 / 10000 : ℝ) ^ 2 ≤ (3766027 / 1000000000) ^ 2 / (284 / 10000) ^ 2 :=
      div_le_div_of_nonneg_right hK2 (by norm_num)
    have p4 : X ^ 2 / (635 / 10000 : ℝ) ^ 2 ≤ (1946199 / 1000000000) ^ 2 / (635 / 10000) ^ 2 :=
      div_le_div_of_nonneg_right hX2 (by norm_num)
    have p5 : Q ^ 2 / (1 / 10 : ℝ) ^ 2 ≤ (4942136 / 1000000000) ^ 2 / (1 / 10) ^ 2 :=
      div_le_div_of_nonneg_right hQ2 (by norm_num)
    have p6 : 5 / (mA n : ℝ) / (9 / 100 : ℝ) ^ 2 ≤ 5 / 16384 ^ 2 / (9 / 100) ^ 2 :=
      div_le_div_of_nonneg_right hm5 (by norm_num)
    have p7 : b / (67 / 1000 : ℝ) ^ 2 ≤ 6053068 / 100000000000 / (67 / 1000) ^ 2 :=
      div_le_div_of_nonneg_right hb (by norm_num)
    have p8 : ξ / (1 / 25 : ℝ) ^ 2 ≤ 2677650 / 100000000000 / (1 / 25) ^ 2 :=
      div_le_div_of_nonneg_right hξ' (by norm_num)
    have p9 : (1 : ℝ) / 50000 / 16384 + 68000000 / (10000 * 16384) ^ 2 +
        (3766027 / 1000000000) ^ 2 / (284 / 10000) ^ 2 +
        (1946199 / 1000000000) ^ 2 / (635 / 10000) ^ 2 +
        (1 / 50000 / 16384 + 68000000 / (10000 * 16384) ^ 2 +
          (4942136 / 1000000000) ^ 2 / (1 / 10) ^ 2 + 5 / 16384 ^ 2 / (9 / 100) ^ 2 +
          6053068 / 100000000000 / (67 / 1000) ^ 2) +
        2677650 / 100000000000 / (1 / 25) ^ 2 ≤ 51189 / 1000000 := by norm_num
    linarith
  -- (2) the spread
  have h2 : 2 * (4 / (n : ℝ) * (78728 / 100000 / √(n : ℝ))) ^ 2 /
      ((1 - 3 / 4) * (4 / (n : ℝ) * (222757 / 1000000))) ^ 2 ≤ 24397 / 1000000 := by
    have e := spread_term_eq (√(n : ℝ)) hs0
    rw [hsq] at e
    rw [e]
    calc 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 / 4) * (222757 / 1000000)) ^ 2 * (1 / (n : ℝ))
        ≤ 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 / 4) * (222757 / 1000000)) ^ 2 * (1 / 16384) :=
          mul_le_mul_of_nonneg_left hy (by norm_num)
      _ ≤ 24397 / 1000000 := by norm_num
  -- (3) the `W` stage
  have h3 : 4849 / 20000 * (1 / (n : ℝ)) * (4 / (n : ℝ)) /
      ((1 / 15) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤ 1993 / 100000 := by
    rw [W_term_eq (n : ℝ) hx0]
    calc 4849 / 20000 / ((1 / 15 : ℝ) ^ 2 * (3 / 4 * (222757 / 1000000))) * (1 / (n : ℝ))
        ≤ 4849 / 20000 / ((1 / 15 : ℝ) ^ 2 * (3 / 4 * (222757 / 1000000))) * (1 / 16384) :=
          mul_le_mul_of_nonneg_left hy (by norm_num)
      _ ≤ 1993 / 100000 := by norm_num
  -- (4) the Gaussian step
  have h4 : IA n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000)
      (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) K X δ (9 / 100) (88 / 100)
      (8441 / 10000) (9 / 100) Q ξ (9193 / 10000) (3 / 10) (8 / 39) (1 / 47) /
      ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤
      352703 / 1000000 := by
    unfold IA
    rw [← had, ← hbd, A_term_eq a b ξ (n : ℝ) (k : ℝ) hx0 hk0]
    have q1 := mul_le_mul_of_nonneg_left ha (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * 2))) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q2 := mul_le_mul_of_nonneg_left hb (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 1 / (3 / 10)) *
          (2 * (2 / (1 - 8441 / 10000)))))) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q3 := mul_le_mul_of_nonneg_left hξ' (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / 47) * ((1 + 1 / (8 / 39)) * (2 * (2 / (1 - 9193 / 10000))))) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q4 := mul_le_mul_of_nonneg_left h1k (by norm_num :
      (0 : ℝ) ≤ ((1 + 1 / (1 / 47)) * 4) /
        ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))))
    have q5 : ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 3 / 10) * 2))) /
          ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) *
          (8717411 / 1000000000 : ℝ) +
        ((1 + 1 / 47) * ((1 + 8 / 39) * ((1 + 1 / (3 / 10)) *
            (2 * (2 / (1 - 8441 / 10000)))))) /
          ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) *
          (6053068 / 100000000000) +
        ((1 + 1 / 47) * ((1 + 1 / (8 / 39)) * (2 * (2 / (1 - 9193 / 10000))))) /
          ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) *
          (2677650 / 100000000000) +
        ((1 + 1 / (1 / 47)) * 4) /
          ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 * (222757 / 1000000)))) * (1 / 1638400) ≤
        352703 / 1000000 := by norm_num
    linarith
  have h5 : κ * IA n k (284 / 10000) (635 / 10000) (12522 / 10000) (1908 / 1000)
      (273 / 1000) (251 / 1000) (51 / 10) (56 / 1000) (1 / 10) K X δ (9 / 100) (88 / 100)
      (8441 / 10000) (9 / 100) Q ξ (9193 / 10000) (3 / 10) (8 / 39) (1 / 47) /
      ((1 / 2 - 1 / 15) ^ 2 * (3 / 4 * (4 / (n : ℝ) * (222757 / 1000000)))) ≤
      κ * (352703 / 1000000) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h4 hκ0
  unfold pFail7
  linarith

/-- **The level as a function of the constant `κ` of the Gaussian tail** (`2Φ̄(a) ≤ κ/a²`): for
every `n ≥ 16 384`, `k ≥ 100n`, the program `fullProg150 k n n` succeeds with probability at
least `1 − (0.095516 + 0.352703·κ)`. (`κ = 1` is Chebyshev's inequality at the last step.) -/
theorem gaussLevel151_of_kap {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hκ0 : 0 ≤ κ) (hn : 16384 ≤ n) (hk : 100 * n ≤ k) :
    1 - (95516 / 1000000 + κ * (352703 / 1000000)) ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn4 : 4096 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [hnt]; field_simp
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA6 : 1000000 ≤ mA n := by
    unfold mA
    calc 1000000 ≤ 4096 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn4 2
  have hcF : cF2o (mA n) ≤ 4728 / 1000 * t ^ 2 := by
    have h1 := BstLean.Part136.cF2o_sq_le hmA6
    have h0 := (BstLean.Part136.cF2o_pos hmA).le
    rw [mA_eqR] at h1
    have h2 : (2235 : ℝ) / 100 / (n : ℝ) ^ 2 = 2235 / 100 * (t ^ 2) ^ 2 := by
      rw [ht2]; field_simp
    rw [h2] at h1
    have h3 : cF2o (mA n) ^ 2 ≤ (4728 / 1000 * t ^ 2) ^ 2 := by
      refine h1.trans ?_
      have : 0 ≤ (t ^ 2) ^ 2 := by positivity
      nlinarith
    exact le_trans (le_abs_self _) (abs_le_of_sq_le_sq h3 (by positivity))
  have hΔK : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dK2 n (mA n) q ≤ 393278 / 1000000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dK2_le hn4 hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dX2 n (mA n) q ≤ 16034 / 100000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dX2_le hn4 hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dQ1 n (mA n) q ≤ 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dQ1_le hn4 hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hP : POK2 (6662 / 10000) (6969 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
      (1908 / 1000) (273 / 1000) (251 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hP3 : POK3 (6969 / 10000) (284 / 10000) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8517 / 10000) (8441 / 10000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hsq : √(8441 / 10000 : ℝ) ≤ 91876 / 100000 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hy4 : (√(8441 / 10000 : ℝ) + 1 / 25) ^ 2 ≤ 9193 / 10000 := by
    have h0 := Real.sqrt_nonneg (8441 / 10000 : ℝ)
    nlinarith
  -- the arithmetic centre
  have hlam : (0 : ℝ) < √(n : ℝ) / 10 := by positivity
  have hd := arith_dispOK2 hn4 (goodEvFR hn4).to0 (winOK2_149 hn4) (εD := 9 / 100)
    (εQ := 1 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlam (σ := 2 / 5)
    (by norm_num) (sigma_ok hn4) (J := n) (by omega) (fun _ h1 h2 => dQ1_le hn4 h1 h2)
    (fun _ h1 h2 => dQ1_nonneg h1 h2 (by omega))
  have hξ0 : 0 ≤ xiArith2 n n (9 / 100) (1 / 10) (√(n : ℝ) / 10) (dQb149 n) (2 / 5) := by
    have h1 := xiBin2_nonneg n (σ := 2 / 5) (by norm_num) (mA n)
    have h2 := CQn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num) hlam
    have h3 := CEn_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num)
    have h4 := C0n_nonneg (n := n) (εD := 9 / 100) (εQ := 1 / 10) (by norm_num) (by norm_num)
      (by norm_num) hlam
    unfold xiArith2
    positivity
  have hxi := xiA2_le hn4
  -- the program is the sample mean on the good event
  have hwin := winOK2_149 hn4
  have hgE : ∀ p ∈ TXJ k (goodX234 n (284 / 10000) (635 / 10000) (9 / 100) (1 / 10)
      (67 / 1000) (bTW n) (1 / 25)),
      (fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () =
        gSampH (bTW n) k p.1.1 p.1.2.1 p.1.2.2 p.2 := by
    intro p hp
    have hW : p.1.1 ∈ goodWAG (Gwin n) := hp.1.1.1
    have hτ : 0 < tauWA p.1.1 := (hwin (p.1.1.1, p.1.1.2.1) hW).2.1
    exact fullProg150_gSampH (k := k) (J := n) p.1.1 p.1.2.1 p.1.2.2 p.2 hτ
  have h := gaussLevel151_formula hκ hn4 hk1 hP hP3 (ζ₃ := 9 / 100) (by norm_num)
    (dQb := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2) hdQ
    (fun q hq1 hq2 => dQ1_nonneg hq1 hq2 hn1)
    (η := 51 / 10) (by norm_num) (ζ := 56 / 1000) (by norm_num) (ζ₂ := 1 / 10) (by norm_num)
    (ΔKb := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2)
    (ΔXb := 16034 / 100000 * t + 11363 / 1000 * t ^ 2) (by positivity) (by positivity) hΔK
    (fun q hq1 hq2 => dK2_nonneg hq1 hq2 hn1) hΔX (fun q _ _ => dX2_nonneg hn1) hcF
    (measurable_bTW n) (D4 := 1 / 25) (y4 := 9193 / 10000) (by norm_num) hy4 (by norm_num) hξ0 hd
    (η₃ := 3 / 10) (by norm_num) (η₄ := 8 / 39) (by norm_num) (η₅ := 1 / 47) (by norm_num)
    (θ := 3 / 4) (by norm_num) (by norm_num) (εW := 1 / 15) (by norm_num) (by norm_num)
    (fun p : Joint k n => (fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) ()) hgE
  refine le_trans ?_ h
  have hnum := pFail7_num hκ0 hn hk hxi
  rw [← ht] at hnum
  linarith

/-- **A Lean level with the Gaussian last step: the straight-line program `fullProg150 k n n`
of Part 150 (no forward pass of `A`; `n + 1` binomial atoms in both hidden layers of `A`;
`k ≥ 100n` forward passes of `F`) succeeds with probability at least `3/4`, for every
`n ≥ 16 384`.** (Part 150, with Chebyshev's inequality at the last step: `7/10`.) -/
theorem gaussLevel151 (hn : 16384 ≤ n) (hk : 100 * n ≤ k) :
    3 / 4 ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have h := gaussLevel151_of_kap (κ := 2 / 5) (fun a ha => two_PhiBar_le_kap ha) (by norm_num)
    hn hk
  refine le_trans ?_ h
  norm_num

end BstLean.Part151
