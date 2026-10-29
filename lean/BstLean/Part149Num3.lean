import BstLean.Part149Final3
import BstLean.Part149Num2

/-!
# Part 149, item 5: the explicit failure probability of the program with the mean-field centre

Do not use `sorry`, `native_decide` or `axiom`.

* `pFail3_eq`: the bound `pFail3` as a polynomial in `t = 1/√n`.
* **`onePassA149`**: for every `n ≥ 4096`:
  `Pr(|gOutB − B| ≤ sd/2) ≥ 1 − (1835/n + 130287/(n√n) + 5368347/n²)`.
  The bound is below `1` from about `n = 5000`.
* `onePassA149_8192` (`≥ 1/2`), `onePassA149_16384` (`≥ 8/10`), `onePassA149_99` (`≥ 99/100` for
  `n ≥ 250 000`).

The centre `bMF` uses ORACLES (the exact first-layer mean `b1`, the number `N2`, the function
`ψ_s`). There is no arithmetic program and no operation count here.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part141 BstLean.Part145

variable {n : ℕ}

lemma pFail3_eq {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb t : ℝ}
    (hη₁ : η₁ ≠ 0) (hθ0 : θ ≠ 0) (hθ1 : 1 - θ ≠ 0) (ht : 0 < t) (hnt : (n : ℝ) = 1 / t ^ 2)
    (hst : √(n : ℝ) = 1 / t) :
    pFail3 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb εD εQ π₀ Dmax yhi ζ₃ η₃ dQb =
      t ^ 2 / 50000 + 68 / 100 * t ^ 4 + ΔKb ^ 2 / Δmax ^ 2 + ΔXb ^ 2 / ΔXmax ^ 2 +
        (t ^ 2 / 50000 + 68 / 100 * t ^ 4 + dQb ^ 2 / εQ ^ 2 + 5 * t ^ 4 / εD ^ 2 +
          (cQ3 π₀ ζ₃ * dQb ^ 2 + cD3 εD π₀ ζ₃ * (5 * t ^ 4)) / Dmax ^ 2) +
        ((1 + η₁) * (4849 / 20000 * 4) * t ^ 2 + (1 + 1 / η₁) *
          ((1 + η₃) * (2 * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb) +
            (1 + 1 / η₃) * (2 * (2 / (1 - yhi)) *
              (cQ3 π₀ ζ₃ * dQb ^ 2 + cD3 εD π₀ ζ₃ * (5 * t ^ 4))))) /
          (θ * (222757 / 1000000)) +
        2 * (78728 / 100000) ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) * t ^ 2 := by
  have hm : (mA n : ℝ) = 1 / t ^ 4 := by
    rw [mA_eqR, hnt]; field_simp
  have h5 : (5 : ℝ) / (mA n : ℝ) = 5 * t ^ 4 := by rw [hm]; field_simp
  unfold pFail3 xiB
  rw [h5, qA_cast, hst, hnt]
  generalize EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb = E
  generalize ΔKb ^ 2 / Δmax ^ 2 = u
  generalize ΔXb ^ 2 / ΔXmax ^ 2 = w'
  generalize dQb ^ 2 / εQ ^ 2 = u2
  generalize 5 * t ^ 4 / εD ^ 2 = u3
  generalize (cQ3 π₀ ζ₃ * dQb ^ 2 + cD3 εD π₀ ζ₃ * (5 * t ^ 4)) = X
  generalize X / Dmax ^ 2 = u4
  generalize 2 / (1 - yhi) = Y
  have ht' : t ≠ 0 := ht.ne'
  field_simp
  ring

lemma dQ1_nonneg {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) (hn : 1 ≤ n) :
    0 ≤ dQ1 n (mA n) q := by
  have h2 := jCosC_nonneg n
  have h3 := (window_nonneg hq1 hq2).1
  have h4 : 0 ≤ (1 - q ^ 2) / √(n : ℝ) := div_nonneg h3 (Real.sqrt_nonneg _)
  have h5 : 0 ≤ m4c n q := Real.sqrt_nonneg _
  unfold dQ1
  positivity

/-- **The program with the mean-field centre of `A` (one product with `A₂`; the first-layer
mean is an oracle) succeeds**: for every `n ≥ 4096`,
`Pr_{W, A, F}(|gOutB − B| ≤ sd/2) ≥ 1 − (1835/n + 130287/(n√n) + 5368347/n²)`. -/
theorem onePassA149 (hn : 4096 ≤ n) :
    1 - (1835 / (n : ℝ) + 130287 / ((n : ℝ) * √(n : ℝ)) + 5368347 / (n : ℝ) ^ 2) ≤
      (mlpTriple 2 n).real (okOutB149 n) := by
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hst : √(n : ℝ) = 1 / t := by rw [ht]; field_simp
  have hnt : (n : ℝ) = 1 / t ^ 2 := by
    rw [ht, div_pow, one_pow, Real.sq_sqrt hx0.le]; field_simp
  have ht2 : t ^ 2 = 1 / (n : ℝ) := by rw [hnt]; field_simp
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmA6 : 1000000 ≤ mA n := by
    unfold mA
    calc 1000000 ≤ 4096 ^ 2 := by norm_num
      _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
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
    refine (dK2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hΔX : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dX2 n (mA n) q ≤ 16034 / 100000 * t + 11363 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dX2_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hdQ : ∀ q : ℝ, 462 / 1000 ≤ q → q ≤ 527 / 1000 →
      dQ1 n (mA n) q ≤ 534859 / 1000000 * t + 12510 / 1000 * t ^ 2 := by
    intro q hq1 hq2
    refine (dQ1_le hn hq1 hq2).trans (le_of_eq ?_)
    rw [ht2, ht]; ring
  have hP : POK2 (6662 / 10000) (6969 / 10000) (284 / 10000) (635 / 10000) (12522 / 10000)
      (1908 / 1000) (273 / 1000) (251 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hP3 : POK3 (6969 / 10000) (284 / 10000) (9 / 100) (1 / 10) (88 / 100) (67 / 1000)
      (8517 / 10000) (8441 / 10000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num⟩
  have h := onePassA149_formula hn hP hP3 (ζ₃ := 9 / 100) (by norm_num) (η₃ := 31 / 100)
    (by norm_num) (dQb := 534859 / 1000000 * t + 12510 / 1000 * t ^ 2) hdQ
    (fun q hq1 hq2 => dQ1_nonneg hq1 hq2 hn1)
    (η := 51 / 10) (by norm_num) (ζ := 56 / 1000)
    (by norm_num) (ζ₂ := 1 / 10) (by norm_num) (η₁ := 24) (by norm_num) (θ := 95 / 100)
    (by norm_num) (by norm_num) (ΔKb := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2)
    (ΔXb := 16034 / 100000 * t + 11363 / 1000 * t ^ 2) (by positivity) (by positivity) hΔK
    (fun q hq1 hq2 => dK2_nonneg hq1 hq2 hn1) hΔX (fun q _ _ => dX2_nonneg hn1) hcF
  refine le_trans ?_ h
  rw [pFail3_eq (by norm_num) (by norm_num) (by norm_num) ht0 hnt hst]
  have e2 : (1835 : ℝ) / (n : ℝ) = 1835 * t ^ 2 := by rw [ht2]; ring
  have e3 : (130287 : ℝ) / ((n : ℝ) * √(n : ℝ)) = 130287 * t ^ 3 := by
    rw [hst, hnt]; field_simp
  have e4 : (5368347 : ℝ) / (n : ℝ) ^ 2 = 5368347 * t ^ 4 := by
    rw [hnt]; field_simp
  rw [e2, e3, e4]
  unfold EA2 kK2 kX2 kD2 cQ3 cD3 Kq
  have p2 : 0 < t ^ 2 := by positivity
  have p3 : 0 < t ^ 3 := by positivity
  have p4 : 0 < t ^ 4 := by positivity
  clear_value t
  ring_nf
  linarith

lemma pn3_le {n₀ : ℕ} (hn₀ : 0 < n₀) {s₀ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ^ 2 ≤ n₀)
    (hn : n₀ ≤ n) :
    1835 / (n : ℝ) + 130287 / ((n : ℝ) * √(n : ℝ)) + 5368347 / (n : ℝ) ^ 2 ≤
      1835 / (n₀ : ℝ) + 130287 / ((n₀ : ℝ) * s₀) + 5368347 / (n₀ : ℝ) ^ 2 := by
  have hx : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hsq : s₀ ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (hs.trans hx)
  have a2 : (1835 : ℝ) / (n : ℝ) ≤ 1835 / (n₀ : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hx0 hx
  have a3 : (130287 : ℝ) / ((n : ℝ) * √(n : ℝ)) ≤ 130287 / ((n₀ : ℝ) * s₀) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul hx hsq hs₀.le (by linarith))
  have a4 : (5368347 : ℝ) / (n : ℝ) ^ 2 ≤ 5368347 / (n₀ : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hx0.le hx 2)
  linarith

/-- Every `n ≥ 8192`: success probability at least `1/2`. -/
theorem onePassA149_8192 (hn : 8192 ≤ n) : 1 / 2 ≤ (mlpTriple 2 n).real (okOutB149 n) := by
  refine le_trans ?_ (onePassA149 (n := n) (by omega))
  have h := pn3_le (n := n) (n₀ := 8192) (by norm_num) (s₀ := 90) (by norm_num) (by norm_num) hn
  norm_num at h ⊢
  linarith

/-- Every `n ≥ 16384`: success probability at least `8/10`. -/
theorem onePassA149_16384 (hn : 16384 ≤ n) :
    8 / 10 ≤ (mlpTriple 2 n).real (okOutB149 n) := by
  refine le_trans ?_ (onePassA149 (n := n) (by omega))
  have h := pn3_le (n := n) (n₀ := 16384) (by norm_num) (s₀ := 128) (by norm_num) (by norm_num)
    hn
  norm_num at h ⊢
  linarith

/-- Level `99/100` for every `n ≥ 250 000` (outside the frontier interval). -/
theorem onePassA149_99 (hn : 250000 ≤ n) : 99 / 100 ≤ (mlpTriple 2 n).real (okOutB149 n) := by
  refine le_trans ?_ (onePassA149 (n := n) (by omega))
  have h := pn3_le (n := n) (n₀ := 250000) (by norm_num) (s₀ := 500) (by norm_num) (by norm_num)
    hn
  norm_num at h ⊢
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms onePassA149
open BstLean.Part149 in
#print axioms onePassA149_8192
open BstLean.Part149 in
#print axioms onePassA149_16384
open BstLean.Part149 in
#print axioms onePassA149_99
