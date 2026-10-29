import BstLean.Part149Final2

/-!
# Part 149, item 4, second route: the explicit failure probability of the idealized program

Do not use `sorry`, `native_decide` or `axiom`.

* `pFail2_eq`: the bound `pFail2` as a polynomial in `t = 1/√n`.
* **`twoStage149b`**: for every `n ≥ 4096`:
  `Pr(|gOutA − B| ≤ sd/2) ≥ 1 − (1052/n + 85938/(n√n) + 3366545/n²)`.
* `twoStage149b_4096` (`≥ 21/100`), `twoStage149b_8192` (`≥ 7/10`), `twoStage149b_16384`
  (`≥ 88/100`), `twoStage149b_99` (`≥ 99/100` for `n ≥ 160 000`).
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part141 BstLean.Part145

variable {n : ℕ}

lemma pFail2_eq {Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb t : ℝ} (hη₁ : η₁ ≠ 0)
    (hθ0 : θ ≠ 0) (hθ1 : 1 - θ ≠ 0) (ht : 0 < t) (hnt : (n : ℝ) = 1 / t ^ 2)
    (hst : √(n : ℝ) = 1 / t) :
    pFail2 n Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ η₁ θ ΔKb ΔXb δb =
      t ^ 2 / 50000 + 68 / 100 * t ^ 4 + ΔKb ^ 2 / Δmax ^ 2 + ΔXb ^ 2 / ΔXmax ^ 2 +
        ((1 + η₁) * (4849 / 20000 * 4) * t ^ 2 + (1 + 1 / η₁) *
          (2 * EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb)) /
          (θ * (222757 / 1000000)) +
        2 * (78728 / 100000) ^ 2 / (4 * θ * (1 - θ) * (222757 / 1000000) ^ 2) * t ^ 2 := by
  unfold pFail2
  rw [qA_cast, hst, hnt]
  generalize EA2 (6662 / 10000) Δmax ΔXmax r₁ r₂ w g η ζ ζ₂ ΔKb ΔXb δb = E
  generalize ΔKb ^ 2 / Δmax ^ 2 = u
  generalize ΔXb ^ 2 / ΔXmax ^ 2 = w'
  have ht' : t ≠ 0 := ht.ne'
  field_simp
  ring

lemma dK2_nonneg {q : ℝ} (hq1 : 462 / 1000 ≤ q) (hq2 : q ≤ 527 / 1000) (hn : 1 ≤ n) :
    0 ≤ dK2 n (mA n) q := by
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have h1 := (BstLean.Part136.cF2o_pos hmA).le
  have h2 := jCosC_nonneg n
  have h3 := (window_nonneg hq1 hq2).1
  have h4 : 0 ≤ (1 - q ^ 2) / √(n : ℝ) := div_nonneg h3 (Real.sqrt_nonneg _)
  have h5 : 0 ≤ m4c n q := Real.sqrt_nonneg _
  unfold dK2
  positivity

lemma dX2_nonneg {q : ℝ} (hn : 1 ≤ n) : 0 ≤ dX2 n (mA n) q := by
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have h1 := (BstLean.Part136.cF2o_pos hmA).le
  have h2 := jCosC_nonneg n
  have h5 : 0 ≤ m4c n q := Real.sqrt_nonneg _
  have h6 : 0 ≤ √(q * (1 - q) ^ 2 * (1 - q / 2) / (n : ℝ)) := Real.sqrt_nonneg _
  unfold dX2
  positivity

/-- **The idealized program with no forward pass of `A` at a sampled input (exact centre of
`A`) succeeds, rate `1/n`**: for every `n ≥ 4096`,
`Pr_{W, A, F}(|gOutA − B| ≤ sd/2) ≥ 1 − (1052/n + 85938/(n√n) + 3366545/n²)`. -/
theorem twoStage149b (hn : 4096 ≤ n) :
    1 - (1052 / (n : ℝ) + 85938 / ((n : ℝ) * √(n : ℝ)) + 3366545 / (n : ℝ) ^ 2) ≤
      (mlpTriple 2 n).real (okOut149 n) := by
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
  have hP : POK2 (6662 / 10000) (6969 / 10000) (335 / 10000) (536 / 10000) (12573 / 10000)
      (1926 / 1000) (272 / 1000) (247 / 1000) :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have h := twoStage149b_formula hn hP (η := 54 / 10) (by norm_num) (ζ := 64 / 1000)
    (by norm_num) (ζ₂ := 9 / 100) (by norm_num) (η₁ := 19) (by norm_num) (θ := 94 / 100)
    (by norm_num) (by norm_num) (ΔKb := 393278 / 1000000 * t + 11363 / 1000 * t ^ 2)
    (ΔXb := 16034 / 100000 * t + 11363 / 1000 * t ^ 2) (by positivity) (by positivity) hΔK
    (fun q hq1 hq2 => dK2_nonneg hq1 hq2 hn1) hΔX (fun q _ _ => dX2_nonneg hn1) hcF
  refine le_trans ?_ h
  rw [pFail2_eq (by norm_num) (by norm_num) (by norm_num) ht0 hnt hst]
  have e2 : (1052 : ℝ) / (n : ℝ) = 1052 * t ^ 2 := by rw [ht2]; ring
  have e3 : (85938 : ℝ) / ((n : ℝ) * √(n : ℝ)) = 85938 * t ^ 3 := by
    rw [hst, hnt]; field_simp
  have e4 : (3366545 : ℝ) / (n : ℝ) ^ 2 = 3366545 * t ^ 4 := by
    rw [hnt]; field_simp
  rw [e2, e3, e4]
  unfold EA2 kK2 kX2 kD2
  have p2 : 0 < t ^ 2 := by positivity
  have p3 : 0 < t ^ 3 := by positivity
  have p4 : 0 < t ^ 4 := by positivity
  clear_value t
  ring_nf
  linarith

lemma pn2_le {n₀ : ℕ} (hn₀ : 0 < n₀) {s₀ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ^ 2 ≤ n₀)
    (hn : n₀ ≤ n) :
    1052 / (n : ℝ) + 85938 / ((n : ℝ) * √(n : ℝ)) + 3366545 / (n : ℝ) ^ 2 ≤
      1052 / (n₀ : ℝ) + 85938 / ((n₀ : ℝ) * s₀) + 3366545 / (n₀ : ℝ) ^ 2 := by
  have hx : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hsq : s₀ ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (hs.trans hx)
  have a2 : (1052 : ℝ) / (n : ℝ) ≤ 1052 / (n₀ : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hx0 hx
  have a3 : (85938 : ℝ) / ((n : ℝ) * √(n : ℝ)) ≤ 85938 / ((n₀ : ℝ) * s₀) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul hx hsq hs₀.le (by linarith))
  have a4 : (3366545 : ℝ) / (n : ℝ) ^ 2 ≤ 3366545 / (n₀ : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hx0.le hx 2)
  linarith

/-- Every `n ≥ 4096` (the whole frontier interval): success probability at least `21/100`. -/
theorem twoStage149b_4096 (hn : 4096 ≤ n) : 21 / 100 ≤ (mlpTriple 2 n).real (okOut149 n) := by
  refine le_trans ?_ (twoStage149b hn)
  have h := pn2_le (n := n) (n₀ := 4096) (by norm_num) (s₀ := 64) (by norm_num) (by norm_num) hn
  norm_num at h ⊢
  linarith

/-- Every `n ≥ 8192`: success probability at least `7/10`. -/
theorem twoStage149b_8192 (hn : 8192 ≤ n) : 7 / 10 ≤ (mlpTriple 2 n).real (okOut149 n) := by
  refine le_trans ?_ (twoStage149b (n := n) (by omega))
  have h := pn2_le (n := n) (n₀ := 8192) (by norm_num) (s₀ := 90) (by norm_num) (by norm_num) hn
  norm_num at h ⊢
  linarith

/-- Every `n ≥ 16384`: success probability at least `88/100`. -/
theorem twoStage149b_16384 (hn : 16384 ≤ n) :
    88 / 100 ≤ (mlpTriple 2 n).real (okOut149 n) := by
  refine le_trans ?_ (twoStage149b (n := n) (by omega))
  have h := pn2_le (n := n) (n₀ := 16384) (by norm_num) (s₀ := 128) (by norm_num) (by norm_num)
    hn
  norm_num at h ⊢
  linarith

/-- Level `99/100` for every `n ≥ 160 000` (outside the frontier interval). -/
theorem twoStage149b_99 (hn : 160000 ≤ n) : 99 / 100 ≤ (mlpTriple 2 n).real (okOut149 n) := by
  refine le_trans ?_ (twoStage149b (n := n) (by omega))
  have h := pn2_le (n := n) (n₀ := 160000) (by norm_num) (s₀ := 400) (by norm_num) (by norm_num)
    hn
  norm_num at h ⊢
  linarith

end BstLean.Part149

open BstLean.Part149 in
#print axioms twoStage149b
open BstLean.Part149 in
#print axioms twoStage149b_4096
open BstLean.Part149 in
#print axioms twoStage149b_8192
open BstLean.Part149 in
#print axioms twoStage149b_16384
open BstLean.Part149 in
#print axioms twoStage149b_99
