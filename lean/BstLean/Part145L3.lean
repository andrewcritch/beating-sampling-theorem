import BstLean.Part145L2

/-!
# Part 145 (pointwise frame constant), file 3: the numbers

Bounds of `lam0 s n`, `rho1 s n`, `r2 ε₁ ε₂ n` for every `n ≥ n₀ ≥ 4096`, from rational
certificates (as `frameB_num` of Part 140): `1 ≤ r₀²·n₀³` (thus `n²/m_W ≤ r₀`),
`15/(8n₀) ≤ k₆²`, `0.372·22.35·r₀ ≤ kK²`, `77.94·r₀ ≤ kD²`.

* `ncDet_le`: `n·cDet n ≤ 3017/20000 + 0.138/(2n₀) + 0.001·(17321/20000) + 0.4·k₆`.
* `lam0_le`: `lam0 s n ≤ (3017/20000 + 0.138/(2n₀) + 0.001·(17321/20000) + 0.4·k₆ + 4/25)/s`.
* `rho1_le`: `rho1 s n ≤ (kK + kD)/s`.
* `r2_le`: `r2 ε₁ ε₂ n ≤ (4.465/ε₂² + 0.448·22.35/ε₁²)·r₀/n`; `r2_le0`: the same with `r₀/n₀`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142
open BstLean.Part143

/-- `n·cDet n ≤ 3017/20000 + 0.138/(2n₀) + 0.001·(17321/20000) + 0.4·k₆` for `n ≥ n₀ ≥ 1`. -/
lemma ncDet_le {n n0 : ℕ} (hn0 : 1 ≤ n0) (hn : n0 ≤ n) {k6 : ℝ} (hk60 : 0 ≤ k6)
    (hk6 : 15 / (8 * (n0 : ℝ)) ≤ k6 ^ 2) :
    (n : ℝ) * cDet n ≤ 3017 / 20000 + 138 / 1000 / (2 * (n0 : ℝ)) +
      1 / 1000 * (17321 / 20000) + 2 / 5 * k6 := by
  have hn0' : (1 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0pos : (0 : ℝ) < n0 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have s3 := Part136.sqrt3_le
  have s30 : 0 ≤ √3 := Real.sqrt_nonneg _
  have hne6 := n_e6_le hn0pos hn' hk60 hk6
  unfold cDet
  rw [hNcast]
  have e : (n : ℝ) * (3017 / 10000 / (2 * (n : ℝ)) +
      138 / 1000 * (2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2))) + 1 / 1000 * (√3 / (2 * (n : ℝ))) +
      2 / 5 * √(15 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 4)))) =
      3017 / 20000 + 138 / 1000 * (1 / (2 * (n : ℝ) + 2)) + 1 / 1000 * (√3 / 2) +
        2 / 5 * ((n : ℝ) * √(15 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 4)))) := by
    field_simp
    ring
  rw [e]
  have h2 : 138 / 1000 * (1 / (2 * (n : ℝ) + 2)) ≤ 138 / 1000 / (2 * (n0 : ℝ)) := by
    rw [div_eq_mul_one_div (138 / 1000 : ℝ) (2 * (n0 : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h3 : 1 / 1000 * (√3 / 2) ≤ 1 / 1000 * (17321 / 20000) :=
    mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have h4 := mul_le_mul_of_nonneg_left hne6 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  linarith

/-- **The constant part**: `lam0 s n ≤ (3017/20000 + 0.138/(2n₀) + 0.001·(17321/20000) +
0.4·k₆ + 4/25)/s` for `n ≥ n₀ ≥ 1`. -/
theorem lam0_le {n n0 : ℕ} (hn0 : 1 ≤ n0) (hn : n0 ≤ n) {s k6 : ℝ} (hs : 0 < s)
    (hk60 : 0 ≤ k6) (hk6 : 15 / (8 * (n0 : ℝ)) ≤ k6 ^ 2) :
    lam0 s n ≤ (3017 / 20000 + 138 / 1000 / (2 * (n0 : ℝ)) + 1 / 1000 * (17321 / 20000) +
      2 / 5 * k6 + 4 / 25) / s := by
  have h1 := ncDet_le hn0 hn hk60 hk6
  have h2 := nd0_le (n := n) (by omega)
  unfold lam0
  refine div_le_div_of_nonneg_right ?_ hs.le
  rw [mul_add]
  linarith

/-- **The fluctuating part**: `rho1 s n ≤ (kK + kD)/s` for `n ≥ n₀ ≥ 4096`, with
`0.372·22.35·r₀ ≤ kK²` and `77.94·r₀ ≤ kD²`. -/
theorem rho1_le {n n0 : ℕ} (hn0 : 4096 ≤ n0) (hn : n0 ≤ n) {s r0 kK kD : ℝ} (hs : 0 < s)
    (hr0 : 0 ≤ r0) (hr : 1 ≤ r0 ^ 2 * (n0 : ℝ) ^ 3)
    (hkK0 : 0 ≤ kK) (hkK : 372 / 1000 * (2235 / 100 * r0) ≤ kK ^ 2)
    (hkD0 : 0 ≤ kD) (hkD : 7794 / 100 * r0 ≤ kD ^ 2) :
    rho1 s n ≤ (kK + kD) / s := by
  have hn4 : 4096 ≤ n := hn0.trans hn
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn4
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn4
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hrat := ratio_le (by omega : 1 ≤ n0) hn hr0 hr
  have hcF2 := cF2o_sq_le hmM
  have hcD2 := cDst143s_sq_le hn4
  have a1 : (n : ℝ) * √(372 / 1000) * cF2o (mW n) ≤ kK := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hkK0)
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have h1 : (n : ℝ) ^ 2 * (372 / 1000) * cF2o (mW n) ^ 2 ≤
        (n : ℝ) ^ 2 * (372 / 1000) * (2235 / 100 / (mW n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcF2 (by positivity)
    have e : (n : ℝ) ^ 2 * (372 / 1000) * (2235 / 100 / (mW n : ℝ)) =
        372 / 1000 * (2235 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ))) := by ring
    rw [e] at h1
    have h2 : 372 / 1000 * (2235 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ))) ≤
        372 / 1000 * (2235 / 100 * r0) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrat (by norm_num)) (by norm_num)
    linarith
  have a2 : (n : ℝ) * cDst143s (2 * n) (mW n) ≤ kD := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hkD0)
    rw [mul_pow]
    have h1 : (n : ℝ) ^ 2 * cDst143s (2 * n) (mW n) ^ 2 ≤
        (n : ℝ) ^ 2 * (7794 / 100 / (mW n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcD2 (sq_nonneg _)
    have e : (n : ℝ) ^ 2 * (7794 / 100 / (mW n : ℝ)) =
        7794 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
    rw [e] at h1
    have h2 : 7794 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) ≤ 7794 / 100 * r0 :=
      mul_le_mul_of_nonneg_left hrat (by norm_num)
    linarith
  unfold rho1
  exact div_le_div_of_nonneg_right (add_le_add a1 a2) hs.le

/-- **The capped part**: `r2 ε₁ ε₂ n ≤ (4.465/ε₂² + 0.448·22.35/ε₁²)·r₀/n` for
`n ≥ n₀ ≥ 4096`. -/
theorem r2_le {n n0 : ℕ} (hn0 : 4096 ≤ n0) (hn : n0 ≤ n) (ε₁ ε₂ : ℝ) {r0 : ℝ}
    (hr0 : 0 ≤ r0) (hr : 1 ≤ r0 ^ 2 * (n0 : ℝ) ^ 3) :
    r2 ε₁ ε₂ n ≤
      (4465 / 1000 / ε₂ ^ 2 + 448 / 1000 * (2235 / 100) / ε₁ ^ 2) * r0 / (n : ℝ) := by
  have hn4 : 4096 ≤ n := hn0.trans hn
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn4
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn4
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hrat := ratio_le (by omega : 1 ≤ n0) hn hr0 hr
  have hcF2 := cF2o_sq_le hmM
  have hcH2 := cHat143_sq_le (N := 2 * n) (m := mW n) (by omega) hmM
  -- `1/m ≤ r₀/n²`
  have hinv : 1 / (mW n : ℝ) ≤ r0 / (n : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    refine le_trans (le_of_eq ?_) hrat
    ring
  have b1 : cHat143 (2 * n) (mW n) ^ 2 / ε₂ ^ 2 ≤ 4465 / 1000 * (r0 / (n : ℝ) ^ 2) / ε₂ ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    refine hcH2.trans ?_
    rw [div_eq_mul_one_div (4465 / 1000 : ℝ) (mW n : ℝ)]
    exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  have b2 : 448 / 1000 * cF2o (mW n) ^ 2 / ε₁ ^ 2 ≤
      448 / 1000 * (2235 / 100 * (r0 / (n : ℝ) ^ 2)) / ε₁ ^ 2 := by
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine hcF2.trans ?_
    rw [div_eq_mul_one_div (2235 / 100 : ℝ) (mW n : ℝ)]
    exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  unfold r2
  have h3 := mul_le_mul_of_nonneg_left (add_le_add b1 b2) hnpos.le
  refine h3.trans (le_of_eq ?_)
  field_simp

/-- The capped part with `r₀/n₀`. -/
theorem r2_le0 {n n0 : ℕ} (hn0 : 4096 ≤ n0) (hn : n0 ≤ n) (ε₁ ε₂ : ℝ) {r0 : ℝ}
    (hr0 : 0 ≤ r0) (hr : 1 ≤ r0 ^ 2 * (n0 : ℝ) ^ 3) :
    r2 ε₁ ε₂ n ≤
      (4465 / 1000 / ε₂ ^ 2 + 448 / 1000 * (2235 / 100) / ε₁ ^ 2) * r0 / (n0 : ℝ) := by
  have hn0' : (4096 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  refine (r2_le hn0 hn ε₁ ε₂ hr0 hr).trans ?_
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) hn'

end BstLean.Part145

open BstLean.Part145 in
#print axioms Gwin_compl
open BstLean.Part145 in
#print axioms frameLfX
open BstLean.Part145 in
#print axioms LfX_DKV_mean
open BstLean.Part145 in
#print axioms ncDet_le
open BstLean.Part145 in
#print axioms lam0_le
open BstLean.Part145 in
#print axioms rho1_le
open BstLean.Part145 in
#print axioms r2_le
open BstLean.Part145 in
#print axioms r2_le0
