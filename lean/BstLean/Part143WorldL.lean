import BstLean.Part143World

/-!
# Part 143, helper `world`: the numbers of `Part143World` again, for `n ≥ 13225 = 115²`

The lemmas `…16W` of `Part143World` with the hypothesis `13225 ≤ n` (`√n ≥ 115`); names `…WL`.

* **`tau143s_leL`**: `tau143s n ≤ 1.0331/√n`; `tau143_leL`: `tau143 n ≤ 1.0791/√n`.
* `sU2_WL` (`0.2375/√n`), `eWr2_WL` (`0.9871/√n`), `betaLin_WL` (`8.738/n`),
  `betaW_WL` (`0.0765/√n`), `eWsmall_WL` (`0.2267/√n`), `jCos_WL` (`0.2260/√n`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142

section numL

variable {n : ℕ} (hn : 13225 ≤ n)

include hn

lemma nR_geWL : (13225 : ℝ) ≤ n := by exact_mod_cast hn

lemma sqrt_n_geWL : (115 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_geWL hn
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` for `n ≥ 13225`. -/
lemma yzWL : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ z ≤ 1 / 115 ∧ r ≤ 707107 / 1000000 * z ∧
    y = z * z ∧ y ≤ 1 / 115 * z := by
  have hx := nR_geWL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geWL hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 115 := one_div_le_one_div_of_le (by norm_num) hs
  have hyz : 1 / (n : ℝ) = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    hz0, by positivity, hz1, ?_, hyz, ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [hyz]
    exact mul_le_mul_of_nonneg_right hz1 hz0.le

lemma K4_leWL : K4 n ≤ 34647 / 10000 := by
  have hx := nR_geWL hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 13225 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-- `sU(2n) ≤ 0.3610/√n` for `n ≥ 13225`. -/
lemma sU_WL : sU (2 * n) ≤ 3610 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 3610 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (17321 / 10000) / 2 * (1 / 115 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- The hidden layers of `W`: `eHid (m_W) ≤ (429/10⁶)/√n`, `√(epsW m_W) ≤ (102/10⁶)/√n` and
`epsW m_W ≤ (11/2³⁰)/n` (as `eHid_u` of Part 142). -/
lemma eHid_WL :
    eHid (mW n) ≤ 429 / 1000000 * (1 / √(n : ℝ)) ∧
      √(epsW (mW n)) ≤ 102 / 1000000 * (1 / √(n : ℝ)) ∧
      epsW (mW n) ≤ 11 / 1073741824 * (1 / (n : ℝ)) := by
  have hn4 : 4096 ≤ n := by omega
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn4
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hε := epsW_scale hn4
  have hε0 := epsW_nonneg (mW n)
  have hsW := sqrt_mW_scale hn4
  have hsW0 : (0 : ℝ) < √(mW n : ℝ) := by nlinarith
  have hm := mW_geR hn4
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have s1 : √(5 * epsW (mW n)) ≤ 23 / 100000 * u := by
    have := sqrt_le_div_s hn4 (x := 5 * epsW (mW n)) (c := 23 / 100000) (by norm_num)
      (by nlinarith)
    rwa [div_eq_mul_one_div, ← hu] at this
  have s2 : √(epsW (mW n)) ≤ 102 / 1000000 * u := by
    have := sqrt_le_div_s hn4 (x := epsW (mW n)) (c := 102 / 1000000) (by norm_num)
      (by nlinarith)
    rwa [div_eq_mul_one_div, ← hu] at this
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have hiW : 1 / √(mW n : ℝ) ≤ 1 / 32768 * u := by
    rw [hu, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsW
  have hiW0 : 0 ≤ 1 / √(mW n : ℝ) := by positivity
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 32768 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 32768 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  refine ⟨?_, s2, ?_⟩
  · unfold eHid
    linarith
  · rw [mul_one_div, le_div_iff₀ hx0]
    exact hε

/-- `jCos n ≤ 0.2260/√n` for `n ≥ 13225`. -/
lemma jCos_WL : jCos n ≤ 2260 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have hK := K4_leWL hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (34647 / 10000) * (1 / 115 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  unfold jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y)) ?_
  · rw [hy]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 2260 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWsmall n m_W ≤ 0.2267/√n` for `n ≥ 13225`. -/
lemma eWsmall_WL : eWsmall n (mW n) ≤ 2267 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  obtain ⟨hH, hE, -⟩ := eHid_WL hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hJ := jCos_WL hn
  have eJ : (2260 : ℝ) / 10000 / √(n : ℝ) = 2260 / 10000 * z := by rw [hz]; ring
  rw [eJ] at hJ
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 115) * (429 / 1000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall
  refine le_trans (le_of_eq (?_ : _ = jCos n + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 2267 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWr(2n, n, m_W) ≤ 0.9893/√n` for `n ≥ 13225`. -/
lemma eWr_WL : eWr (2 * n) n (mW n) ≤ 9893 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have h1 := sU_WL hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall_WL hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (3610 : ℝ) / 10000 / √(n : ℝ) = 3610 / 10000 * z := by rw [hz]; ring
  have e2 : (2267 : ℝ) / 10000 / √(n : ℝ) = 2267 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU (2 * n) ≤ 3610 / 10000 / 115 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (3610 / 10000 / 115)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 9893 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- `betaLin n ≤ 8.738/n` for `n ≥ 13225`. -/
lemma betaLin_WL : betaLin n ≤ 8738 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have hK := K4_leWL hn
  have hK0 := K4_nonneg n
  have hJ := jCos_WL hn
  have hJ0 : 0 ≤ jCos n := by unfold jCos; positivity
  have eJ : (2260 : ℝ) / 10000 / √(n : ℝ) = 2260 / 10000 * z := by rw [hz]; ring
  rw [eJ] at hJ
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have a1 : 2 * K4 n * y ≤ 2 * (34647 / 10000) * y :=
    mul_le_mul_of_nonneg_right (by linarith) hy0.le
  have a2 : z + jCos n ≤ 12260 / 10000 * z := by linarith
  have a3 : √2 * z + 2 * K4 n * y ≤ 14745 / 10000 * z := by
    have b1 : √2 * z ≤ 141422 / 100000 * z := mul_le_mul_of_nonneg_right h2 hz0.le
    have b2 : 2 * K4 n * y ≤ 2 * (34647 / 10000) * (1 / 115 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith
  have a4 : (z + jCos n) * (√2 * z + 2 * K4 n * y) ≤
      12260 / 10000 * z * (14745 / 10000 * z) :=
    mul_le_mul a2 a3 (by positivity) (by positivity)
  unfold betaLin
  refine le_trans (le_of_eq (?_ : _ = 2 * K4 n * y +
    (z + jCos n) * (√2 * z + 2 * K4 n * y))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 8738 / 1000 * y) (le_of_eq (by rw [hy]; ring))
    have e : 12260 / 10000 * z * (14745 / 10000 * z) = 12260 / 10000 * (14745 / 10000) * y := by
      rw [hyz]; ring
    rw [e] at a4
    linarith

/-- `betaW n m_W ≤ 0.0765/√n` for `n ≥ 13225` (`betaLin` is `≤ 8.738/n`; the bound of the
hidden layers `eHid` is stated with `1/√n`). -/
lemma betaW_WL : betaW n (mW n) ≤ 765 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  obtain ⟨hH, -, hE⟩ := eHid_WL hn
  have hB := betaLin_WL hn
  have eB : (8738 : ℝ) / 1000 / (n : ℝ) = 8738 / 1000 * y := by rw [hy]; ring
  rw [eB] at hB
  rw [← hz] at hH
  rw [← hy] at hE
  unfold betaW
  refine le_trans (?_ : _ ≤ 765 / 10000 * z) (le_of_eq (by rw [hz]; ring))
  linarith

/-- **`tau143 n ≤ 1.0791/√n`** for `n ≥ 13225`. -/
theorem tau143_leL : tau143 n ≤ 10791 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have h1 := eWr_WL hn
  have h2 := sU_WL hn
  have h3 := betaW_WL hn
  have e1 : (9893 : ℝ) / 10000 / √(n : ℝ) = 9893 / 10000 * z := by rw [hz]; ring
  have e2 : (3610 : ℝ) / 10000 / √(n : ℝ) = 3610 / 10000 * z := by rw [hz]; ring
  have e3 : (765 : ℝ) / 10000 / √(n : ℝ) = 765 / 10000 * z := by rw [hz]; ring
  have e4 : (10791 : ℝ) / 10000 / √(n : ℝ) = 10791 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have hs0 := sU_nonneg (2 * n)
  have hb0 := betaW_nonneg n (mW n)
  have hq := q_mem
  have hq2 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq.1, hq.2]
  have hsm := eWsmall_nonneg n (mW n)
  have hw0 : 0 ≤ eWr (2 * n) n (mW n) := by unfold eWr; positivity
  unfold tau143
  refine sqrt_le_of_sq (by positivity) ?_
  have p1 : eWr (2 * n) n (mW n) ^ 2 ≤ (9893 / 10000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU (2 * n) ^ 2 ≤ (3610 / 10000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU (2 * n) * betaW n (mW n) ≤ 3610 / 10000 * z * (765 / 10000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end numL

section numL2

variable {n : ℕ} (hn : 13225 ≤ n)

include hn

/-- `sU2(2n) ≤ 0.2375/√n` for `n ≥ 13225`. -/
lemma sU2_WL : sU2 (2 * n) ≤ 2375 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU2
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 8 / 25 * r + 149024 / 100000 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 2375 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 149024 / 100000 * √3 / 2 * y ≤
        149024 / 100000 * (17321 / 10000) / 2 * (1 / 115 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- `eWr2(2n, n, m_W) ≤ 0.9871/√n` for `n ≥ 13225`. -/
lemma eWr2_WL : eWr2 (2 * n) n (mW n) ≤ 9871 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have h1 := sU2_WL hn
  have h10 := sU2_nonneg (2 * n)
  have h2 := eWsmall_WL hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (2375 : ℝ) / 10000 / √(n : ℝ) = 2375 / 10000 * z := by rw [hz]; ring
  have e2 : (2267 : ℝ) / 10000 / √(n : ℝ) = 2267 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU2 (2 * n) ≤ 2375 / 10000 / 115 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (2375 / 10000 / 115)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr2
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 9871 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- **`tau143s n ≤ 1.0331/√n`** for `n ≥ 13225`. -/
theorem tau143s_leL : tau143s n ≤ 10331 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWL hn
  have h1 := eWr2_WL hn
  have h2 := sU2_WL hn
  have h3 := betaW_WL hn
  have e1 : (9871 : ℝ) / 10000 / √(n : ℝ) = 9871 / 10000 * z := by rw [hz]; ring
  have e2 : (2375 : ℝ) / 10000 / √(n : ℝ) = 2375 / 10000 * z := by rw [hz]; ring
  have e3 : (765 : ℝ) / 10000 / √(n : ℝ) = 765 / 10000 * z := by rw [hz]; ring
  have e4 : (10331 : ℝ) / 10000 / √(n : ℝ) = 10331 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have hs0 := sU2_nonneg (2 * n)
  have hb0 := betaW_nonneg n (mW n)
  have hw0 := eWr2_nonneg (2 * n) n (mW n)
  unfold tau143s
  refine sqrt_le_of_sq (by positivity) ?_
  have p1 : eWr2 (2 * n) n (mW n) ^ 2 ≤ (9871 / 10000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU2 (2 * n) ^ 2 ≤ (2375 / 10000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU2 (2 * n) * betaW n (mW n) ≤ 2375 / 10000 * z * (765 / 10000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end numL2

end BstLean.Part143

open BstLean.Part143 in
#print axioms tau143s_leL
open BstLean.Part143 in
#print axioms tau143_leL
