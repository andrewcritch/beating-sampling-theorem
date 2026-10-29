import BstLean.Part143World

/-!
# Part 145, helper `world`: the numbers of `Part143World` again, for `n ≥ 9216 = 96²`

The lemmas `…16W` of `Part143World` with the hypothesis `9216 ≤ n` (`√n ≥ 96`); names `…WM`.

* **`tau143s_leM`**: `tau143s n ≤ 1.0809/√n`; `tau143_leM`: `tau143 n ≤ 1.1265/√n`.
* `sU2_WM` (`0.2398/√n`), `eWr2_WM` (`1.0327/√n`), `betaLin_WM` (`8.819/n`),
  `betaW_WM` (`0.0923/√n`), `eWsmall_WM` (`0.2714/√n`), `jCos_WM` (`0.2707/√n`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

section numM

variable {n : ℕ} (hn : 9216 ≤ n)

include hn

lemma nR_geWM : (9216 : ℝ) ≤ n := by exact_mod_cast hn

lemma sqrt_n_geWM : (96 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_geWM hn
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` for `n ≥ 9216`. -/
lemma yzWM : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ z ≤ 1 / 96 ∧ r ≤ 707107 / 1000000 * z ∧
    y = z * z ∧ y ≤ 1 / 96 * z := by
  have hx := nR_geWM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geWM hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 96 := one_div_le_one_div_of_le (by norm_num) hs
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

lemma K4_leWM : K4 n ≤ 34649 / 10000 := by
  have hx := nR_geWM hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 9216 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-- `sU(2n) ≤ 0.3614/√n` for `n ≥ 9216`. -/
lemma sU_WM : sU (2 * n) ≤ 3614 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 3614 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (17321 / 10000) / 2 * (1 / 96 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- The hidden layers of `W`: `eHid (m_W) ≤ (429/10⁶)/√n`, `√(epsW m_W) ≤ (102/10⁶)/√n` and
`epsW m_W ≤ (11/2³⁰)/n` (as `eHid_u` of Part 142). -/
lemma eHid_WM :
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

/-- `jCos n ≤ 0.2707/√n` for `n ≥ 9216`. -/
lemma jCos_WM : jCos n ≤ 2707 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have hK := K4_leWM hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (34649 / 10000) * (1 / 96 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  unfold jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y)) ?_
  · rw [hy]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 2707 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWsmall n m_W ≤ 0.2714/√n` for `n ≥ 9216`. -/
lemma eWsmall_WM : eWsmall n (mW n) ≤ 2714 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  obtain ⟨hH, hE, -⟩ := eHid_WM hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hJ := jCos_WM hn
  have eJ : (2707 : ℝ) / 10000 / √(n : ℝ) = 2707 / 10000 * z := by rw [hz]; ring
  rw [eJ] at hJ
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 96) * (429 / 1000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall
  refine le_trans (le_of_eq (?_ : _ = jCos n + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 2714 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWr(2n, n, m_W) ≤ 1.0352/√n` for `n ≥ 9216`. -/
lemma eWr_WM : eWr (2 * n) n (mW n) ≤ 10352 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have h1 := sU_WM hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall_WM hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (3614 : ℝ) / 10000 / √(n : ℝ) = 3614 / 10000 * z := by rw [hz]; ring
  have e2 : (2714 : ℝ) / 10000 / √(n : ℝ) = 2714 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU (2 * n) ≤ 3614 / 10000 / 96 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (3614 / 10000 / 96)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 10352 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- `betaLin n ≤ 8.819/n` for `n ≥ 9216`. -/
lemma betaLin_WM : betaLin n ≤ 8819 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have hK := K4_leWM hn
  have hK0 := K4_nonneg n
  have hJ := jCos_WM hn
  have hJ0 : 0 ≤ jCos n := by unfold jCos; positivity
  have eJ : (2707 : ℝ) / 10000 / √(n : ℝ) = 2707 / 10000 * z := by rw [hz]; ring
  rw [eJ] at hJ
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have a1 : 2 * K4 n * y ≤ 2 * (34649 / 10000) * y :=
    mul_le_mul_of_nonneg_right (by linarith) hy0.le
  have a2 : z + jCos n ≤ 12707 / 10000 * z := by linarith
  have a3 : √2 * z + 2 * K4 n * y ≤ 14865 / 10000 * z := by
    have b1 : √2 * z ≤ 141422 / 100000 * z := mul_le_mul_of_nonneg_right h2 hz0.le
    have b2 : 2 * K4 n * y ≤ 2 * (34649 / 10000) * (1 / 96 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith
  have a4 : (z + jCos n) * (√2 * z + 2 * K4 n * y) ≤
      12707 / 10000 * z * (14865 / 10000 * z) :=
    mul_le_mul a2 a3 (by positivity) (by positivity)
  unfold betaLin
  refine le_trans (le_of_eq (?_ : _ = 2 * K4 n * y +
    (z + jCos n) * (√2 * z + 2 * K4 n * y))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 8819 / 1000 * y) (le_of_eq (by rw [hy]; ring))
    have e : 12707 / 10000 * z * (14865 / 10000 * z) =
        12707 / 10000 * (14865 / 10000) * y := by
      rw [hyz]; ring
    rw [e] at a4
    linarith

/-- `betaW n m_W ≤ 0.0923/√n` for `n ≥ 9216` (`betaLin` is `≤ 8.819/n`; the bound of the
hidden layers `eHid` is stated with `1/√n`). -/
lemma betaW_WM : betaW n (mW n) ≤ 923 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  obtain ⟨hH, -, hE⟩ := eHid_WM hn
  have hB := betaLin_WM hn
  have eB : (8819 : ℝ) / 1000 / (n : ℝ) = 8819 / 1000 * y := by rw [hy]; ring
  rw [eB] at hB
  rw [← hz] at hH
  rw [← hy] at hE
  unfold betaW
  refine le_trans (?_ : _ ≤ 923 / 10000 * z) (le_of_eq (by rw [hz]; ring))
  linarith

/-- **`tau143 n ≤ 1.1265/√n`** for `n ≥ 9216`. -/
theorem tau143_leM : tau143 n ≤ 11265 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have h1 := eWr_WM hn
  have h2 := sU_WM hn
  have h3 := betaW_WM hn
  have e1 : (10352 : ℝ) / 10000 / √(n : ℝ) = 10352 / 10000 * z := by rw [hz]; ring
  have e2 : (3614 : ℝ) / 10000 / √(n : ℝ) = 3614 / 10000 * z := by rw [hz]; ring
  have e3 : (923 : ℝ) / 10000 / √(n : ℝ) = 923 / 10000 * z := by rw [hz]; ring
  have e4 : (11265 : ℝ) / 10000 / √(n : ℝ) = 11265 / 10000 * z := by rw [hz]; ring
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
  have p1 : eWr (2 * n) n (mW n) ^ 2 ≤ (10352 / 10000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU (2 * n) ^ 2 ≤ (3614 / 10000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU (2 * n) * betaW n (mW n) ≤ 3614 / 10000 * z * (923 / 10000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end numM

section numM2

variable {n : ℕ} (hn : 9216 ≤ n)

include hn

/-- `sU2(2n) ≤ 0.2398/√n` for `n ≥ 9216`. -/
lemma sU2_WM : sU2 (2 * n) ≤ 2398 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU2
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 8 / 25 * r + 149024 / 100000 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 2398 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 149024 / 100000 * √3 / 2 * y ≤
        149024 / 100000 * (17321 / 10000) / 2 * (1 / 96 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- `eWr2(2n, n, m_W) ≤ 1.0327/√n` for `n ≥ 9216`. -/
lemma eWr2_WM : eWr2 (2 * n) n (mW n) ≤ 10327 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have h1 := sU2_WM hn
  have h10 := sU2_nonneg (2 * n)
  have h2 := eWsmall_WM hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (2398 : ℝ) / 10000 / √(n : ℝ) = 2398 / 10000 * z := by rw [hz]; ring
  have e2 : (2714 : ℝ) / 10000 / √(n : ℝ) = 2714 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU2 (2 * n) ≤ 2398 / 10000 / 96 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (2398 / 10000 / 96)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr2
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 10327 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- **`tau143s n ≤ 1.0809/√n`** for `n ≥ 9216`. -/
theorem tau143s_leM : tau143s n ≤ 10809 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzWM hn
  have h1 := eWr2_WM hn
  have h2 := sU2_WM hn
  have h3 := betaW_WM hn
  have e1 : (10327 : ℝ) / 10000 / √(n : ℝ) = 10327 / 10000 * z := by rw [hz]; ring
  have e2 : (2398 : ℝ) / 10000 / √(n : ℝ) = 2398 / 10000 * z := by rw [hz]; ring
  have e3 : (923 : ℝ) / 10000 / √(n : ℝ) = 923 / 10000 * z := by rw [hz]; ring
  have e4 : (10809 : ℝ) / 10000 / √(n : ℝ) = 10809 / 10000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have hs0 := sU2_nonneg (2 * n)
  have hb0 := betaW_nonneg n (mW n)
  have hw0 := eWr2_nonneg (2 * n) n (mW n)
  unfold tau143s
  refine sqrt_le_of_sq (by positivity) ?_
  have p1 : eWr2 (2 * n) n (mW n) ^ 2 ≤ (10327 / 10000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU2 (2 * n) ^ 2 ≤ (2398 / 10000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU2 (2 * n) * betaW n (mW n) ≤ 2398 / 10000 * z * (923 / 10000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end numM2

end BstLean.Part145

open BstLean.Part145 in
#print axioms tau143s_leM
open BstLean.Part145 in
#print axioms tau143_leM
open BstLean.Part145 in
#print axioms sU2_WM
open BstLean.Part145 in
#print axioms eWr2_WM
open BstLean.Part145 in
#print axioms betaW_WM
