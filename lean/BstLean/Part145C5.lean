import BstLean.Part145C3

/-!
# Part 145, helper `Part145C5`: the numbers of the World chain with `jCosC`, for `n ≥ 4096 = 64²`

The pattern is the pattern of `Part145WorldM` (made by `gen_c4.py` with the threshold `4096`);
names `…CR`.

* **`tau143sC_leR`**: `tau143sC n ≤ 0.90734/√n`.
* `jCosC_CR` (`4.47439/n`), `eWsmallC_CR` (`0.0705588/√n`), `sU2_CR` (`0.2464403/√n`),
  `eWr2_CR` (`eWr2C ≤ 0.8345007/√n`), `betaLinC_CR` (`8.56056/n`), `betaWC_CR` (`0.1341878/√n`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

section numCR

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

lemma nR_geCR : (4096 : ℝ) ≤ n := by exact_mod_cast hn

lemma sqrt_n_geCR : (64 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_geCR hn
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` for `n ≥ 4096`. -/
lemma yzCR : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ z ≤ 1 / 64 ∧ r ≤ 707107 / 1000000 * z ∧
    y = z * z ∧ y ≤ 1 / 64 * z := by
  have hx := nR_geCR hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geCR hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) hs
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

lemma K4_leCR : K4 n ≤ 3465793 / 1000000 := by
  have hx := nR_geCR hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-- The hidden layers of `W`: `eHid (m_W) ≤ (429/10⁶)/√n`, `√(epsW m_W) ≤ (102/10⁶)/√n` and
`epsW m_W ≤ (11/2³⁰)/n` (as `eHid_u` of Part 142). -/
lemma eHid_CR :
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

/-- `jCosC n ≤ 4.47439/n` for `n ≥ 4096`. -/
lemma jCosC_CR : jCosC n ≤ 447439 / 100000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hx := nR_geCR hn
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have h2 := Part133.sqrt2_le
  have h20 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hK0 := K4_nonneg n
  have hK := K4_leCR hn
  have hQ0 := qCos_nonneg n
  have hQ : qCos n ≤ 4121434 / 100000 * y ^ 2 := by
    have e1 : 1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3 =
        1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3 := by rw [hy]; ring
    have e : qCos n = √(1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3) * y ^ 2 := by
      unfold qCos
      rw [e1, hy]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right (sqrt_le_of_sq (by norm_num) ?_) (by positivity)
    have a1 : y ^ 2 ≤ (1 / 4096) ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    have a2 : y ^ 3 ≤ (1 / 4096) ^ 3 := pow_le_pow_left₀ hy0.le hy1 3
    norm_num at a1 a2 ⊢
    linarith
  have eK : K4 n / (n : ℝ) = K4 n * y := by rw [hy]; ring
  unfold jCosC
  rw [eK]
  have hKy : K4 n * y ≤ 3465793 / 1000000 * y := mul_le_mul_of_nonneg_right hK hy0.le
  have hKy0 : 0 ≤ K4 n * y := by positivity
  have hsQ : √2 * qCos n ≤ 141422 / 100000 * (4121434 / 100000 * y ^ 2) :=
    mul_le_mul h2 hQ hQ0 (by norm_num)
  have hsQ0 : 0 ≤ √2 * qCos n := by positivity
  have hsK : √2 * (K4 n * y) ≤ 141422 / 100000 * (3465793 / 1000000 * y) :=
    mul_le_mul h2 hKy hKy0 (by norm_num)
  have hsK0 : 0 ≤ √2 * (K4 n * y) := by positivity
  have hy3 : y ^ 3 = (y * z) ^ 2 := by rw [hyz]; ring
  have t3 : √(K4 n * y * (√2 * qCos n)) ≤ 142130 / 10000 * (y * z) := by
    refine sqrt_le_of_sq (by positivity) ?_
    have := mul_le_mul hKy hsQ hsQ0 (by positivity)
    refine this.trans ?_
    have e : 3465793 / 1000000 * y * (141422 / 100000 * (4121434 / 100000 * y ^ 2)) =
        3465793 / 1000000 * (141422 / 100000) * (4121434 / 100000) * y ^ 3 := by ring
    rw [e, mul_pow, ← hy3]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have t4 : √(√2 * (K4 n * y) * (√2 * qCos n)) ≤ 169022 / 10000 * (y * z) := by
    refine sqrt_le_of_sq (by positivity) ?_
    have := mul_le_mul hsK hsQ hsQ0 (by positivity)
    refine this.trans ?_
    have e : 141422 / 100000 * (3465793 / 1000000 * y) *
        (141422 / 100000 * (4121434 / 100000 * y ^ 2)) =
        141422 / 100000 * (3465793 / 1000000) * (141422 / 100000) *
          (4121434 / 100000) * y ^ 3 := by ring
    rw [e, mul_pow, ← hy3]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hyzs : y * z ≤ y * (1 / 64) := mul_le_mul_of_nonneg_left hz1 hy0.le
  have hy2 : y ^ 2 ≤ y * (1 / 4096) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hy1 hy0.le
  refine le_trans (?_ : _ ≤ 447439 / 100000 * y) (le_of_eq (by rw [hy]; ring))
  linarith

/-- `eWsmallC n m_W ≤ 0.0705588/√n` for `n ≥ 4096`. -/
lemma eWsmallC_CR : eWsmallC n (mW n) ≤ 705588 / 10000000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  obtain ⟨hH, hE, -⟩ := eHid_CR hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hJ := jCosC_CR hn
  have eJ : (447439 / 100000 : ℝ) / (n : ℝ) = 447439 / 100000 * y := by rw [hy]; ring
  rw [eJ] at hJ
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 64) * (429 / 1000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmallC
  refine le_trans (le_of_eq (?_ : _ = jCosC n + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hz]; ring
  · refine le_trans (?_ : _ ≤ 705588 / 10000000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `sU2(2n) ≤ 0.2464403/√n` for `n ≥ 4096`. -/
lemma sU2_CR : sU2 (2 * n) ≤ 2464403 / 10000000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU2
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 8 / 25 * r + 149024 / 100000 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 2464403 / 10000000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 149024 / 100000 * √3 / 2 * y ≤
        149024 / 100000 * (17321 / 10000) / 2 * (1 / 64 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

/-- `eWr2C(2n, n, m_W) ≤ 0.8345007/√n` for `n ≥ 4096`. -/
lemma eWr2_CR : eWr2C (2 * n) n (mW n) ≤ 8345007 / 10000000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have h1 := sU2_CR hn
  have h10 := sU2_nonneg (2 * n)
  have h2 := eWsmallC_CR hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e1 : (2464403 / 10000000 : ℝ) / √(n : ℝ) = 2464403 / 10000000 * z := by rw [hz]; ring
  have e2 : (705588 / 10000000 : ℝ) / √(n : ℝ) = 705588 / 10000000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  have h1' : sU2 (2 * n) ≤ 2464403 / 10000000 / 64 := by linarith
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (2464403 / 10000000 / 64)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr2C
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU2 (2 * n)) +
    eWsmallC n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 8345007 / 10000000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `betaLinC n ≤ 8.56056/n` for `n ≥ 4096`. -/
lemma betaLinC_CR : betaLinC n ≤ 856056 / 100000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hK := K4_leCR hn
  have hK0 := K4_nonneg n
  have hJ := jCosC_CR hn
  have hJ0 : 0 ≤ jCosC n := jCosC_nonneg n
  have eJ : (447439 / 100000 : ℝ) / (n : ℝ) = 447439 / 100000 * y := by rw [hy]; ring
  rw [eJ] at hJ
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have a1 : 2 * K4 n * y ≤ 2 * (3465793 / 1000000) * y :=
    mul_le_mul_of_nonneg_right (by linarith) hy0.le
  have a2 : z + jCosC n ≤ 6847439 / 6400000 * z := by linarith
  have a3 : √2 * z + 2 * K4 n * y ≤ 48720833 / 32000000 * z := by
    have b1 : √2 * z ≤ 141422 / 100000 * z := mul_le_mul_of_nonneg_right h2 hz0.le
    have b2 : 2 * K4 n * y ≤ 2 * (3465793 / 1000000) * (1 / 64 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith
  have a4 : (z + jCosC n) * (√2 * z + 2 * K4 n * y) ≤
      6847439 / 6400000 * z * (48720833 / 32000000 * z) :=
    mul_le_mul a2 a3 (by positivity) (by positivity)
  unfold betaLinC
  refine le_trans (le_of_eq (?_ : _ = 2 * K4 n * y +
    (z + jCosC n) * (√2 * z + 2 * K4 n * y))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 856056 / 100000 * y) (le_of_eq (by rw [hy]; ring))
    have e : 6847439 / 6400000 * z * (48720833 / 32000000 * z) =
        6847439 / 6400000 * (48720833 / 32000000) * y := by
      rw [hyz]; ring
    rw [e] at a4
    linarith

/-- `betaWC n m_W ≤ 0.1341878/√n` for `n ≥ 4096`. -/
lemma betaWC_CR : betaWC n (mW n) ≤ 1341878 / 10000000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  obtain ⟨hH, -, hE⟩ := eHid_CR hn
  have hB := betaLinC_CR hn
  have eB : (856056 / 100000 : ℝ) / (n : ℝ) = 856056 / 100000 * y := by rw [hy]; ring
  rw [eB] at hB
  rw [← hz] at hH
  rw [← hy] at hE
  unfold betaWC
  refine le_trans (?_ : _ ≤ 1341878 / 10000000 * z) (le_of_eq (by rw [hz]; ring))
  linarith

/-- **`tau143sC n ≤ 0.90734/√n`** for `n ≥ 4096`. -/
theorem tau143sC_leR : tau143sC n ≤ 90734 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have h1 := eWr2_CR hn
  have h2 := sU2_CR hn
  have h3 := betaWC_CR hn
  have e1 : (8345007 / 10000000 : ℝ) / √(n : ℝ) = 8345007 / 10000000 * z := by rw [hz]; ring
  have e2 : (2464403 / 10000000 : ℝ) / √(n : ℝ) = 2464403 / 10000000 * z := by rw [hz]; ring
  have e3 : (1341878 / 10000000 : ℝ) / √(n : ℝ) = 1341878 / 10000000 * z := by rw [hz]; ring
  have e4 : (90734 / 100000 : ℝ) / √(n : ℝ) = 90734 / 100000 * z := by rw [hz]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have hs0 := sU2_nonneg (2 * n)
  have hb0 := betaWC_nonneg n (mW n)
  have hw0 := eWr2C_nonneg (2 * n) n (mW n)
  unfold tau143sC
  refine sqrt_le_of_sq (by positivity) ?_
  have p1 : eWr2C (2 * n) n (mW n) ^ 2 ≤ (8345007 / 10000000 * z) ^ 2 := pow_le_pow_left₀ hw0 h1 2
  have p2 : sU2 (2 * n) ^ 2 ≤ (2464403 / 10000000 * z) ^ 2 := pow_le_pow_left₀ hs0 h2 2
  have p3 : sU2 (2 * n) * betaWC n (mW n) ≤ 2464403 / 10000000 * z * (1341878 / 10000000 * z) :=
    mul_le_mul h2 h3 hb0 (by positivity)
  nlinarith [sq_nonneg z]

end numCR

end BstLean.Part145

open BstLean.Part145 in
#print axioms lin_cos_L2c
open BstLean.Part145 in
#print axioms jCosC_le
open BstLean.Part145 in
#print axioms tX_L2_145C
open BstLean.Part145 in
#print axioms tau143sC_leR
