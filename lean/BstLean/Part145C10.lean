import BstLean.Part145C5
import BstLean.Part145C9

/-!
# Part 145, helper `Part145C10`: the numbers of `m4C` and `pWC` for `n ≥ 4096 = 64²`

(Made by `gen_c10.py` with the threshold `4096`.)

* **`m4C_leR`**: `m4C n ≤ 5.2683/n`; **`pWC_leR`**: `pWC n ≤ 0.30902/√n`
  (`sig4·tau143sC n ≤ 0.39959/√n`).
* `qCos_MR`, `parts_MR`, `sU4_MR` (`0.3350673/√n`), `a1_MR` (`1.8601586/√n`),
  `aL_MR` (`2.2266363/√n`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part139
open BstLean.Part142 BstLean.Part143

section numMR

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

lemma qCos_MR : qCos n ≤ 2060717 / 50000 * (1 / (n : ℝ)) ^ 2 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hx := nR_geCR hn
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  rw [← hy]
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

lemma parts_MR : √(kEC n) ≤ 186167 / 100000 * (1 / √(n : ℝ)) ∧
    √(qCos n) ≤ 64199 / 10000 * (1 / (n : ℝ)) ∧
    √(√(qCos n * (√2 * qCos n))) ≤ 7001 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hK := K4_leCR hn
  have hK0 := K4_nonneg n
  have hQ := qCos_MR hn
  have hQ0 := qCos_nonneg n
  have h2 := Part133.sqrt2_le
  have h20 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  rw [← hy] at hQ ⊢
  rw [← hz]
  refine ⟨?_, ?_, ?_⟩
  · unfold kEC
    refine sqrt_le_of_sq (by positivity) ?_
    have e : K4 n / (n : ℝ) = K4 n * y := by rw [hy]; ring
    have e2 : (186167 / 100000 * z) ^ 2 = (186167 / 100000) ^ 2 * y := by rw [hyz]; ring
    rw [e, e2]
    have a1 := mul_le_mul_of_nonneg_right hK hy0.le
    have a2 : 3465793 / 1000000 * y ≤ (186167 / 100000) ^ 2 * y :=
      mul_le_mul_of_nonneg_right (by norm_num) hy0.le
    linarith
  · refine sqrt_le_of_sq (by positivity) ?_
    have a2 : 2060717 / 50000 * y ^ 2 ≤ (64199 / 10000 * y) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg y)
    linarith
  · have a1 : √(qCos n * (√2 * qCos n)) ≤ 49013 / 1000 * y ^ 2 := by
      refine sqrt_le_of_sq (by positivity) ?_
      have b1 : √2 * qCos n ≤ 141422 / 100000 * (2060717 / 50000 * y ^ 2) :=
        mul_le_mul h2 hQ hQ0 (by norm_num)
      have b2 := mul_le_mul hQ b1 (by positivity) (by positivity)
      refine b2.trans ?_
      have e : 2060717 / 50000 * y ^ 2 * (141422 / 100000 * (2060717 / 50000 * y ^ 2)) =
          2060717 / 50000 * (141422 / 100000) * (2060717 / 50000) * (y ^ 2) ^ 2 := by ring
      rw [e, mul_pow]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    refine sqrt_le_of_sq (by positivity) (a1.trans ?_)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg y)

/-- `sU4(2n) ≤ 0.3350673/√n` for `n ≥ 4096`. -/
lemma sU4_MR : sU4 (2 * n) ≤ 3350673 / 10000000 * (1 / √(n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have h105 : √(105 : ℝ) ≤ 10247 / 1000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have h1050 := Real.sqrt_nonneg (105 : ℝ)
  unfold sU4
  rw [hc, ← hz]
  have a : √(√3 / (2 * (n : ℝ))) ≤ 46531 / 50000 * z := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e1 : √3 / (2 * (n : ℝ)) = √3 / 2 * y := by rw [hy]; ring
    have e2 : (46531 / 50000 * z) ^ 2 = (46531 / 50000) ^ 2 * y := by rw [hyz]; ring
    rw [e1, e2]
    have b1 : √3 / 2 ≤ (46531 / 50000) ^ 2 := by
      have : (17321 : ℝ) / 10000 / 2 ≤ (46531 / 50000) ^ 2 := by norm_num
      linarith
    exact mul_le_mul_of_nonneg_right b1 hy0.le
  have b : √(√105 / (2 * (n : ℝ)) ^ 2) ≤ 32011 / 20000 * y := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e1 : √105 / (2 * (n : ℝ)) ^ 2 = √105 / 4 * y ^ 2 := by rw [hy]; ring
    rw [e1, mul_pow]
    have b1 : √105 / 4 ≤ (32011 / 20000) ^ 2 := by
      have : (10247 / 1000 : ℝ) / 4 ≤ (32011 / 20000) ^ 2 := by norm_num
      linarith
    exact mul_le_mul_of_nonneg_right b1 (sq_nonneg y)
  linarith

/-- `a1G(2n, n, m_W) ≤ 1.8601586/√n` for `n ≥ 4096`. -/
lemma a1_MR : a1G (2 * n) n (mW n) ≤ 9300793 / 5000000 * (1 / √(n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  obtain ⟨hk, hsq, hqq⟩ := parts_MR hn
  have hsU := sU4_MR hn
  have hsU0 := sU4_nonneg (2 * n)
  have hE := (eHid_inv (n := n) (by omega)).1
  have hE0 := eHid_nonneg (mW n)
  rw [← hy] at hsq hqq hE
  rw [← hz] at hk hsU ⊢
  have hk0 := Real.sqrt_nonneg (kEC n)
  have hq := kappa2_zero_ge
  have hq1 := q_mem
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have hq3 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [hq1.1, hq1.2]
  have hsU' : sU4 (2 * n) ≤ 3350673 / 10000000 / 64 := by linarith
  have t1 : √(kEC n) * (1 - kappa (kappa 0) ^ 2 + 2 * sU4 (2 * n)) ≤
      186167 / 100000 * z * (1 - (49372 / 100000) ^ 2 + 2 * (3350673 / 10000000 / 64)) :=
    mul_le_mul hk (by linarith) (by positivity) (by positivity)
  have t3 : √(2 * eHid (mW n)) ≤ 23019 / 100000 * z := by
    refine sqrt_le_of_sq (by positivity) ?_
    have e2 : (23019 / 100000 * z) ^ 2 = (23019 / 100000) ^ 2 * y := by rw [hyz]; ring
    rw [e2]
    have a2 : 2 * (26493 / 1000000) * y ≤ (23019 / 100000) ^ 2 * y :=
      mul_le_mul_of_nonneg_right (by norm_num) hy0.le
    linarith
  have t4 : √(kEC n) * √(2 * eHid (mW n)) ≤ 186167 / 100000 * z * (23019 / 100000 * z) :=
    mul_le_mul hk t3 (Real.sqrt_nonneg _) (by positivity)
  have e4 : 186167 / 100000 * z * (23019 / 100000 * z) = 186167 / 100000 * (23019 / 100000) * y := by rw [hyz]; ring
  rw [e4] at t4
  unfold a1G j4C
  linarith

/-- `aL4G(2n, n, m_W) ≤ 2.2266363/√n` for `n ≥ 4096`. -/
lemma aL_MR : aL4G (2 * n) n (mW n) ≤ 22266363 / 10000000 * (1 / √(n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hx := nR_geCR hn
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have ha := a1_MR hn
  have ha0 := a1G_nonneg (2 * n) n (mW n)
  have hsU := sU4_MR hn
  have hQ := qCos_MR hn
  have hQ0 := qCos_nonneg n
  rw [← hy] at hQ
  rw [← hz] at ha hsU ⊢
  have h1 : a1G (2 * n) n (mW n) ^ 4 ≤ (9300793 / 5000000 * z) ^ 4 := pow_le_pow_left₀ ha0 ha 4
  have h2 : qCos n ^ 2 ≤ (2060717 / 50000 * y ^ 2) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  have hy2 : y ^ 2 ≤ (1 / 4096) ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
  have h3 : z ^ 4 * y ^ 2 ≤ z ^ 4 * (1 / 4096) ^ 2 :=
    mul_le_mul_of_nonneg_left hy2 (by positivity)
  have e2 : (2060717 / 50000 * y ^ 2) ^ 2 = (2060717 / 50000) ^ 2 * (z ^ 4 * y ^ 2) := by rw [hyz]; ring
  rw [e2] at h2
  have hnum : (9300793 / 5000000 : ℝ) ^ 4 + 8192 * ((2060717 / 50000) ^ 2 * (1 / 4096) ^ 2) ≤
      (1891569 / 1000000) ^ 4 := by norm_num
  have h4 := mul_le_mul_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ z ^ 4)
  have hx4 : a1G (2 * n) n (mW n) ^ 4 + t4C n ≤ ((1891569 / 1000000 * z) ^ 2) ^ 2 := by
    unfold t4C
    have e5 : ((1891569 / 1000000 * z) ^ 2) ^ 2 = (1891569 / 1000000) ^ 4 * z ^ 4 := by ring
    have e6 : (9300793 / 5000000 * z) ^ 4 = (9300793 / 5000000) ^ 4 * z ^ 4 := by ring
    rw [e5]
    rw [e6] at h1
    linarith
  have h5 : √(a1G (2 * n) n (mW n) ^ 4 + t4C n) ≤ (1891569 / 1000000 * z) ^ 2 :=
    sqrt_le_of_sq (by positivity) hx4
  have h6 : √(√(a1G (2 * n) n (mW n) ^ 4 + t4C n)) ≤ 1891569 / 1000000 * z :=
    sqrt_le_of_sq (by positivity) h5
  unfold aL4G
  linarith

/-- **`m4C n ≤ 5.2683/n`** for `n ≥ 4096`. -/
theorem m4C_leR : m4C n ≤ 52683 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hA := aL_MR hn
  have hA0 := aL4G_nonneg (2 * n) n (mW n)
  obtain ⟨hE, hε⟩ := eHid_inv (n := n) (by omega)
  have hE0 := eHid_nonneg (mW n)
  have hε0 := epsW_nonneg (mW n)
  rw [← hy] at hE hε
  rw [← hz] at hA
  refine le_trans (?_ : _ ≤ 52683 / 10000 * y) (le_of_eq (by rw [hy]; ring))
  unfold m4C m4G
  refine sqrt_le_of_sq (by positivity) ?_
  have h4 : aL4G (2 * n) n (mW n) ^ 4 ≤ (22266363 / 10000000 * z) ^ 4 := pow_le_pow_left₀ hA0 hA 4
  have h2 : aL4G (2 * n) n (mW n) ^ 2 ≤ (22266363 / 10000000 * z) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have e4 : (22266363 / 10000000 * z) ^ 4 = (22266363 / 10000000) ^ 4 * y ^ 2 := by rw [hyz]; ring
  have e2 : (22266363 / 10000000 * z) ^ 2 = (22266363 / 10000000) ^ 2 * y := by rw [hyz]; ring
  rw [e4] at h4
  rw [e2] at h2
  have h3 : aL4G (2 * n) n (mW n) ^ 2 * eHid (mW n) ≤ (22266363 / 10000000) ^ 2 * y * (26493 / 1000000 * y) :=
    mul_le_mul h2 hE hE0 (by positivity)
  have h5 : eHid (mW n) ^ 2 ≤ (26493 / 1000000 * y) ^ 2 := pow_le_pow_left₀ hE0 hE 2
  have hnum : (22266363 / 10000000 : ℝ) ^ 4 + 24 * ((22266363 / 10000000) ^ 2 * (26493 / 1000000)) + 28 * (26493 / 1000000) ^ 2 +
      32 * (381471 / 10000000000) ≤ (52683 / 10000) ^ 2 := by norm_num
  have h6 := mul_le_mul_of_nonneg_right hnum (sq_nonneg y)
  have e7 : (52683 / 10000 * y) ^ 2 = (52683 / 10000) ^ 2 * y ^ 2 := by ring
  have e8 : (26493 / 1000000 * y) ^ 2 = (26493 / 1000000) ^ 2 * y ^ 2 := by ring
  rw [e7]
  rw [e8] at h5
  linarith

/-- **`pWC n ≤ 0.30902/√n`** for `n ≥ 4096` (`sig4·tau143sC n ≤ 0.39959/√n`). -/
theorem pWC_leR : pWC n ≤ 15451 / 50000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hz1, hr1, hyz, hyz'⟩ := yzCR hn
  have hx := nR_geCR hn
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hτ : tau143sC n ≤ 45367 / 50000 * z :=
    (tau143sC_leR hn).trans (le_of_eq (by rw [hz]; ring))
  have hτ0 := tau143sC_nonneg n
  have hm : m4C n ≤ 52683 / 10000 * y := (m4C_leR hn).trans (le_of_eq (by rw [hy]; ring))
  have hm0 := m4C_nonneg n
  have hs4 := sig4_le
  have hs40 := sig4_nonneg
  have hsv : sW = 619 / 2000 := rfl
  have hwv : wW = 1 / 5 := rfl
  have hC0 : 0 ≤ sig4 ^ 2 - sW ^ 2 := by
    have := sW_le_sig4
    have := sW_pos
    nlinarith
  have hC1 : sig4 ^ 2 - sW ^ 2 ≤ (4404 / 10000) ^ 2 - sW ^ 2 := by
    have := pow_le_pow_left₀ hs40 hs4 2
    linarith
  refine le_trans (?_ : _ ≤ 15451 / 50000 * z) (le_of_eq (by rw [hz]; ring))
  unfold pWC
  refine sqrt_le_of_sq (by positivity) ?_
  have h1 : tau143sC n ^ 2 ≤ (45367 / 50000 * z) ^ 2 := pow_le_pow_left₀ hτ0 hτ 2
  have h2 : m4C n ^ 2 ≤ (52683 / 10000 * y) ^ 2 := pow_le_pow_left₀ hm0 hm 2
  have h3 : (sig4 ^ 2 - sW ^ 2) * m4C n ^ 2 ≤
      ((4404 / 10000) ^ 2 - sW ^ 2) * (52683 / 10000 * y) ^ 2 :=
    mul_le_mul hC1 h2 (sq_nonneg _) (by rw [hsv]; norm_num)
  have ey : y ^ 2 = z ^ 2 * y := by
    calc y ^ 2 = y * y := by ring
      _ = z * z * y := by rw [← hyz]
      _ = z ^ 2 * y := by ring
  have h4 : z ^ 2 * y ≤ z ^ 2 * (1 / 4096) := mul_le_mul_of_nonneg_left hy1 (sq_nonneg z)
  have h5 := mul_le_mul_of_nonneg_left h1 (sq_nonneg sW)
  rw [hsv] at h3 h5 ⊢
  rw [hwv]
  have hnum : (619 / 2000 : ℝ) ^ 2 * (45367 / 50000) ^ 2 +
      ((4404 / 10000) ^ 2 - (619 / 2000) ^ 2) * ((52683 / 10000) ^ 2 * (1 / 4096)) / (1 / 5) ^ 2 ≤
      (15451 / 50000) ^ 2 := by norm_num
  have ew : ∀ t : ℝ, t / (1 / 5) ^ 2 = 25 * t := fun t => by ring
  rw [ew] at hnum ⊢
  have h6 := mul_le_mul_of_nonneg_right hnum (sq_nonneg z)
  have e1 : (45367 / 50000 * z) ^ 2 = (45367 / 50000) ^ 2 * z ^ 2 := by ring
  have e2 : (52683 / 10000 * y) ^ 2 = (52683 / 10000) ^ 2 * y ^ 2 := by ring
  have e3 : (15451 / 50000 * z) ^ 2 = (15451 / 50000) ^ 2 * z ^ 2 := by ring
  rw [e1] at h5
  rw [e2, ey] at h3
  rw [e3]
  have h7 : ((4404 / 10000 : ℝ) ^ 2 - (619 / 2000) ^ 2) * ((52683 / 10000) ^ 2 * (z ^ 2 * y)) ≤
      ((4404 / 10000) ^ 2 - (619 / 2000) ^ 2) * ((52683 / 10000) ^ 2 * (z ^ 2 * (1 / 4096))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by norm_num)) (by norm_num)
  linarith

end numMR

end BstLean.Part145

open BstLean.Part145 in
#print axioms m4C_leR
open BstLean.Part145 in
#print axioms pWC_leR
