import BstLean.Part143Big

/-!
# Part 143: the numeric constants of `Part143Big` again, for `n ≥ 13225 = 115²`

The lemmas of `Part143Big` (there with `16384 ≤ n`) with the hypothesis `13225 ≤ n`
(`√n ≥ 115`, `√(m_F) ≥ 10.7238·√n`, `m_W ≥ 115·n³`), each constant computed again; names with
the suffix `L`. Headlines: `inv_mFL`, `f1_L`, `f2_L`, `f3_L`, `dA0_L`, `dA1_L`, `dA2_L`,
`cAdltL`, `N0_L`, `sqrt_eps4_L`, `tauW142_L`, `eAFr_L`, `Vb_L`, `EHH_L`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

section bigL

variable {n : ℕ} (hn : 13225 ≤ n)

include hn

lemma nR_geL : (13225 : ℝ) ≤ n := by exact_mod_cast hn

lemma n4096_ofL : 4096 ≤ n := by omega

lemma sqrt_n_geL : (115 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_geL hn
  exact Real.le_sqrt_of_sq_le (by linarith)

lemma yzL : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 13225 ∧ z ≤ 1 / 115 ∧ r ≤ 707107 / 1000000 * z ∧
    r ≤ 1 / 162 ∧ y = z * z ∧ y ≤ 1 / 115 * z := by
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geL hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have h162 : (162 : ℝ) ≤ √(2 * (n : ℝ)) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 115 := one_div_le_one_div_of_le (by norm_num) hs
  have hyz : 1 / (n : ℝ) = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    hz0, by positivity, one_div_le_one_div_of_le (by norm_num) hx,
    hz1, ?_, one_div_le_one_div_of_le (by norm_num) h162, hyz, ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [hyz]
    exact mul_le_mul_of_nonneg_right hz1 hz0.le

lemma K4_leL : K4 n ≤ 346463 / 100000 := by
  have hx := nR_geL hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 13225 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

lemma inv_mFL :
    1 / √(mF n : ℝ) ≤ 10000 / 107238 * (1 / √(n : ℝ)) ∧
      1 / (mF n : ℝ) ≤ 1 / 13225 * (1 / √(n : ℝ)) := by
  have hx := nR_geL hn
  have hs := sqrt_n_geL hn
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hms := BstLean.Part139.mF_ge_s (n4096_ofL hn)
  have hm0 : (0 : ℝ) < mF n := by nlinarith
  have h8 : 107238 / 10000 * √(n : ℝ) ≤ √(mF n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : (107238 / 10000 * √(n : ℝ)) ^ 2 = (107238 / 10000) ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    rw [h1]
    have h2 : 115 * (n : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by nlinarith
    have h3 : ((107238 : ℝ) / 10000) ^ 2 * (n : ℝ) ≤ 115 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
    linarith
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have e : 10000 / 107238 * (1 / √(n : ℝ)) * √(mF n : ℝ) =
        √(mF n : ℝ) / (107238 / 10000 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 13225 * (1 / √(n : ℝ)) * (mF n : ℝ) = (mF n : ℝ) / (13225 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have h2 : 13225 * √(n : ℝ) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right hx hs0.le
    linarith

lemma mW_geL : 115 * (n : ℝ) ^ 3 ≤ mW n := by
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast mW_sq_ge n
  have h6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
  have h2 : (115 * (n : ℝ) ^ 3) ^ 2 ≤ (mW n : ℝ) ^ 2 := by
    calc (115 * (n : ℝ) ^ 3) ^ 2 = 13225 * (n : ℝ) ^ 6 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 6 := mul_le_mul_of_nonneg_right (by linarith) h6
      _ = (n : ℝ) ^ 7 := by ring
      _ ≤ _ := h1
  exact (abs_le_of_sq_le_sq' h2 (Nat.cast_nonneg _)).2

lemma mW_posL : (0 : ℝ) < mW n := by
  have hx := nR_geL hn
  have h := mW_geL hn
  have : (0 : ℝ) < 115 * (n : ℝ) ^ 3 := by positivity
  linarith

lemma mW_moreL : (n : ℝ) / (mW n : ℝ) ≤ 1 / 20113571875 ∧
    (n : ℝ) / (mW n : ℝ) ≤ 1 / 1520875 * (1 / (n : ℝ)) ∧
    141822 * √(n : ℝ) ≤ √(mW n : ℝ) := by
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mW_geL hn
  have hm0 := mW_posL hn
  have hsq : (174900625 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h3 : 174900625 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hsq hx0.le
    calc 174900625 * (n : ℝ) ≤ (n : ℝ) ^ 2 * (n : ℝ) := this
      _ = (n : ℝ) ^ 3 := by ring
  have h35 : 20113571875 * (n : ℝ) ≤ mW n := by linarith
  have h3' : 13225 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hx (sq_nonneg (n : ℝ))
    calc 13225 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
      _ = (n : ℝ) ^ 3 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 1520875 * (1 / (n : ℝ)) * (1520875 * (n : ℝ) ^ 2) = (n : ℝ) := by
      field_simp
    have : 1 / 1520875 * (1 / (n : ℝ)) * (1520875 * (n : ℝ) ^ 2) ≤
        1 / 1520875 * (1 / (n : ℝ)) * (mW n : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, Real.sq_sqrt hx0.le]
    have : (141822 : ℝ) ^ 2 * (n : ℝ) ≤ 20113571875 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) hx0.le
    linarith

lemma sqrt_one_addL : √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 13225 := by
  have hx := nR_geL hn
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 2 / (n : ℝ) ≤ 2 / 13225 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

lemma sU_L : sU (2 * n) ≤ 36092 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := s3_le16
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 36092 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (173206 / 100000) / 2 * (1 / 115 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

lemma sU_constL : sU (2 * n) ≤ 3139 / 1000000 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have h := sU_L hn
  have e : (36092 : ℝ) / 100000 / √(n : ℝ) = 36092 / 100000 * z := by rw [hz]; ring
  rw [e] at h
  linarith

lemma epsWL : epsW (mW n) * (n : ℝ) ≤ 1001 / 100 / 20113571875 := by
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm0 := mW_posL hn
  obtain ⟨a2, -, -⟩ := mW_moreL hn
  have hm := mW_geR (n4096_ofL hn)
  have e : epsW (mW n) * (n : ℝ) = (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) := by
    unfold epsW
    field_simp
    ring
  have a1 : 25 / (mW n : ℝ) ≤ 1 / 100 := by
    rw [div_le_iff₀ hm0]; linarith
  have a10 : (0 : ℝ) ≤ 25 / (mW n : ℝ) := by positivity
  have a20 : (0 : ℝ) ≤ (n : ℝ) / (mW n : ℝ) := by positivity
  rw [e]
  calc (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) ≤ 1001 / 100 * (1 / 20113571875) :=
        mul_le_mul (by linarith) a2 a20 (by norm_num)
    _ = _ := by norm_num

lemma eHid_uL :
    eHid (mW n) ≤ 9568 / 100000000 * (1 / √(n : ℝ)) ∧
      √(epsW (mW n)) ≤ 2231 / 100000000 * (1 / √(n : ℝ)) := by
  have hn4 := n4096_ofL hn
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn4
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hε := epsWL hn
  have hε0 := epsW_nonneg (mW n)
  obtain ⟨-, -, hsW⟩ := mW_moreL hn
  have hsW0 : (0 : ℝ) < √(mW n : ℝ) := by nlinarith
  have hm := mW_geR hn4
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have s1 : √(5 * epsW (mW n)) ≤ 4989 / 100000000 * u := by
    have := sqrt_le_div_s hn4 (x := 5 * epsW (mW n)) (c := 4989 / 100000000) (by norm_num)
      (by
        have e : 5 * epsW (mW n) * (n : ℝ) = 5 * (epsW (mW n) * (n : ℝ)) := by ring
        rw [e]
        refine le_trans (mul_le_mul_of_nonneg_left hε (by norm_num)) ?_
        norm_num)
    rwa [div_eq_mul_one_div, ← hu] at this
  have s2 : √(epsW (mW n)) ≤ 2231 / 100000000 * u := by
    have := sqrt_le_div_s hn4 (x := epsW (mW n)) (c := 2231 / 100000000) (by norm_num)
      (hε.trans (by norm_num))
    rwa [div_eq_mul_one_div, ← hu] at this
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have hiW : 1 / √(mW n : ℝ) ≤ 1 / 141822 * u := by
    rw [hu, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsW
  have hiW0 : 0 ≤ 1 / √(mW n : ℝ) := by positivity
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 141822 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 141822 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  refine ⟨?_, s2⟩
  unfold eHid
  linarith

lemma eWsmallL : eWsmall n (mW n) ≤ 22610 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  obtain ⟨hH, hE⟩ := eHid_uL hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hK := K4_leL hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (346463 / 100000) * (1 / 115 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 115) * (9568 / 100000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hy, hz]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 22610 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

lemma eWr_L : eWr (2 * n) n (mW n) ≤ 98861 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have h1 := sU_constL hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmallL hn
  have hq := BstLean.Part132.kappa2_zero_ge'
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49373 / 100000) ^ 2 := by nlinarith
  have e2 : (22610 : ℝ) / 100000 / √(n : ℝ) = 22610 / 100000 * z := by rw [hz]; ring
  rw [e2] at h2
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49373 / 100000) ^ 2 + 2 * (3139 / 1000000)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 98861 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

theorem tauW142_L : tauW142 n ≤ 134953 / 100000 / √(n : ℝ) := by
  have h2 := eWr_L hn
  have h3 := sU_L hn
  unfold tauW142
  have e : (134953 : ℝ) / 100000 / √(n : ℝ) =
      98861 / 100000 / √(n : ℝ) + 36092 / 100000 / √(n : ℝ) := by ring
  rw [e]
  linarith

lemma f1_L : f1 (mF n) ≤ 32349 / 100000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mFL hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h3 := s3_le16
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have e : f1 (mF n) = 2 * (√3 * (1 / √(mF n : ℝ))) + 6 * (1 / (mF n : ℝ)) := by
    unfold f1; ring
  have e2 : 32349 / 100000 / √(n : ℝ) = 32349 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p1 : √3 * (1 / √(mF n : ℝ)) ≤ 173206 / 100000 * (10000 / 107238 * (1 / √(n : ℝ))) :=
    mul_le_mul h3 ha ha0 (by norm_num)
  linarith

lemma f2_L : f2 (mF n) ≤ 3810 / 100000 / √(n : ℝ) := by
  have hn4 := n4096_ofL hn
  obtain ⟨ha, hb⟩ := inv_mFL hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have hb0 : (0 : ℝ) ≤ 1 / (mF n : ℝ) := by positivity
  have h5 := AgD.sqrt5_le'
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hbG := bG_kappa_le
  have hbG0 := bG_nonneg kGood_kappa
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have hKr := Kr_le hn4
  have hKr0 := Kr_nonneg (mF n)
  have e : f2 (mF n) = bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) +
      4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) := by
    unfold f2; ring
  have e2 : 3810 / 100000 / √(n : ℝ) = 3810 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : bG kappa * √5 ≤ 363382 / 1000000 * (223607 / 100000) :=
    mul_le_mul hbG h5 h50 (by norm_num)
  have p1 : bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) ≤
      363382 / 1000000 * (223607 / 100000) / 2 * (10000 / 107238 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) ha ha0 (by norm_num)
  have q0 : kappa 0 * Kr (mF n) ≤ 31831 / 100000 * (21652 / 10000) :=
    mul_le_mul hk hKr hKr0 (by norm_num)
  have q1 : 4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) ≤
      4 * (31831 / 100000 * (21652 / 10000)) * (1 / 13225 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  linarith

lemma f3_L : f3 (mF n) ≤ 6638 / 100000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mFL hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h5 := AgD.sqrt5_le'
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have e : f3 (mF n) = kappa 0 * √5 * (1 / √(mF n : ℝ)) := by
    unfold f3; ring
  have e2 : 6638 / 100000 / √(n : ℝ) = 6638 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : kappa 0 * √5 ≤ 31831 / 100000 * (223607 / 100000) :=
    mul_le_mul hk h5 h50 (by norm_num)
  have p1 : kappa 0 * √5 * (1 / √(mF n : ℝ)) ≤
      31831 / 100000 * (223607 / 100000) * (10000 / 107238 * (1 / √(n : ℝ))) :=
    mul_le_mul p0 ha ha0 (by norm_num)
  linarith

lemma nsqL : (174900625 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hx := nR_geL hn
  nlinarith

lemma Q5_L : √(1 + 5 / (mA n : ℝ)) ≤ 1 + 2 / 100000000 := by
  have h2 := nsqL hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 5 / (n : ℝ) ^ 2 ≤ 5 / 174900625 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma Q2_L : √(1 + 2 / (mA n : ℝ)) ≤ 1 + 1 / 100000000 := by
  have h2 := nsqL hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 2 / (n : ℝ) ^ 2 ≤ 2 / 174900625 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma sSL : AgD.sS (mA n) ≤ 200000004 / 100000000 := by
  have := Q5_L hn
  unfold AgD.sS
  linarith

lemma SSL : AgD.SS (mA n) ≤ 200000009 / 100000000 := by
  have h1 := Q5_L hn
  have h2 := sSL hn
  have h3 := AgD.sS_nn (mA n)
  unfold AgD.SS
  calc √(1 + 5 / (mA n : ℝ)) * AgD.sS (mA n)
      ≤ (1 + 2 / 100000000) * (200000004 / 100000000) := by gcongr
    _ ≤ 200000009 / 100000000 := by norm_num

lemma DSL : AgD.DS (mA n) ≤ 894429 / 100000 * (1 / (n : ℝ)) := by
  have h5 := AgD.sqrt5_le'
  have h2 := sSL hn
  have h3 := AgD.sS_nn (mA n)
  have h4 := AgD.dS_le (n4096_ofL hn)
  unfold AgD.DS
  rw [sqrt_mA]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  rw [← hy] at h4 ⊢
  refine le_trans (le_of_eq (?_ : _ = √5 * y * AgD.sS (mA n) + AgD.dS (mA n))) ?_
  · rw [hy]; ring
  · calc √5 * y * AgD.sS (mA n) + AgD.dS (mA n)
        ≤ 223607 / 100000 * y * (200000004 / 100000000) + 447214 / 100000 * y := by gcongr
      _ ≤ 894429 / 100000 * y := by linarith

lemma LSL : AgD.LS (mA n) ≤ 342 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have hn4 := n4096_ofL hn
  have h5 := AgD.sqrt5_le'
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have h2 := sSL hn
  have h3 := AgD.sS_nn (mA n)
  have h4 := AgD.dS_le hn4
  have h4n := AgD.dS_nn (mA n)
  have h6 := AgD.lS_le hn4
  unfold AgD.LS
  rw [sqrt_mA, mA_eqR]
  rw [← hy] at h4 h6 ⊢
  have hyy : y ^ 2 ≤ y * (1 / 13225) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = AgD.lS (mA n) + 4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) +
    √5 * y * AgD.dS (mA n))) ?_
  · rw [hy]; ring
  · calc AgD.lS (mA n) + 4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) + √5 * y * AgD.dS (mA n)
        ≤ 176 / 10 * y ^ 2 + 4 * (11 / 5) * y ^ 2 * (200000004 / 100000000) +
          223607 / 100000 * y * (447214 / 100000 * y) := by gcongr
      _ ≤ 342 / 100000 * y := by nlinarith

lemma nc0_L : AgD.nc0 (mA n) ≤ 81298 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have hn4 := n4096_ofL hn
  have h5 := AgD.sqrt5_le'
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hb := AgD.bk_le
  have hb0 := bG_nonneg kGood_kappa
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := kGood_kappa.nonneg_on KGood.zero_mem
  unfold AgD.nc0
  rw [sqrt_mA, mA_eqR]
  rw [← hy]
  have hyy : y ^ 2 ≤ y * (1 / 13225) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2))) ?_
  · rw [hy]; ring
  · calc bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2)
        ≤ 363382 / 1000000 * (223607 / 100000) * y +
          31831 / 100000 * (8 * (11 / 5) * y ^ 2) := by gcongr
      _ ≤ 81298 / 100000 * y := by nlinarith

theorem dA1_L : dA1 n (mA n) ≤ 1 + 1 / 13225 := by
  unfold dA1
  exact sqrt_one_addL hn

theorem dA0_L : dA0 n (mA n) ≤ 81305 / 100000 / (n : ℝ) := by
  have h1 := sqrt_one_addL hn
  have a1 := nc0_L hn
  have n1 := AgD.nc0_nn (mA n)
  have hy0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold dA0
  refine le_trans (?_ : _ ≤ 81305 / 100000 * (1 / (n : ℝ))) (le_of_eq (by ring))
  calc √(1 + 2 / (n : ℝ)) * AgD.nc0 (mA n)
      ≤ (1 + 1 / 13225) * (81298 / 100000 * (1 / (n : ℝ))) := by gcongr
    _ ≤ 81305 / 100000 * (1 / (n : ℝ)) := by nlinarith

theorem dA2_L : dA2 n (mA n) ≤ 103932 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have h1 := sqrt_one_addL hn
  have h3 := s3_le16
  have hQ := Q2_L hn
  unfold dA2
  rw [sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))))) ?_
  · rw [hy]; ring
  · refine le_trans (?_ : _ ≤ 103932 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))
        ≤ (1 + 1 / 13225) * (2 * (173206 / 100000) * y + 173206 / 100000 * y *
          (4 * (1 + 1 / 100000000))) := by gcongr
      _ ≤ 103932 / 10000 * y := by nlinarith

theorem cAdltL : cAdlt n (mA n) ≤ 70427 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzL hn
  have hn4 := n4096_ofL hn
  have h2 := Part133.sqrt2_le
  have hK4 := K4_leL hn
  have hK40 := K4_nonneg n
  have a2 := SSL hn
  have a3 := DSL hn
  have a4 := LSL hn
  have n2 := AgD.SS_nn (mA n)
  have n3 := AgD.DS_nn (mA n)
  rw [← hy] at a3 a4
  have hzy : z * y ≤ y * (1 / 115) := by nlinarith
  unfold cAdlt
  refine le_trans (le_of_eq (?_ : _ = AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) +
    √2 * z * AgD.DS (mA n))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 70427 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n)
        ≤ 342 / 100000 * y + 346463 / 100000 * y * (200000009 / 100000000) +
          141422 / 100000 * z * (894429 / 100000 * y) := by gcongr
      _ ≤ 70427 / 10000 * y := by nlinarith

lemma N0_L : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ 1 + 7565 / 100000000 := by
  have h2 := nsqL hn
  have h1 : 5 / (mA n : ℝ) ≤ 5 / 174900625 := by
    rw [mA_eqR]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have h10 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have h3 := sqrt_one_addL hn
  have h30 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
  calc (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))
      ≤ (1 + 5 / 174900625) * (1 + 1 / 13225) := mul_le_mul (by linarith) h3 h30 (by norm_num)
    _ ≤ 1 + 7565 / 100000000 := by norm_num

lemma sqrt_eps4_L : √(eps4 n (mA n)) ≤ 141449 / 100000 / √(n : ℝ) := by
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  refine sqrt_le_div_s (n4096_ofL hn) (by norm_num) ?_
  unfold eps4
  rw [mA_eqR]
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 13225 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyn : y * (n : ℝ) = 1 := by rw [hy]; field_simp
  have e1 : 5 / (n : ℝ) ^ 2 = 5 * y ^ 2 := by rw [hy]; ring
  have e2 : 2 / (n : ℝ) = 2 * y := by rw [hy]; ring
  rw [e1, e2]
  have hy2 : y ^ 2 ≤ 1 / 13225 * y := by nlinarith
  have hy20 : 0 ≤ y ^ 2 := by positivity
  have hb : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1 ≤ 200076 / 100000 * y := by
    have h5 : 5 * y ^ 2 ≤ 5 / 13225 * y := by nlinarith
    have h50 : 0 ≤ 5 * y ^ 2 := by positivity
    have h5c : 5 * y ^ 2 ≤ 1 / 1000000 := by nlinarith
    have h6 : (1 + 5 * y ^ 2) ^ 2 ≤ 1 + 7562 / 10000000 * y := by nlinarith
    have h7 : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) ≤ (1 + 7562 / 10000000 * y) * (1 + 2 * y) :=
      mul_le_mul_of_nonneg_right h6 (by linarith)
    nlinarith
  calc ((1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1) * (n : ℝ)
      ≤ 200076 / 100000 * y * (n : ℝ) := mul_le_mul_of_nonneg_right hb hx0.le
    _ = 200076 / 100000 := by rw [mul_assoc, hyn, mul_one]
    _ ≤ (141449 / 100000) ^ 2 := by norm_num

lemma cF2oL : cF2o (mF n) ≤ 44066 / 100000 / √(n : ℝ) := by
  have hn4 := n4096_ofL hn
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geL hn
  have hm := mF_geR hn4
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hms := BstLean.Part139.mF_ge_s hn4
  have hmF : 115 * (n : ℝ) ≤ mF n := by
    have := mul_le_mul_of_nonneg_left hs hx0.le
    linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hc : (5 * kappa 0 + √6) ^ 2 ≤ 163301 / 10000 := by
    have h1 : 5 * kappa 0 + √6 ≤ 404105 / 100000 := by linarith
    have h0 : 0 ≤ 5 * kappa 0 + √6 := by positivity
    nlinarith
  have h5 : 5 / (mF n : ℝ) ≤ 5 / 262144 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  unfold cF2o
  refine sqrt_le_div_s hn4 (by norm_num) ?_
  have e : 6 * (1 + 5 / (mF n : ℝ)) / (mF n : ℝ) + (5 * kappa 0 + √6) ^ 2 / (mF n : ℝ) =
      (6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (mF n : ℝ) := by ring
  have h7 : 6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2 ≤ 223303 / 10000 := by
    norm_num at h5 ⊢
    linarith
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hm0]
  have hc2 : (223303 : ℝ) / 10000 ≤ (44066 / 100000) ^ 2 * 115 := by norm_num
  calc (6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2) * (n : ℝ)
      ≤ 223303 / 10000 * (n : ℝ) := mul_le_mul_of_nonneg_right h7 hx0.le
    _ ≤ (44066 / 100000) ^ 2 * 115 * (n : ℝ) := mul_le_mul_of_nonneg_right hc2 hx0.le
    _ = (44066 / 100000) ^ 2 * (115 * (n : ℝ)) := by ring
    _ ≤ (44066 / 100000) ^ 2 * (mF n : ℝ) := mul_le_mul_of_nonneg_left hmF (by norm_num)

lemma cArL : cAr (kappa ∘ kappa) (mA n) n ≤ 183559 / 100000 / √(n : ℝ) := by
  obtain ⟨y, u, r, hy, hu, hr, hy0, hu0, hr0, hy1, hu1, hr1, hr2, hyz, hnu⟩ := yzL hn
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK := K4_leL hn
  have hK0 := K4_nonneg n
  have hq := kappa2_zero_le
  have hq0 := q_mem.1
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hA : 5 / (mA n : ℝ) ≤ 3 / 100000000 := by
    have h2' := nsqL hn
    rw [mA_eqR, div_le_iff₀ (by positivity)]
    linarith
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hsA := Q5_L hn
  have hsA0 := Real.sqrt_nonneg (1 + 5 / (mA n : ℝ))
  rw [hy] at hnu
  have t1 : (1 + √2 * kappa (kappa 0)) / √(n : ℝ) ≤
      (1 + 141422 / 100000 * (49376 / 100000)) * u := by
    rw [div_eq_mul_one_div, ← hu]
    have : 1 + √2 * kappa (kappa 0) ≤ 1 + 141422 / 100000 * (49376 / 100000) := by
      have := mul_le_mul h2 hq hq0 (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right this hu0.le
  have t2 : 2 * K4 n * kappa (kappa 0) / (n : ℝ) ≤
      2 * (346463 / 100000) * (49376 / 100000) * (1 / 115 * u) := by
    rw [div_eq_mul_one_div]
    have a : 2 * K4 n * kappa (kappa 0) ≤ 2 * (346463 / 100000) * (49376 / 100000) := by
      have := mul_le_mul hK hq hq0 (by norm_num)
      linarith
    exact mul_le_mul a hnu (by positivity) (by norm_num)
  have t3 : (5 * kappa (kappa 0) + √6) / (n : ℝ) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 115 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t4 : (5 + √6) / (n : ℝ) ≤ (5 + 24495 / 10000) * (1 / 115 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t10 : 0 ≤ (1 + √2 * kappa (kappa 0)) / √(n : ℝ) := by positivity
  have t20 : 0 ≤ 2 * K4 n * kappa (kappa 0) / (n : ℝ) := by positivity
  have t30 : 0 ≤ (5 * kappa (kappa 0) + √6) / (n : ℝ) := by positivity
  unfold cAr
  simp only [Function.comp_apply]
  rw [sqrt_mA, div_eq_mul_one_div (183559 / 100000 : ℝ), ← hu]
  have e1 : ((1 + √2 * kappa (kappa 0)) / √(n : ℝ) + 2 * K4 n * kappa (kappa 0) / (n : ℝ)) *
      (1 + 5 / (mA n : ℝ)) ≤
      ((1 + 141422 / 100000 * (49376 / 100000)) * u +
        2 * (346463 / 100000) * (49376 / 100000) * (1 / 115 * u)) * (1 + 3 / 100000000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have e2 : (5 * kappa (kappa 0) + √6) / (n : ℝ) * √(1 + 5 / (mA n : ℝ)) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 115 * u) * (1 + 2 / 100000000) :=
    mul_le_mul t3 hsA hsA0 (by positivity)
  nlinarith

theorem eAFr_L : eAFr n (mA n) (mF n) ≤ 22763 / 10000 / √(n : ℝ) := by
  have hs := sqrt_n_geL hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := cF2oL hn
  have h10 : 0 ≤ cF2o (mF n) := Real.sqrt_nonneg _
  have h3 := cArL hn
  have e1 := N0_L hn
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  rw [div_eq_mul_one_div, ← hu] at h1 h3 ⊢
  have e2 : cF2o (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) ≤
      44066 / 100000 * u * (1 + 7565 / 100000000) :=
    mul_le_mul h1 e1 (by positivity) (by positivity)
  unfold eAFr
  nlinarith

theorem Vb_L : Vb n ≤ 24801 / 100000 := by
  have hn4 := n4096_ofL hn
  have hn1 : 1 ≤ n := by omega
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geL hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr_L hn
  have h2 := eWr_L hn
  have h3 := sU_L hn
  have h4 := sig4_le
  have h40 := sig4_nonneg
  have hsU := sU_nonneg (2 * n)
  have hW0 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have hQ := q0_ge16
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 115 := by
    rw [ht]
    exact one_div_le_one_div_of_le (by norm_num) hs
  have e1 : (22763 : ℝ) / 10000 / √(n : ℝ) = 22763 / 10000 * t := by rw [ht]; ring
  have e2 : (98861 : ℝ) / 100000 / √(n : ℝ) = 98861 / 100000 * t := by rw [ht]; ring
  have e3 : (36092 : ℝ) / 100000 / √(n : ℝ) = 36092 / 100000 * t := by rw [ht]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h5 : sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) ≤
      4404 / 10000 * (134953 / 100000 * t) := by
    apply mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  have h6 : 183 / 100 / (n : ℝ) ≤ 183 / 100 / 13225 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold Vb
  nlinarith

theorem EHH_leL : EHH n (1 / 20) ≤ 2427 / 10 * (n : ℝ) / (mW n : ℝ) := by
  have hn4 := n4096_ofL hn
  have hm0 := mW_posL hn
  have hn' := nR_geL hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1 := OmegaH2_le hn4
  have h2 := BetaH_le hn4
  rw [div_eq_mul_one_div (1195 : ℝ), ← hx] at h1
  rw [div_eq_mul_one_div (17200 : ℝ), ← hx] at h2
  have hc := cRhoH_ge
  have hw := wLowH_pos
  have hk : (n : ℝ) / (wLowH ^ 2 * cRhoH (1 / 20)) ≤ (n : ℝ) * (202 / 1000) := by
    have a1 : (n : ℝ) / (wLowH ^ 2 * cRhoH (1 / 20)) ≤ (n : ℝ) / (wLowH ^ 2 * (528 / 100)) :=
      div_le_div_of_nonneg_left hn0.le (by positivity)
        (mul_le_mul_of_nonneg_left hc (by positivity))
    refine a1.trans ?_
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hn0.le
    unfold wLowH
    norm_num
  have hO0 := OmegaH2_nonneg n (1 / 20)
  have h3 : (n : ℝ) / (wLowH ^ 2 * cRhoH (1 / 20)) * OmegaH2 n (1 / 20) ≤
      (n : ℝ) * (202 / 1000) * (1195 * x) :=
    mul_le_mul hk h1 hO0 (by positivity)
  unfold EHH
  rw [div_eq_mul_one_div (2427 / 10 * (n : ℝ)), ← hx]
  have h4 : 17200 * x ≤ 131 / 100 * (n : ℝ) * x := by
    refine mul_le_mul_of_nonneg_right ?_ hx0.le
    linarith
  have h5 : 0 ≤ (n : ℝ) * x := by positivity
  nlinarith

theorem EHH_L : EHH n (1 / 20) ≤ 15958 / 100000000 / (n : ℝ) := by
  have hx := nR_geL hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := EHH_leL hn
  obtain ⟨-, h2, -⟩ := mW_moreL hn
  have e : 2427 / 10 * (n : ℝ) / (mW n : ℝ) = 2427 / 10 * ((n : ℝ) / (mW n : ℝ)) := by ring
  rw [e] at h
  have e2 : (15958 : ℝ) / 100000000 / (n : ℝ) = 15958 / 100000000 * (1 / (n : ℝ)) := by ring
  rw [e2]
  have hy0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  nlinarith

end bigL

end BstLean.Part143

open BstLean.Part143 in
#print axioms inv_mFL
open BstLean.Part143 in
#print axioms f2_L
open BstLean.Part143 in
#print axioms f3_L
open BstLean.Part143 in
#print axioms dA0_L
open BstLean.Part143 in
#print axioms dA1_L
open BstLean.Part143 in
#print axioms dA2_L
open BstLean.Part143 in
#print axioms cAdltL
open BstLean.Part143 in
#print axioms N0_L
open BstLean.Part143 in
#print axioms sqrt_eps4_L
open BstLean.Part143 in
#print axioms tauW142_L
open BstLean.Part143 in
#print axioms eAFr_L
open BstLean.Part143 in
#print axioms Vb_L
open BstLean.Part143 in
#print axioms EHH_L
