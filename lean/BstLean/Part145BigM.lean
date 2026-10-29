import BstLean.Part143Big

/-!
# Part 145: the numeric constants of `Part143Big` again, for `n ≥ 9216 = 96²`

The lemmas of `Part143Big` (there with `16384 ≤ n`) with the hypothesis `9216 ≤ n`
(`√n ≥ 96`, `√(m_F) ≥ 9.7979·√n`, `m_W ≥ 96·n³`), each constant computed again; names with
the suffix `M`. Headlines: `inv_mFM`, `f1_M`, `f2_M`, `f3_M`, `dA0_M`, `dA1_M`, `dA2_M`,
`cAdltM`, `N0_M`, `sqrt_eps4_M`, `tauW142_M`, `eAFr_M`, `Vb_M`, `EHH_M`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142
open BstLean.Part143

section bigM

variable {n : ℕ} (hn : 9216 ≤ n)

include hn

lemma nR_geM : (9216 : ℝ) ≤ n := by exact_mod_cast hn

lemma n4096_ofM : 4096 ≤ n := by omega

lemma sqrt_n_geM : (96 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_geM hn
  exact Real.le_sqrt_of_sq_le (by linarith)

lemma yzM : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 9216 ∧ z ≤ 1 / 96 ∧ r ≤ 707107 / 1000000 * z ∧
    r ≤ 1 / 135 ∧ y = z * z ∧ y ≤ 1 / 96 * z := by
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geM hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have h135 : (135 : ℝ) ≤ √(2 * (n : ℝ)) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 96 := one_div_le_one_div_of_le (by norm_num) hs
  have hyz : 1 / (n : ℝ) = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    hz0, by positivity, one_div_le_one_div_of_le (by norm_num) hx,
    hz1, ?_, one_div_le_one_div_of_le (by norm_num) h135, hyz, ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [hyz]
    exact mul_le_mul_of_nonneg_right hz1 hz0.le

lemma K4_leM : K4 n ≤ 346486 / 100000 := by
  have hx := nR_geM hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 9216 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

lemma inv_mFM :
    1 / √(mF n : ℝ) ≤ 10000 / 97979 * (1 / √(n : ℝ)) ∧
      1 / (mF n : ℝ) ≤ 1 / 9216 * (1 / √(n : ℝ)) := by
  have hx := nR_geM hn
  have hs := sqrt_n_geM hn
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hms := BstLean.Part139.mF_ge_s (n4096_ofM hn)
  have hm0 : (0 : ℝ) < mF n := by nlinarith
  have h8 : 97979 / 10000 * √(n : ℝ) ≤ √(mF n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : (97979 / 10000 * √(n : ℝ)) ^ 2 = (97979 / 10000) ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    rw [h1]
    have h2 : 96 * (n : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by nlinarith
    have h3 : ((97979 : ℝ) / 10000) ^ 2 * (n : ℝ) ≤ 96 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
    linarith
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have e : 10000 / 97979 * (1 / √(n : ℝ)) * √(mF n : ℝ) =
        √(mF n : ℝ) / (97979 / 10000 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 9216 * (1 / √(n : ℝ)) * (mF n : ℝ) = (mF n : ℝ) / (9216 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have h2 : 9216 * √(n : ℝ) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right hx hs0.le
    linarith

lemma mW_geM : 96 * (n : ℝ) ^ 3 ≤ mW n := by
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast mW_sq_ge n
  have h6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
  have h2 : (96 * (n : ℝ) ^ 3) ^ 2 ≤ (mW n : ℝ) ^ 2 := by
    calc (96 * (n : ℝ) ^ 3) ^ 2 = 9216 * (n : ℝ) ^ 6 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 6 := mul_le_mul_of_nonneg_right (by linarith) h6
      _ = (n : ℝ) ^ 7 := by ring
      _ ≤ _ := h1
  exact (abs_le_of_sq_le_sq' h2 (Nat.cast_nonneg _)).2

lemma mW_posM : (0 : ℝ) < mW n := by
  have hx := nR_geM hn
  have h := mW_geM hn
  have : (0 : ℝ) < 96 * (n : ℝ) ^ 3 := by positivity
  linarith

lemma mW_moreM : (n : ℝ) / (mW n : ℝ) ≤ 1 / 8153726976 ∧
    (n : ℝ) / (mW n : ℝ) ≤ 1 / 884736 * (1 / (n : ℝ)) ∧
    90297 * √(n : ℝ) ≤ √(mW n : ℝ) := by
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mW_geM hn
  have hm0 := mW_posM hn
  have hsq : (84934656 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h3 : 84934656 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hsq hx0.le
    calc 84934656 * (n : ℝ) ≤ (n : ℝ) ^ 2 * (n : ℝ) := this
      _ = (n : ℝ) ^ 3 := by ring
  have h35 : 8153726976 * (n : ℝ) ≤ mW n := by linarith
  have h3' : 9216 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hx (sq_nonneg (n : ℝ))
    calc 9216 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
      _ = (n : ℝ) ^ 3 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 884736 * (1 / (n : ℝ)) * (884736 * (n : ℝ) ^ 2) = (n : ℝ) := by
      field_simp
    have : 1 / 884736 * (1 / (n : ℝ)) * (884736 * (n : ℝ) ^ 2) ≤
        1 / 884736 * (1 / (n : ℝ)) * (mW n : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, Real.sq_sqrt hx0.le]
    have : (90297 : ℝ) ^ 2 * (n : ℝ) ≤ 8153726976 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) hx0.le
    linarith

lemma sqrt_one_addM : √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 9216 := by
  have hx := nR_geM hn
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 2 / (n : ℝ) ≤ 2 / 9216 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

lemma sU_M : sU (2 * n) ≤ 36140 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := s3_le16
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 36140 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (173206 / 100000) / 2 * (1 / 96 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

lemma sU_constM : sU (2 * n) ≤ 3765 / 1000000 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have h := sU_M hn
  have e : (36140 : ℝ) / 100000 / √(n : ℝ) = 36140 / 100000 * z := by rw [hz]; ring
  rw [e] at h
  linarith

lemma epsWM : epsW (mW n) * (n : ℝ) ≤ 1001 / 100 / 8153726976 := by
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm0 := mW_posM hn
  obtain ⟨a2, -, -⟩ := mW_moreM hn
  have hm := mW_geR (n4096_ofM hn)
  have e : epsW (mW n) * (n : ℝ) = (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) := by
    unfold epsW
    field_simp
    ring
  have a1 : 25 / (mW n : ℝ) ≤ 1 / 100 := by
    rw [div_le_iff₀ hm0]; linarith
  have a10 : (0 : ℝ) ≤ 25 / (mW n : ℝ) := by positivity
  have a20 : (0 : ℝ) ≤ (n : ℝ) / (mW n : ℝ) := by positivity
  rw [e]
  calc (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) ≤ 1001 / 100 * (1 / 8153726976) :=
        mul_le_mul (by linarith) a2 a20 (by norm_num)
    _ = _ := by norm_num

lemma eHid_uM :
    eHid (mW n) ≤ 15026 / 100000000 * (1 / √(n : ℝ)) ∧
      √(epsW (mW n)) ≤ 3504 / 100000000 * (1 / √(n : ℝ)) := by
  have hn4 := n4096_ofM hn
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn4
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hε := epsWM hn
  have hε0 := epsW_nonneg (mW n)
  obtain ⟨-, -, hsW⟩ := mW_moreM hn
  have hsW0 : (0 : ℝ) < √(mW n : ℝ) := by nlinarith
  have hm := mW_geR hn4
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have s1 : √(5 * epsW (mW n)) ≤ 7835 / 100000000 * u := by
    have := sqrt_le_div_s hn4 (x := 5 * epsW (mW n)) (c := 7835 / 100000000) (by norm_num)
      (by
        have e : 5 * epsW (mW n) * (n : ℝ) = 5 * (epsW (mW n) * (n : ℝ)) := by ring
        rw [e]
        refine le_trans (mul_le_mul_of_nonneg_left hε (by norm_num)) ?_
        norm_num)
    rwa [div_eq_mul_one_div, ← hu] at this
  have s2 : √(epsW (mW n)) ≤ 3504 / 100000000 * u := by
    have := sqrt_le_div_s hn4 (x := epsW (mW n)) (c := 3504 / 100000000) (by norm_num)
      (hε.trans (by norm_num))
    rwa [div_eq_mul_one_div, ← hu] at this
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have hiW : 1 / √(mW n : ℝ) ≤ 1 / 90297 * u := by
    rw [hu, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsW
  have hiW0 : 0 ≤ 1 / √(mW n : ℝ) := by positivity
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 90297 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 90297 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  refine ⟨?_, s2⟩
  unfold eHid
  linarith

lemma eWsmallM : eWsmall n (mW n) ≤ 27092 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  obtain ⟨hH, hE⟩ := eHid_uM hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hK := K4_leM hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (346486 / 100000) * (1 / 96 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 96) * (15026 / 100000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hy, hz]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 27092 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

lemma eWr_M : eWr (2 * n) n (mW n) ≤ 103469 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have h1 := sU_constM hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmallM hn
  have hq := BstLean.Part132.kappa2_zero_ge'
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49373 / 100000) ^ 2 := by nlinarith
  have e2 : (27092 : ℝ) / 100000 / √(n : ℝ) = 27092 / 100000 * z := by rw [hz]; ring
  rw [e2] at h2
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49373 / 100000) ^ 2 + 2 * (3765 / 1000000)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 103469 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

theorem tauW142_M : tauW142 n ≤ 139609 / 100000 / √(n : ℝ) := by
  have h2 := eWr_M hn
  have h3 := sU_M hn
  unfold tauW142
  have e : (139609 : ℝ) / 100000 / √(n : ℝ) =
      103469 / 100000 / √(n : ℝ) + 36140 / 100000 / √(n : ℝ) := by ring
  rw [e]
  linarith

lemma f1_M : f1 (mF n) ≤ 35421 / 100000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mFM hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h3 := s3_le16
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have e : f1 (mF n) = 2 * (√3 * (1 / √(mF n : ℝ))) + 6 * (1 / (mF n : ℝ)) := by
    unfold f1; ring
  have e2 : 35421 / 100000 / √(n : ℝ) = 35421 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p1 : √3 * (1 / √(mF n : ℝ)) ≤ 173206 / 100000 * (10000 / 97979 * (1 / √(n : ℝ))) :=
    mul_le_mul h3 ha ha0 (by norm_num)
  linarith

lemma f2_M : f2 (mF n) ≤ 4177 / 100000 / √(n : ℝ) := by
  have hn4 := n4096_ofM hn
  obtain ⟨ha, hb⟩ := inv_mFM hn
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
  have e2 : 4177 / 100000 / √(n : ℝ) = 4177 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : bG kappa * √5 ≤ 363382 / 1000000 * (223607 / 100000) :=
    mul_le_mul hbG h5 h50 (by norm_num)
  have p1 : bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) ≤
      363382 / 1000000 * (223607 / 100000) / 2 * (10000 / 97979 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) ha ha0 (by norm_num)
  have q0 : kappa 0 * Kr (mF n) ≤ 31831 / 100000 * (21652 / 10000) :=
    mul_le_mul hk hKr hKr0 (by norm_num)
  have q1 : 4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) ≤
      4 * (31831 / 100000 * (21652 / 10000)) * (1 / 9216 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  linarith

lemma f3_M : f3 (mF n) ≤ 7265 / 100000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mFM hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h5 := AgD.sqrt5_le'
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have e : f3 (mF n) = kappa 0 * √5 * (1 / √(mF n : ℝ)) := by
    unfold f3; ring
  have e2 : 7265 / 100000 / √(n : ℝ) = 7265 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : kappa 0 * √5 ≤ 31831 / 100000 * (223607 / 100000) :=
    mul_le_mul hk h5 h50 (by norm_num)
  have p1 : kappa 0 * √5 * (1 / √(mF n : ℝ)) ≤
      31831 / 100000 * (223607 / 100000) * (10000 / 97979 * (1 / √(n : ℝ))) :=
    mul_le_mul p0 ha ha0 (by norm_num)
  linarith

lemma nsqM : (84934656 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hx := nR_geM hn
  nlinarith

lemma Q5_M : √(1 + 5 / (mA n : ℝ)) ≤ 1 + 3 / 100000000 := by
  have h2 := nsqM hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 5 / (n : ℝ) ^ 2 ≤ 5 / 84934656 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma Q2_M : √(1 + 2 / (mA n : ℝ)) ≤ 1 + 2 / 100000000 := by
  have h2 := nsqM hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 2 / (n : ℝ) ^ 2 ≤ 2 / 84934656 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma sSM : AgD.sS (mA n) ≤ 200000006 / 100000000 := by
  have := Q5_M hn
  unfold AgD.sS
  linarith

lemma SSM : AgD.SS (mA n) ≤ 200000013 / 100000000 := by
  have h1 := Q5_M hn
  have h2 := sSM hn
  have h3 := AgD.sS_nn (mA n)
  unfold AgD.SS
  calc √(1 + 5 / (mA n : ℝ)) * AgD.sS (mA n)
      ≤ (1 + 3 / 100000000) * (200000006 / 100000000) := by gcongr
    _ ≤ 200000013 / 100000000 := by norm_num

lemma DSM : AgD.DS (mA n) ≤ 894429 / 100000 * (1 / (n : ℝ)) := by
  have h5 := AgD.sqrt5_le'
  have h2 := sSM hn
  have h3 := AgD.sS_nn (mA n)
  have h4 := AgD.dS_le (n4096_ofM hn)
  unfold AgD.DS
  rw [sqrt_mA]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  rw [← hy] at h4 ⊢
  refine le_trans (le_of_eq (?_ : _ = √5 * y * AgD.sS (mA n) + AgD.dS (mA n))) ?_
  · rw [hy]; ring
  · calc √5 * y * AgD.sS (mA n) + AgD.dS (mA n)
        ≤ 223607 / 100000 * y * (200000006 / 100000000) + 447214 / 100000 * y := by gcongr
      _ ≤ 894429 / 100000 * y := by linarith

lemma LSM : AgD.LS (mA n) ≤ 491 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have hn4 := n4096_ofM hn
  have h5 := AgD.sqrt5_le'
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have h2 := sSM hn
  have h3 := AgD.sS_nn (mA n)
  have h4 := AgD.dS_le hn4
  have h4n := AgD.dS_nn (mA n)
  have h6 := AgD.lS_le hn4
  unfold AgD.LS
  rw [sqrt_mA, mA_eqR]
  rw [← hy] at h4 h6 ⊢
  have hyy : y ^ 2 ≤ y * (1 / 9216) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = AgD.lS (mA n) + 4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) +
    √5 * y * AgD.dS (mA n))) ?_
  · rw [hy]; ring
  · calc AgD.lS (mA n) + 4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) + √5 * y * AgD.dS (mA n)
        ≤ 176 / 10 * y ^ 2 + 4 * (11 / 5) * y ^ 2 * (200000006 / 100000000) +
          223607 / 100000 * y * (447214 / 100000 * y) := by gcongr
      _ ≤ 491 / 100000 * y := by nlinarith

lemma nc0_M : AgD.nc0 (mA n) ≤ 81316 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have hn4 := n4096_ofM hn
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
  have hyy : y ^ 2 ≤ y * (1 / 9216) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2))) ?_
  · rw [hy]; ring
  · calc bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2)
        ≤ 363382 / 1000000 * (223607 / 100000) * y +
          31831 / 100000 * (8 * (11 / 5) * y ^ 2) := by gcongr
      _ ≤ 81316 / 100000 * y := by nlinarith

theorem dA1_M : dA1 n (mA n) ≤ 1 + 1 / 9216 := by
  unfold dA1
  exact sqrt_one_addM hn

theorem dA0_M : dA0 n (mA n) ≤ 81325 / 100000 / (n : ℝ) := by
  have h1 := sqrt_one_addM hn
  have a1 := nc0_M hn
  have n1 := AgD.nc0_nn (mA n)
  have hy0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold dA0
  refine le_trans (?_ : _ ≤ 81325 / 100000 * (1 / (n : ℝ))) (le_of_eq (by ring))
  calc √(1 + 2 / (n : ℝ)) * AgD.nc0 (mA n)
      ≤ (1 + 1 / 9216) * (81316 / 100000 * (1 / (n : ℝ))) := by gcongr
    _ ≤ 81325 / 100000 * (1 / (n : ℝ)) := by nlinarith

theorem dA2_M : dA2 n (mA n) ≤ 103935 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have h1 := sqrt_one_addM hn
  have h3 := s3_le16
  have hQ := Q2_M hn
  unfold dA2
  rw [sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))))) ?_
  · rw [hy]; ring
  · refine le_trans (?_ : _ ≤ 103935 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))
        ≤ (1 + 1 / 9216) * (2 * (173206 / 100000) * y + 173206 / 100000 * y *
          (4 * (1 + 2 / 100000000))) := by gcongr
      _ ≤ 103935 / 10000 * y := by nlinarith

theorem cAdltM : cAdlt n (mA n) ≤ 70664 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzM hn
  have hn4 := n4096_ofM hn
  have h2 := Part133.sqrt2_le
  have hK4 := K4_leM hn
  have hK40 := K4_nonneg n
  have a2 := SSM hn
  have a3 := DSM hn
  have a4 := LSM hn
  have n2 := AgD.SS_nn (mA n)
  have n3 := AgD.DS_nn (mA n)
  rw [← hy] at a3 a4
  have hzy : z * y ≤ y * (1 / 96) := by nlinarith
  unfold cAdlt
  refine le_trans (le_of_eq (?_ : _ = AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) +
    √2 * z * AgD.DS (mA n))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 70664 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n)
        ≤ 491 / 100000 * y + 346486 / 100000 * y * (200000013 / 100000000) +
          141422 / 100000 * z * (894429 / 100000 * y) := by gcongr
      _ ≤ 70664 / 10000 * y := by nlinarith

lemma N0_M : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ 1 + 10857 / 100000000 := by
  have h2 := nsqM hn
  have h1 : 5 / (mA n : ℝ) ≤ 5 / 84934656 := by
    rw [mA_eqR]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have h10 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have h3 := sqrt_one_addM hn
  have h30 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
  calc (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))
      ≤ (1 + 5 / 84934656) * (1 + 1 / 9216) := mul_le_mul (by linarith) h3 h30 (by norm_num)
    _ ≤ 1 + 10857 / 100000000 := by norm_num

lemma sqrt_eps4_M : √(eps4 n (mA n)) ≤ 141460 / 100000 / √(n : ℝ) := by
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  refine sqrt_le_div_s (n4096_ofM hn) (by norm_num) ?_
  unfold eps4
  rw [mA_eqR]
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 9216 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyn : y * (n : ℝ) = 1 := by rw [hy]; field_simp
  have e1 : 5 / (n : ℝ) ^ 2 = 5 * y ^ 2 := by rw [hy]; ring
  have e2 : 2 / (n : ℝ) = 2 * y := by rw [hy]; ring
  rw [e1, e2]
  have hy2 : y ^ 2 ≤ 1 / 9216 * y := by nlinarith
  have hy20 : 0 ≤ y ^ 2 := by positivity
  have hb : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1 ≤ 200109 / 100000 * y := by
    have h5 : 5 * y ^ 2 ≤ 5 / 9216 * y := by nlinarith
    have h50 : 0 ≤ 5 * y ^ 2 := by positivity
    have h5c : 5 * y ^ 2 ≤ 1 / 1000000 := by nlinarith
    have h6 : (1 + 5 * y ^ 2) ^ 2 ≤ 1 + 10851 / 10000000 * y := by nlinarith
    have h7 : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) ≤ (1 + 10851 / 10000000 * y) * (1 + 2 * y) :=
      mul_le_mul_of_nonneg_right h6 (by linarith)
    nlinarith
  calc ((1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1) * (n : ℝ)
      ≤ 200109 / 100000 * y * (n : ℝ) := mul_le_mul_of_nonneg_right hb hx0.le
    _ = 200109 / 100000 := by rw [mul_assoc, hyn, mul_one]
    _ ≤ (141460 / 100000) ^ 2 := by norm_num

lemma cF2oM : cF2o (mF n) ≤ 48230 / 100000 / √(n : ℝ) := by
  have hn4 := n4096_ofM hn
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geM hn
  have hm := mF_geR hn4
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hms := BstLean.Part139.mF_ge_s hn4
  have hmF : 96 * (n : ℝ) ≤ mF n := by
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
  have hc2 : (223303 : ℝ) / 10000 ≤ (48230 / 100000) ^ 2 * 96 := by norm_num
  calc (6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2) * (n : ℝ)
      ≤ 223303 / 10000 * (n : ℝ) := mul_le_mul_of_nonneg_right h7 hx0.le
    _ ≤ (48230 / 100000) ^ 2 * 96 * (n : ℝ) := mul_le_mul_of_nonneg_right hc2 hx0.le
    _ = (48230 / 100000) ^ 2 * (96 * (n : ℝ)) := by ring
    _ ≤ (48230 / 100000) ^ 2 * (mF n : ℝ) := mul_le_mul_of_nonneg_left hmF (by norm_num)

lemma cArM : cAr (kappa ∘ kappa) (mA n) n ≤ 186276 / 100000 / √(n : ℝ) := by
  obtain ⟨y, u, r, hy, hu, hr, hy0, hu0, hr0, hy1, hu1, hr1, hr2, hyz, hnu⟩ := yzM hn
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK := K4_leM hn
  have hK0 := K4_nonneg n
  have hq := kappa2_zero_le
  have hq0 := q_mem.1
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hA : 5 / (mA n : ℝ) ≤ 6 / 100000000 := by
    have h2' := nsqM hn
    rw [mA_eqR, div_le_iff₀ (by positivity)]
    linarith
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hsA := Q5_M hn
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
      2 * (346486 / 100000) * (49376 / 100000) * (1 / 96 * u) := by
    rw [div_eq_mul_one_div]
    have a : 2 * K4 n * kappa (kappa 0) ≤ 2 * (346486 / 100000) * (49376 / 100000) := by
      have := mul_le_mul hK hq hq0 (by norm_num)
      linarith
    exact mul_le_mul a hnu (by positivity) (by norm_num)
  have t3 : (5 * kappa (kappa 0) + √6) / (n : ℝ) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 96 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t4 : (5 + √6) / (n : ℝ) ≤ (5 + 24495 / 10000) * (1 / 96 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t10 : 0 ≤ (1 + √2 * kappa (kappa 0)) / √(n : ℝ) := by positivity
  have t20 : 0 ≤ 2 * K4 n * kappa (kappa 0) / (n : ℝ) := by positivity
  have t30 : 0 ≤ (5 * kappa (kappa 0) + √6) / (n : ℝ) := by positivity
  unfold cAr
  simp only [Function.comp_apply]
  rw [sqrt_mA, div_eq_mul_one_div (186276 / 100000 : ℝ), ← hu]
  have e1 : ((1 + √2 * kappa (kappa 0)) / √(n : ℝ) + 2 * K4 n * kappa (kappa 0) / (n : ℝ)) *
      (1 + 5 / (mA n : ℝ)) ≤
      ((1 + 141422 / 100000 * (49376 / 100000)) * u +
        2 * (346486 / 100000) * (49376 / 100000) * (1 / 96 * u)) * (1 + 6 / 100000000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have e2 : (5 * kappa (kappa 0) + √6) / (n : ℝ) * √(1 + 5 / (mA n : ℝ)) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 96 * u) * (1 + 3 / 100000000) :=
    mul_le_mul t3 hsA hsA0 (by positivity)
  nlinarith

theorem eAFr_M : eAFr n (mA n) (mF n) ≤ 23452 / 10000 / √(n : ℝ) := by
  have hs := sqrt_n_geM hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := cF2oM hn
  have h10 : 0 ≤ cF2o (mF n) := Real.sqrt_nonneg _
  have h3 := cArM hn
  have e1 := N0_M hn
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  rw [div_eq_mul_one_div, ← hu] at h1 h3 ⊢
  have e2 : cF2o (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) ≤
      48230 / 100000 * u * (1 + 10857 / 100000000) :=
    mul_le_mul h1 e1 (by positivity) (by positivity)
  unfold eAFr
  nlinarith

theorem Vb_M : Vb n ≤ 25394 / 100000 := by
  have hn4 := n4096_ofM hn
  have hn1 : 1 ≤ n := by omega
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_geM hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr_M hn
  have h2 := eWr_M hn
  have h3 := sU_M hn
  have h4 := sig4_le
  have h40 := sig4_nonneg
  have hsU := sU_nonneg (2 * n)
  have hW0 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have hQ := q0_ge16
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 96 := by
    rw [ht]
    exact one_div_le_one_div_of_le (by norm_num) hs
  have e1 : (23452 : ℝ) / 10000 / √(n : ℝ) = 23452 / 10000 * t := by rw [ht]; ring
  have e2 : (103469 : ℝ) / 100000 / √(n : ℝ) = 103469 / 100000 * t := by rw [ht]; ring
  have e3 : (36140 : ℝ) / 100000 / √(n : ℝ) = 36140 / 100000 * t := by rw [ht]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h5 : sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) ≤
      4404 / 10000 * (139609 / 100000 * t) := by
    apply mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  have h6 : 183 / 100 / (n : ℝ) ≤ 183 / 100 / 9216 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold Vb
  nlinarith

theorem EHH_leM : EHH n (1 / 20) ≤ 2433 / 10 * (n : ℝ) / (mW n : ℝ) := by
  have hn4 := n4096_ofM hn
  have hm0 := mW_posM hn
  have hn' := nR_geM hn
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
  rw [div_eq_mul_one_div (2433 / 10 * (n : ℝ)), ← hx]
  have h4 : 17200 * x ≤ 187 / 100 * (n : ℝ) * x := by
    refine mul_le_mul_of_nonneg_right ?_ hx0.le
    linarith
  have h5 : 0 ≤ (n : ℝ) * x := by positivity
  nlinarith

theorem EHH_M : EHH n (1 / 20) ≤ 27500 / 100000000 / (n : ℝ) := by
  have hx := nR_geM hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := EHH_leM hn
  obtain ⟨-, h2, -⟩ := mW_moreM hn
  have e : 2433 / 10 * (n : ℝ) / (mW n : ℝ) = 2433 / 10 * ((n : ℝ) / (mW n : ℝ)) := by ring
  rw [e] at h
  have e2 : (27500 : ℝ) / 100000000 / (n : ℝ) = 27500 / 100000000 * (1 / (n : ℝ)) := by ring
  rw [e2]
  have hy0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  nlinarith

end bigM

end BstLean.Part145

open BstLean.Part145 in
#print axioms inv_mFM
open BstLean.Part145 in
#print axioms f1_M
open BstLean.Part145 in
#print axioms f2_M
open BstLean.Part145 in
#print axioms f3_M
open BstLean.Part145 in
#print axioms dA0_M
open BstLean.Part145 in
#print axioms dA1_M
open BstLean.Part145 in
#print axioms dA2_M
open BstLean.Part145 in
#print axioms cAdltM
open BstLean.Part145 in
#print axioms N0_M
open BstLean.Part145 in
#print axioms sqrt_eps4_M
open BstLean.Part145 in
#print axioms tauW142_M
open BstLean.Part145 in
#print axioms eAFr_M
open BstLean.Part145 in
#print axioms Vb_M
open BstLean.Part145 in
#print axioms EHH_M
