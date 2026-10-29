import BstLean.Part142Dist

/-!
# Part 142: the numeric constants again, for `n ≥ 32768 = 2¹⁵`

Role: `delegations/statements/p142-spec.md`, item 4 (the least `n₀` of level `99/100`). The
level `99/100` is proved for `n ≥ 32768` only, so the constants of `Part142Dist`,
`Part142AgentD`, `Part142FD` and of Part 139 are proved again here with the hypothesis
`32768 ≤ n` (`√n ≥ 181`, `√(m_F) ≥ 13.45·√n`, `m_W ≥ 181·n³`).

* `tauW142_big`: `tauW142 n ≤ 1.2646/√n`.
* `f1_big`, `f2_big`, `f3_big`; `cA0_big`, `cA1_big`, `cA2_big`, `dA0_big`, `dA1_big`, `dA2_big`,
  `cAdlt_big`; `N0_big`, `sqrt_eps4_big`.
* `goodHat_big`: `Pr(goodHat n fails) ≤ 0.002 + 20.63/n`.
* `gD_big`: `gD0 n ≤ 0.5812/√n`, `gD1 n ≤ 1.9299/√n`, `gD2 n ≤ 10.52/n`.
* `eD142a_big`: `eD142a n ≤ 1.798/√n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part142

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141

section big

variable {n : ℕ} (hn : 32768 ≤ n)

include hn

lemma nR_ge_big : (32768 : ℝ) ≤ n := by exact_mod_cast hn

lemma n4096_of_big : 4096 ≤ n := by omega

/-- `√n ≥ 181` for `n ≥ 32768`. -/
lemma sqrt_n_ge_big : (181 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_ge_big hn
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` for `n ≥ 32768`. -/
lemma yzB : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 32768 ∧ z ≤ 1 / 181 ∧ r ≤ 707107 / 1000000 * z ∧
    r ≤ 1 / 256 ∧ y = z * z ∧ y ≤ 1 / 181 * z := by
  have hx := nR_ge_big hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge_big hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have h256 : (256 : ℝ) ≤ √(2 * (n : ℝ)) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 181 := one_div_le_one_div_of_le (by norm_num) hs
  have hyz : 1 / (n : ℝ) = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    hz0, by positivity, one_div_le_one_div_of_le (by norm_num) hx,
    hz1, ?_, one_div_le_one_div_of_le (by norm_num) h256, hyz, ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [hyz]
    exact mul_le_mul_of_nonneg_right hz1 hz0.le

/-! ## Basic -/

/-- `K₄(n) ≤ 3.4644` for `n ≥ 32768` (the value `3.4643` is too small:
`3.4643² < 12 + 48/32768`). -/
lemma K4_le_big : K4 n ≤ 34644 / 10000 := by
  have hx := nR_ge_big hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 32768 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-- `1/√m_F ≤ (20/269)·(1/√n)` (`269/20 = 13.45`) and `1/m_F ≤ (1/32768)·(1/√n)`. -/
lemma inv_mF_big :
    1 / √(mF n : ℝ) ≤ 20 / 269 * (1 / √(n : ℝ)) ∧
      1 / (mF n : ℝ) ≤ 1 / 32768 * (1 / √(n : ℝ)) := by
  have hx := nR_ge_big hn
  have hs := sqrt_n_ge_big hn
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hms := BstLean.Part139.mF_ge_s (n4096_of_big hn)
  have hm0 : (0 : ℝ) < mF n := by nlinarith
  have h8 : 269 / 20 * √(n : ℝ) ≤ √(mF n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : (269 / 20 * √(n : ℝ)) ^ 2 = 72361 / 400 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]; norm_num
    rw [h1]
    have h2 : 181 * (n : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by nlinarith
    linarith
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have e : 20 / 269 * (1 / √(n : ℝ)) * √(mF n : ℝ) = √(mF n : ℝ) / (269 / 20 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 32768 * (1 / √(n : ℝ)) * (mF n : ℝ) = (mF n : ℝ) / (32768 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have h2 : 32768 * √(n : ℝ) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right hx hs0.le
    linarith

/-- `m_W ≥ 181·n³` for `n ≥ 32768`. -/
lemma mW_ge_big : 181 * (n : ℝ) ^ 3 ≤ mW n := by
  have hx := nR_ge_big hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast mW_sq_ge n
  have h6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
  have h2 : (181 * (n : ℝ) ^ 3) ^ 2 ≤ (mW n : ℝ) ^ 2 := by
    calc (181 * (n : ℝ) ^ 3) ^ 2 = 32761 * (n : ℝ) ^ 6 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 6 := mul_le_mul_of_nonneg_right (by linarith) h6
      _ = (n : ℝ) ^ 7 := by ring
      _ ≤ _ := h1
  exact (abs_le_of_sq_le_sq' h2 (Nat.cast_nonneg _)).2

lemma sqrt_one_add_big : √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 32768 := by
  have hx := nR_ge_big hn
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 2 / (n : ℝ) ≤ 2 / 32768 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-! ## The World link and the inputs -/

lemma sU_big : sU (2 * n) ≤ 3601 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 3601 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (17321 / 10000) / 2 * (1 / 181 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

lemma sU_const_big : sU (2 * n) ≤ 2 / 1000 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have h := sU_big hn
  have e : (3601 : ℝ) / 10000 / √(n : ℝ) = 3601 / 10000 * z := by rw [hz]; ring
  rw [e] at h
  linarith

/-- The hidden layers of `W`: `eHid (m_W) ≤ (429/10⁶)/√n` and `√(epsW m_W) ≤ (102/10⁶)/√n`
(the bounds inside `eWsmall_scale` of Part 139). -/
lemma eHid_u :
    eHid (mW n) ≤ 429 / 1000000 * (1 / √(n : ℝ)) ∧
      √(epsW (mW n)) ≤ 102 / 1000000 * (1 / √(n : ℝ)) := by
  have hn4 := n4096_of_big hn
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
  refine ⟨?_, s2⟩
  unfold eHid
  linarith

lemma eWsmall_big : eWsmall n (mW n) ≤ 1442 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  obtain ⟨hH, hE⟩ := eHid_u hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hK := K4_le_big hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (34644 / 10000) * (1 / 181 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 181) * (429 / 1000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hy, hz]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 1442 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

lemma eWr_big : eWr (2 * n) n (mW n) ≤ 9045 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have h1 := sU_const_big hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall_big hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have e2 : (1442 : ℝ) / 10000 / √(n : ℝ) = 1442 / 10000 * z := by rw [hz]; ring
  rw [e2] at h2
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49372 / 100000) ^ 2 + 2 * (2 / 1000)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 9045 / 10000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- **`tauW142 n ≤ 1.2646/√n`** for `n ≥ 32768`. -/
theorem tauW142_big : tauW142 n ≤ 12646 / 10000 / √(n : ℝ) := by
  have h2 := eWr_big hn
  have h3 := sU_big hn
  unfold tauW142
  have e : (12646 : ℝ) / 10000 / √(n : ℝ) =
      9045 / 10000 / √(n : ℝ) + 3601 / 10000 / √(n : ℝ) := by ring
  rw [e]
  linarith

/-! ## The link of `F` -/

lemma f1_big : f1 (mF n) ≤ 2578 / 10000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF_big hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have e : f1 (mF n) = 2 * (√3 * (1 / √(mF n : ℝ))) + 6 * (1 / (mF n : ℝ)) := by
    unfold f1; ring
  have e2 : 2578 / 10000 / √(n : ℝ) = 2578 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p1 : √3 * (1 / √(mF n : ℝ)) ≤ 17321 / 10000 * (20 / 269 * (1 / √(n : ℝ))) :=
    mul_le_mul h3 ha ha0 (by norm_num)
  linarith

lemma f2_big : f2 (mF n) ≤ 303 / 10000 / √(n : ℝ) := by
  have hn4 := n4096_of_big hn
  obtain ⟨ha, hb⟩ := inv_mF_big hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have hb0 : (0 : ℝ) ≤ 1 / (mF n : ℝ) := by positivity
  have h5 := sqrt5_le
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
  have e2 : 303 / 10000 / √(n : ℝ) = 303 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : bG kappa * √5 ≤ 363382 / 1000000 * (223607 / 100000) :=
    mul_le_mul hbG h5 h50 (by norm_num)
  have p1 : bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) ≤
      363382 / 1000000 * (223607 / 100000) / 2 * (20 / 269 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) ha ha0 (by norm_num)
  have q0 : kappa 0 * Kr (mF n) ≤ 31831 / 100000 * (21652 / 10000) :=
    mul_le_mul hk hKr hKr0 (by norm_num)
  have q1 : 4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) ≤
      4 * (31831 / 100000 * (21652 / 10000)) * (1 / 32768 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  linarith

lemma f3_big : f3 (mF n) ≤ 530 / 10000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF_big hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h5 := sqrt5_le
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have e : f3 (mF n) = kappa 0 * √5 * (1 / √(mF n : ℝ)) := by
    unfold f3; ring
  have e2 : 530 / 10000 / √(n : ℝ) = 530 / 10000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : kappa 0 * √5 ≤ 31831 / 100000 * (223607 / 100000) :=
    mul_le_mul hk h5 h50 (by norm_num)
  have p1 : kappa 0 * √5 * (1 / √(mF n : ℝ)) ≤
      31831 / 100000 * (223607 / 100000) * (20 / 269 * (1 / √(n : ℝ))) :=
    mul_le_mul p0 ha ha0 (by norm_num)
  linarith

/-! ## The Agent network -/

lemma Q5_big : √(1 + 5 / (mA n : ℝ)) ≤ 1 + 1 / 1000000 := by
  have hx := nR_ge_big hn
  have h2 : (1000000000 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 5 / (n : ℝ) ^ 2 ≤ 5 / 1000000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma sS_big : AgD.sS (mA n) ≤ 2000002 / 1000000 := by
  have := Q5_big hn
  unfold AgD.sS
  linarith

lemma SS_big : AgD.SS (mA n) ≤ 200001 / 100000 := by
  have h1 := Q5_big hn
  have h2 := sS_big hn
  have h3 := AgD.sS_nn (mA n)
  unfold AgD.SS
  calc √(1 + 5 / (mA n : ℝ)) * AgD.sS (mA n)
      ≤ (1 + 1 / 1000000) * (2000002 / 1000000) := by gcongr
    _ ≤ 200001 / 100000 := by norm_num

lemma nc0_big : AgD.nc0 (mA n) ≤ 813 / 1000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have hn4 := n4096_of_big hn
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
  have hyy : y ^ 2 ≤ y * (1 / 32768) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2))) ?_
  · rw [hy]; ring
  · calc bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2)
        ≤ 363382 / 1000000 * (223607 / 100000) * y +
          31831 / 100000 * (8 * (11 / 5) * y ^ 2) := by gcongr
      _ ≤ 813 / 1000 * y := by nlinarith

/-- `cA1 ≤ 1.41422/√n`. -/
theorem cA1_big : cA1 n (mA n) ≤ 141422 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  rw [cA1_eq]
  refine le_trans (le_of_eq (?_ : _ = 2 * r)) ?_
  · rw [hr]; ring
  · refine le_trans (?_ : _ ≤ 141422 / 100000 * z) (le_of_eq ?_)
    · linarith
    · rw [hz]; ring

/-- `cA2 ≤ 10.49/n`. -/
theorem cA2_big : cA2 n (mA n) ≤ 1049 / 100 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have h3 := Part133.sqrt3_le
  have hQ := AgD.Q2_le (n4096_of_big hn)
  have hyr : y * r ≤ y * (1 / 256) := mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [cA2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (2 * (2 * √3 * y) + 2 * √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))) * r + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) + √3 * y * 2)) ?_
  · rw [hy, hr]; ring
  · refine le_trans (?_ : _ ≤ 1049 / 100 * y) (le_of_eq (by rw [hy]; ring))
    calc (2 * (2 * √3 * y) + 2 * √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * r +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) + √3 * y * 2
        ≤ (2 * (2 * (17321 / 10000) * y) + 2 * (17321 / 10000) * y * (4 * (1001 / 1000))) * r +
          17321 / 10000 * y * (4 * (1001 / 1000)) + 17321 / 10000 * y * 2 := by gcongr
      _ ≤ 1049 / 100 * y := by nlinarith

/-- `cA0 ≤ 0.495/√n`. -/
theorem cA0_big : cA0 n (mA n) ≤ 495 / 1000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have hn4 := n4096_of_big hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb2 := bG_nonneg hG
  have hb3 := bG_nonneg hGk
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b2 := AgD.b2_le
  have g2 := AgD.g2_le
  have b3 := AgD.b3_le
  have g3 := AgD.g3_le
  have h5 := AgD.sqrt5_le'
  have h2 := Part133.sqrt2_le
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hK4 := K4_le_big hn
  have hK40 := K4_nonneg n
  have a1 := nc0_big hn
  have a2 := SS_big hn
  have a3 := AgD.DS_le hn4
  have a4 := AgD.LS_le hn4
  have a5 := sS_big hn
  have a6 := AgD.dS_le hn4
  have a7 := AgD.lS_le hn4
  have n1 := AgD.nc0_nn (mA n)
  have n2 := AgD.SS_nn (mA n)
  have n3 := AgD.DS_nn (mA n)
  have n4 := AgD.LS_nn (mA n)
  have n5 := AgD.sS_nn (mA n)
  have n6 := AgD.dS_nn (mA n)
  have n7 := AgD.lS_nn (mA n)
  rw [← hy] at a1 a3 a4 a6 a7
  rw [cA0_eq, sqrt_mA, mA_eqR]
  refine le_trans (le_of_eq (?_ : _ =
    2 * AgD.nc0 (mA n) * r + bG (kappa ∘ kappa) * AgD.SS (mA n) * r +
      (kappa ∘ kappa) 0 * (K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n) +
        2 * AgD.LS (mA n)) +
      (bG (kappa ∘ kappa) * (√5 * (y / 2)) * AgD.sS (mA n) +
        (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) + √5 * y * AgD.dS (mA n) +
          2 * AgD.lS (mA n))) +
      (bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
        ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)))) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 495 / 1000 * z) (le_of_eq (by rw [hz]; ring))
    have step : 2 * AgD.nc0 (mA n) * r + bG (kappa ∘ kappa) * AgD.SS (mA n) * r +
          (kappa ∘ kappa) 0 * (K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n) +
            2 * AgD.LS (mA n)) +
          (bG (kappa ∘ kappa) * (√5 * (y / 2)) * AgD.sS (mA n) +
            (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) +
              √5 * y * AgD.dS (mA n) + 2 * AgD.lS (mA n))) +
          (bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
            ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))
        ≤ 2 * (813 / 1000 * y) * r + 33087 / 100000 * (200001 / 100000) * r +
          49376 / 100000 * (34644 / 10000 * y * (200001 / 100000) +
            141422 / 100000 * z * (895 / 100 * y) + 2 * (12 / 1000 * y)) +
          (33087 / 100000 * (223607 / 100000 * (y / 2)) * (2000002 / 1000000) +
            49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (2000002 / 1000000) +
              223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2))) +
          (28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
            1 * (4 * (11 / 5) * y ^ 2 * 2)) := by gcongr
    refine step.trans ?_
    -- reduce to a linear inequality in `z`
    have hyr : y * r ≤ 1 / 256 * (1 / 181 * z) := by
      have := mul_le_mul hyz' hr2 hr0.le (by positivity : (0 : ℝ) ≤ 1 / 181 * z)
      nlinarith
    have hzy : z * y ≤ 1 / 181 * (1 / 181 * z) := by
      have := mul_le_mul hz1 hyz' hy0.le (by norm_num : (0 : ℝ) ≤ 1 / 181)
      linarith
    have hyy : y ^ 2 ≤ 1 / 32768 * (1 / 181 * z) := by
      have := mul_le_mul hy1 hyz' hy0.le (by norm_num : (0 : ℝ) ≤ 1 / 32768)
      nlinarith
    have e : 2 * (813 / 1000 * y) * r + 33087 / 100000 * (200001 / 100000) * r +
          49376 / 100000 * (34644 / 10000 * y * (200001 / 100000) +
            141422 / 100000 * z * (895 / 100 * y) + 2 * (12 / 1000 * y)) +
          (33087 / 100000 * (223607 / 100000 * (y / 2)) * (2000002 / 1000000) +
            49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (2000002 / 1000000) +
              223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2))) +
          (28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
            1 * (4 * (11 / 5) * y ^ 2 * 2)) =
        1626 / 1000 * (y * r) + 33087 / 100000 * (200001 / 100000) * r +
          (49376 / 100000 * (34644 / 10000 * (200001 / 100000) + 24 / 1000) +
            33087 / 100000 * (223607 / 100000 / 2) * (2000002 / 1000000) +
            28416 / 100000 * (223607 / 100000)) * y +
          49376 / 100000 * (141422 / 100000) * (895 / 100) * (z * y) +
          (49376 / 100000 * (4 * (11 / 5) * (2000002 / 1000000) +
            223607 / 100000 * (447214 / 100000) + 352 / 10) + 88 / 5) * y ^ 2 := by ring
    rw [e]
    have c1 : 33087 / 100000 * (200001 / 100000) * r ≤
        33087 / 100000 * (200001 / 100000) * (707107 / 1000000 * z) :=
      mul_le_mul_of_nonneg_left hr1 (by norm_num)
    have c2 : (49376 / 100000 * (34644 / 10000 * (200001 / 100000) + 24 / 1000) +
        33087 / 100000 * (223607 / 100000 / 2) * (2000002 / 1000000) +
        28416 / 100000 * (223607 / 100000)) * y ≤
        (49376 / 100000 * (34644 / 10000 * (200001 / 100000) + 24 / 1000) +
        33087 / 100000 * (223607 / 100000 / 2) * (2000002 / 1000000) +
        28416 / 100000 * (223607 / 100000)) * (1 / 181 * z) :=
      mul_le_mul_of_nonneg_left hyz' (by norm_num)
    have c3 : 1626 / 1000 * (y * r) ≤ 1626 / 1000 * (1 / 256 * (1 / 181 * z)) :=
      mul_le_mul_of_nonneg_left hyr (by norm_num)
    have c4 : 49376 / 100000 * (141422 / 100000) * (895 / 100) * (z * y) ≤
        49376 / 100000 * (141422 / 100000) * (895 / 100) * (1 / 181 * (1 / 181 * z)) :=
      mul_le_mul_of_nonneg_left hzy (by norm_num)
    have c5 : (49376 / 100000 * (4 * (11 / 5) * (2000002 / 1000000) +
        223607 / 100000 * (447214 / 100000) + 352 / 10) + 88 / 5) * y ^ 2 ≤
        (49376 / 100000 * (4 * (11 / 5) * (2000002 / 1000000) +
        223607 / 100000 * (447214 / 100000) + 352 / 10) + 88 / 5) *
          (1 / 32768 * (1 / 181 * z)) :=
      mul_le_mul_of_nonneg_left hyy (by norm_num)
    linarith

/-- `dA1 ≤ 1 + 1/32768`. -/
theorem dA1_big : dA1 n (mA n) ≤ 1 + 1 / 32768 := by
  unfold dA1
  exact sqrt_one_add_big hn

/-- `dA0 ≤ 0.814/n`. -/
theorem dA0_big : dA0 n (mA n) ≤ 814 / 1000 / (n : ℝ) := by
  have h1 := sqrt_one_add_big hn
  have a1 := nc0_big hn
  have n1 := AgD.nc0_nn (mA n)
  have hy0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold dA0
  refine le_trans (?_ : _ ≤ 814 / 1000 * (1 / (n : ℝ))) (le_of_eq (by ring))
  calc √(1 + 2 / (n : ℝ)) * AgD.nc0 (mA n)
      ≤ (1 + 1 / 32768) * (813 / 1000 * (1 / (n : ℝ))) := by gcongr
    _ ≤ 814 / 1000 * (1 / (n : ℝ)) := by nlinarith

/-- `dA2 ≤ 10.4/n`. -/
theorem dA2_big : dA2 n (mA n) ≤ 104 / 10 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have h1 := sqrt_one_add_big hn
  have h3 := Part133.sqrt3_le
  have hQ := AgD.Q2_le (n4096_of_big hn)
  unfold dA2
  rw [sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))))) ?_
  · rw [hy]; ring
  · refine le_trans (?_ : _ ≤ 104 / 10 * y) (le_of_eq (by rw [hy]; ring))
    calc √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))
        ≤ (1 + 1 / 32768) * (2 * (17321 / 10000) * y + 17321 / 10000 * y *
          (4 * (1001 / 1000))) := by gcongr
      _ ≤ 104 / 10 * y := by nlinarith

/-- `cAdlt ≤ 7.02/n`. -/
theorem cAdlt_big : cAdlt n (mA n) ≤ 702 / 100 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have hn4 := n4096_of_big hn
  have h2 := Part133.sqrt2_le
  have hK4 := K4_le_big hn
  have hK40 := K4_nonneg n
  have a2 := SS_big hn
  have a3 := AgD.DS_le hn4
  have a4 := AgD.LS_le hn4
  have n2 := AgD.SS_nn (mA n)
  have n3 := AgD.DS_nn (mA n)
  rw [← hy] at a3 a4
  have hzy : z * y ≤ y * (1 / 181) := by nlinarith
  unfold cAdlt
  refine le_trans (le_of_eq (?_ : _ = AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) +
    √2 * z * AgD.DS (mA n))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 702 / 100 * y) (le_of_eq (by rw [hy]; ring))
    calc AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n)
        ≤ 12 / 1000 * y + 34644 / 10000 * y * (200001 / 100000) +
          141422 / 100000 * z * (895 / 100 * y) := by gcongr
      _ ≤ 702 / 100 * y := by nlinarith

/-! ## The norm factor and `eps4` -/

lemma N0_big : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 30000 := by
  have hx := nR_ge_big hn
  have h2 : (1000000000 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h1 : 5 / (mA n : ℝ) ≤ 5 / 1000000000 := by
    rw [mA_eqR]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have h10 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have h3 := sqrt_one_add_big hn
  have h30 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
  calc (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))
      ≤ (1 + 5 / 1000000000) * (1 + 1 / 32768) := mul_le_mul (by linarith) h3 h30 (by norm_num)
    _ ≤ 1 + 1 / 30000 := by norm_num

lemma sqrt_eps4_big : √(eps4 n (mA n)) ≤ 14144 / 10000 / √(n : ℝ) := by
  have hx := nR_ge_big hn
  have hx0 : (0 : ℝ) < n := by linarith
  refine sqrt_le_div_s (n4096_of_big hn) (by norm_num) ?_
  unfold eps4
  rw [mA_eqR]
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 32768 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyn : y * (n : ℝ) = 1 := by rw [hy]; field_simp
  have e1 : 5 / (n : ℝ) ^ 2 = 5 * y ^ 2 := by rw [hy]; ring
  have e2 : 2 / (n : ℝ) = 2 * y := by rw [hy]; ring
  rw [e1, e2]
  have hy2 : y ^ 2 ≤ 1 / 32768 * y := by nlinarith
  have hy20 : 0 ≤ y ^ 2 := by positivity
  have hb : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1 ≤ 20005 / 10000 * y := by
    have h5 : 5 * y ^ 2 ≤ 1 / 6000 * y := by nlinarith
    have h50 : 0 ≤ 5 * y ^ 2 := by positivity
    have h6 : (1 + 5 * y ^ 2) ^ 2 ≤ 1 + 1 / 2900 * y := by nlinarith
    have h7 : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) ≤ (1 + 1 / 2900 * y) * (1 + 2 * y) :=
      mul_le_mul_of_nonneg_right h6 (by linarith)
    nlinarith
  calc ((1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1) * (n : ℝ)
      ≤ 20005 / 10000 * y * (n : ℝ) := mul_le_mul_of_nonneg_right hb hx0.le
    _ = 20005 / 10000 := by rw [mul_assoc, hyn, mul_one]
    _ ≤ (14144 / 10000) ^ 2 := by norm_num

/-! ## The bad hidden event -/

/-- **`Pr(goodHat n fails) ≤ 0.002 + 20.63/n`** for `n ≥ 32768`. -/
theorem goodHat_big :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 2 / 1000 + 2063 / 100 / (n : ℝ) := by
  have hx := nR_ge_big hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := goodHat_prob_sharp (n4096_of_big hn)
  have hm := mW_ge_big hn
  have hm0 : (0 : ℝ) < mW n := by
    have : (0 : ℝ) < 181 * (n : ℝ) ^ 3 := by positivity
    linarith
  have hρ : (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / 181 * (1 / (n : ℝ)) := by
    rw [div_le_iff₀ hm0]
    have e : 1 / 181 * (1 / (n : ℝ)) * (181 * (n : ℝ) ^ 3) = (n : ℝ) ^ 2 := by
      field_simp
    have : 1 / 181 * (1 / (n : ℝ)) * (181 * (n : ℝ) ^ 3) ≤
        1 / 181 * (1 / (n : ℝ)) * (mW n : ℝ) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    linarith
  have hρ0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (mW n : ℝ) := by positivity
  set ρ : ℝ := (n : ℝ) ^ 2 / (mW n : ℝ) with hρd
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 32768 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have e3 : 3212000 * ρ / (n : ℝ) = 3212000 * (ρ * y) := by rw [hy]; ring
  have e4 : (2063 : ℝ) / 100 / (n : ℝ) = 2063 / 100 * y := by rw [hy]; ring
  rw [e3] at h
  rw [e4]
  have p : ρ * y ≤ 1 / 181 * y * (1 / 32768) := mul_le_mul hρ hy1 hy0.le (by positivity)
  linarith

/-! ## The constants of the distance kernel -/

/-- **`gD0 n ≤ 0.5812/√n`, `gD1 n ≤ 1.9299/√n`, `gD2 n ≤ 10.52/n`** for `n ≥ 32768`. -/
theorem gD_big :
    gD0 n ≤ 5812 / 10000 / √(n : ℝ) ∧ gD1 n ≤ 19299 / 10000 / √(n : ℝ) ∧
      gD2 n ≤ 1052 / 100 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * z := fun c => by rw [hz]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * y := fun c => by rw [hy]; ring
  have F1 := f1_big hn
  have F2 := f2_big hn
  have F3 := f3_big hn
  have F4 := f4_le
  have A0 := cA0_big hn
  have A1 := cA1_big hn
  have A2 := cA2_big hn
  have D0 := dA0_big hn
  have D1 := dA1_big hn
  have D2 := dA2_big hn
  have C5 := cAdlt_big hn
  have hN0 := N0_big hn
  have hE := sqrt_eps4_big hn
  rw [cv] at F1 F2 F3 A0 A1 hE
  rw [cn] at A2 D0 D2 C5
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have f1n := f1_nonneg (mF n)
  have f4n := f4_nonneg
  have hN00 : 0 ≤ (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) := by positivity
  have hE0 := Real.sqrt_nonneg (eps4 n (mA n))
  have D0c : dA0 n (mA n) ≤ 814 / 1000 / 32768 := by nlinarith
  have C5c : cAdlt n (mA n) ≤ 702 / 100 / 181 * z := by nlinarith
  have hEc : √(eps4 n (mA n)) ≤ 14144 / 10000 / 181 := by nlinarith
  have p1 := mul_le_lin F1 D0c b0 (by positivity)
  have p2 := mul_le_lin F2 hN0 hN00 (by positivity)
  have p3 := mul_le_lin F3 hEc hE0 (by positivity)
  have p4 : f4 * cAdlt n (mA n) ≤ 63662 / 100000 * (702 / 100 / 181 * z) :=
    mul_le_mul F4 C5c b3 (by norm_num)
  have p5 := mul_le_lin F1 D1 b1 (by positivity)
  -- `f1 ≤ (0.2578/181)` as a constant, then times `dA2 ≤ 10.4·y`
  have F1c : f1 (mF n) ≤ 2578 / 10000 / 181 := by nlinarith
  have p6 : f1 (mF n) * dA2 n (mA n) ≤ 2578 / 10000 / 181 * (104 / 10 * y) :=
    mul_le_mul F1c D2 b2 (by norm_num)
  rw [cv, cv, cn]
  refine ⟨?_, ?_, ?_⟩
  · unfold gD0
    linarith
  · unfold gD1
    linarith
  · unfold gD2
    linarith

/-- **`eD142a n ≤ 1.798/√n`** for `n ≥ 32768`. -/
theorem eD142a_big : eD142a n ≤ 1798 / 1000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yzB hn
  have hn4 := n4096_of_big hn
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * z := fun c => by rw [hz]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * y := fun c => by rw [hy]; ring
  obtain ⟨G0, G1, G2⟩ := gD_big hn
  rw [cv] at G0 G1
  rw [cn] at G2
  obtain ⟨g0n, g1n, g2n⟩ := gD_nonneg n
  have G2z : gD2 n ≤ 1052 / 100 / 181 * z := by nlinarith
  have hτ := tauW142_big hn
  rw [cv] at hτ
  have hτ0 := tauW142_nonneg hn4
  have hτc : tauW142 n ≤ 12646 / 10000 / 181 := by nlinarith
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have h20 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have hs4 := sig4_le
  have hs40 := sig4_nonneg
  have r1 := mul_le_lin G1 (show 1 - kappa^[4] 0 + tauW142 n ≤
    319057 / 1000000 + 12646 / 10000 / 181 by linarith) (by linarith) (by positivity)
  have r2 := mul_le_lin G2z (show 1 - kappa (kappa 0) + tauW142 n ≤
    50628 / 100000 + 12646 / 10000 / 181 by linarith) (by linarith) (by positivity)
  have r3 : sig4 * tauW142 n ≤ 4404 / 10000 * (12646 / 10000 * z) :=
    mul_le_mul hs4 hτ hτ0 (by norm_num)
  rw [cv]
  unfold eD142a
  linarith

end big

end BstLean.Part142

open BstLean.Part142 in
#print axioms tauW142_big
open BstLean.Part142 in
#print axioms goodHat_big
open BstLean.Part142 in
#print axioms gD_big
open BstLean.Part142 in
#print axioms eD142a_big
