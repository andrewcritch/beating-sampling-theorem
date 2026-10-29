import BstLean.Part139Final

/-!
# Part 139: the failure probability decreases as `1/n`

Role: `delegations/statements/p139-spec.md`, item 3 ("`p_n ≤ C/n^a` for large `n`").

The constants `e_P`, `e_V` of Part 133 are bounded in Part 133 by numbers that hold for every
`n ≥ 4096`. Here they are bounded by `c/√n`:

* `eP139_scale`: `e_P ≤ 4.074/√n`; `eV_scale`: `e_V ≤ 1.47/√n`; `vSpread_scale`: `v_n ≤ 64/n`.
* **`standInSucceeds139_rate`**: for every `n ≥ 4096`:
  `Pr_{W,A,F}(|g₀ − B| ≤ sd/2) ≥ 1 − (0.002 + 1951/n)`.
* `standInSucceeds139_frontier`: `≥ 87/100` for `n ≥ 16384`;
  **`standInSucceeds139_99`**: `≥ 99/100` for `n ≥ 243875`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136 BstLean.Part138

lemma s_mul (n : ℕ) : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)

section scale

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `√x ≤ c/√n` if `x·n ≤ c²`. -/
lemma sqrt_le_div_s {x c : ℝ} (hc : 0 ≤ c) (h : x * n ≤ c ^ 2) : √x ≤ c / √(n : ℝ) := by
  have hx := nR_ge hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine sqrt_le_of_sq (by positivity) ?_
  rw [div_pow, Real.sq_sqrt hn0.le, le_div_iff₀ hn0]
  exact h

/-- `1/n ≤ (1/64)·(1/√n)`. -/
lemma inv_n_le : 1 / (n : ℝ) ≤ 1 / 64 * (1 / √(n : ℝ)) := by
  have hs := sqrt_n_ge hn
  have hss := s_mul n
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hn0 : (0 : ℝ) < n := by nlinarith
  rw [div_le_iff₀ hn0]
  have : 1 / 64 * (1 / √(n : ℝ)) * (n : ℝ) = √(n : ℝ) / 64 := by
    field_simp
    nlinarith
  rw [this]
  linarith

/-- `m_F ≥ n·√n`. -/
lemma mF_ge_s : (n : ℝ) * √(n : ℝ) ≤ mF n := by
  have hx := nR_ge hn
  have h0 : n ^ 3 ≤ mF n ^ 2 := (mF_le_iff n (mF n)).mp le_rfl
  have h1 : (n : ℝ) ^ 3 ≤ (mF n : ℝ) ^ 2 := by exact_mod_cast h0
  have hss := s_mul n
  have h2 : ((n : ℝ) * √(n : ℝ)) ^ 2 ≤ (mF n : ℝ) ^ 2 := by
    calc ((n : ℝ) * √(n : ℝ)) ^ 2 = (n : ℝ) ^ 2 * (√(n : ℝ) * √(n : ℝ)) := by ring
      _ = (n : ℝ) ^ 3 := by rw [hss]; ring
      _ ≤ _ := h1
  exact (abs_le_of_sq_le_sq' h2 (Nat.cast_nonneg _)).2

/-- `m_W ≥ 2¹⁸·n²`. -/
lemma mW_ge_sq : 262144 * (n : ℝ) ^ 2 ≤ mW n := by
  have hx := nR_ge hn
  have h1 : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast mW_sq_ge n
  have h3 : (4096 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
  have h2 : (262144 * (n : ℝ) ^ 2) ^ 2 ≤ (mW n : ℝ) ^ 2 := by
    calc (262144 * (n : ℝ) ^ 2) ^ 2 = 4096 ^ 3 * (n : ℝ) ^ 4 := by ring
      _ ≤ (n : ℝ) ^ 3 * (n : ℝ) ^ 4 := by gcongr
      _ = (n : ℝ) ^ 7 := by ring
      _ ≤ _ := h1
  exact (abs_le_of_sq_le_sq' h2 (Nat.cast_nonneg _)).2

/-- `n/m_W ≤ 2⁻¹⁸/n`. -/
lemma n_div_mW_scale : (n : ℝ) / (mW n : ℝ) ≤ 1 / 262144 / (n : ℝ) := by
  have hx := nR_ge hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := mW_ge_sq hn
  have hm0 : (0 : ℝ) < mW n := by nlinarith
  rw [div_le_div_iff₀ hm0 hn0]
  nlinarith

/-- `√(m_W) ≥ 2¹⁵·√n`. -/
lemma sqrt_mW_scale : 32768 * √(n : ℝ) ≤ √(mW n : ℝ) := by
  have hx := nR_ge hn
  have h := mW_ge_sq hn
  have hss := s_mul n
  have hs0 := Real.sqrt_nonneg (n : ℝ)
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith

lemma cF2o_scale : cF2o (mF n) ≤ 5908 / 10000 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hm := mF_geR hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hms := mF_ge_s hn
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hc : (5 * kappa 0 + √6) ^ 2 ≤ 16331 / 1000 := by
    have h1 : 5 * kappa 0 + √6 ≤ 40411 / 10000 := by linarith
    have h0 : 0 ≤ 5 * kappa 0 + √6 := by positivity
    nlinarith
  have h5 : 5 / (mF n : ℝ) ≤ 5 / 262144 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hm
  unfold cF2o
  refine sqrt_le_div_s hn (by norm_num) ?_
  have e : 6 * (1 + 5 / (mF n : ℝ)) / (mF n : ℝ) + (5 * kappa 0 + √6) ^ 2 / (mF n : ℝ) =
      (6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (mF n : ℝ) := by ring
  have h7 : 6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2 ≤ 22332 / 1000 := by
    norm_num at h5 ⊢
    linarith
  rw [e, div_mul_eq_mul_div, div_le_iff₀ hm0]
  nlinarith

lemma cAr_scale : cAr (kappa ∘ kappa) (mA n) n ≤ 19455 / 10000 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hin := inv_n_le hn
  have hK := K4_le hn
  have hK0 := K4_nonneg n
  have hq := kappa2_zero_le
  have hq0 := q_mem.1
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hA := inv_mA_le hn
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hsA : √(1 + 5 / (mA n : ℝ)) ≤ 1 + 1 / 1000000 :=
    sqrt_le_of_sq (by norm_num) (by nlinarith)
  have hsA0 := Real.sqrt_nonneg (1 + 5 / (mA n : ℝ))
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hnu : 1 / (n : ℝ) ≤ 1 / 64 * u := hin
  have t1 : (1 + √2 * kappa (kappa 0)) / √(n : ℝ) ≤
      (1 + 141422 / 100000 * (49376 / 100000)) * u := by
    rw [div_eq_mul_one_div, ← hu]
    have : 1 + √2 * kappa (kappa 0) ≤ 1 + 141422 / 100000 * (49376 / 100000) := by
      have := mul_le_mul h2 hq hq0 (by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right this hu0.le
  have t2 : 2 * K4 n * kappa (kappa 0) / (n : ℝ) ≤
      2 * (3466 / 1000) * (49376 / 100000) * (1 / 64 * u) := by
    rw [div_eq_mul_one_div]
    have a : 2 * K4 n * kappa (kappa 0) ≤ 2 * (3466 / 1000) * (49376 / 100000) := by
      have := mul_le_mul hK hq hq0 (by norm_num)
      linarith
    exact mul_le_mul a hnu (by positivity) (by norm_num)
  have t3 : (5 * kappa (kappa 0) + √6) / (n : ℝ) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 64 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t4 : (5 + √6) / (n : ℝ) ≤ (5 + 24495 / 10000) * (1 / 64 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t10 : 0 ≤ (1 + √2 * kappa (kappa 0)) / √(n : ℝ) := by positivity
  have t20 : 0 ≤ 2 * K4 n * kappa (kappa 0) / (n : ℝ) := by positivity
  have t30 : 0 ≤ (5 * kappa (kappa 0) + √6) / (n : ℝ) := by positivity
  unfold cAr
  simp only [Function.comp_apply]
  rw [sqrt_mA, div_eq_mul_one_div (19455 / 10000 : ℝ), ← hu]
  have e1 : ((1 + √2 * kappa (kappa 0)) / √(n : ℝ) + 2 * K4 n * kappa (kappa 0) / (n : ℝ)) *
      (1 + 5 / (mA n : ℝ)) ≤
      ((1 + 141422 / 100000 * (49376 / 100000)) * u +
        2 * (3466 / 1000) * (49376 / 100000) * (1 / 64 * u)) * (1 + 3 / 10000000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have e2 : (5 * kappa (kappa 0) + √6) / (n : ℝ) * √(1 + 5 / (mA n : ℝ)) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 64 * u) * (1 + 1 / 1000000) :=
    mul_le_mul t3 hsA hsA0 (by positivity)
  nlinarith

lemma eAFr_scale : eAFr n (mA n) (mF n) ≤ 25365 / 10000 / √(n : ℝ) := by
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := cF2o_scale hn
  have h10 : 0 ≤ cF2o (mF n) := Real.sqrt_nonneg _
  have h2 := sqrt_one_add_le hn
  have h20 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
  have h3 := cAr_scale hn
  have hA := inv_mA_le hn
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  rw [div_eq_mul_one_div, ← hu] at h1 h3 ⊢
  have e1 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ (1 + 3 / 10000000) * (1 + 1 / 4096) :=
    mul_le_mul (by linarith) h2 h20 (by norm_num)
  have e2 : cF2o (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) ≤
      5908 / 10000 * u * ((1 + 3 / 10000000) * (1 + 1 / 4096)) :=
    mul_le_mul h1 e1 (by positivity) (by positivity)
  unfold eAFr
  nlinarith

lemma sU_scale : sU (2 * n) ≤ 3629 / 10000 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hin := inv_n_le hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h2l : (141421 / 100000 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h3 := Part133.sqrt3_le
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  unfold sU
  rw [hc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_one_div (3629 / 10000 : ℝ), ← hu]
  have t1 : 507 / 1000 / (√2 * √(n : ℝ)) ≤ 507 / 1000 / (141421 / 100000) * u := by
    rw [hu, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right h2l hs0.le)
  have t2 : 8 / 25 * √3 / (2 * (n : ℝ)) ≤ 8 / 25 * (17321 / 10000) / 2 * (1 / 64 * u) := by
    have e : 8 / 25 * √3 / (2 * (n : ℝ)) = 8 / 25 * √3 / 2 * (1 / (n : ℝ)) := by
      field_simp
    rw [e]
    exact mul_le_mul (by linarith) hin (by positivity) (by norm_num)
  nlinarith

/-- `epsW m ≤ 11/m` for `m = m_W n`. -/
lemma epsW_scale : epsW (mW n) * (n : ℝ) ≤ 11 / 1073741824 := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mW_geR hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have h2 := mW_ge_sq hn
  have h30 : 1073741824 * (n : ℝ) ≤ mW n := by nlinarith
  have e : epsW (mW n) * (n : ℝ) = (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) := by
    unfold epsW
    field_simp
    ring
  have a1 : 25 / (mW n : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hm0]; linarith
  have a10 : (0 : ℝ) ≤ 25 / (mW n : ℝ) := by positivity
  have a2 : (n : ℝ) / (mW n : ℝ) ≤ 1 / 1073741824 := by
    rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  have a20 : (0 : ℝ) ≤ (n : ℝ) / (mW n : ℝ) := by positivity
  rw [e]
  calc (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) ≤ 11 * (1 / 1073741824) :=
        mul_le_mul (by linarith) a2 a20 (by norm_num)
    _ = _ := by norm_num

lemma eWsmall_scale : eWsmall n (mW n) ≤ 4069 / 10000 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hin := inv_n_le hn
  have hK : √(12 + 48 / (n : ℝ)) ≤ 3466 / 1000 := K4_le hn
  have hK0 := Real.sqrt_nonneg (12 + 48 / (n : ℝ))
  have hε := epsW_scale hn
  have hε0 := epsW_nonneg (mW n)
  have hsW := sqrt_mW_scale hn
  have hsW0 : (0 : ℝ) < √(mW n : ℝ) := by nlinarith
  have hm := mW_geR hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 / 64 := by rw [hu]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have s1 : √(5 * epsW (mW n)) ≤ 23 / 100000 * u := by
    have := sqrt_le_div_s hn (x := 5 * epsW (mW n)) (c := 23 / 100000) (by norm_num)
      (by nlinarith)
    rwa [div_eq_mul_one_div, ← hu] at this
  have s2 : √(epsW (mW n)) ≤ 102 / 1000000 * u := by
    have := sqrt_le_div_s hn (x := epsW (mW n)) (c := 102 / 1000000) (by norm_num)
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
  have t1 : 15 / 2 * √(12 + 48 / (n : ℝ)) / (n : ℝ) ≤ 15 / 2 * (3466 / 1000) * (1 / 64 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hin (by positivity) (by norm_num)
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 32768 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 32768 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  have hH : eHid (mW n) ≤ 429 / 1000000 * u := by
    unfold eHid
    nlinarith
  have hH0 := eHid_nonneg (mW n)
  have t4 : 2 / √(n : ℝ) ≤ 2 / 64 := by gcongr
  have t40 : 0 ≤ 2 / √(n : ℝ) := by positivity
  have t5 : (1 + 2 / √(n : ℝ)) * eHid (mW n) ≤ (1 + 2 / 64) * (429 / 1000000 * u) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall jCos
  rw [div_eq_mul_one_div (4069 / 10000 : ℝ), ← hu]
  nlinarith

lemma eWr_scale : eWr (2 * n) n (mW n) ≤ 11746 / 10000 / √(n : ℝ) := by
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := sU_bound hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall_scale hn
  have hq := kappa2_zero_ge
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49372 / 100000) ^ 2 := by nlinarith
  have hq20 : 0 ≤ 1 - kappa (kappa 0) ^ 2 := by nlinarith [q_mem.1]
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  rw [div_eq_mul_one_div, ← hu] at h2 ⊢
  have t2 : u * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      u * (1 - (49372 / 100000) ^ 2 + 2 * (568 / 100000)) :=
    mul_le_mul_of_nonneg_left (by linarith) hu0.le
  unfold eWr
  rw [← hu]
  nlinarith

/-- **`e_P ≤ 4.074/√n`** for `n ≥ 4096`. -/
lemma eP139_scale : eP139 n ≤ 4074 / 1000 / √(n : ℝ) := by
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr_scale hn
  have h2 := eWr_scale hn
  have h3 := sU_scale hn
  unfold eP139
  rw [div_eq_mul_one_div] at h1 h2 h3 ⊢
  linarith

/-- **`e_V ≤ 1.47/√n`** for `n ≥ 4096`. -/
lemma eV_scale : eV n (mA n) (mF n) ≤ 147 / 100 / √(n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hm := mF_geR hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hms := mF_ge_s hn
  -- `(1 + 5/m_F)² ≤ 1 + β₁/n`, `(1 + 5/m_A)² ≤ 1 + β₂/n`
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 4096 := by
    rw [ht]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have htn : t * (n : ℝ) = 1 := by rw [ht]; field_simp
  have hF : 5 / (mF n : ℝ) ≤ 5 / 64 * t := by
    rw [div_le_iff₀ hm0]
    have : (64 : ℝ) * (n : ℝ) ≤ mF n := by nlinarith
    have h1 : 5 / 64 * t * (64 * (n : ℝ)) = 5 := by
      rw [ht]; field_simp
    nlinarith
  have hF0 : (0 : ℝ) ≤ 5 / (mF n : ℝ) := by positivity
  have hA : 5 / (mA n : ℝ) = 5 * t ^ 2 := by
    rw [mA_eqR, ht]; field_simp
  have a1 : (1 + 5 / (mF n : ℝ)) ^ 2 ≤ 1 + 1563 / 10000 * t := by nlinarith
  have a2 : (1 + 5 / (mA n : ℝ)) ^ 2 ≤ 1 + 245 / 100000 * t := by
    rw [hA]
    have q1 : t ^ 2 ≤ t * (1 / 4096) := by nlinarith
    have q2 : t ^ 4 ≤ t * (1 / 4096) ^ 3 := by
      have : t ^ 3 ≤ (1 / 4096) ^ 3 := pow_le_pow_left₀ ht0.le ht1 3
      nlinarith
    have e : (1 + 5 * t ^ 2) ^ 2 = 1 + 10 * t ^ 2 + 25 * t ^ 4 := by ring
    rw [e]
    norm_num at q2 ⊢
    linarith
  have a10 : (0 : ℝ) ≤ (1 + 5 / (mF n : ℝ)) ^ 2 := by positivity
  have a20 : (0 : ℝ) ≤ (1 + 5 / (mA n : ℝ)) ^ 2 := by positivity
  have a12 : (1 + 5 / (mF n : ℝ)) ^ 2 * (1 + 5 / (mA n : ℝ)) ^ 2 ≤
      (1 + 1563 / 10000 * t) * (1 + 245 / 100000 * t) :=
    mul_le_mul a1 a2 a20 (by positivity)
  have e2 : 2 / (n : ℝ) = 2 * t := by rw [ht]; ring
  have a123 : (1 + 5 / (mF n : ℝ)) ^ 2 * (1 + 5 / (mA n : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) ≤
      (1 + 1563 / 10000 * t) * (1 + 245 / 100000 * t) * (1 + 2 * t) := by
    rw [e2]
    exact mul_le_mul_of_nonneg_right a12 (by positivity)
  have hpoly : (1 + 1563 / 10000 * t) * (1 + 245 / 100000 * t) * (1 + 2 * t) - 1 ≤
      21608 / 10000 * t := by
    nlinarith [mul_nonneg ht0.le ht0.le, mul_nonneg (mul_nonneg ht0.le ht0.le) ht0.le,
      mul_le_mul_of_nonneg_left ht1 ht0.le,
      mul_le_mul_of_nonneg_left ht1 (mul_nonneg ht0.le ht0.le)]
  unfold eV
  refine sqrt_le_div_s hn (by norm_num) ?_
  have : ((1 + 5 / (mF n : ℝ)) ^ 2 * (1 + 5 / (mA n : ℝ)) ^ 2 * (1 + 2 / (n : ℝ)) - 1) *
      (n : ℝ) ≤ 21608 / 10000 * t * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hx0.le
  have e3 : 21608 / 10000 * t * (n : ℝ) = 21608 / 10000 := by rw [mul_assoc, htn, mul_one]
  rw [e3] at this
  refine this.trans ?_
  norm_num

/-- **`v_n ≤ 64/n`** for `n ≥ 4096`. -/
lemma vSpread_scale : vSpread n ≤ 64 / (n : ℝ) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hss := s_mul n
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  obtain ⟨hP0, -, hV0, -⟩ := vTot_nonneg (2 * n) (mW n) n (mA n) (mF n) hmF hmA hn1
  have hP := eP139_scale hn
  have hV := eV_scale hn
  have hP0' : 0 ≤ eP139 n := hP0
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have huu : u * u = 1 / (n : ℝ) := by
    rw [hu, div_mul_div_comm, hss, one_mul]
  rw [div_eq_mul_one_div] at hP hV
  rw [← hu] at hP hV
  rw [div_eq_mul_one_div, ← huu]
  unfold vSpread
  have h1 : (eV n (mA n) (mF n) + eP139 n) ^ 2 ≤ ((147 / 100 + 4074 / 1000) * u) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : eP139 n ^ 2 ≤ (4074 / 1000 * u) ^ 2 := pow_le_pow_left₀ hP0' hP 2
  nlinarith [mul_pos hu0 hu0]

/-- **The rate.** For every `n ≥ 4096`:
`Pr_{W,A,F}(|g₀ − B| ≤ sd/2) ≥ 1 − (0.002 + 1951/n)`. -/
theorem standInSucceeds139_rate :
    1 - (2 / 1000 + 1951 / (n : ℝ)) ≤ (mlpTriple 2 n).real (okSet n) := by
  have hx := nR_ge hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := standInSucceeds139_formula hn (θ := 1 / 10) (by norm_num) (by norm_num)
    (ζ := 1 / 20) (by norm_num) (by norm_num)
  have hQ : kappa^[6] 0 ≤ 777243 / 1000000 := kappa6_zero_le''
  have hy : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by linarith
  have hv := vSpread_scale hn
  have hv0 : 0 ≤ vSpread n := by unfold vSpread; positivity
  have hEH := EH_le hn
  have hEH0 := (EH_pos hn (by norm_num : (0 : ℝ) < 1 / 20)).le
  have hnm := n_div_mW_scale hn
  set t : ℝ := 1 / (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have hEH' : EH n (1 / 20) ≤ 470 / 262144 * t := by
    have e : 470 * (n : ℝ) / (mW n : ℝ) = 470 * ((n : ℝ) / (mW n : ℝ)) := by ring
    rw [e] at hEH
    have e2 : (1 : ℝ) / 262144 / (n : ℝ) = 1 / 262144 * t := by rw [ht]; ring
    rw [e2] at hnm
    linarith
  have e99 : 99 / 100 / (n : ℝ) = 99 / 100 * t := by rw [ht]; ring
  have e64 : 64 / (n : ℝ) = 64 * t := by rw [ht]; ring
  have e1951 : 1951 / (n : ℝ) = 1951 * t := by rw [ht]; ring
  rw [e64] at hv
  -- the Markov term
  have t1 : 4 * (2 * (99 / 100 / (n : ℝ)) + 8 * EH n (1 / 20)) /
      (1 / 10 * (1 - kappa^[6] 0)) ≤ 3582 / 10 * t := by
    rw [e99, div_le_iff₀ (by nlinarith)]
    nlinarith
  -- the Chebyshev term
  have t2 : vSpread n / ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 ≤ 15924 / 10 * t := by
    have hden : ((1 - 1 / 10) * (222757 / 1000000 : ℝ)) ^ 2 ≤
        ((1 - 1 / 10) * (1 - kappa^[6] 0)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 2
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  rw [e1951]
  linarith

/-- In the frontier interval: for `n ≥ 16384`, `Pr(|g₀ − B| ≤ sd/2) ≥ 87/100`. -/
theorem standInSucceeds139_frontier (h16 : 16384 ≤ n) :
    87 / 100 ≤ (mlpTriple 2 n).real (okSet n) := by
  have h := standInSucceeds139_rate hn
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast h16
  have : 1951 / (n : ℝ) ≤ 1951 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

/-- **Level `99/100`.** For `n ≥ 243875`: `Pr(|g₀ − B| ≤ sd/2) ≥ 99/100`. -/
theorem standInSucceeds139_99 (hbig : 243875 ≤ n) :
    99 / 100 ≤ (mlpTriple 2 n).real (okSet n) := by
  have h := standInSucceeds139_rate hn
  have hx : (243875 : ℝ) ≤ n := by exact_mod_cast hbig
  have : 1951 / (n : ℝ) ≤ 1951 / 243875 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this
  linarith

end scale

end BstLean.Part139

open BstLean.Part139 in
#print axioms vSpread_scale
open BstLean.Part139 in
#print axioms standInSucceeds139_rate
open BstLean.Part139 in
#print axioms standInSucceeds139_frontier
open BstLean.Part139 in
#print axioms standInSucceeds139_99
