import BstLean.Part142Final

/-!
# Part 143: the numeric constants of Part 142 again, for `n ≥ 16384 = 2¹⁴`

The lemmas of `Part142Big` (there with `32768 ≤ n`) with the hypothesis `16384 ≤ n`
(`√n ≥ 128`, `√(m_F) ≥ 11.3137·√n`, `m_W ≥ 128·n³`), each constant computed again, and new
bounds of `sA0`, `sA2`, `eAFr`, `Vb`, `EHH`, `pertA`, `XA142`, `eD142` and of the bad hidden
event for `n ≥ 16384`.
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

/-- `√3 ≤ 1.73206`. -/
lemma s3_le16 : √(3 : ℝ) ≤ 173206 / 100000 :=
  Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

/-- `cgS (κ∘κ) = (1 − κ(0))/2 ≤ 0.3408455`. -/
lemma cg2_le16 : AgS.cgS (kappa ∘ kappa) ≤ 3408455 / 10000000 := by
  have := kappa_zero_ge
  rw [AgS.cg2_eq]
  linarith

/-- `0.222757 ≤ 1 − κ^{∘6}(0)` (from `BstLean.Part139.kappa6_zero_le''`). -/
lemma q0_le16 : (222757 : ℝ) / 1000000 ≤ 1 - kappa^[6] 0 := by
  have := BstLean.Part139.kappa6_zero_le''
  linarith

/-- `1 − κ^{∘6}(0) ≤ 0.2229` (from `BstLean.Part132.kappa6_zero_ge'`). -/
lemma q0_ge16 : 1 - kappa^[6] 0 ≤ (2229 : ℝ) / 10000 := by
  have := BstLean.Part132.kappa6_zero_ge'
  linarith

section big

variable {n : ℕ} (hn : 16384 ≤ n)

include hn

lemma nR_ge16 : (16384 : ℝ) ≤ n := by exact_mod_cast hn

lemma n4096_of16 : 4096 ≤ n := by omega

/-- `√n ≥ 128` for `n ≥ 16384`. -/
lemma sqrt_n_ge16 : (128 : ℝ) ≤ √(n : ℝ) := by
  have hx := nR_ge16 hn
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` for `n ≥ 16384`. -/
lemma yz16 : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 16384 ∧ z ≤ 1 / 128 ∧ r ≤ 707107 / 1000000 * z ∧
    r ≤ 1 / 181 ∧ y = z * z ∧ y ≤ 1 / 128 * z := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge16 hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h2 : (14142135 : ℝ) / 10000000 ≤ √2 := (Real.le_sqrt' (by norm_num)).2 (by norm_num)
  have h20 : (0 : ℝ) < √2 := by linarith
  have e2 : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := Real.sqrt_mul (by norm_num) _
  have h181 : (181 : ℝ) ≤ √(2 * (n : ℝ)) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hz1 : 1 / √(n : ℝ) ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num) hs
  have hyz : 1 / (n : ℝ) = 1 / √(n : ℝ) * (1 / √(n : ℝ)) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hz0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  refine ⟨1 / (n : ℝ), 1 / √(n : ℝ), 1 / √(2 * (n : ℝ)), rfl, rfl, rfl, by positivity,
    hz0, by positivity, one_div_le_one_div_of_le (by norm_num) hx,
    hz1, ?_, one_div_le_one_div_of_le (by norm_num) h181, hyz, ?_⟩
  · rw [e2, div_le_iff₀ (by positivity)]
    have e : 707107 / 1000000 * (1 / √(n : ℝ)) * (√2 * √(n : ℝ)) = 707107 / 1000000 * √2 := by
      field_simp
    rw [e]
    nlinarith
  · rw [hyz]
    exact mul_le_mul_of_nonneg_right hz1 hz0.le

/-! ## Basic -/

/-- `K₄(n) ≤ 3.46453` for `n ≥ 16384`. -/
lemma K4_le16 : K4 n ≤ 346453 / 100000 := by
  have hx := nR_ge16 hn
  unfold K4
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 48 / (n : ℝ) ≤ 48 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-- `1/√m_F ≤ (10000/113137)·(1/√n)` (`11.3137² ≤ 128`) and `1/m_F ≤ (1/16384)·(1/√n)`. -/
lemma inv_mF16 :
    1 / √(mF n : ℝ) ≤ 10000 / 113137 * (1 / √(n : ℝ)) ∧
      1 / (mF n : ℝ) ≤ 1 / 16384 * (1 / √(n : ℝ)) := by
  have hx := nR_ge16 hn
  have hs := sqrt_n_ge16 hn
  have hss : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hms := BstLean.Part139.mF_ge_s (n4096_of16 hn)
  have hm0 : (0 : ℝ) < mF n := by nlinarith
  have h8 : 113137 / 10000 * √(n : ℝ) ≤ √(mF n : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : (113137 / 10000 * √(n : ℝ)) ^ 2 = (113137 / 10000) ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    rw [h1]
    have h2 : 128 * (n : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by nlinarith
    have h3 : ((113137 : ℝ) / 10000) ^ 2 * (n : ℝ) ≤ 128 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
    linarith
  constructor
  · rw [div_le_iff₀ (by linarith)]
    have e : 10000 / 113137 * (1 / √(n : ℝ)) * √(mF n : ℝ) =
        √(mF n : ℝ) / (113137 / 10000 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 16384 * (1 / √(n : ℝ)) * (mF n : ℝ) = (mF n : ℝ) / (16384 * √(n : ℝ)) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have h2 : 16384 * √(n : ℝ) ≤ (n : ℝ) * √(n : ℝ) :=
      mul_le_mul_of_nonneg_right hx hs0.le
    linarith

/-- `m_W ≥ 128·n³` for `n ≥ 16384`. -/
lemma mW_ge16 : 128 * (n : ℝ) ^ 3 ≤ mW n := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h1 : (n : ℝ) ^ 7 ≤ (mW n : ℝ) ^ 2 := by exact_mod_cast mW_sq_ge n
  have h6 : (0 : ℝ) ≤ (n : ℝ) ^ 6 := by positivity
  have h2 : (128 * (n : ℝ) ^ 3) ^ 2 ≤ (mW n : ℝ) ^ 2 := by
    calc (128 * (n : ℝ) ^ 3) ^ 2 = 16384 * (n : ℝ) ^ 6 := by ring
      _ ≤ (n : ℝ) * (n : ℝ) ^ 6 := mul_le_mul_of_nonneg_right (by linarith) h6
      _ = (n : ℝ) ^ 7 := by ring
      _ ≤ _ := h1
  exact (abs_le_of_sq_le_sq' h2 (Nat.cast_nonneg _)).2

lemma mW_pos16 : (0 : ℝ) < mW n := by
  have hx := nR_ge16 hn
  have h := mW_ge16 hn
  have : (0 : ℝ) < 128 * (n : ℝ) ^ 3 := by positivity
  linarith

/-- The true ratio: `n²/m_W ≤ 1/(128·n)` for `n ≥ 16384`. -/
lemma ratio16 : (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / 128 * (1 / (n : ℝ)) := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mW_ge16 hn
  have hm0 := mW_pos16 hn
  rw [div_le_iff₀ hm0]
  have e : 1 / 128 * (1 / (n : ℝ)) * (128 * (n : ℝ) ^ 3) = (n : ℝ) ^ 2 := by
    field_simp
  have : 1 / 128 * (1 / (n : ℝ)) * (128 * (n : ℝ) ^ 3) ≤
      1 / 128 * (1 / (n : ℝ)) * (mW n : ℝ) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  linarith

/-- `n/m_W ≤ 2⁻³⁵`, `n/m_W ≤ (1/2097152)·(1/n)` and `√(m_W) ≥ 185363·√n`. -/
lemma mW_more16 : (n : ℝ) / (mW n : ℝ) ≤ 1 / 34359738368 ∧
    (n : ℝ) / (mW n : ℝ) ≤ 1 / 2097152 * (1 / (n : ℝ)) ∧
    185363 * √(n : ℝ) ≤ √(mW n : ℝ) := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mW_ge16 hn
  have hm0 := mW_pos16 hn
  have hsq : (268435456 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h3 : 268435456 * (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hsq hx0.le
    calc 268435456 * (n : ℝ) ≤ (n : ℝ) ^ 2 * (n : ℝ) := this
      _ = (n : ℝ) ^ 3 := by ring
  have h35 : 34359738368 * (n : ℝ) ≤ mW n := by linarith
  have h3' : 16384 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hx (sq_nonneg (n : ℝ))
    calc 16384 * (n : ℝ) ^ 2 ≤ (n : ℝ) * (n : ℝ) ^ 2 := this
      _ = (n : ℝ) ^ 3 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ hm0 (by norm_num)]
    linarith
  · rw [div_le_iff₀ hm0]
    have e : 1 / 2097152 * (1 / (n : ℝ)) * (2097152 * (n : ℝ) ^ 2) = (n : ℝ) := by
      field_simp
    have : 1 / 2097152 * (1 / (n : ℝ)) * (2097152 * (n : ℝ) ^ 2) ≤
        1 / 2097152 * (1 / (n : ℝ)) * (mW n : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, Real.sq_sqrt hx0.le]
    have : (185363 : ℝ) ^ 2 * (n : ℝ) ≤ 34359738368 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) hx0.le
    linarith

lemma sqrt_one_add16 : √(1 + 2 / (n : ℝ)) ≤ 1 + 1 / 16384 := by
  have hx := nR_ge16 hn
  refine sqrt_le_of_sq (by norm_num) ?_
  have : 2 / (n : ℝ) ≤ 2 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  norm_num at this ⊢
  linarith

/-! ## The World link and the inputs -/

/-- `sU (2n) ≤ 0.36067/√n`. -/
lemma sU16 : sU (2 * n) ≤ 36067 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hc : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h3 := s3_le16
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  unfold sU
  rw [hc]
  refine le_trans (le_of_eq (?_ : _ = 507 / 1000 * r + 8 / 25 * √3 / 2 * y)) ?_
  · rw [hr, hy]; ring
  · refine le_trans (?_ : _ ≤ 36067 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    have p : 8 / 25 * √3 / 2 * y ≤ 8 / 25 * (173206 / 100000) / 2 * (1 / 128 * z) :=
      mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
    linarith

lemma sU_const16 : sU (2 * n) ≤ 2818 / 1000000 := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have h := sU16 hn
  have e : (36067 : ℝ) / 100000 / √(n : ℝ) = 36067 / 100000 * z := by rw [hz]; ring
  rw [e] at h
  linarith

/-- `epsW (m_W)·n ≤ 10.01/2³⁵`. -/
lemma epsW16 : epsW (mW n) * (n : ℝ) ≤ 1001 / 100 / 34359738368 := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm0 := mW_pos16 hn
  obtain ⟨a2, -, -⟩ := mW_more16 hn
  have hm := mW_geR (n4096_of16 hn)
  have e : epsW (mW n) * (n : ℝ) = (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) := by
    unfold epsW
    field_simp
    ring
  have a1 : 25 / (mW n : ℝ) ≤ 1 / 100 := by
    rw [div_le_iff₀ hm0]; linarith
  have a10 : (0 : ℝ) ≤ 25 / (mW n : ℝ) := by positivity
  have a20 : (0 : ℝ) ≤ (n : ℝ) / (mW n : ℝ) := by positivity
  rw [e]
  calc (10 + 25 / (mW n : ℝ)) * ((n : ℝ) / (mW n : ℝ)) ≤ 1001 / 100 * (1 / 34359738368) :=
        mul_le_mul (by linarith) a2 a20 (by norm_num)
    _ = _ := by norm_num

/-- The hidden layers of `W`: `eHid (m_W) ≤ (7323/10⁸)/√n` and `√(epsW m_W) ≤ (1707/10⁸)/√n`. -/
lemma eHid_u16 :
    eHid (mW n) ≤ 7323 / 100000000 * (1 / √(n : ℝ)) ∧
      √(epsW (mW n)) ≤ 1707 / 100000000 * (1 / √(n : ℝ)) := by
  have hn4 := n4096_of16 hn
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge hn4
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hε := epsW16 hn
  have hε0 := epsW_nonneg (mW n)
  obtain ⟨-, -, hsW⟩ := mW_more16 hn
  have hsW0 : (0 : ℝ) < √(mW n : ℝ) := by nlinarith
  have hm := mW_geR hn4
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hk := kappa_zero_le
  have hk0 : 0 ≤ kappa 0 := (kappa_mem (t := 0) (by norm_num) (by norm_num)).1
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have s1 : √(5 * epsW (mW n)) ≤ 382 / 10000000 * u := by
    have := sqrt_le_div_s hn4 (x := 5 * epsW (mW n)) (c := 382 / 10000000) (by norm_num)
      (by
        have e : 5 * epsW (mW n) * (n : ℝ) = 5 * (epsW (mW n) * (n : ℝ)) := by ring
        rw [e]
        refine le_trans (mul_le_mul_of_nonneg_left hε (by norm_num)) ?_
        norm_num)
    rwa [div_eq_mul_one_div, ← hu] at this
  have s2 : √(epsW (mW n)) ≤ 1707 / 100000000 * u := by
    have := sqrt_le_div_s hn4 (x := epsW (mW n)) (c := 1707 / 100000000) (by norm_num)
      (hε.trans (by norm_num))
    rwa [div_eq_mul_one_div, ← hu] at this
  have h5 : 5 / (mW n : ℝ) ≤ 1 / 1000 := by
    rw [div_le_iff₀ hm0]; linarith
  have s3 : √(1 + 5 / (mW n : ℝ)) ≤ 1 + 1 / 1000 := sqrt_le_of_sq (by norm_num) (by linarith)
  have s30 := Real.sqrt_nonneg (1 + 5 / (mW n : ℝ))
  have hiW : 1 / √(mW n : ℝ) ≤ 1 / 185363 * u := by
    rw [hu, div_mul_div_comm, mul_one]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsW
  have hiW0 : 0 ≤ 1 / √(mW n : ℝ) := by positivity
  have t2 : √6 * √(1 + 5 / (mW n : ℝ)) / √(mW n : ℝ) ≤
      24495 / 10000 * (1 + 1 / 1000) * (1 / 185363 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul h6 s3 s30 (by norm_num)) hiW hiW0 (by norm_num)
  have t3 : (5 * kappa 0 + √6) / √(mW n : ℝ) ≤
      (5 * (31831 / 100000) + 24495 / 10000) * (1 / 185363 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hiW hiW0 (by norm_num)
  refine ⟨?_, s2⟩
  unfold eHid
  linarith

/-- `eWsmall n (m_W) ≤ 0.20311/√n`. -/
lemma eWsmall16 : eWsmall n (mW n) ≤ 20311 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  obtain ⟨hH, hE⟩ := eHid_u16 hn
  rw [← hz] at hH hE
  have hH0 := eHid_nonneg (mW n)
  have hK := K4_le16 hn
  have hK0 := K4_nonneg n
  have t1 : 15 / 2 * K4 n * y ≤ 15 / 2 * (346453 / 100000) * (1 / 128 * z) :=
    mul_le_mul (by linarith) hyz' hy0.le (by norm_num)
  have t5 : (1 + 2 * z) * eHid (mW n) ≤ (1 + 2 / 128) * (7323 / 100000000 * z) :=
    mul_le_mul (by linarith) hH hH0 (by norm_num)
  unfold eWsmall jCos
  refine le_trans (le_of_eq (?_ : _ = 15 / 2 * K4 n * y + (1 + 2 * z) * eHid (mW n) +
    2 * √(epsW (mW n)))) ?_
  · rw [hy, hz]; unfold K4; ring
  · refine le_trans (?_ : _ ≤ 20311 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    linarith

/-- `eWr (2n) n (m_W) ≤ 0.96498/√n`. -/
lemma eWr16 : eWr (2 * n) n (mW n) ≤ 96498 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have h1 := sU_const16 hn
  have h10 := sU_nonneg (2 * n)
  have h2 := eWsmall16 hn
  have hq := BstLean.Part132.kappa2_zero_ge'
  have hq1 := q_mem.2
  have hq2 : 1 - kappa (kappa 0) ^ 2 ≤ 1 - (49373 / 100000) ^ 2 := by nlinarith
  have e2 : (20311 : ℝ) / 100000 / √(n : ℝ) = 20311 / 100000 * z := by rw [hz]; ring
  rw [e2] at h2
  have t2 : z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) ≤
      z * (1 - (49373 / 100000) ^ 2 + 2 * (2818 / 1000000)) :=
    mul_le_mul_of_nonneg_left (by linarith) hz0.le
  unfold eWr
  refine le_trans (le_of_eq (?_ : _ = z * (1 - kappa (kappa 0) ^ 2 + 2 * sU (2 * n)) +
    eWsmall n (mW n))) ?_
  · rw [hz]
  · refine le_trans (?_ : _ ≤ 96498 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    nlinarith

/-- **`tauW142 n ≤ 1.32565/√n`** for `n ≥ 16384`. -/
theorem tauW142_16 : tauW142 n ≤ 132565 / 100000 / √(n : ℝ) := by
  have h2 := eWr16 hn
  have h3 := sU16 hn
  unfold tauW142
  have e : (132565 : ℝ) / 100000 / √(n : ℝ) =
      96498 / 100000 / √(n : ℝ) + 36067 / 100000 / √(n : ℝ) := by ring
  rw [e]
  linarith

/-! ## The link of `F` -/

/-- `f1 (m_F) ≤ 0.30656/√n`. -/
lemma f1_16 : f1 (mF n) ≤ 30656 / 100000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF16 hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h3 := s3_le16
  have h30 := Real.sqrt_nonneg (3 : ℝ)
  have e : f1 (mF n) = 2 * (√3 * (1 / √(mF n : ℝ))) + 6 * (1 / (mF n : ℝ)) := by
    unfold f1; ring
  have e2 : 30656 / 100000 / √(n : ℝ) = 30656 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p1 : √3 * (1 / √(mF n : ℝ)) ≤ 173206 / 100000 * (10000 / 113137 * (1 / √(n : ℝ))) :=
    mul_le_mul h3 ha ha0 (by norm_num)
  linarith

/-- `f2 (m_F) ≤ 0.03608/√n`. -/
lemma f2_16 : f2 (mF n) ≤ 3608 / 100000 / √(n : ℝ) := by
  have hn4 := n4096_of16 hn
  obtain ⟨ha, hb⟩ := inv_mF16 hn
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
  have e2 : 3608 / 100000 / √(n : ℝ) = 3608 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : bG kappa * √5 ≤ 363382 / 1000000 * (223607 / 100000) :=
    mul_le_mul hbG h5 h50 (by norm_num)
  have p1 : bG kappa * √5 / 2 * (1 / √(mF n : ℝ)) ≤
      363382 / 1000000 * (223607 / 100000) / 2 * (10000 / 113137 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) ha ha0 (by norm_num)
  have q0 : kappa 0 * Kr (mF n) ≤ 31831 / 100000 * (21652 / 10000) :=
    mul_le_mul hk hKr hKr0 (by norm_num)
  have q1 : 4 * (kappa 0 * Kr (mF n)) * (1 / (mF n : ℝ)) ≤
      4 * (31831 / 100000 * (21652 / 10000)) * (1 / 16384 * (1 / √(n : ℝ))) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  linarith

/-- `f3 (m_F) ≤ 0.06292/√n`. -/
lemma f3_16 : f3 (mF n) ≤ 6292 / 100000 / √(n : ℝ) := by
  obtain ⟨ha, hb⟩ := inv_mF16 hn
  have hr0 : (0 : ℝ) < 1 / √(n : ℝ) := by positivity
  have ha0 : (0 : ℝ) ≤ 1 / √(mF n : ℝ) := by positivity
  have h5 := AgD.sqrt5_le'
  have h50 := Real.sqrt_nonneg (5 : ℝ)
  have hk := kappa_zero_le
  have hk0 := kappa0_nonneg
  have e : f3 (mF n) = kappa 0 * √5 * (1 / √(mF n : ℝ)) := by
    unfold f3; ring
  have e2 : 6292 / 100000 / √(n : ℝ) = 6292 / 100000 * (1 / √(n : ℝ)) := by ring
  rw [e, e2]
  have p0 : kappa 0 * √5 ≤ 31831 / 100000 * (223607 / 100000) :=
    mul_le_mul hk h5 h50 (by norm_num)
  have p1 : kappa 0 * √5 * (1 / √(mF n : ℝ)) ≤
      31831 / 100000 * (223607 / 100000) * (10000 / 113137 * (1 / √(n : ℝ))) :=
    mul_le_mul p0 ha ha0 (by norm_num)
  linarith

/-! ## The Agent network -/

lemma nsq16 : (268435456 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hx := nR_ge16 hn
  nlinarith

lemma Q5_16 : √(1 + 5 / (mA n : ℝ)) ≤ 1 + 1 / 100000000 := by
  have h2 := nsq16 hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 5 / (n : ℝ) ^ 2 ≤ 5 / 268435456 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma Q2_16 : √(1 + 2 / (mA n : ℝ)) ≤ 1 + 1 / 100000000 := by
  have h2 := nsq16 hn
  refine sqrt_le_of_sq (by norm_num) ?_
  rw [mA_eqR]
  have h : 2 / (n : ℝ) ^ 2 ≤ 2 / 268435456 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  norm_num at h ⊢
  linarith

lemma sS16 : AgD.sS (mA n) ≤ 200000002 / 100000000 := by
  have := Q5_16 hn
  unfold AgD.sS
  linarith

lemma SS16 : AgD.SS (mA n) ≤ 200000005 / 100000000 := by
  have h1 := Q5_16 hn
  have h2 := sS16 hn
  have h3 := AgD.sS_nn (mA n)
  unfold AgD.SS
  calc √(1 + 5 / (mA n : ℝ)) * AgD.sS (mA n)
      ≤ (1 + 1 / 100000000) * (200000002 / 100000000) := by gcongr
    _ ≤ 200000005 / 100000000 := by norm_num

/-- `DS (m_A) ≤ 8.94429/n`. -/
lemma DS16 : AgD.DS (mA n) ≤ 894429 / 100000 * (1 / (n : ℝ)) := by
  have h5 := AgD.sqrt5_le'
  have h2 := sS16 hn
  have h3 := AgD.sS_nn (mA n)
  have h4 := AgD.dS_le (n4096_of16 hn)
  unfold AgD.DS
  rw [sqrt_mA]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  rw [← hy] at h4 ⊢
  refine le_trans (le_of_eq (?_ : _ = √5 * y * AgD.sS (mA n) + AgD.dS (mA n))) ?_
  · rw [hy]; ring
  · calc √5 * y * AgD.sS (mA n) + AgD.dS (mA n)
        ≤ 223607 / 100000 * y * (200000002 / 100000000) + 447214 / 100000 * y := by gcongr
      _ ≤ 894429 / 100000 * y := by linarith

/-- `LS (m_A) ≤ 0.00276/n`. -/
lemma LS16 : AgD.LS (mA n) ≤ 276 / 100000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
  have h5 := AgD.sqrt5_le'
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have h2 := sS16 hn
  have h3 := AgD.sS_nn (mA n)
  have h4 := AgD.dS_le hn4
  have h4n := AgD.dS_nn (mA n)
  have h6 := AgD.lS_le hn4
  unfold AgD.LS
  rw [sqrt_mA, mA_eqR]
  rw [← hy] at h4 h6 ⊢
  have hyy : y ^ 2 ≤ y * (1 / 16384) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = AgD.lS (mA n) + 4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) +
    √5 * y * AgD.dS (mA n))) ?_
  · rw [hy]; ring
  · calc AgD.lS (mA n) + 4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) + √5 * y * AgD.dS (mA n)
        ≤ 176 / 10 * y ^ 2 + 4 * (11 / 5) * y ^ 2 * (200000002 / 100000000) +
          223607 / 100000 * y * (447214 / 100000 * y) := by gcongr
      _ ≤ 276 / 100000 * y := by nlinarith

/-- `nc0 (m_A) ≤ 0.8129/n`. -/
lemma nc0_16 : AgD.nc0 (mA n) ≤ 8129 / 10000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
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
  have hyy : y ^ 2 ≤ y * (1 / 16384) := by nlinarith
  refine le_trans (le_of_eq (?_ : _ = bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2))) ?_
  · rw [hy]; ring
  · calc bG kappa * √5 * y + kappa 0 * (8 * Kr (mA n) * y ^ 2)
        ≤ 363382 / 1000000 * (223607 / 100000) * y +
          31831 / 100000 * (8 * (11 / 5) * y ^ 2) := by gcongr
      _ ≤ 8129 / 10000 * y := by nlinarith

/-- `cA1 ≤ 1.414214/√n`. -/
theorem cA1_16 : cA1 n (mA n) ≤ 1414214 / 1000000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  rw [cA1_eq]
  refine le_trans (le_of_eq (?_ : _ = 2 * r)) ?_
  · rw [hr]; ring
  · refine le_trans (?_ : _ ≤ 1414214 / 1000000 * z) (le_of_eq ?_)
    · linarith
    · rw [hz]; ring

/-- `cA2 ≤ 10.5073/n`. -/
theorem cA2_16 : cA2 n (mA n) ≤ 105073 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have h3 := s3_le16
  have hQ := Q2_16 hn
  have hyr : y * r ≤ y * (1 / 181) := mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [cA2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (2 * (2 * √3 * y) + 2 * √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))) * r + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) + √3 * y * 2)) ?_
  · rw [hy, hr]; ring
  · refine le_trans (?_ : _ ≤ 105073 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc (2 * (2 * √3 * y) + 2 * √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * r +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) + √3 * y * 2
        ≤ (2 * (2 * (173206 / 100000) * y) + 2 * (173206 / 100000) * y *
            (4 * (1 + 1 / 100000000))) * r +
          173206 / 100000 * y * (4 * (1 + 1 / 100000000)) + 173206 / 100000 * y * 2 := by
          gcongr
      _ ≤ 105073 / 10000 * y := by nlinarith

/-- `cA0 ≤ 0.50589/√n`. -/
theorem cA0_16 : cA0 n (mA n) ≤ 50589 / 100000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
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
  have hK4 := K4_le16 hn
  have hK40 := K4_nonneg n
  have a1 := nc0_16 hn
  have a2 := SS16 hn
  have a3 := DS16 hn
  have a4 := LS16 hn
  have a5 := sS16 hn
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
  · refine le_trans (?_ : _ ≤ 50589 / 100000 * z) (le_of_eq (by rw [hz]; ring))
    have step : 2 * AgD.nc0 (mA n) * r + bG (kappa ∘ kappa) * AgD.SS (mA n) * r +
          (kappa ∘ kappa) 0 * (K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n) +
            2 * AgD.LS (mA n)) +
          (bG (kappa ∘ kappa) * (√5 * (y / 2)) * AgD.sS (mA n) +
            (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) +
              √5 * y * AgD.dS (mA n) + 2 * AgD.lS (mA n))) +
          (bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
            ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))
        ≤ 2 * (8129 / 10000 * y) * r + 33087 / 100000 * (200000005 / 100000000) * r +
          49376 / 100000 * (346453 / 100000 * y * (200000005 / 100000000) +
            141422 / 100000 * z * (894429 / 100000 * y) + 2 * (276 / 100000 * y)) +
          (33087 / 100000 * (223607 / 100000 * (y / 2)) * (200000002 / 100000000) +
            49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (200000002 / 100000000) +
              223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2))) +
          (28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
            1 * (4 * (11 / 5) * y ^ 2 * 2)) := by gcongr
    refine step.trans ?_
    -- reduce to a linear inequality in `z`
    have hyr : y * r ≤ 1 / 181 * (1 / 128 * z) := by
      have := mul_le_mul hyz' hr2 hr0.le (by positivity : (0 : ℝ) ≤ 1 / 128 * z)
      nlinarith
    have hzy : z * y ≤ 1 / 128 * (1 / 128 * z) := by
      have := mul_le_mul hz1 hyz' hy0.le (by norm_num : (0 : ℝ) ≤ 1 / 128)
      linarith
    have hyy : y ^ 2 ≤ 1 / 16384 * (1 / 128 * z) := by
      have := mul_le_mul hy1 hyz' hy0.le (by norm_num : (0 : ℝ) ≤ 1 / 16384)
      nlinarith
    have e : 2 * (8129 / 10000 * y) * r + 33087 / 100000 * (200000005 / 100000000) * r +
          49376 / 100000 * (346453 / 100000 * y * (200000005 / 100000000) +
            141422 / 100000 * z * (894429 / 100000 * y) + 2 * (276 / 100000 * y)) +
          (33087 / 100000 * (223607 / 100000 * (y / 2)) * (200000002 / 100000000) +
            49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (200000002 / 100000000) +
              223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2))) +
          (28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
            1 * (4 * (11 / 5) * y ^ 2 * 2)) =
        16258 / 10000 * (y * r) + 33087 / 100000 * (200000005 / 100000000) * r +
          (49376 / 100000 * (346453 / 100000 * (200000005 / 100000000) + 552 / 100000) +
            33087 / 100000 * (223607 / 100000 / 2) * (200000002 / 100000000) +
            28416 / 100000 * (223607 / 100000)) * y +
          49376 / 100000 * (141422 / 100000) * (894429 / 100000) * (z * y) +
          (49376 / 100000 * (4 * (11 / 5) * (200000002 / 100000000) +
            223607 / 100000 * (447214 / 100000) + 352 / 10) + 88 / 5) * y ^ 2 := by ring
    rw [e]
    have c1 : 33087 / 100000 * (200000005 / 100000000) * r ≤
        33087 / 100000 * (200000005 / 100000000) * (707107 / 1000000 * z) :=
      mul_le_mul_of_nonneg_left hr1 (by norm_num)
    have c2 : (49376 / 100000 * (346453 / 100000 * (200000005 / 100000000) + 552 / 100000) +
        33087 / 100000 * (223607 / 100000 / 2) * (200000002 / 100000000) +
        28416 / 100000 * (223607 / 100000)) * y ≤
        (49376 / 100000 * (346453 / 100000 * (200000005 / 100000000) + 552 / 100000) +
        33087 / 100000 * (223607 / 100000 / 2) * (200000002 / 100000000) +
        28416 / 100000 * (223607 / 100000)) * (1 / 128 * z) :=
      mul_le_mul_of_nonneg_left hyz' (by norm_num)
    have c3 : 16258 / 10000 * (y * r) ≤ 16258 / 10000 * (1 / 181 * (1 / 128 * z)) :=
      mul_le_mul_of_nonneg_left hyr (by norm_num)
    have c4 : 49376 / 100000 * (141422 / 100000) * (894429 / 100000) * (z * y) ≤
        49376 / 100000 * (141422 / 100000) * (894429 / 100000) * (1 / 128 * (1 / 128 * z)) :=
      mul_le_mul_of_nonneg_left hzy (by norm_num)
    have c5 : (49376 / 100000 * (4 * (11 / 5) * (200000002 / 100000000) +
        223607 / 100000 * (447214 / 100000) + 352 / 10) + 88 / 5) * y ^ 2 ≤
        (49376 / 100000 * (4 * (11 / 5) * (200000002 / 100000000) +
        223607 / 100000 * (447214 / 100000) + 352 / 10) + 88 / 5) *
          (1 / 16384 * (1 / 128 * z)) :=
      mul_le_mul_of_nonneg_left hyy (by norm_num)
    linarith

/-- `dA1 ≤ 1 + 1/16384`. -/
theorem dA1_16 : dA1 n (mA n) ≤ 1 + 1 / 16384 := by
  unfold dA1
  exact sqrt_one_add16 hn

/-- `dA0 ≤ 0.81295/n`. -/
theorem dA0_16 : dA0 n (mA n) ≤ 81295 / 100000 / (n : ℝ) := by
  have h1 := sqrt_one_add16 hn
  have a1 := nc0_16 hn
  have n1 := AgD.nc0_nn (mA n)
  have hy0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold dA0
  refine le_trans (?_ : _ ≤ 81295 / 100000 * (1 / (n : ℝ))) (le_of_eq (by ring))
  calc √(1 + 2 / (n : ℝ)) * AgD.nc0 (mA n)
      ≤ (1 + 1 / 16384) * (8129 / 10000 * (1 / (n : ℝ))) := by gcongr
    _ ≤ 81295 / 100000 * (1 / (n : ℝ)) := by nlinarith

/-- `dA2 ≤ 10.393/n`. -/
theorem dA2_16 : dA2 n (mA n) ≤ 103930 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have h1 := sqrt_one_add16 hn
  have h3 := s3_le16
  have hQ := Q2_16 hn
  unfold dA2
  rw [sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y *
    (4 * √(1 + 2 / (mA n : ℝ)))))) ?_
  · rw [hy]; ring
  · refine le_trans (?_ : _ ≤ 103930 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc √(1 + 2 / (n : ℝ)) * (2 * √3 * y + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))))
        ≤ (1 + 1 / 16384) * (2 * (173206 / 100000) * y + 173206 / 100000 * y *
          (4 * (1 + 1 / 100000000))) := by gcongr
      _ ≤ 103930 / 10000 * y := by nlinarith

/-- `cAdlt ≤ 7.0307/n`. -/
theorem cAdlt16 : cAdlt n (mA n) ≤ 70307 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
  have h2 := Part133.sqrt2_le
  have hK4 := K4_le16 hn
  have hK40 := K4_nonneg n
  have a2 := SS16 hn
  have a3 := DS16 hn
  have a4 := LS16 hn
  have n2 := AgD.SS_nn (mA n)
  have n3 := AgD.DS_nn (mA n)
  rw [← hy] at a3 a4
  have hzy : z * y ≤ y * (1 / 128) := by nlinarith
  unfold cAdlt
  refine le_trans (le_of_eq (?_ : _ = AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) +
    √2 * z * AgD.DS (mA n))) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 70307 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc AgD.LS (mA n) + K4 n * y * AgD.SS (mA n) + √2 * z * AgD.DS (mA n)
        ≤ 276 / 100000 * y + 346453 / 100000 * y * (200000005 / 100000000) +
          141422 / 100000 * z * (894429 / 100000 * y) := by gcongr
      _ ≤ 70307 / 10000 * y := by nlinarith

/-! ## The norm factor and `eps4` -/

/-- `(1 + 5/m_A)·√(1 + 2/n) ≤ 1 + 6106/10⁸`. -/
lemma N0_16 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ 1 + 6106 / 100000000 := by
  have h2 := nsq16 hn
  have h1 : 5 / (mA n : ℝ) ≤ 5 / 268435456 := by
    rw [mA_eqR]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2
  have h10 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have h3 := sqrt_one_add16 hn
  have h30 := Real.sqrt_nonneg (1 + 2 / (n : ℝ))
  calc (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))
      ≤ (1 + 5 / 268435456) * (1 + 1 / 16384) := mul_le_mul (by linarith) h3 h30 (by norm_num)
    _ ≤ 1 + 6106 / 100000000 := by norm_num

/-- `√(eps4 n (m_A)) ≤ 1.41444/√n`. -/
lemma sqrt_eps4_16 : √(eps4 n (mA n)) ≤ 141444 / 100000 / √(n : ℝ) := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  refine sqrt_le_div_s (n4096_of16 hn) (by norm_num) ?_
  unfold eps4
  rw [mA_eqR]
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 16384 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyn : y * (n : ℝ) = 1 := by rw [hy]; field_simp
  have e1 : 5 / (n : ℝ) ^ 2 = 5 * y ^ 2 := by rw [hy]; ring
  have e2 : 2 / (n : ℝ) = 2 * y := by rw [hy]; ring
  rw [e1, e2]
  have hy2 : y ^ 2 ≤ 1 / 16384 * y := by nlinarith
  have hy20 : 0 ≤ y ^ 2 := by positivity
  have hb : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1 ≤ 200062 / 100000 * y := by
    have h5 : 5 * y ^ 2 ≤ 5 / 16384 * y := by nlinarith
    have h50 : 0 ≤ 5 * y ^ 2 := by positivity
    have h5c : 5 * y ^ 2 ≤ 1 / 1000000 := by nlinarith
    have h6 : (1 + 5 * y ^ 2) ^ 2 ≤ 1 + 6104 / 10000000 * y := by nlinarith
    have h7 : (1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) ≤ (1 + 6104 / 10000000 * y) * (1 + 2 * y) :=
      mul_le_mul_of_nonneg_right h6 (by linarith)
    nlinarith
  calc ((1 + 5 * y ^ 2) ^ 2 * (1 + 2 * y) - 1) * (n : ℝ)
      ≤ 200062 / 100000 * y * (n : ℝ) := mul_le_mul_of_nonneg_right hb hx0.le
    _ = 200062 / 100000 := by rw [mul_assoc, hyn, mul_one]
    _ ≤ (141444 / 100000) ^ 2 := by norm_num

/-! ## The bad hidden event -/

/-- The two events of the computed centre, with their true rate:
`Pr(goodDist n (3/4) fails) + Pr(goodT n (1/400000) fails) ≤ 29.93/n` for `n ≥ 16384`. -/
theorem goodHatExtra16 :
    (hidGauss (2 * n) (mW n)).real (goodDist n (3 / 4))ᶜ +
      (hidGauss (2 * n) (mW n)).real (goodT n (1 / 400000))ᶜ ≤ 2993 / 100 / (n : ℝ) := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hn4 := n4096_of16 hn
  have hm0 := mW_pos16 hn
  have hρ := ratio16 hn
  have hρ0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / (mW n : ℝ) := by positivity
  have h2 := goodDist_prob_sharp hn4 (Xc := 3 / 4) (by norm_num)
  have h3 := goodT_prob_sharp hn4 (dT := 1 / 400000) (by norm_num)
  set ρ : ℝ := (n : ℝ) ^ 2 / (mW n : ℝ) with hρd
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 16384 := by
    rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have e2 : 672 * ρ / ((3 : ℝ) / 4 - 8 / 25) ^ 2 = 672 / (43 / 100) ^ 2 * ρ := by ring
  have e3 : 803 / 100 * ρ / ((n : ℝ) * (1 / 400000)) = 3212000 * (ρ * y) := by
    rw [hy]; field_simp; ring
  have e4 : (2993 : ℝ) / 100 / (n : ℝ) = 2993 / 100 * y := by rw [hy]; ring
  rw [e2] at h2
  rw [e3] at h3
  rw [e4]
  have p : ρ * y ≤ 1 / 128 * y * (1 / 16384) := mul_le_mul hρ hy1 hy0.le (by positivity)
  have p2 : 672 / (43 / 100) ^ 2 * ρ ≤ 672 / (43 / 100) ^ 2 * (1 / 128 * y) :=
    mul_le_mul_of_nonneg_left hρ (by norm_num)
  have p3 : (672 : ℝ) / (43 / 100) ^ 2 * (1 / 128 * y) + 3212000 * (1 / 128 * y * (1 / 16384)) ≤
      2993 / 100 * y := by
    have : (672 : ℝ) / (43 / 100) ^ 2 * (1 / 128) + 3212000 * (1 / 128 * (1 / 16384)) ≤
        2993 / 100 := by norm_num
    nlinarith
  linarith

/-- **`Pr(goodHat n fails) ≤ 0.002 + 29.93/n`** for `n ≥ 16384`. -/
theorem goodHat16 :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 2 / 1000 + 2993 / 100 / (n : ℝ) := by
  have hn4 := n4096_of16 hn
  have hn1 : 1 ≤ n := by omega
  have hE := goodHatExtra16 hn
  set P := hidGauss (2 * n) (mW n) with hP
  have h1 : P.real (good136 n)ᶜ ≤ 2 / 1000 := by
    rw [measureReal_compl (good136_meas hn1), probReal_univ]
    have := good136_prob hn4
    linarith
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have a : P.real (goodHat n)ᶜ ≤ P.real
      (((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have b := measureReal_union_le (μ := P) ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ)
    (goodT n (1 / 400000))ᶜ
  have c := measureReal_union_le (μ := P) (good136 n)ᶜ (goodDist n (3 / 4))ᶜ
  linarith

/-! ## The constants of the distance kernel -/

/-- **`gD0 n ≤ 0.6145/√n`, `gD1 n ≤ 2.0274/√n`, `gD2 n ≤ 10.5572/n`** for `n ≥ 16384`. -/
theorem gD16 :
    gD0 n ≤ 6145 / 10000 / √(n : ℝ) ∧ gD1 n ≤ 20274 / 10000 / √(n : ℝ) ∧
      gD2 n ≤ 105572 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * z := fun c => by rw [hz]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * y := fun c => by rw [hy]; ring
  have F1 := f1_16 hn
  have F2 := f2_16 hn
  have F3 := f3_16 hn
  have F4 := f4_le
  have A0 := cA0_16 hn
  have A1 := cA1_16 hn
  have A2 := cA2_16 hn
  have D0 := dA0_16 hn
  have D1 := dA1_16 hn
  have D2 := dA2_16 hn
  have C5 := cAdlt16 hn
  have hN0 := N0_16 hn
  have hE := sqrt_eps4_16 hn
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
  have D0c : dA0 n (mA n) ≤ 81295 / 100000 / 16384 := by nlinarith
  have C5c : cAdlt n (mA n) ≤ 70307 / 10000 / 128 * z := by nlinarith
  have hEc : √(eps4 n (mA n)) ≤ 141444 / 100000 / 128 := by nlinarith
  have p1 := mul_le_lin F1 D0c b0 (by positivity)
  have p2 := mul_le_lin F2 hN0 hN00 (by positivity)
  have p3 := mul_le_lin F3 hEc hE0 (by positivity)
  have p4 : f4 * cAdlt n (mA n) ≤ 63662 / 100000 * (70307 / 10000 / 128 * z) :=
    mul_le_mul F4 C5c b3 (by norm_num)
  have p5 := mul_le_lin F1 D1 b1 (by positivity)
  have F1c : f1 (mF n) ≤ 30656 / 100000 / 128 := by nlinarith
  have p6 : f1 (mF n) * dA2 n (mA n) ≤ 30656 / 100000 / 128 * (103930 / 10000 * y) :=
    mul_le_mul F1c D2 b2 (by norm_num)
  rw [cv, cv, cn]
  refine ⟨?_, ?_, ?_⟩
  · unfold gD0
    linarith
  · unfold gD1
    linarith
  · unfold gD2
    linarith

/-- **`eD142a n ≤ 1.9088/√n`** for `n ≥ 16384`. -/
theorem eD142a16 : eD142a n ≤ 19088 / 10000 / √(n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * z := fun c => by rw [hz]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * y := fun c => by rw [hy]; ring
  obtain ⟨G0, G1, G2⟩ := gD16 hn
  rw [cv] at G0 G1
  rw [cn] at G2
  obtain ⟨g0n, g1n, g2n⟩ := gD_nonneg n
  have G2z : gD2 n ≤ 105572 / 10000 / 128 * z := by nlinarith
  have hτ := tauW142_16 hn
  rw [cv] at hτ
  have hτ0 := tauW142_nonneg hn4
  have hτc : tauW142 n ≤ 132565 / 100000 / 128 := by nlinarith
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have h20 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have hs4 := sig4_le
  have hs40 := sig4_nonneg
  have r1 := mul_le_lin G1 (show 1 - kappa^[4] 0 + tauW142 n ≤
    319057 / 1000000 + 132565 / 100000 / 128 by linarith) (by linarith) (by positivity)
  have r2 := mul_le_lin G2z (show 1 - kappa (kappa 0) + tauW142 n ≤
    50628 / 100000 + 132565 / 100000 / 128 by linarith) (by linarith) (by positivity)
  have r3 : sig4 * tauW142 n ≤ 4404 / 10000 * (132565 / 100000 * z) :=
    mul_le_mul hs4 hτ hτ0 (by norm_num)
  rw [cv]
  unfold eD142a
  linarith

/-! ## The Agent network, the form of Part 142 (`sA0`, `sA2`) -/

/-- `q3 (m_A) 0 ≤ 0.6365/n`. -/
lemma q3z16 : AgD.q3 (mA n) 0 ≤ 6365 / 10000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := hG.comp_kappa
  have hb3 := bG_nonneg hGk
  have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have b3 := AgD.b3_le
  have g3 := AgD.g3_le
  have h5 := AgD.sqrt5_le'
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 16384) := by nlinarith
  unfold AgD.q3
  rw [sqrt_mA, mA_eqR, ← hy]
  refine le_trans (le_of_eq (?_ : _ = bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
    ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2))) ?_
  · rw [hy]; ring
  · calc bG ((kappa ∘ kappa) ∘ kappa) * (√5 * (y / 2)) * 2 +
          ((kappa ∘ kappa) ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * 2)
        ≤ 28416 / 100000 * (223607 / 100000 * (y / 2)) * 2 +
          1 * (4 * (11 / 5) * y ^ 2 * 2) := by gcongr
      _ ≤ 6365 / 10000 * y := by nlinarith

/-- `q2 (m_A) 0 ≤ 0.7418/n`. -/
lemma q2z16 : AgD.q2 (mA n) 0 ≤ 7418 / 10000 * (1 / (n : ℝ)) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
  have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
  have hb2 := bG_nonneg hG
  have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
  have b2 := AgD.b2_le
  have g2 := AgD.g2_le
  have h5 := AgD.sqrt5_le'
  have hK := AgD.Kr_mA_le hn4
  have hK0 := Kr_nonneg (mA n)
  have a5 := sS16 hn
  have a6 := AgD.dS_le hn4
  have a7 := AgD.lS_le hn4
  have n5 := AgD.sS_nn (mA n)
  have n6 := AgD.dS_nn (mA n)
  have n7 := AgD.lS_nn (mA n)
  have hyy : y ^ 2 ≤ y * (1 / 16384) := by nlinarith
  unfold AgD.q2 AgD.eS
  rw [sqrt_mA, mA_eqR, ← hy]
  rw [← hy] at a6 a7
  refine le_trans (le_of_eq (?_ : _ = bG (kappa ∘ kappa) * (√5 * (y / 2)) * AgD.sS (mA n) +
    (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) + √5 * y * AgD.dS (mA n) +
      2 * AgD.lS (mA n)))) ?_
  · rw [hy]; ring
  · calc bG (kappa ∘ kappa) * (√5 * (y / 2)) * AgD.sS (mA n) +
          (kappa ∘ kappa) 0 * (4 * Kr (mA n) * y ^ 2 * AgD.sS (mA n) +
            √5 * y * AgD.dS (mA n) + 2 * AgD.lS (mA n))
        ≤ 33087 / 100000 * (223607 / 100000 * (y / 2)) * (200000002 / 100000000) +
          49376 / 100000 * (4 * (11 / 5) * y ^ 2 * (200000002 / 100000000) +
            223607 / 100000 * y * (447214 / 100000 * y) + 2 * (176 / 10 * y ^ 2)) := by gcongr
      _ ≤ 7418 / 10000 * y := by nlinarith

/-- `sA2 ≤ 10.6161/n` for `n ≥ 16384`. -/
theorem sA2_16 : sA2 n (mA n) ≤ 106161 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have h3 := s3_le16
  have h2 := Part133.sqrt2_le
  have hQ := Q2_16 hn
  have hcg := AgS.cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le16
  have hzy : z * y ≤ y * (1 / 128) := by nlinarith
  rw [sA2_eq, sqrt_mA]
  refine le_trans (le_of_eq (?_ : _ = (1 + √2 + AgS.cgS (kappa ∘ kappa)) * (2 * √3 * y +
    √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
    2 * √3 * y)) ?_
  · rw [hy, hz]; ring
  · refine le_trans (?_ : _ ≤ 106161 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc (1 + √2 + AgS.cgS (kappa ∘ kappa)) * (2 * √3 * y +
          √3 * y * (4 * √(1 + 2 / (mA n : ℝ)))) * z + √3 * y * (4 * √(1 + 2 / (mA n : ℝ))) +
          2 * √3 * y
        ≤ (1 + 141422 / 100000 + 3408455 / 10000000) * (2 * (173206 / 100000) * y +
          173206 / 100000 * y * (4 * (1 + 1 / 100000000))) * z +
          173206 / 100000 * y * (4 * (1 + 1 / 100000000)) + 2 * (173206 / 100000) * y := by
          gcongr
      _ ≤ 106161 / 10000 * y := by nlinarith

/-- `sA0 ≤ 8.385/n` for `n ≥ 16384`. -/
theorem sA0_16 : sA0 n (mA n) ≤ 8385 / 1000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz, hyz'⟩ := yz16 hn
  have hn4 := n4096_of16 hn
  have h2 := Part133.sqrt2_le
  have hcg := AgS.cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le16
  have hK4 := K4_le16 hn
  have hK40 := K4_nonneg n
  have a1 := nc0_16 hn
  have a2 := SS16 hn
  have a3 := DS16 hn
  have a4 := LS16 hn
  have a5 := q2z16 hn
  have a6 := q3z16 hn
  have n1 := AgD.nc0_nn (mA n)
  have n2 := AgD.SS_nn (mA n)
  have n3 := AgD.DS_nn (mA n)
  have n4 := AgD.LS_nn (mA n)
  have n5 : 0 ≤ AgD.q2 (mA n) 0 := by
    have hG : KGood (kappa ∘ kappa) := kGood_kappa.comp_kappa
    have hb2 := bG_nonneg hG
    have hg2 : 0 ≤ (kappa ∘ kappa) 0 := hG.nonneg_on KGood.zero_mem
    have := AgD.sS_nn (mA n); have := AgD.dS_nn (mA n); have := AgD.lS_nn (mA n)
    have := Kr_nonneg (mA n)
    unfold AgD.q2 AgD.eS; positivity
  have n6 : 0 ≤ AgD.q3 (mA n) 0 := by
    have hGk : KGood ((kappa ∘ kappa) ∘ kappa) := (kGood_kappa.comp_kappa).comp_kappa
    have hb3 := bG_nonneg hGk
    have hg3 : 0 ≤ ((kappa ∘ kappa) ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
    have := Kr_nonneg (mA n)
    unfold AgD.q3; positivity
  rw [← hy] at a1 a3 a4 a5 a6
  have hzy : z * y ≤ y * (1 / 128) := by nlinarith
  have hyr : y * r ≤ y * (1 / 181) := mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [sA0_eq]
  refine le_trans (le_of_eq (?_ : _ =
    ((1 + √2) * AgD.q3 (mA n) 0 + AgS.cgS (kappa ∘ kappa) * AgD.nc0 (mA n) +
      (1 + √2) * AgD.q2 (mA n) 0 +
      (1 + √2 + AgS.cgS (kappa ∘ kappa)) * AgD.LS (mA n)) * z +
    K4 n * y * AgD.SS (mA n) + AgD.DS (mA n) * r + AgD.q2 (mA n) 0 + AgD.q3 (mA n) 0)) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 8385 / 1000 * y) (le_of_eq (by rw [hy]; ring))
    calc ((1 + √2) * AgD.q3 (mA n) 0 + AgS.cgS (kappa ∘ kappa) * AgD.nc0 (mA n) +
          (1 + √2) * AgD.q2 (mA n) 0 +
          (1 + √2 + AgS.cgS (kappa ∘ kappa)) * AgD.LS (mA n)) * z +
          K4 n * y * AgD.SS (mA n) + AgD.DS (mA n) * r + AgD.q2 (mA n) 0 + AgD.q3 (mA n) 0
        ≤ ((1 + 141422 / 100000) * (6365 / 10000 * y) +
          3408455 / 10000000 * (8129 / 10000 * y) +
          (1 + 141422 / 100000) * (7418 / 10000 * y) +
          (1 + 141422 / 100000 + 3408455 / 10000000) * (276 / 100000 * y)) * z +
          346453 / 100000 * y * (200000005 / 100000000) + 894429 / 100000 * y * r +
          7418 / 10000 * y + 6365 / 10000 * y := by gcongr
      _ ≤ 8385 / 1000 * y := by nlinarith

/-! ## The links of `F` and `A` of the same-`A` kernel (`eAFr`) and `Vb` -/

/-- `cF2o (m_F) ≤ 0.41768/√n`. -/
lemma cF2o16 : cF2o (mF n) ≤ 41768 / 100000 / √(n : ℝ) := by
  have hn4 := n4096_of16 hn
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge16 hn
  have hm := mF_geR hn4
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hms := BstLean.Part139.mF_ge_s hn4
  have hmF : 128 * (n : ℝ) ≤ mF n := by
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
  have hc2 : (223303 : ℝ) / 10000 ≤ (41768 / 100000) ^ 2 * 128 := by norm_num
  calc (6 * (1 + 5 / (mF n : ℝ)) + (5 * kappa 0 + √6) ^ 2) * (n : ℝ)
      ≤ 223303 / 10000 * (n : ℝ) := mul_le_mul_of_nonneg_right h7 hx0.le
    _ ≤ (41768 / 100000) ^ 2 * 128 * (n : ℝ) := mul_le_mul_of_nonneg_right hc2 hx0.le
    _ = (41768 / 100000) ^ 2 * (128 * (n : ℝ)) := by ring
    _ ≤ (41768 / 100000) ^ 2 * (mF n : ℝ) := mul_le_mul_of_nonneg_left hmF (by norm_num)

/-- `cAr (κ∘κ) (m_A) n ≤ 1.82164/√n`. -/
lemma cAr16 : cAr (kappa ∘ kappa) (mA n) n ≤ 182164 / 100000 / √(n : ℝ) := by
  obtain ⟨y, u, r, hy, hu, hr, hy0, hu0, hr0, hy1, hu1, hr1, hr2, hyz, hnu⟩ := yz16 hn
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK := K4_le16 hn
  have hK0 := K4_nonneg n
  have hq := kappa2_zero_le
  have hq0 := q_mem.1
  have h2 := Part133.sqrt2_le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have h6 := Part133.sqrt6_le
  have h60 := Real.sqrt_nonneg (6 : ℝ)
  have hA : 5 / (mA n : ℝ) ≤ 2 / 100000000 := by
    have h2' := nsq16 hn
    rw [mA_eqR, div_le_iff₀ (by positivity)]
    linarith
  have hA0 : (0 : ℝ) ≤ 5 / (mA n : ℝ) := by positivity
  have hsA := Q5_16 hn
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
      2 * (346453 / 100000) * (49376 / 100000) * (1 / 128 * u) := by
    rw [div_eq_mul_one_div]
    have a : 2 * K4 n * kappa (kappa 0) ≤ 2 * (346453 / 100000) * (49376 / 100000) := by
      have := mul_le_mul hK hq hq0 (by norm_num)
      linarith
    exact mul_le_mul a hnu (by positivity) (by norm_num)
  have t3 : (5 * kappa (kappa 0) + √6) / (n : ℝ) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 128 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t4 : (5 + √6) / (n : ℝ) ≤ (5 + 24495 / 10000) * (1 / 128 * u) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hnu (by positivity) (by norm_num)
  have t10 : 0 ≤ (1 + √2 * kappa (kappa 0)) / √(n : ℝ) := by positivity
  have t20 : 0 ≤ 2 * K4 n * kappa (kappa 0) / (n : ℝ) := by positivity
  have t30 : 0 ≤ (5 * kappa (kappa 0) + √6) / (n : ℝ) := by positivity
  unfold cAr
  simp only [Function.comp_apply]
  rw [sqrt_mA, div_eq_mul_one_div (182164 / 100000 : ℝ), ← hu]
  have e1 : ((1 + √2 * kappa (kappa 0)) / √(n : ℝ) + 2 * K4 n * kappa (kappa 0) / (n : ℝ)) *
      (1 + 5 / (mA n : ℝ)) ≤
      ((1 + 141422 / 100000 * (49376 / 100000)) * u +
        2 * (346453 / 100000) * (49376 / 100000) * (1 / 128 * u)) * (1 + 2 / 100000000) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have e2 : (5 * kappa (kappa 0) + √6) / (n : ℝ) * √(1 + 5 / (mA n : ℝ)) ≤
      (5 * (49376 / 100000) + 24495 / 10000) * (1 / 128 * u) * (1 + 1 / 100000000) :=
    mul_le_mul t3 hsA hsA0 (by positivity)
  nlinarith

/-- **`eAFr n (m_A) (m_F) ≤ 2.2394/√n`** for `n ≥ 16384`. -/
theorem eAFr16 : eAFr n (mA n) (mF n) ≤ 22394 / 10000 / √(n : ℝ) := by
  have hs := sqrt_n_ge16 hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := cF2o16 hn
  have h10 : 0 ≤ cF2o (mF n) := Real.sqrt_nonneg _
  have h3 := cAr16 hn
  have e1 := N0_16 hn
  set u : ℝ := 1 / √(n : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  rw [div_eq_mul_one_div, ← hu] at h1 h3 ⊢
  have e2 : cF2o (mF n) * ((1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ))) ≤
      41768 / 100000 * u * (1 + 6106 / 100000000) :=
    mul_le_mul h1 e1 (by positivity) (by positivity)
  unfold eAFr
  nlinarith

/-- **`Vb n ≤ 0.2451`** for `n ≥ 16384`. -/
theorem Vb16 : Vb n ≤ 2451 / 10000 := by
  have hn4 := n4096_of16 hn
  have hn1 : 1 ≤ n := by omega
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge16 hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have h1 := eAFr16 hn
  have h2 := eWr16 hn
  have h3 := sU16 hn
  have h4 := sig4_le
  have h40 := sig4_nonneg
  have hsU := sU_nonneg (2 * n)
  have hW0 := eWr_nonneg142 hn1 (2 * n) (mW n)
  have hQ := q0_ge16
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 / 128 := by
    rw [ht]
    exact one_div_le_one_div_of_le (by norm_num) hs
  have e1 : (22394 : ℝ) / 10000 / √(n : ℝ) = 22394 / 10000 * t := by rw [ht]; ring
  have e2 : (96498 : ℝ) / 100000 / √(n : ℝ) = 96498 / 100000 * t := by rw [ht]; ring
  have e3 : (36067 : ℝ) / 100000 / √(n : ℝ) = 36067 / 100000 * t := by rw [ht]; ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have h5 : sig4 * (eWr (2 * n) n (mW n) + sU (2 * n)) ≤
      4404 / 10000 * (132565 / 100000 * t) := by
    apply mul_le_mul h4 (by linarith) (by positivity) (by norm_num)
  have h6 : 183 / 100 / (n : ℝ) ≤ 183 / 100 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold Vb
  nlinarith

/-! ## `EHH`, `pertA`, `XA142` -/

/-- `EHH n (1/20) ≤ 242.5·n/m_W` for `n ≥ 16384` (Part 140: `250` for `n ≥ 4096`). -/
theorem EHH_le16 : EHH n (1 / 20) ≤ 2425 / 10 * (n : ℝ) / (mW n : ℝ) := by
  have hn4 := n4096_of16 hn
  have hm0 := mW_pos16 hn
  have hn' := nR_ge16 hn
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
  rw [div_eq_mul_one_div (2425 / 10 * (n : ℝ)), ← hx]
  have h4 : 17200 * x ≤ 105 / 100 * (n : ℝ) * x := by
    refine mul_le_mul_of_nonneg_right ?_ hx0.le
    linarith
  have h5 : 0 ≤ (n : ℝ) * x := by positivity
  nlinarith

/-- **`EHH n (1/20) ≤ (11564/10⁸)/n`** for `n ≥ 16384`. -/
theorem EHH16 : EHH n (1 / 20) ≤ 11564 / 100000000 / (n : ℝ) := by
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h := EHH_le16 hn
  obtain ⟨-, h2, -⟩ := mW_more16 hn
  have e : 2425 / 10 * (n : ℝ) / (mW n : ℝ) = 2425 / 10 * ((n : ℝ) / (mW n : ℝ)) := by ring
  rw [e] at h
  have e2 : (11564 : ℝ) / 100000000 / (n : ℝ) = 11564 / 100000000 * (1 / (n : ℝ)) := by ring
  rw [e2]
  have hy0 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  nlinarith

omit hn in
/-- `pertA n = (27501/10⁸)/n` (exact; `n ≥ 1`). -/
theorem pertA16 (hn1 : 1 ≤ n) : pertA n = 27501 / 100000000 / (n : ℝ) := by
  rw [pertA_eq hn1]; ring

/-- `XA142 n (1/20) η η′` for `n ≥ 16384`, every `η, η′ > 0`. -/
theorem XA142_gen16 {η η' : ℝ} (hη : 0 < η) (hη' : 0 < η') :
    XA142 n (1 / 20) η η' ≤
      ((1 + η') * ((1 + η) * (183 / 100) * (2451 / 10000) +
          4 * (1 + 1 / η) * (11564 / 100000000)) +
        (1 + 1 / η') * (27501 / 100000000)) * (1 / (n : ℝ)) := by
  have hn4 := n4096_of16 hn
  have hx := nR_ge16 hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hE := EHH16 hn
  have hp := pertA_eq (n := n) (by omega)
  have hV := Vb16 hn
  set y : ℝ := 1 / (n : ℝ) with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have e183 : 183 / 100 / (n : ℝ) = 183 / 100 * y := by rw [hy]; ring
  have eE : (11564 : ℝ) / 100000000 / (n : ℝ) = 11564 / 100000000 * y := by rw [hy]; ring
  rw [eE] at hE
  unfold XA142
  rw [e183, hp]
  have a : (1 + η) * (183 / 100 * y) * Vb n ≤ (1 + η) * (183 / 100 * y) * (2451 / 10000) :=
    mul_le_mul_of_nonneg_left hV (by positivity)
  have b : 4 * (1 + 1 / η) * EHH n (1 / 20) ≤ 4 * (1 + 1 / η) * (11564 / 100000000 * y) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have c : (1 + η') * ((1 + η) * (183 / 100 * y) * Vb n + 4 * (1 + 1 / η) * EHH n (1 / 20)) ≤
      (1 + η') * ((1 + η) * (183 / 100 * y) * (2451 / 10000) +
        4 * (1 + 1 / η) * (11564 / 100000000 * y)) :=
    mul_le_mul_of_nonneg_left (add_le_add a b) (by positivity)
  calc (1 + η') * ((1 + η) * (183 / 100 * y) * Vb n + 4 * (1 + 1 / η) * EHH n (1 / 20)) +
        (1 + 1 / η') * (27501 / 100000000 * y)
      ≤ (1 + η') * ((1 + η) * (183 / 100 * y) * (2451 / 10000) +
        4 * (1 + 1 / η) * (11564 / 100000000 * y)) +
        (1 + 1 / η') * (27501 / 100000000 * y) := by linarith
    _ = _ := by ring

/-- **`XA142 n (1/20) (1/30) (1/40) ≤ 0.5011/n`** for `n ≥ 16384` (the best of the tried
`(η, η′)`). -/
theorem XA142_16 : XA142 n (1 / 20) (1 / 30) (1 / 40) ≤ 5011 / 10000 * (1 / (n : ℝ)) := by
  have hx := nR_ge16 hn
  have h := XA142_gen16 hn (η := 1 / 30) (η' := 1 / 40) (by norm_num) (by norm_num)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  norm_num

/-- `XA142 n (1/20) (1/20) (1/100) ≤ 0.5133/n` for `n ≥ 16384` (the `(η, η′)` of `XA142_le`). -/
theorem XA142_16' : XA142 n (1 / 20) (1 / 20) (1 / 100) ≤ 5133 / 10000 * (1 / (n : ℝ)) := by
  have hx := nR_ge16 hn
  have h := XA142_gen16 hn (η := 1 / 20) (η' := 1 / 100) (by norm_num) (by norm_num)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  norm_num

/-! ## `eD142` -/

omit hn in
/-- `eD142_arith` of Part 142 with the bounds of `sA0`, `sA2` and of `|hD1|` as parameters
(Part 142 has `8.6`, `10.9` and `2·F1·D1` there). -/
lemma eD142_arith16 (hn4 : 4096 ≤ n) {t T F1 F2 F3 D0 D1 D2 C5 N0 E4 TW S0 S2 H1 : ℝ}
    (ht : t = 1 / √(n : ℝ)) (hT : t ≤ T) (hT0 : 0 ≤ T)
    (hF1 : f1 (mF n) ≤ F1 * t) (hF2 : f2 (mF n) ≤ F2 * t) (hF3 : f3 (mF n) ≤ F3 * t)
    (qD0 : dA0 n (mA n) ≤ D0 * t ^ 2) (qD1 : dA1 n (mA n) ≤ D1)
    (qD2 : dA2 n (mA n) ≤ D2 * t ^ 2) (hC5 : cAdlt n (mA n) ≤ C5 * t ^ 2)
    (hN0 : (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) ≤ N0)
    (hE4 : √(eps4 n (mA n)) ≤ E4 * t) (hTW : tauW142 n ≤ TW * t)
    (hS0 : sA0 n (mA n) ≤ S0 * t ^ 2) (hS2 : sA2 n (mA n) ≤ S2 * t ^ 2)
    (hF1p : 0 ≤ F1) (hF2p : 0 ≤ F2) (hF3p : 0 ≤ F3) (hD0p : 0 ≤ D0) (hD2p : 0 ≤ D2)
    (hC5p : 0 ≤ C5) (hE4p : 0 ≤ E4) (hTWp : 0 ≤ TW) (hS0p : 0 ≤ S0) (hS2p : 0 ≤ S2)
    (hFD : 3408 / 10000 ≤ 2 * F1 * D1) (hH1a : 2 * F1 * D1 - 3408 / 10000 ≤ H1)
    (hH1b : 3408455 / 10000000 ≤ H1) :
    eD142 n ≤ (2 * F1 * D0 * T ^ 2 + 2 * F2 * N0 + 2 * F3 * E4 * T +
        63662 / 100000 * C5 * T + S0 * T +
      (2 * F1 * D1 - 3408 / 10000) * (319057 / 1000000) +
      (2 * F1 * D2 * T ^ 2 + S2 * T) * (50628 / 100000) +
      24143 / 10000 * (2229 / 10000) +
      (H1 + 2 * F1 * D2 * T ^ 2 + S2 * T +
        24143 / 10000 * (4404 / 10000)) * (TW * T) + 4404 / 10000 * TW) * t := by
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hx0
  have ht0 : 0 < t := by rw [ht]; positivity
  have et2 : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have ht2 : t ^ 2 ≤ T * t := by nlinarith
  have ht20 : 0 ≤ t ^ 2 := by positivity
  have hTT : t ^ 2 ≤ T ^ 2 := by nlinarith
  have F4 := f4_le
  have f4n := f4_nonneg
  have S1 := sA1_le hn4
  have S1' := sA1'_ge hn4
  rw [cv] at S1 S1'
  have f1n := f1_nonneg (mF n)
  have b0 := dA0_nonneg n (mA n)
  have b1 := dA1_nonneg n (mA n)
  have b2 := dA2_nonneg n (mA n)
  have b3 := cAdlt_nonneg n (mA n)
  have s0n := sA0_nonneg n (mA n)
  have s1n := sA1_nonneg n
  have s1'n := sA1'_nonneg n
  have s2n := sA2_nonneg n (mA n)
  have hN00 : 0 ≤ (1 + 5 / (mA n : ℝ)) * √(1 + 2 / (n : ℝ)) := by positivity
  have hE0 := Real.sqrt_nonneg (eps4 n (mA n))
  have hτ0 := tauW142_nonneg hn4
  have D0c : dA0 n (mA n) ≤ D0 * T ^ 2 := qD0.trans (mul_le_mul_of_nonneg_left hTT hD0p)
  have D2c : dA2 n (mA n) ≤ D2 * T ^ 2 := qD2.trans (mul_le_mul_of_nonneg_left hTT hD2p)
  have C5c : cAdlt n (mA n) ≤ C5 * T * t := by
    have h := mul_le_mul_of_nonneg_left ht2 hC5p
    linarith
  have S0c : sA0 n (mA n) ≤ S0 * T * t := by
    have h := mul_le_mul_of_nonneg_left ht2 hS0p
    linarith
  have S2c : sA2 n (mA n) ≤ S2 * T * t := by
    have h := mul_le_mul_of_nonneg_left ht2 hS2p
    linarith
  have E4c : √(eps4 n (mA n)) ≤ E4 * T := hE4.trans (mul_le_mul_of_nonneg_left hT hE4p)
  have TWc : tauW142 n ≤ TW * T := hTW.trans (mul_le_mul_of_nonneg_left hT hTWp)
  have hF1t : 0 ≤ F1 * t := by positivity
  have p1 := mul_le_lin hF1 D0c b0 hF1t
  have p2 := mul_le_lin hF2 hN0 hN00 (by positivity)
  have p3 := mul_le_lin hF3 E4c hE0 (by positivity)
  have p4 : f4 * cAdlt n (mA n) ≤ 63662 / 100000 * (C5 * T * t) :=
    mul_le_mul F4 C5c b3 (by norm_num)
  have p5 := mul_le_lin hF1 qD1 b1 hF1t
  have p6 := mul_le_lin hF1 D2c b2 hF1t
  have G0 : hD0 n ≤ (2 * F1 * D0 * T ^ 2 + 2 * F2 * N0 + 2 * F3 * E4 * T +
      63662 / 100000 * C5 * T + S0 * T) * t := by
    unfold hD0
    linarith
  have G1u : hD1 n ≤ (2 * F1 * D1 - 3408 / 10000) * t := by
    unfold hD1
    linarith
  have G1a : |hD1 n| ≤ H1 * t := by
    have hA0 : 0 ≤ 2 * f1 (mF n) * dA1 n (mA n) := by positivity
    have hS1h : sA1' n ≤ 3408455 / 10000000 * t := by
      unfold sA1'
      rw [cv]
      exact mul_le_mul_of_nonneg_right cg2_le16 ht0.le
    have h1 : (2 * F1 * D1 - 3408 / 10000) * t ≤ H1 * t :=
      mul_le_mul_of_nonneg_right hH1a ht0.le
    have h2 : 3408455 / 10000000 * t ≤ H1 * t := mul_le_mul_of_nonneg_right hH1b ht0.le
    have hlow : -(sA1' n) ≤ hD1 n := by unfold hD1; linarith
    rw [abs_le]
    constructor <;> linarith
  have G2 : hD2 n ≤ (2 * F1 * D2 * T ^ 2 + S2 * T) * t := by
    unfold hD2
    linarith
  have G3 : hD3 n ≤ 24143 / 10000 * t := S1
  obtain ⟨g0n, g2n, g3n⟩ := hD_nonneg n
  have h4 : 1 - kappa^[4] 0 ≤ 319057 / 1000000 := one_sub_k4_le
  have h40 : 0 ≤ 1 - kappa^[4] 0 := one_sub_k4_nonneg
  have h2 : 1 - kappa (kappa 0) ≤ 50628 / 100000 := by have := kappa2_zero_ge; linarith
  have h20 : 0 ≤ 1 - kappa (kappa 0) := by have := kappa2_zero_le; linarith
  have h6 : 1 - kappa^[6] 0 ≤ 2229 / 10000 := q0_ge16
  have h60 : 0 ≤ 1 - kappa^[6] 0 := by have := q0_le16; linarith
  have hs4 := sig4_le
  have hs40 := sig4_nonneg
  have r1 : hD1 n * (1 - kappa^[4] 0) ≤
      (2 * F1 * D1 - 3408 / 10000) * (319057 / 1000000) * t := by
    by_cases hneg : hD1 n ≤ 0
    · have hU : 0 ≤ (2 * F1 * D1 - 3408 / 10000) * (319057 / 1000000) * t :=
        mul_nonneg (mul_nonneg (by linarith) (by norm_num)) ht0.le
      have : hD1 n * (1 - kappa^[4] 0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg h40
      linarith
    · rw [not_le] at hneg
      have hU0 : 0 ≤ (2 * F1 * D1 - 3408 / 10000) * t :=
        mul_nonneg (by linarith) ht0.le
      have := mul_le_mul G1u h4 h40 hU0
      linarith
  have r2 := mul_le_lin G2 h2 h20 (by positivity)
  have r3 := mul_le_lin G3 h6 h60 (by positivity)
  have r4a : hD3 n * sig4 ≤ 24143 / 10000 * (4404 / 10000) * t :=
    mul_le_lin G3 hs4 hs40 (by positivity)
  have hsum0 : 0 ≤ |hD1 n| + hD2 n + hD3 n * sig4 := by positivity
  have hH1p : 0 ≤ H1 := by linarith
  have hsum : |hD1 n| + hD2 n + hD3 n * sig4 ≤
      (H1 + 2 * F1 * D2 * T ^ 2 + S2 * T +
        24143 / 10000 * (4404 / 10000)) * t := by linarith
  have r4 := mul_le_lin hsum TWc hτ0 (by positivity)
  have r5 : sig4 * tauW142 n ≤ 4404 / 10000 * (TW * t) :=
    mul_le_mul hs4 hTW hτ0 (by norm_num)
  unfold eD142
  linarith

/-- **`eD142 n ≤ 1.4406/√n`** for `n ≥ 16384`. -/
theorem eD142_16 : eD142 n ≤ 14406 / 10000 / √(n : ℝ) := by
  have hn4 := n4096_of16 hn
  have hx := nR_ge hn4
  have hx0 : (0 : ℝ) < n := by linarith
  have hs := sqrt_n_ge16 hn
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  set t : ℝ := 1 / √(n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht128 : t ≤ 1 / 128 := by
    rw [ht]; exact one_div_le_one_div_of_le (by norm_num) hs
  have et2 : t ^ 2 = 1 / (n : ℝ) := by
    rw [ht, div_pow, Real.sq_sqrt hx0.le]; norm_num
  have cv : ∀ c : ℝ, c / √(n : ℝ) = c * t := fun c => by rw [ht]; ring
  have cn : ∀ c : ℝ, c / (n : ℝ) = c * t ^ 2 := fun c => by rw [et2]; ring
  have F1 := f1_16 hn
  have F2 := f2_16 hn
  have F3 := f3_16 hn
  have D0 := dA0_16 hn
  have D1 := dA1_16 hn
  have D2 := dA2_16 hn
  have C5 := cAdlt16 hn
  have hτ := tauW142_16 hn
  have hE := sqrt_eps4_16 hn
  have hN0 := N0_16 hn
  have S0 := sA0_16 hn
  have S2 := sA2_16 hn
  rw [cv] at F1 F2 F3 hτ hE
  rw [cn] at D0 D2 C5 S0 S2
  have h := eD142_arith16 hn4 (H1 := 3408455 / 10000000) ht ht128 (by norm_num)
    F1 F2 F3 D0 D1 D2 C5 hN0 hE hτ S0 S2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rw [cv]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ ht0.le)
  norm_num

end big

end BstLean.Part143

open BstLean.Part143 in
#print axioms tauW142_16
open BstLean.Part143 in
#print axioms goodHat16
open BstLean.Part143 in
#print axioms goodHatExtra16
open BstLean.Part143 in
#print axioms gD16
open BstLean.Part143 in
#print axioms eD142a16
open BstLean.Part143 in
#print axioms sA0_16
open BstLean.Part143 in
#print axioms sA2_16
open BstLean.Part143 in
#print axioms eAFr16
open BstLean.Part143 in
#print axioms Vb16
open BstLean.Part143 in
#print axioms EHH16
open BstLean.Part143 in
#print axioms pertA16
open BstLean.Part143 in
#print axioms XA142_gen16
open BstLean.Part143 in
#print axioms XA142_16
open BstLean.Part143 in
#print axioms eD142_16
