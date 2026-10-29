import BstLean.Part280Table
import BstLean.Part276Prices

/-! Part 280, task 2 (prices): the four Markov prices of the sharp table event for every
`n` in 11883–12224, with the M2 node cap `Q = .58` and node moment `H = .5275`.

All bounds hold on the whole interval. Each quantity is bounded by its value at the
end of the interval that makes it largest (one block, `11883 ≤ n ≤ 12224`). -/
namespace BstLean.Part280
open Real
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part170 BstLean.Part171
open BstLean.Part172 BstLean.Part212 BstLean.Part213 BstLean.Part216 BstLean.Part220
open BstLean.Part223
open BstLean.Part276 (fourA)

variable {n : ℕ}

theorem tA_eq (n : ℕ) : tA n = 2 / (n : ℝ) ^ 2 := by
  unfold tA mA
  push_cast
  ring

/-! ### The statistics constant -/

theorem radius_constantN (hn : 11883 ≤ n) : exactRadius (n - 1 - 1) 128 ≤ 1011 / 1000 := by
  have hd : ((n - 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  apply le_of_pow_le_pow_left₀ (by norm_num : (256 : ℕ) ≠ 0) (by norm_num)
  have h := exactRadius_pow (by omega : 2 ≤ n - 1 - 1) (by norm_num : 1 ≤ (128 : ℕ))
  rw [show 2 * 128 = 256 from rfl] at h
  rw [h, hd]
  have hp : radialProduct (n - 1 - 1) 128 ≤ ((n : ℝ) - 2 + 254) ^ 128 := by
    unfold radialProduct
    calc
      _ ≤ ∏ _i ∈ Finset.range 128, ((n : ℝ) - 2 + 254) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          have hi' : (i : ℝ) ≤ 127 := by
            exact_mod_cast (show i ≤ 127 from by have := Finset.mem_range.mp hi; omega)
          rw [hd]
          linarith
      _ = _ := by simp
  have h1 : (0 : ℝ) < (n : ℝ) - 2 - 1 := by linarith
  rw [div_le_iff₀ (pow_pos h1 128)]
  calc
    _ ≤ ((n : ℝ) - 2 + 254) ^ 128 := hp
    _ ≤ ((1011 / 1000 : ℝ) ^ 2 * ((n : ℝ) - 2 - 1)) ^ 128 :=
        pow_le_pow_left₀ (by linarith) (by nlinarith) 128
    _ = _ := by ring

theorem log_mN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) : Real.log (mA n : ℝ) ≤ 19 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : (n : ℝ) ≤ 12224 := by exact_mod_cast hn2
  have hmE : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hm : (0 : ℝ) < (mA n : ℝ) := by rw [hmE]; positivity
  rw [Real.log_le_iff_le_exp hm]
  have he := Real.exp_one_gt_d9
  have h19 : Real.exp 19 = Real.exp 1 ^ 19 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h19]
  have hp := pow_le_pow_left₀ (by norm_num) he.le 19
  refine le_trans ?_ hp
  rw [hmE]
  calc (n : ℝ) ^ 2 ≤ 12224 ^ 2 := by gcongr
    _ ≤ _ := by norm_num

theorem paperT0N (hn : 11883 ≤ n) (hn2 : n ≤ 12224) : paperT0 n ≤ 61645 / 10000 := by
  unfold paperT0
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have := log_mN hn hn2
  calc 2 * Real.log (mA n : ℝ) ≤ 2 * 19 := by linarith
    _ ≤ _ := by norm_num

theorem statistics_constantN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) :
    statisticsConstant (paperBound256 n) ≤ 32 / 10 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h0 := paperT0_bounds (by omega : 8000 ≤ n) (by omega : n ≤ 16384)
  have ht : paperTail256 n ≤ 10 :=
    (min_le_left _ _).trans BstLean.Part276.gaussian_constant10
  have hh : √(2 / (n : ℝ)) ≤ 12974 / 1000000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hx0]
    nlinarith
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have htp : 0 ≤ paperT0 n := by linarith [h0.1]
  have htt : 0 ≤ paperTail256 n := by
    unfold paperTail256
    exact le_min (gaussMomConst_nonneg _) (div_nonneg (by positivity) htp)
  have hs2 : √(2 / (n : ℝ)) * √(n : ℝ) = √2 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hx0.ne']
  have hR := radius_constantN hn
  have hR0 : 0 ≤ exactRadius (n - 1 - 1) 128 := by
    unfold exactRadius
    exact div_nonneg (rpow_nonneg
      (radialProduct_pos (by omega : 1 ≤ n - 1 - 1) 128).le _) (sqrt_nonneg _)
  have hL : paperLJ256 n ≤
      (1011 / 1000 : ℝ) * (14143 / 10000 + 12974 / 1000000 * (61645 / 10000 + 10)) := by
    change exactRadius (n - 1 - 1) 128 * √(2 / (n : ℝ)) *
      (√(n : ℝ) + paperT0 n + paperTail256 n) ≤ _
    have e : exactRadius (n - 1 - 1) 128 * √(2 / (n : ℝ)) *
        (√(n : ℝ) + paperT0 n + paperTail256 n) = exactRadius (n - 1 - 1) 128 *
          (√2 + √(2 / (n : ℝ)) * (paperT0 n + paperTail256 n)) := by
      rw [← hs2]; ring
    rw [e]
    refine mul_le_mul hR ?_ (add_nonneg (sqrt_nonneg _)
      (mul_nonneg (sqrt_nonneg _) (add_nonneg htp htt))) (by norm_num)
    have := mul_le_mul hh (add_le_add (paperT0N hn hn2) ht) (add_nonneg htp htt) (by norm_num)
    linarith
  have ha : paperActivationFactor n ≤ 1 + 14143 / 10000 * 10 / 11883 := by
    have hprod := mul_le_mul h2 BstLean.Part276.gaussian_constant10
      (gaussMomConst_nonneg 128) (by norm_num : (0 : ℝ) ≤ 14143 / 10000)
    unfold paperActivationFactor
    have h3 : √2 * gaussMomConst 128 / (n : ℝ) ≤ 14143 / 10000 * 10 / 11883 := by
      calc √2 * gaussMomConst 128 / (n : ℝ) ≤ 14143 / 10000 * 10 / (n : ℝ) :=
            div_le_div_of_nonneg_right hprod hx0.le
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    linarith
  have hr : (30000 : ℝ) ^ ((64 : ℝ)⁻¹) ≤ 11748 / 10000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 30000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp
    simp only [one_div] at hp
    rw [hp]
    norm_num
  have hL0 : 0 ≤ paperLJ256 n := by
    unfold paperLJ256
    exact mul_nonneg (mul_nonneg hR0 (sqrt_nonneg _))
      (add_nonneg (add_nonneg (sqrt_nonneg _) htp) htt)
  have ha0 : 0 ≤ paperActivationFactor n :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (paperActivationFactor_ge_one _)
  unfold statisticsConstant paperBound256
  calc
    _ ≤ (11748 / 10000 : ℝ) *
      (((1011 / 1000 : ℝ) * (14143 / 10000 + 12974 / 1000000 * (61645 / 10000 + 10))) ^ 2 *
        (1 + 14143 / 10000 * 10 / 11883 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 32 / 10 := by norm_num

theorem statistics_constant_posN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) :
    0 < statisticsConstant (paperBound256 n) :=
  statisticsConstant_pos ((paperStatisticsBound_pos (by omega : 4 ≤ n)
    (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by omega) (by omega)))

/-! ### The scalar envelope -/

/-- The M2 envelope: cap `Q = .58`, operator 160, variance bounds `.17/n` and `2.6/n`. -/
noncomputable def envN (n : ℕ) (C : ℝ) : RAData :=
  envelopeData n (58 / 100) 160 (17 / (100 * n)) (26 / (10 * n)) C C C

theorem envelopeD_leN (hn : 11883 ≤ n) :
    envelopeD n (58 / 100) ≤ 58 / 100 * (2 / 11883 ^ 2) / (11883 - 2) := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  unfold envelopeD
  rw [tA_eq]
  gcongr
  all_goals linarith

theorem envelopeV_leN (hn : 11883 ≤ n) :
    envelopeV n (58 / 100) ≤ 8 * (2 / 11883 ^ 2) / 11883 * (58 / 100) / (11883 - 2) := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  unfold envelopeV
  rw [tA_eq]
  gcongr
  all_goals linarith

theorem envelopeGap_geN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) :
    17 / (100 * 12224) / 2 - 2 * (2 / 11883 ^ 2) * (58 / 100 * 160 ^ 2 / (11883 - 2)) ≤
      envelopeGap n (58 / 100) 160 (17 / (100 * n)) := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : (n : ℝ) ≤ 12224 := by exact_mod_cast hn2
  unfold envelopeGap
  rw [tA_eq]
  have h1 : 17 / (100 * 12224) / 2 ≤ 17 / (100 * (n : ℝ)) / 2 := by
    gcongr
  have h2 : 2 * (2 / (n : ℝ) ^ 2) * (58 / 100 * 160 ^ 2 / ((n : ℝ) - 2)) ≤
      2 * (2 / 11883 ^ 2) * (58 / 100 * 160 ^ 2 / (11883 - 2)) := by
    have h2p : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    gcongr
    all_goals first | linarith | exact div_nonneg (by positivity) h2p.le
  linarith

theorem inverseRadius8_leN (hn : 11883 ≤ n) :
    inverseRadius8 (n - 1) ≤ ((11883 - 3) * (11883 - 5) * (11883 - 7) * (11883 - 9) : ℝ)⁻¹ := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  unfold inverseRadius8
  rw [hd]
  apply inv_anti₀ (by norm_num)
  have e : ((n : ℝ) - 1 - 2) * ((n : ℝ) - 1 - 4) * ((n : ℝ) - 1 - 6) * ((n : ℝ) - 1 - 8) =
      ((n : ℝ) - 3) * ((n : ℝ) - 5) * ((n : ℝ) - 7) * ((n : ℝ) - 9) := by ring
  rw [e]
  have h3 : (0 : ℝ) ≤ (n : ℝ) - 3 := by linarith
  have h5 : (0 : ℝ) ≤ (n : ℝ) - 5 := by linarith
  have h7 : (0 : ℝ) ≤ (n : ℝ) - 7 := by linarith
  gcongr
  all_goals first | linarith | positivity | exact mul_nonneg h3 h5 |
    exact mul_nonneg (mul_nonneg h3 h5) h7

theorem envN_D {C : ℝ} (hn : 11883 ≤ n) (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (envN n C).D ∧ (envN n C).D ≤ 443 / 10 ^ 14 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := envelopeD_leN hn
  have hD0 : 0 ≤ envelopeD n (58 / 100) := by
    unfold envelopeD
    rw [tA_eq]
    have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    positivity
  change 0 ≤ envelopeD n (58 / 100) * (C + C) ∧ envelopeD n (58 / 100) * (C + C) ≤ _
  refine ⟨mul_nonneg hD0 (by linarith), ?_⟩
  calc envelopeD n (58 / 100) * (C + C) ≤ (58 / 100 * (2 / 11883 ^ 2) / (11883 - 2)) *
        (32 / 10 + 32 / 10) :=
          mul_le_mul hD (by linarith) (by linarith) (by norm_num)
    _ ≤ _ := by norm_num

theorem envN_V {C : ℝ} (hn : 11883 ≤ n) (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (envN n C).V ∧ (envN n C).V ≤ 1490 / 10 ^ 18 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hV := envelopeV_leN hn
  have hV0 : 0 ≤ envelopeV n (58 / 100) := by
    unfold envelopeV
    rw [tA_eq]
    have : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    positivity
  obtain ⟨hD0, hD⟩ := envN_D hn hC hC4
  change 0 ≤ envelopeV n (58 / 100) * C + (envelopeD n (58 / 100) * (C + C)) ^ 2 ∧
    envelopeV n (58 / 100) * C + (envelopeD n (58 / 100) * (C + C)) ^ 2 ≤ _
  change 0 ≤ envelopeD n (58 / 100) * (C + C) at hD0
  change envelopeD n (58 / 100) * (C + C) ≤ 443 / 10 ^ 14 at hD
  refine ⟨add_nonneg (mul_nonneg hV0 hC) (sq_nonneg _), ?_⟩
  calc envelopeV n (58 / 100) * C + (envelopeD n (58 / 100) * (C + C)) ^ 2 ≤
        (8 * (2 / 11883 ^ 2) / 11883 * (58 / 100) / (11883 - 2)) * (32 / 10) +
          (443 / 10 ^ 14) ^ 2 :=
          add_le_add (mul_le_mul hV hC4 hC (by norm_num)) (pow_le_pow_left₀ hD0 hD 2)
    _ ≤ _ := by norm_num

theorem envN_P {C : ℝ} (hn : 11883 ≤ n) (hn2 : n ≤ 12224) (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) :
    0 ≤ (envN n C).P ∧ (envN n C).P ≤ 368 / 10 ^ 17 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := envelopeGap_geN hn hn2
  have hg0 : (0 : ℝ) < 17 / (100 * 12224) / 2 -
      2 * (2 / 11883 ^ 2) * (58 / 100 * 160 ^ 2 / (11883 - 2)) := by norm_num
  have hI := inverseRadius8_leN hn
  have hI0 : 0 ≤ inverseRadius8 (n - 1) := by
    unfold inverseRadius8
    have hd : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hd]
    apply inv_nonneg.mpr
    have h1 : (0 : ℝ) ≤ (n : ℝ) - 1 - 8 := by linarith
    have h2 : (0 : ℝ) ≤ (n : ℝ) - 1 - 6 := by linarith
    have h3 : (0 : ℝ) ≤ (n : ℝ) - 1 - 4 := by linarith
    have h4 : (0 : ℝ) ≤ (n : ℝ) - 1 - 2 := by linarith
    positivity
  have hc4 := BstLean.Part162.cLS_nonneg 4
  have hT : 8 * tA n / n * (58 / 100) ≤ 8 * (2 / 11883 ^ 2) / 11883 * (58 / 100) := by
    rw [tA_eq]
    gcongr
  have hT0 : 0 ≤ 8 * tA n / n * (58 / 100) := by rw [tA_eq]; positivity
  change 0 ≤ envelopeP n (58 / 100) 160 (17 / (100 * n)) * C ^ 4 ∧
    envelopeP n (58 / 100) 160 (17 / (100 * n)) * C ^ 4 ≤ _
  unfold envelopeP
  constructor
  · exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) hI0) (by positivity))
      (by positivity)
  · calc
      _ ≤ (28115 / 10000 : ℝ) ^ 8 * (8 * (2 / 11883 ^ 2) / 11883 * (58 / 100)) ^ 4 *
          ((11883 - 3) * (11883 - 5) * (11883 - 7) * (11883 - 9) : ℝ)⁻¹ /
          (17 / (100 * 12224) / 2 -
            2 * (2 / 11883 ^ 2) * (58 / 100 * 160 ^ 2 / (11883 - 2))) ^ 8 * (32 / 10) ^ 4 := by
        gcongr <;> first | exact cLS4_le | assumption | positivity | norm_num
      _ ≤ _ := by norm_num

structure CoefficientBoundsN (n : ℕ) (C : ℝ) : Prop where
  f0 : (envN n C).f0 n 160 ≤ 430 / 10 ^ 11
  f1 : (envN n C).f1 n 160 ≤ 142 / 10 ^ 11
  f2 : (envN n C).f2 ≤ 336 / 10 ^ 12
  w0 : (envN n C).w0 n 160 ≤ 1740 / 10 ^ 14
  w1 : (envN n C).w1 n 160 ≤ 1230 / 10 ^ 14
  w2 : (envN n C).w2 n 160 ≤ 444 / 10 ^ 14

theorem coefficient_boundsN {C : ℝ} (hn : 11883 ≤ n) (hn2 : n ≤ 12224)
    (hC : 0 ≤ C) (hC4 : C ≤ 32 / 10) : CoefficientBoundsN n C := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : (n : ℝ) ≤ 12224 := by exact_mod_cast hn2
  have hx0 : (0 : ℝ) < n := by linarith
  let d := envN n C
  have hd : 0 ≤ d.D ∧ d.D ≤ 443 / 10 ^ 14 := envN_D hn hC hC4
  have hh : 0 ≤ d.H ∧ d.H ≤ 443 / 10 ^ 14 := hd
  have hv : 0 ≤ d.V ∧ d.V ≤ 1490 / 10 ^ 18 := envN_V hn hC hC4
  have hp : 0 ≤ d.P ∧ d.P ≤ 368 / 10 ^ 17 := envN_P hn hn2 hC hC4
  obtain ⟨hφ0L, hφ0, hφ1L, hφ1⟩ := BstLean.Part154.phiG_bounds_NumA
  have hφ00 : 0 ≤ phiG 0 := by linarith
  have hφ10 : 0 ≤ phiG 1 := by linarith
  have hsm : (3729 / 1000000 : ℝ) ≤ √(17 / (100 * n) : ℝ) := by
    apply le_sqrt_of_sq_le
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hsm0 : 0 ≤ √(17 / (100 * n) : ℝ) := sqrt_nonneg _
  have h2L : (14142 / 10000 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hD : √d.D ≤ 2105 / 10 ^ 9 :=
    (sqrt_le_sqrt hd.2).trans (sqrt_le_iff.mpr (by norm_num))
  have hV : √d.V ≤ 3861 / 10 ^ 11 :=
    (sqrt_le_sqrt hv.2).trans (sqrt_le_iff.mpr (by norm_num))
  have ht : √(tA n) * 160 ≤ 1905 / 100000 := by
    have hs : √(tA n) ≤ 119013 / 10 ^ 9 := by
      apply sqrt_le_iff.mpr
      refine ⟨by norm_num, ?_⟩
      rw [tA_eq, div_le_iff₀ (pow_pos hx0 2)]
      nlinarith
    linarith
  have hS : √(26 / (10 * n) : ℝ) ≤ 1480 / 100000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hG : tA n * (160 : ℝ) ^ 2 + 26 / (10 * n) ≤ 5815 / 10000000 := by
    rw [tA_eq]
    have e1 : 2 / (n : ℝ) ^ 2 * 160 ^ 2 ≤ 2 / 11883 ^ 2 * 160 ^ 2 := by gcongr
    have e2 : 26 / (10 * (n : ℝ)) ≤ 26 / (10 * 11883) := by gcongr
    have e3 : (2 / 11883 ^ 2 * 160 ^ 2 + 26 / (10 * 11883) : ℝ) ≤ 5815 / 10000000 := by
      norm_num
    linarith
  have hG0 : 0 ≤ tA n * (160 : ℝ) ^ 2 + 26 / (10 * n) := by rw [tA_eq]; positivity
  have ht0 : 0 ≤ √(tA n) * 160 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RAData.f0
    change AF0 (√(17 / (100 * n) : ℝ)) (tA n * 160 ^ 2 + 26 / (10 * n)) d.H d.V d.P ≤ _
    unfold AF0
    calc
      _ ≤ (39895 / 100000 : ℝ) / (2 * (3729 / 1000000)) * (443 / 10 ^ 14) + 1 / 2 * ((39895 / 100000) / ((14142 / 10000) * (3729 / 1000000) ^ 3) * (1490 / 10 ^ 18)) + (368 / 10 ^ 17) * (3 / 2 * (39895 / 100000) / (3729 / 1000000) * (5815 / 10000000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f1
    change AF1 (√(17 / (100 * n) : ℝ)) d.D d.V d.P (√(tA n) * 160) ≤ _
    unfold AF1
    calc
      _ ≤ 1 / 2 * (2 * (24198 / 100000 : ℝ) / (3729 / 1000000) ^ 2 * ((2105 / 10 ^ 9) * (3861 / 10 ^ 11))) + (368 / 10 ^ 17) * (2 * (2 * (14143 / 10000) * (1905 / 100000))) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.f2
    change AF2 (√(17 / (100 * n) : ℝ)) d.D ≤ _
    unfold AF2
    calc
      _ ≤ 1 / 2 * ((14143 / 10000 : ℝ) * (39895 / 100000) / (3729 / 1000000) * (443 / 10 ^ 14)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hd.1
          | positivity
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w0
    change AW0 (√(17 / (100 * n) : ℝ)) (tA n * 160 ^ 2 + 26 / (10 * n)) d.H d.V d.P ≤ _
    unfold AW0
    calc
      _ ≤ (443 / 10 ^ 14 : ℝ) + (24198 / 100000) / (2 * (3729 / 1000000) ^ 2) * (1490 / 10 ^ 18) + (368 / 10 ^ 17) * (4 * (5815 / 10000000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w1
    change AW1 (√(17 / (100 * n) : ℝ)) (√(26 / (10 * n) : ℝ)) d.D d.V d.P (√(tA n) * 160) ≤ _
    unfold AW1
    calc
      _ ≤ (14143 / 10000 : ℝ) * (39895 / 100000) / (3729 / 1000000) * ((2105 / 10 ^ 9) * (3861 / 10 ^ 11)) + (368 / 10 ^ 17) * (4 * (14143 / 10000) * (1905 / 100000) * (1480 / 100000)) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hh.2
          | exact hv.2
          | exact hp.2
          | exact hd.1
          | exact hh.1
          | exact hv.1
          | exact hp.1
          | positivity
        all_goals positivity
      _ ≤ _ := by norm_num
  · unfold RAData.w2
    change AW2 d.D d.P (√(tA n) * 160) ≤ _
    unfold AW2
    calc
      _ ≤ (443 / 10 ^ 14 : ℝ) + (368 / 10 ^ 17) * (28 * (1905 / 100000) ^ 2) := by
        gcongr <;> first
          | assumption
          | exact hd.2
          | exact hp.2
          | exact hd.1
          | exact hp.1
          | positivity
        all_goals positivity
      _ ≤ _ := by norm_num

theorem coefficient_nonnegN {C : ℝ} (hn : 11883 ≤ n) (hn2 : n ≤ 12224) (hC : 0 ≤ C)
    (hC4 : C ≤ 32 / 10) :
    0 ≤ (envN n C).f0 n 160 ∧ 0 ≤ (envN n C).f1 n 160 ∧ 0 ≤ (envN n C).f2 ∧
    0 ≤ (envN n C).w0 n 160 ∧ 0 ≤ (envN n C).w1 n 160 ∧ 0 ≤ (envN n C).w2 n 160 := by
  let d := envN n C
  have hD : 0 ≤ d.D := (envN_D hn hC hC4).1
  have hH : 0 ≤ d.H := hD
  have hV : 0 ≤ d.V := (envN_V hn hC hC4).1
  have hP : 0 ≤ d.P := (envN_P hn hn2 hC hC4).1
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hG : 0 ≤ tA n * (160 : ℝ) ^ 2 + d.Smax := by
    change 0 ≤ tA n * (160 : ℝ) ^ 2 + 26 / (10 * n)
    rw [tA_eq]; positivity
  change 0 ≤ d.f0 n 160 ∧ 0 ≤ d.f1 n 160 ∧ 0 ≤ d.f2 ∧
    0 ≤ d.w0 n 160 ∧ 0 ≤ d.w1 n 160 ∧ 0 ≤ d.w2 n 160
  dsimp only [RAData.f0, RAData.f1, RAData.f2, RAData.w0, RAData.w1, RAData.w2]
  unfold AF0 AF1 AF2 AW0 AW1 AW2
  exact ⟨by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

theorem location_correctionN (hn : 11883 ≤ n) :
    locationR16 n ≤ 2 * (228 / 100 : ℝ) / 11883 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (715 : ℝ) ^ (1 / 8 : ℝ) ≤ 228 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 715)
      (by norm_num : (8 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold locationR16
  gcongr

theorem energy_correctionN (hn : 11883 ≤ n) :
    energyR16 n ≤ 2 * (370 / 100 : ℝ) / 11883 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (1216070380 : ℝ) ^ (1 / 16 : ℝ) ≤ 370 / 100 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 1216070380)
      (by norm_num : (16 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    rw [hp]
    norm_num
  unfold energyR16
  gcongr

theorem bias_pricesN {C : ℝ} (hn : 11883 ≤ n) (hn2 : n ≤ 12224) (hCp : 0 < C)
    (hC4 : C ≤ 32 / 10) :
    (completeRAData (envN n C) n 160).locationBound n 160 ≤ (940 / 100000 : ℝ) ^ 16 ∧
    (completeRAData (envN n C) n 160).energyBound n 160 ≤ (626 / 100000 : ℝ) ^ 16 := by
  have hC := hCp.le
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : (n : ℝ) ≤ 12224 := by exact_mod_cast hn2
  have hx0 : (0 : ℝ) < n := by linarith
  let d := envN n C
  have F := coefficient_boundsN hn hn2 hC hC4
  obtain ⟨hf0, hf1, hf2, hw0, hw1, hw2⟩ := coefficient_nonnegN hn hn2 hC hC4
  have hDp : 0 < d.D := by
    change 0 < envelopeD n (58 / 100) * (C + C)
    unfold envelopeD
    rw [tA_eq]
    have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    have hCC : 0 < C + C := by linarith
    exact mul_pos (div_pos (mul_pos (by norm_num) (div_pos (by norm_num) (pow_pos hx0 2))) h2) hCC
  have hV0 : 0 ≤ d.V := (envN_V hn hC hC4).1
  have hP0 : 0 ≤ d.P := (envN_P hn hn2 hC hC4).1
  have hsm : 0 < √(17 / (100 * n) : ℝ) := Real.sqrt_pos.mpr (div_pos (by norm_num) (by linarith))
  have hG0 : 0 ≤ tA n * (160 : ℝ) ^ 2 + 26 / (10 * n) := by rw [tA_eq]; positivity
  have hf0p : 0 < d.f0 n 160 := by
    change 0 < AF0 (√(17 / (100 * n) : ℝ)) (tA n * 160 ^ 2 + 26 / (10 * n)) d.D d.V d.P
    unfold AF0
    have t1 : 0 < phiG 0 / (2 * √(17 / (100 * n) : ℝ)) * d.D :=
      mul_pos (div_pos (phiG_pos 0) (by linarith)) hDp
    have t2 : 0 ≤ 1 / 2 * (phiG 0 / (√2 * √(17 / (100 * n) : ℝ) ^ 3) * d.V) :=
      mul_nonneg (by norm_num) (mul_nonneg (div_nonneg (phiG_pos 0).le (by positivity)) hV0)
    have t3 : 0 ≤ d.P * (3 / 2 * phiG 0 / √(17 / (100 * n) : ℝ) *
        (tA n * 160 ^ 2 + 26 / (10 * n))) :=
      mul_nonneg hP0 (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (phiG_pos 0).le)
        hsm.le) hG0)
    linarith
  have hw0p : 0 < d.w0 n 160 := by
    change 0 < AW0 (√(17 / (100 * n) : ℝ)) (tA n * 160 ^ 2 + 26 / (10 * n)) d.D d.V d.P
    unfold AW0
    have t2 : 0 ≤ phiG 1 / (2 * √(17 / (100 * n) : ℝ) ^ 2) * d.V :=
      mul_nonneg (div_nonneg (phiG_pos 1).le (by positivity)) hV0
    have t3 : 0 ≤ d.P * (4 * (tA n * 160 ^ 2 + 26 / (10 * n))) :=
      mul_nonneg hP0 (by positivity)
    linarith
  have hπ : √(π / 2) ≤ (126 / 100 : ℝ) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have := pi_lt_d4
    linarith
  have htF : radiusPolynomialRoot16 (d.f0 n 160) (d.f1 n 160) d.f2 ≤
      (430 / 10 ^ 11 : ℝ) + 14 / 5 * (142 / 10 ^ 11) + 14 * (336 / 10 ^ 12) :=
    (BstLean.Part276.radius_polynomial_root_sharp hf0p hf1 hf2).trans (by
      linarith [F.f0, F.f1, F.f2])
  have htW : radiusPolynomialRoot16 (d.w0 n 160) (d.w1 n 160) (d.w2 n 160) ≤
      (1740 / 10 ^ 14 : ℝ) + 14 / 5 * (1230 / 10 ^ 14) + 14 * (444 / 10 ^ 14) :=
    (BstLean.Part276.radius_polynomial_root_sharp hw0p hw1 hw2).trans (by
      linarith [F.w0, F.w1, F.w2])
  have hcol : collectedSecond (d.f0 n 160) (d.f1 n 160) d.f2 ≤
      (430 / 10 ^ 11 : ℝ) ^ 2 + 2 * (430 / 10 ^ 11) * (142 / 10 ^ 11) * (126 / 100) +
      2 * ((142 / 10 ^ 11) ^ 2 + 2 * (430 / 10 ^ 11) * (336 / 10 ^ 12)) +
      6 * (142 / 10 ^ 11) * (336 / 10 ^ 12) * (126 / 100) + 8 * (336 / 10 ^ 12) ^ 2 := by
    unfold collectedSecond
    gcongr <;> first | exact F.f0 | exact F.f1 | exact F.f2 | exact hπ | assumption
  have hcol0 : 0 ≤ collectedSecond (d.f0 n 160) (d.f1 n 160) d.f2 := by
    unfold collectedSecond
    positivity
  have hrF0 : 0 ≤ locationR16 n := by unfold locationR16; positivity
  have hrW0 : 0 ≤ energyR16 n := by unfold energyR16; positivity
  have htF0 := radiusPolynomialRoot16_nonneg (d.f0 n 160) (d.f1 n 160) d.f2
  have htW0 := radiusPolynomialRoot16_nonneg (d.w0 n 160) (d.w1 n 160) (d.w2 n 160)
  have hmE : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hm : (mA n : ℝ) ≤ 12224 ^ 2 := by rw [hmE]; gcongr
  have hm0 : 0 ≤ (mA n : ℝ) := by positivity
  constructor
  · change (n : ℝ) ^ 8 * (mA n : ℝ) ^ 8 *
      (collectedSecond (d.f0 n 160) (d.f1 n 160) d.f2 + locationR16 n *
        radiusPolynomialRoot16 (d.f0 n 160) (d.f1 n 160) d.f2 ^ 2) ^ 8 ≤ _
    calc
      _ ≤ (12224 : ℝ) ^ 8 * (12224 ^ 2 : ℝ) ^ 8 *
        (((430 / 10 ^ 11 : ℝ) ^ 2 + 2 * (430 / 10 ^ 11) * (142 / 10 ^ 11) * (126 / 100) +
          2 * ((142 / 10 ^ 11) ^ 2 + 2 * (430 / 10 ^ 11) * (336 / 10 ^ 12)) +
          6 * (142 / 10 ^ 11) * (336 / 10 ^ 12) * (126 / 100) + 8 * (336 / 10 ^ 12) ^ 2) +
          (2 * (228 / 100 : ℝ) / 11883) *
          ((430 / 10 ^ 11 : ℝ) + 14 / 5 * (142 / 10 ^ 11) + 14 * (336 / 10 ^ 12)) ^ 2) ^ 8 := by
        gcongr <;> first
          | exact hcol
          | exact location_correctionN hn
          | exact htF
          | exact hm
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num
  · change (mA n : ℝ) ^ 16 *
      (d.w0 n 160 + d.w1 n 160 * √(π / 2) + 2 * d.w2 n 160 +
        energyR16 n * radiusPolynomialRoot16 (d.w0 n 160) (d.w1 n 160)
          (d.w2 n 160)) ^ 16 ≤ _
    calc
      _ ≤ (12224 ^ 2 : ℝ) ^ 16 *
        ((1740 / 10 ^ 14 : ℝ) + (1230 / 10 ^ 14) * (126 / 100) + 2 * (444 / 10 ^ 14) +
          (2 * (370 / 100 : ℝ) / 11883) *
          ((1740 / 10 ^ 14 : ℝ) + 14 / 5 * (1230 / 10 ^ 14) + 14 * (444 / 10 ^ 14))) ^ 16 := by
        gcongr <;> first
          | exact F.w0
          | exact F.w1
          | exact F.w2
          | exact hπ
          | exact energy_correctionN hn
          | exact htW
          | exact hm
          | exact radiusPolynomialRoot16_nonneg _ _ _
          | assumption
      _ ≤ _ := by norm_num

/-! ### The two fluctuation prices -/

noncomputable def sharpHN : ℝ := 5275 / 10000

noncomputable def pricesN (n : ℕ) : Fin 4 → ℝ :=
  completeMomentPrices n (58 / 100) 160 (17 / (100 * n)) (26 / (10 * n))
    (statisticsConstant (paperBound256 n)) √((42 / 10 : ℝ) / n) sharpHN

theorem lambda_productN (hn : 11883 ≤ n) :
    (n : ℝ) * (tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) ≤
      2 * 160 ^ 2 / (11883 * (11883 - 2)) := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have h2' : (n : ℝ) - 2 ≠ 0 := h2.ne'
  have hx0' : (n : ℝ) ≠ 0 := hx0.ne'
  have e : (n : ℝ) * (tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) =
      2 * 160 ^ 2 / ((n : ℝ) * ((n : ℝ) - 2)) := by
    rw [tA_eq]
    first
      | (field_simp; ring)
      | field_simp
  rw [e]
  gcongr
  all_goals linarith

theorem location_fluctuation_priceN (hn : 11883 ≤ n) :
    (k24 * (√(n : ℝ) * √(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) / 2) * √sharpHN) ^ 24 ≤
      (141 / 10 ^ 6 : ℝ) * fourA 0 ^ 24 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hl0 : 0 ≤ tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2)) := by
    have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
    rw [tA_eq]; exact mul_nonneg (by positivity) (div_nonneg (by positivity) h2.le)
  have hprod : √(n : ℝ) * √(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) ≤
      √(2 * 160 ^ 2 / (11883 * (11883 - 2))) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
    exact sqrt_le_sqrt (lambda_productN hn)
  have hk : 0 ≤ k24 := by unfold k24; positivity
  calc
    _ ≤ (k24 * (√(2 * 160 ^ 2 / (11883 * (11883 - 2)) : ℝ) / 2) * √sharpHN) ^ 24 :=
      pow_le_pow_left₀ (mul_nonneg (mul_nonneg hk (by positivity)) (sqrt_nonneg _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hprod (by norm_num)) hk) (sqrt_nonneg _)) 24
    _ = k24 ^ 24 * ((2 * 160 ^ 2 / (11883 * (11883 - 2)) : ℝ)) ^ 12 / 2 ^ 24 *
          sharpHN ^ 12 := by
      have hA : √(2 * 160 ^ 2 / (11883 * (11883 - 2)) : ℝ) ^ 24 =
          ((2 * 160 ^ 2 / (11883 * (11883 - 2)) : ℝ)) ^ 12 := by
        rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num)]
      have hH : √sharpHN ^ 24 = sharpHN ^ 12 := by
        rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul, sq_sqrt (by norm_num [sharpHN])]
      have e : (k24 * (√(2 * 160 ^ 2 / (11883 * (11883 - 2)) : ℝ) / 2) * √sharpHN) ^ 24 =
          k24 ^ 24 * √(2 * 160 ^ 2 / (11883 * (11883 - 2)) : ℝ) ^ 24 / 2 ^ 24 *
            √sharpHN ^ 24 := by ring
      rw [e, hA, hH]
    _ ≤ _ := by
      rw [k24_pow]
      norm_num [fourA, sharpHN, Nat.factorial]

theorem energy_coefficientN (n : ℕ) :
    energyCoefficient18 n ≤ (2 * n * (21165 / 10000 : ℝ) + (269 / 10) * 8) := by
  have h9 : (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 21165 / 10000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((9 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  have h18 : (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) ≤ 8 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (18 : ℕ) ≠ 0) (by norm_num)
    have hp := rpow_inv_natCast_pow
      (by positivity : (0 : ℝ) ≤ 2 * ((18 : ℕ).factorial : ℝ))
      (by norm_num : (18 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hp ⊢
    simp only [one_div] at hp ⊢
    rw [hp]
    norm_num [Nat.factorial]
  unfold energyCoefficient18 BstLean.Part202.beta
  gcongr

theorem energy_fluctuation_priceN (hn : 11883 ≤ n) :
    (√(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) *
      energyCoefficient18 n) ^ 18 * sharpHN ^ 12 * (58 / 100 : ℝ) ^ 6 ≤
        (416 / 10 ^ 6 : ℝ) * fourA 2 ^ 18 := by
  have hx : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h2 : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  set c : ℝ := 4233 / 1000 + 2152 / 10 / 11883 with hc
  have hE : energyCoefficient18 n ≤ c * n := by
    refine (energy_coefficientN n).trans ?_
    have : (2152 / 10 : ℝ) ≤ 2152 / 10 / 11883 * n := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      nlinarith
    rw [hc]
    nlinarith
  have hE0 := energyCoefficient18_nonneg n
  have hl0 : 0 ≤ tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2)) := by
    rw [tA_eq]; exact mul_nonneg (by positivity) (div_nonneg (by positivity) h2.le)
  have hs0 : 0 ≤ √(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) := by
    positivity
  have hprod : (√(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) *
      (c * n)) ^ 2 ≤ 2 * 160 ^ 2 * (42 / 10) * c ^ 2 / (11883 * (11883 - 2)) := by
    have e1 : (√(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) *
        (c * n)) ^ 2 = √(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) ^ 2 *
          √((42 / 10 : ℝ) / n) ^ 2 * (c * n) ^ 2 := by ring
    rw [e1, sq_sqrt hl0, sq_sqrt (div_nonneg (by norm_num) hx0.le)]
    have h2' : (n : ℝ) - 2 ≠ 0 := h2.ne'
    have hx0' : (n : ℝ) ≠ 0 := hx0.ne'
    have e : tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2)) * (42 / 10 / n) * (c * n) ^ 2 =
        2 * 160 ^ 2 * (42 / 10) * c ^ 2 / ((n : ℝ) * ((n : ℝ) - 2)) := by
      rw [tA_eq]
      first
        | (field_simp; ring)
        | field_simp
    rw [e]
    gcongr
    all_goals linarith
  have hX : (√(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) *
      (c * n)) ^ 18 ≤ (2 * 160 ^ 2 * (42 / 10) * c ^ 2 / (11883 * (11883 - 2))) ^ 9 := by
    calc _ = ((√(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) *
          (c * n)) ^ 2) ^ 9 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hprod 9
  have hH0 : (0 : ℝ) ≤ sharpHN ^ 12 := by positivity
  calc
    _ ≤ (√(tA n * ((160 : ℝ) ^ 2 / ((n : ℝ) - 2))) * √((42 / 10 : ℝ) / n) *
        (c * n)) ^ 18 * sharpHN ^ 12 * (58 / 100 : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hs0 hE0) (mul_le_mul_of_nonneg_left hE hs0) 18) hH0)
        (by positivity)
    _ ≤ (2 * 160 ^ 2 * (42 / 10) * c ^ 2 / (11883 * (11883 - 2))) ^ 9 * sharpHN ^ 12 *
        (58 / 100 : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hH0) (by positivity)
    _ ≤ _ := by
      rw [hc]
      norm_num [fourA, sharpHN]

/-- The four Markov prices for every `n` in 11883–12224. -/
theorem four_priceN (hn : 11883 ≤ n) (hn2 : n ≤ 12224) :
    pricesN n 0 / fourA 0 ^ 24 + pricesN n 1 / fourA 1 ^ 16 +
      pricesN n 2 / fourA 2 ^ 18 + pricesN n 3 / fourA 3 ^ 16 ≤ 717 / 10 ^ 6 := by
  have h0 : pricesN n 0 ≤ (141 / 10 ^ 6 : ℝ) * fourA 0 ^ 24 :=
    location_fluctuation_priceN hn
  have h2 : pricesN n 2 ≤ (416 / 10 ^ 6 : ℝ) * fourA 2 ^ 18 :=
    energy_fluctuation_priceN hn
  have hb := bias_pricesN hn hn2 (statistics_constant_posN hn hn2) (statistics_constantN hn hn2)
  have h1 : pricesN n 1 ≤ (940 / 100000 : ℝ) ^ 16 := hb.1
  have h3 : pricesN n 3 ≤ (626 / 100000 : ℝ) ^ 16 := hb.2
  have hd0 : pricesN n 0 / fourA 0 ^ 24 ≤ (141 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourA])).mpr
    exact h0
  have hd2 : pricesN n 2 / fourA 2 ^ 18 ≤ (416 / 10 ^ 6 : ℝ) := by
    apply (div_le_iff₀ (by norm_num [fourA])).mpr
    exact h2
  have hd1 : pricesN n 1 / fourA 1 ^ 16 ≤ (137 / 10 ^ 6 : ℝ) :=
    (div_le_div_of_nonneg_right h1 (by norm_num [fourA])).trans (by norm_num [fourA])
  have hd3 : pricesN n 3 / fourA 3 ^ 16 ≤ (23 / 10 ^ 6 : ℝ) :=
    (div_le_div_of_nonneg_right h3 (by norm_num [fourA])).trans (by norm_num [fourA])
  linarith

end BstLean.Part280
