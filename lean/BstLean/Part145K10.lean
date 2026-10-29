import BstLean.Part145K6
import BstLean.Part145K9

/-!
# Part 145 (K10): the numbers of `Part145K9` at the thresholds `n ≥ 4096` and `n ≥ 4489`

At `mA n = n²`:
* `n ≥ 4096 = 64²`: `kX n ≤ 0.89719`, `rR0x ≤ 3.3076/n`, `cAdltx ≤ 1.9054/n`
  (`kX_leR`, `rR0x_leR`, `cAdltx_leR`; Part 145 before: `K4 n ≤ 3.4658`, `rR0 ≤ 8.4451/n`,
  `cAdlt ≤ 7.1403/n`);
* `n ≥ 4489 = 67²`: `kX n ≤ 0.89516`, `rR0x ≤ 3.2968/n`, `cAdltx ≤ 1.8969/n`
  (`kX_leS`, `rR0x_leS`, `cAdltx_leS`).
`rR1`, `rR1'`, `rR2` do not change (`rR2_leR`, `rR2_leS` of Part 145 stay valid).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part142
open BstLean.Part143

open AgD AgS AgC AgK

/-! ## The threshold `n ≥ 4096 = 64²` -/

section focusR

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `kX n ≤ 0.89719` for `n ≥ 4096` (`K4 n ≥ 3.4641`). -/
theorem kX_leR : kX n ≤ 89719 / 100000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (64 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / √(n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hz0 : 0 < z := by rw [hz]; positivity
  have hz1 : z ≤ 1 / 64 := by rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyz : y = z * z := by
    rw [hy, hz, div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hny : (n : ℝ) * y = 1 := by rw [hy]; field_simp
  have h2 := sqrt2_le
  have h20 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hK0 := K4_nonneg n
  have hK : K4 n ≤ 17329 / 5000 := by
    unfold K4
    refine sqrt_le_of_sq (by norm_num) ?_
    have : 48 / (n : ℝ) ≤ 48 / 4096 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    norm_num at this ⊢
    linarith
  have hQ0 := qCos_nonneg n
  have hQ : qCos n ≤ 25759 / 625 * y ^ 2 := by
    have e : qCos n = √(1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3) * y ^ 2 := by
      have e1 : 1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3 =
          1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3 := by rw [hy]; ring
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
  have hKy : K4 n * y ≤ 17329 / 5000 * y := mul_le_mul_of_nonneg_right hK hy0.le
  have hKy0 : 0 ≤ K4 n * y := by positivity
  have hsQ : √2 * qCos n ≤ 141422 / 100000 * (25759 / 625 * y ^ 2) :=
    mul_le_mul h2 hQ hQ0 (by norm_num)
  have hsQ0 : 0 ≤ √2 * qCos n := by positivity
  have hsK : √2 * (K4 n * y) ≤ 141422 / 100000 * (17329 / 5000 * y) :=
    mul_le_mul h2 hKy hKy0 (by norm_num)
  have hsK0 : 0 ≤ √2 * (K4 n * y) := by positivity
  have hy3 : y ^ 3 = (y * z) ^ 2 := by rw [hyz]; ring
  have t4 : √(√2 * (K4 n * y) * (√2 * qCos n)) ≤ 16903 / 1000 * (y * z) := by
    refine sqrt_le_of_sq (by positivity) ?_
    have := mul_le_mul hsK hsQ hsQ0 (by positivity)
    refine this.trans ?_
    have e : 141422 / 100000 * (17329 / 5000 * y) * (141422 / 100000 * (25759 / 625 * y ^ 2)) =
        141422 / 100000 * (17329 / 5000) * (141422 / 100000) * (25759 / 625) * y ^ 3 := by ring
    rw [e, mul_pow, ← hy3]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hn2 : (n : ℝ) * (K4 n / (2 * (n : ℝ))) = K4 n / 2 := by field_simp
  have e : kX n = K4 n / 4 + (n : ℝ) / 16 * √(√2 * (K4 n * y) * (√2 * qCos n)) +
      (n : ℝ) * (√2 * qCos n) := by
    unfold kX cDx dX
    rw [eK]
    linear_combination (1 / 2) * hn2
  have b1 : (n : ℝ) / 16 * √(√2 * (K4 n * y) * (√2 * qCos n)) ≤ 16903 / 1000 / 16 * z := by
    calc (n : ℝ) / 16 * √(√2 * (K4 n * y) * (√2 * qCos n))
        ≤ (n : ℝ) / 16 * (16903 / 1000 * (y * z)) := mul_le_mul_of_nonneg_left t4 (by positivity)
      _ = 16903 / 1000 / 16 * z * ((n : ℝ) * y) := by ring
      _ = 16903 / 1000 / 16 * z := by rw [hny]; ring
  have b2 : (n : ℝ) * (√2 * qCos n) ≤ 141422 / 100000 * (25759 / 625) * y := by
    calc (n : ℝ) * (√2 * qCos n)
        ≤ (n : ℝ) * (141422 / 100000 * (25759 / 625 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hsQ hx0.le
      _ = 141422 / 100000 * (25759 / 625) * y * ((n : ℝ) * y) := by ring
      _ = 141422 / 100000 * (25759 / 625) * y := by rw [hny]; ring
  rw [e]
  linarith

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` at `n ≥ 4096`. -/
lemma yzrKR : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 4096 ∧ z ≤ 1 / 64 ∧ r ≤ 707107 / 1000000 * z := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096KR hn)
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (64 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, ?_, ?_, hr1⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma SS_leKR : SS (mA n) ≤ 20001 / 10000 := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have h2' : (16777216 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 5 / (n : ℝ) ^ 2 ≤ 5 / 16777216 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have hpos : (0 : ℝ) ≤ 1 + 5 / (mA n : ℝ) := by positivity
  have e : SS (mA n) = 2 * (1 + 5 / (mA n : ℝ)) := by
    unfold SS sS
    calc √(1 + 5 / (mA n : ℝ)) * (2 * √(1 + 5 / (mA n : ℝ)))
        = 2 * (√(1 + 5 / (mA n : ℝ)) * √(1 + 5 / (mA n : ℝ))) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hpos]
  rw [e, mA_eqR]
  linarith

/-- `rR0x ≤ 3.3076/n` for `n ≥ 4096`. -/
theorem rR0x_leR : rR0x n (mA n) ≤ 8269 / 2500 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrKR hn
  have hn4 := n4096KR hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le'
  have hK4 := kX_leR hn
  have hK40 := kX_nonneg n
  have a1 := nc0_le hn4
  have a2 := SS_leKR hn
  have a3 := DS_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_leKR hn
  have a6 := q3z_leKR hn
  have n1 := nc0_nn (mA n)
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a3 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 64) := mul_le_mul_of_nonneg_left hz1 hy0.le
  have hr2 : r ≤ 707107 / 1000000 * (1 / 64) := by linarith
  have hyr : y * r ≤ y * (707107 / 1000000 * (1 / 64)) :=
    mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [rR0x_eq]
  refine le_trans (le_of_eq (?_ : _ =
    (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) + q2 (mA n) 0 +
      (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
    kX n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0)) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 8269 / 2500 * y) (le_of_eq (by rw [hy]; ring))
    calc (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) +
          q2 (mA n) 0 + (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
          kX n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0
        ≤ (63970 / 100000 * y + 34085 / 100000 * (815 / 1000 * y) +
          74817 / 100000 * y + (1 + 34085 / 100000) * (12 / 1000 * y)) * z +
          89719 / 100000 * y * (20001 / 10000) + 895 / 100 * y * r + 74817 / 100000 * y +
          63970 / 100000 * y := by gcongr
      _ ≤ 8269 / 2500 * y := by nlinarith

/-- `cAdltx ≤ 1.9054/n` for `n ≥ 4096`. -/
theorem cAdltx_leR : cAdltx n (mA n) ≤ 9527 / 5000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrKR hn
  have hn4 := n4096KR hn
  have hK4 := kX_leR hn
  have hK40 := kX_nonneg n
  have a2 := SS_leKR hn
  have a3 := DS_le hn4
  have a4 := LS_le hn4
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  rw [← hy] at a3 a4
  have hr2 : r ≤ 707107 / 1000000 * (1 / 64) := by linarith
  have hyr : y * r ≤ y * (707107 / 1000000 * (1 / 64)) :=
    mul_le_mul_of_nonneg_left hr2 hy0.le
  unfold cAdltx
  refine le_trans (le_of_eq (?_ : _ = LS (mA n) + kX n * y * SS (mA n) + r * DS (mA n))) ?_
  · rw [hy, hr]; ring
  · refine le_trans (?_ : _ ≤ 9527 / 5000 * y) (le_of_eq (by rw [hy]; ring))
    calc LS (mA n) + kX n * y * SS (mA n) + r * DS (mA n)
        ≤ 12 / 1000 * y + 89719 / 100000 * y * (20001 / 10000) + r * (895 / 100 * y) := by gcongr
      _ ≤ 9527 / 5000 * y := by nlinarith

end focusR

/-! ## The threshold `n ≥ 4489 = 67²` -/

section focusS

variable {n : ℕ} (hn : 4489 ≤ n)

include hn

/-- `kX n ≤ 0.89516` for `n ≥ 4489` (`K4 n ≥ 3.4641`). -/
theorem kX_leS : kX n ≤ 22379 / 25000 := by
  have hx : (4489 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (67 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / √(n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hz0 : 0 < z := by rw [hz]; positivity
  have hz1 : z ≤ 1 / 67 := by rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs
  have hy1 : y ≤ 1 / 4489 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyz : y = z * z := by
    rw [hy, hz, div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have hny : (n : ℝ) * y = 1 := by rw [hy]; field_simp
  have h2 := sqrt2_le
  have h20 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hK0 := K4_nonneg n
  have hK : K4 n ≤ 69313 / 20000 := by
    unfold K4
    refine sqrt_le_of_sq (by norm_num) ?_
    have : 48 / (n : ℝ) ≤ 48 / 4489 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    norm_num at this ⊢
    linarith
  have hQ0 := qCos_nonneg n
  have hQ : qCos n ≤ 205973 / 5000 * y ^ 2 := by
    have e : qCos n = √(1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3) * y ^ 2 := by
      have e1 : 1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3 =
          1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3 := by rw [hy]; ring
      unfold qCos
      rw [e1, hy]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right (sqrt_le_of_sq (by norm_num) ?_) (by positivity)
    have a1 : y ^ 2 ≤ (1 / 4489) ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    have a2 : y ^ 3 ≤ (1 / 4489) ^ 3 := pow_le_pow_left₀ hy0.le hy1 3
    norm_num at a1 a2 ⊢
    linarith
  have eK : K4 n / (n : ℝ) = K4 n * y := by rw [hy]; ring
  have hKy : K4 n * y ≤ 69313 / 20000 * y := mul_le_mul_of_nonneg_right hK hy0.le
  have hKy0 : 0 ≤ K4 n * y := by positivity
  have hsQ : √2 * qCos n ≤ 141422 / 100000 * (205973 / 5000 * y ^ 2) :=
    mul_le_mul h2 hQ hQ0 (by norm_num)
  have hsQ0 : 0 ≤ √2 * qCos n := by positivity
  have hsK : √2 * (K4 n * y) ≤ 141422 / 100000 * (69313 / 20000 * y) :=
    mul_le_mul h2 hKy hKy0 (by norm_num)
  have hsK0 : 0 ≤ √2 * (K4 n * y) := by positivity
  have hy3 : y ^ 3 = (y * z) ^ 2 := by rw [hyz]; ring
  have t4 : √(√2 * (K4 n * y) * (√2 * qCos n)) ≤ 8449 / 500 * (y * z) := by
    refine sqrt_le_of_sq (by positivity) ?_
    have := mul_le_mul hsK hsQ hsQ0 (by positivity)
    refine this.trans ?_
    have e : 141422 / 100000 * (69313 / 20000 * y) * (141422 / 100000 * (205973 / 5000 * y ^ 2)) =
        141422 / 100000 * (69313 / 20000) * (141422 / 100000) * (205973 / 5000) * y ^ 3 := by ring
    rw [e, mul_pow, ← hy3]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hn2 : (n : ℝ) * (K4 n / (2 * (n : ℝ))) = K4 n / 2 := by field_simp
  have e : kX n = K4 n / 4 + (n : ℝ) / 16 * √(√2 * (K4 n * y) * (√2 * qCos n)) +
      (n : ℝ) * (√2 * qCos n) := by
    unfold kX cDx dX
    rw [eK]
    linear_combination (1 / 2) * hn2
  have b1 : (n : ℝ) / 16 * √(√2 * (K4 n * y) * (√2 * qCos n)) ≤ 8449 / 500 / 16 * z := by
    calc (n : ℝ) / 16 * √(√2 * (K4 n * y) * (√2 * qCos n))
        ≤ (n : ℝ) / 16 * (8449 / 500 * (y * z)) := mul_le_mul_of_nonneg_left t4 (by positivity)
      _ = 8449 / 500 / 16 * z * ((n : ℝ) * y) := by ring
      _ = 8449 / 500 / 16 * z := by rw [hny]; ring
  have b2 : (n : ℝ) * (√2 * qCos n) ≤ 141422 / 100000 * (205973 / 5000) * y := by
    calc (n : ℝ) * (√2 * qCos n)
        ≤ (n : ℝ) * (141422 / 100000 * (205973 / 5000 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hsQ hx0.le
      _ = 141422 / 100000 * (205973 / 5000) * y * ((n : ℝ) * y) := by ring
      _ = 141422 / 100000 * (205973 / 5000) * y := by rw [hny]; ring
  rw [e]
  linarith

/-- `y = 1/n`, `z = 1/√n`, `r = 1/√(2n)` at `n ≥ 4489`. -/
lemma yzrKS : ∃ y z r : ℝ, y = 1 / (n : ℝ) ∧ z = 1 / √(n : ℝ) ∧ r = 1 / √(2 * (n : ℝ)) ∧
    0 < y ∧ 0 < z ∧ 0 < r ∧ y ≤ 1 / 4489 ∧ z ≤ 1 / 67 ∧ r ≤ 707107 / 1000000 * z := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1, hr2, hyz⟩ := yzr (n4096KS hn)
  have hx : (4489 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (67 : ℝ) ≤ √(n : ℝ) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  refine ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, ?_, ?_, hr1⟩
  · rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  · rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs

lemma SS_leKS : SS (mA n) ≤ 20001 / 10000 := by
  have hx : (4489 : ℝ) ≤ n := by exact_mod_cast hn
  have h2' : (20151121 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h' : 5 / (n : ℝ) ^ 2 ≤ 5 / 20151121 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2'
  have hpos : (0 : ℝ) ≤ 1 + 5 / (mA n : ℝ) := by positivity
  have e : SS (mA n) = 2 * (1 + 5 / (mA n : ℝ)) := by
    unfold SS sS
    calc √(1 + 5 / (mA n : ℝ)) * (2 * √(1 + 5 / (mA n : ℝ)))
        = 2 * (√(1 + 5 / (mA n : ℝ)) * √(1 + 5 / (mA n : ℝ))) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hpos]
  rw [e, mA_eqR]
  linarith

/-- `rR0x ≤ 3.2968/n` for `n ≥ 4489`. -/
theorem rR0x_leS : rR0x n (mA n) ≤ 4121 / 1250 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrKS hn
  have hn4 := n4096KS hn
  have hcg := cgS_nonneg (kGood_kappa.comp_kappa)
  have hcl := cg2_le'
  have hK4 := kX_leS hn
  have hK40 := kX_nonneg n
  have a1 := nc0_le hn4
  have a2 := SS_leKS hn
  have a3 := DS_le hn4
  have a4 := LS_le hn4
  have a5 := q2z_leKS hn
  have a6 := q3z_leKS hn
  have n1 := nc0_nn (mA n)
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  have n4 := LS_nn (mA n)
  have n5 := q2z_nn (mA n)
  have n6 := q3z_nn (mA n)
  rw [← hy] at a1 a3 a4 a5 a6
  have hzy : y * z ≤ y * (1 / 67) := mul_le_mul_of_nonneg_left hz1 hy0.le
  have hr2 : r ≤ 707107 / 1000000 * (1 / 67) := by linarith
  have hyr : y * r ≤ y * (707107 / 1000000 * (1 / 67)) :=
    mul_le_mul_of_nonneg_left hr2 hy0.le
  rw [rR0x_eq]
  refine le_trans (le_of_eq (?_ : _ =
    (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) + q2 (mA n) 0 +
      (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
    kX n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0)) ?_
  · rw [hy, hz, hr]; ring
  · refine le_trans (?_ : _ ≤ 4121 / 1250 * y) (le_of_eq (by rw [hy]; ring))
    calc (q3 (mA n) 0 + cgS (kappa ∘ kappa) * nc0 (mA n) +
          q2 (mA n) 0 + (1 + cgS (kappa ∘ kappa)) * LS (mA n)) * z +
          kX n * y * SS (mA n) + DS (mA n) * r + q2 (mA n) 0 + q3 (mA n) 0
        ≤ (63933 / 100000 * y + 34085 / 100000 * (815 / 1000 * y) +
          74750 / 100000 * y + (1 + 34085 / 100000) * (12 / 1000 * y)) * z +
          22379 / 25000 * y * (20001 / 10000) + 895 / 100 * y * r + 74750 / 100000 * y +
          63933 / 100000 * y := by gcongr
      _ ≤ 4121 / 1250 * y := by nlinarith

/-- `cAdltx ≤ 1.8969/n` for `n ≥ 4489`. -/
theorem cAdltx_leS : cAdltx n (mA n) ≤ 18969 / 10000 / (n : ℝ) := by
  obtain ⟨y, z, r, hy, hz, hr, hy0, hz0, hr0, hy1, hz1, hr1⟩ := yzrKS hn
  have hn4 := n4096KS hn
  have hK4 := kX_leS hn
  have hK40 := kX_nonneg n
  have a2 := SS_leKS hn
  have a3 := DS_le hn4
  have a4 := LS_le hn4
  have n2 := SS_nn (mA n)
  have n3 := DS_nn (mA n)
  rw [← hy] at a3 a4
  have hr2 : r ≤ 707107 / 1000000 * (1 / 67) := by linarith
  have hyr : y * r ≤ y * (707107 / 1000000 * (1 / 67)) :=
    mul_le_mul_of_nonneg_left hr2 hy0.le
  unfold cAdltx
  refine le_trans (le_of_eq (?_ : _ = LS (mA n) + kX n * y * SS (mA n) + r * DS (mA n))) ?_
  · rw [hy, hr]; ring
  · refine le_trans (?_ : _ ≤ 18969 / 10000 * y) (le_of_eq (by rw [hy]; ring))
    calc LS (mA n) + kX n * y * SS (mA n) + r * DS (mA n)
        ≤ 12 / 1000 * y + 22379 / 25000 * y * (20001 / 10000) + r * (895 / 100 * y) := by gcongr
      _ ≤ 18969 / 10000 * y := by nlinarith

end focusS

end BstLean.Part145

open BstLean.Part145 in
#print axioms kX_leR
open BstLean.Part145 in
#print axioms rR0x_leR
open BstLean.Part145 in
#print axioms cAdltx_leR
open BstLean.Part145 in
#print axioms kX_leS
open BstLean.Part145 in
#print axioms rR0x_leS
open BstLean.Part145 in
#print axioms cAdltx_leS
