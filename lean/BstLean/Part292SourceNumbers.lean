import BstLean.Part292NodeData
import BstLean.Part172Cls

/-! Simple rational source inequalities valid for every n at least 8000. -/
namespace BstLean.Part292
open Real BstLean.Part130 BstLean.Part170 BstLean.Part171 BstLean.Part223

noncomputable def lowOperator (n : ℕ) : ℝ := sqrt (2/(n : ℝ))*((n : ℝ)+sqrt n+6)
noncomputable def lowSigma (n : ℕ) : ℝ := sqrt (999/2000)/sqrt (n : ℝ)
noncomputable def lowUpperSigma (n : ℕ) : ℝ := (2001/1000)/sqrt (n : ℝ)
noncomputable def lowBiasUpper (n : ℕ) : ℝ := sqrt (5/2)/sqrt (n : ℝ)

theorem low_scales_square {n : ℕ} (hn : 1 ≤ n) :
    lowSigma n^2=(999/2000 : ℝ)/n ∧ lowBiasUpper n^2=(5/2 : ℝ)/n := by
  simp only [lowSigma, lowBiasUpper, div_pow, sq_sqrt (Nat.cast_nonneg n),
    sq_sqrt (by norm_num : (0 : ℝ) ≤ 999/2000), sq_sqrt (by norm_num : (0 : ℝ) ≤ 5/2)]
  constructor <;> trivial

theorem lowOperator_square {n : ℕ} (hn : 8000 ≤ n) : lowOperator n^2 ≤ (2049/1000 : ℝ)*n := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : sqrt (n : ℝ) ≤ (1119/100000 : ℝ)*n := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h : 1 ≤ (1119/100000 : ℝ)^2*n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h hn0.le]
  have hsum : (n : ℝ)+sqrt n+6 ≤ (50597/50000 : ℝ)*n := by linarith
  unfold lowOperator
  rw [mul_pow, sq_sqrt (by positivity)]
  calc
    _ ≤ (2/(n : ℝ))*((50597/50000 : ℝ)*n)^2 := by gcongr
    _ = (2*(50597/50000 : ℝ)^2)*n := by field_simp <;> ring
    _ ≤ _ := by nlinarith

theorem low_lambda_cap {n : ℕ} (hn : 8000 ≤ n) :
    (n : ℝ)*sqrt (tA n*(lowOperator n^2/((n : ℝ)-2))) ≤ 2025/1000 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ)-2 := by linarith
  have hO := lowOperator_square hn
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by norm_num)
  rw [mul_pow, sq_sqrt (by have := tA_nonneg n; positivity)]
  have he : (n : ℝ)^2*(tA n*(lowOperator n^2/((n : ℝ)-2))) =
      2*lowOperator n^2/((n : ℝ)-2) := by
    unfold tA mA
    push_cast
    field_simp <;> ring
  rw [he, div_le_iff₀ hd]
  nlinarith

theorem low_gap_cap {n : ℕ} (hn : 8000 ≤ n) :
    (2487/10000 : ℝ)/n ≤ baseGap n (lowOperator n) (lowSigma n) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ)-2 := by linarith
  have hO := lowOperator_square hn
  rw [baseGap, (low_scales_square (by omega)).1]
  have hnum : 4*lowOperator n^2 ≤ (21/20000 : ℝ)*n*((n : ℝ)-2) := by
    have h : 4*(2049/1000 : ℝ) ≤ (21/20000 : ℝ)*((n : ℝ)-2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h hn0.le]
  unfold tA mA
  push_cast
  apply (le_sub_iff_add_le).mpr
  field_simp
  nlinarith

theorem inverseRadius8_low {n : ℕ} (hn : 8000 ≤ n) :
    inverseRadius8 (n-1) ≤ (1005/1000 : ℝ)/(n : ℝ)^4 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h3 : (2497/2500 : ℝ)*n ≤ (n : ℝ)-3 := by linarith
  have h5 : (2497/2500 : ℝ)*n ≤ (n : ℝ)-5 := by linarith
  have h7 : (2497/2500 : ℝ)*n ≤ (n : ℝ)-7 := by linarith
  have h9 : (2497/2500 : ℝ)*n ≤ (n : ℝ)-9 := by linarith
  have h3pos : 0 ≤ (n : ℝ)-3 := by linarith
  have h5pos : 0 ≤ (n : ℝ)-5 := by linarith
  have h7pos : 0 ≤ (n : ℝ)-7 := by linarith
  have h9pos : 0 ≤ (n : ℝ)-9 := by linarith
  have hp : ((2497/2500 : ℝ)*n)^4 ≤
      ((n : ℝ)-3)*((n : ℝ)-5)*((n : ℝ)-7)*((n : ℝ)-9) := by
    calc
      _ = ((2497/2500 : ℝ)*n)*((2497/2500)*n)*((2497/2500)*n)*((2497/2500)*n) := by ring
      _ ≤ _ := by gcongr
  unfold inverseRadius8
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num only [Nat.cast_one]
  have ha : (0 : ℝ) < (n : ℝ)-1-2 := by linarith
  have hb : (0 : ℝ) < (n : ℝ)-1-4 := by linarith
  have hc : (0 : ℝ) < (n : ℝ)-1-6 := by linarith
  have hd : (0 : ℝ) < (n : ℝ)-1-8 := by linarith
  have hprod : 0 < ((n : ℝ)-1-2)*((n : ℝ)-1-4)*((n : ℝ)-1-6)*((n : ℝ)-1-8) := by positivity
  rw [inv_eq_one_div, div_le_div_iff₀ hprod (pow_pos hn0 4)]
  have hconst : (1 : ℝ) ≤ (1005/1000)*(2497/2500)^4 := by norm_num
  have hmul := mul_le_mul_of_nonneg_right hconst (pow_nonneg hn0.le 4)
  nlinarith [mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 1005/1000)]

theorem base_plane_cap {n : ℕ} (hn : 8000 ≤ n) :
    tA n/((n : ℝ)-2)*(517/200+517/200) ≤ (1035/100 : ℝ)/(n : ℝ)^3 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ)-2 := by linarith
  have he : tA n/((n : ℝ)-2)*(517/200+517/200) =
      (1034/100 : ℝ)/((n : ℝ)^2*((n : ℝ)-2)) := by
    unfold tA mA
    push_cast
    field_simp <;> ring
  rw [he]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hn0 2) hd) (pow_pos hn0 3)).mpr
  have h : (1034/100 : ℝ)*n ≤ (1035/100)*((n : ℝ)-2) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hn0.le 2)]

theorem base_variance_cap {n : ℕ} (hn : 8000 ≤ n) :
    ((8*tA n/(n : ℝ))/((n : ℝ)-2))*(517/200) ≤ (414/10 : ℝ)/(n : ℝ)^4 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ)-2 := by linarith
  have he : ((8*tA n/(n : ℝ))/((n : ℝ)-2))*(517/200) =
      (4136/100 : ℝ)/((n : ℝ)^3*((n : ℝ)-2)) := by
    unfold tA mA
    push_cast
    field_simp <;> ring
  rw [he, div_le_div_iff₀ (mul_pos (pow_pos hn0 3) hd) (pow_pos hn0 4)]
  have h : (4136/100 : ℝ)*n ≤ (414/10)*((n : ℝ)-2) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hn0.le 3)]

theorem base_exceptional_cap {n : ℕ} (hn : 8000 ≤ n) :
    baseExceptionalCoefficient n (lowOperator n) (lowSigma n)*(517/200)^4 ≤
      (8*10^14 : ℝ)/(n : ℝ)^8 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := low_gap_cap hn
  have hg0 : 0 < baseGap n (lowOperator n) (lowSigma n) :=
    lt_of_lt_of_le (by positivity) hg
  have hc := BstLean.Part172.cLS4_le
  have hc0 := BstLean.Part162.cLS_nonneg 4
  have hr := inverseRadius8_low hn
  have hr0 := (inverseRadius8_pos (by omega : 8 < n-1)).le
  have ht : 8*tA n/(n : ℝ) = 16/(n : ℝ)^3 := by
    unfold tA mA
    push_cast
    field_simp <;> ring
  unfold baseExceptionalCoefficient
  rw [ht]
  calc
    _ ≤ (28115/10000 : ℝ)^8*(16/(n : ℝ)^3)^4*
        ((1005/1000)/(n : ℝ)^4)/((2487/10000)/(n : ℝ))^8*(517/200)^4 := by gcongr
    _ = ((28115/10000 : ℝ)^8*16^4*(1005/1000)/(2487/10000)^8*(517/200)^4)/
        (n : ℝ)^8 := by field_simp <;> ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hn0.le 8)
      norm_num

theorem source_scale_caps {n : ℕ} (hn : 8000 ≤ n) :
    tA n*lowOperator n^2+lowBiasUpper n^2 ≤ (7 : ℝ)/n ∧
    sqrt (tA n)*lowOperator n ≤ (3 : ℝ)/sqrt n ∧
    lowBiasUpper n ≤ (2 : ℝ)/sqrt n := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ht := tA_nonneg n
  have hO := lowOperator_square hn
  have hOp : 0 ≤ lowOperator n := by unfold lowOperator; positivity
  have he : tA n*lowOperator n^2 ≤ (4098/1000 : ℝ)/n := by
    unfold tA mA
    push_cast
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hn0 2) hn0]
    nlinarith [mul_le_mul_of_nonneg_right hO hn0.le]
  refine ⟨?_, ?_, ?_⟩
  · rw [(low_scales_square (by omega)).2]
    apply (add_le_add he (le_refl ((5/2 : ℝ)/(n : ℝ)))).trans
    rw [← add_div]
    gcongr
    norm_num
  · apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity)
    rw [mul_pow, sq_sqrt ht, div_pow, sq_sqrt hn0.le]
    apply he.trans
    gcongr
    norm_num
  · unfold lowBiasUpper
    gcongr
    exact sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩

end BstLean.Part292
