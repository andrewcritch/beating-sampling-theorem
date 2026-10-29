import BstLean.Part187All
import BstLean.Part160MFNum
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154C16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R154Num16
import BstLean.Part188R160Lib





namespace BstLean.Part188.Base160_R
open BstLean.Part160 BstLean.Part160.R

open Real
open BstLean.Part153 (wn phiG)
open BstLean.Part154

/-- `y·e^{−y} ≤ 1.81·10⁻⁸` for `y ≥ 20.96` (for the floor `16200`). -/
lemma exp_tail_J {y : ℝ} (hy : (209 / 10 : ℝ) ≤ y) : y * rexp (-y) ≤ 190 / 10 ^ 10 := by
  have h1 : y / 21 ≤ rexp (y / 21 - 1) := by
    have := Real.add_one_le_exp (y / 21 - 1)
    linarith
  have h2 : rexp (y / 21 - 1) * rexp (-y) = rexp (-1) ^ 20 * rexp (-(20 / 21 * y - 19)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have h3 : rexp (-(20 / 21 * y - 19)) ≤ rexp (-(9 / 10)) := Real.exp_le_exp.mpr (by linarith)
  have h4 : rexp (-(9 / 10 : ℝ)) ≤ 434 / 1000 := by
    have q := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 / 10 by norm_num)
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    refine le_trans ?_ q
    norm_num
  have h5 : rexp (-1) ^ 20 ≤ (368 / 1000 : ℝ) ^ 20 :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le 20
  have hp := Real.exp_pos (-y)
  have h6 : 0 ≤ rexp (-1) ^ 20 := by positivity
  calc y * rexp (-y) = 21 * (y / 21 * rexp (-y)) := by ring
    _ ≤ 21 * (rexp (y / 21 - 1) * rexp (-y)) := by gcongr
    _ = 21 * (rexp (-1) ^ 20 * rexp (-(20 / 21 * y - 19))) := by rw [h2]
    _ ≤ 21 * ((368 / 1000 : ℝ) ^ 20 * (434 / 1000)) := by
        gcongr
        exact h3.trans h4
    _ ≤ 190 / 10 ^ 10 := by norm_num

/-- `n·piG a u v ≤ 1.7·10⁻⁵` if the exponent is at least `n/775`, `n ≥ 16200`. -/
lemma n_piG_le {n : ℕ} (hn : 16200 ≤ n) {a u v : ℝ}
    (hE : (n : ℝ) / 775 ≤ (√(1 - u) - 1 / a) ^ 2 / (2 * v)) :
    (n : ℝ) * piG a u v ≤ 17 / 10 ^ 6 := by
  have hn' : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hpi : piG a u v ≤ rexp (-((n : ℝ) / 775)) := by
    unfold piG
    exact Real.exp_le_exp.mpr (neg_le_neg hE)
  have hy : (209 / 10 : ℝ) ≤ (n : ℝ) / 775 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have := exp_tail_J hy
  calc (n : ℝ) * piG a u v ≤ (n : ℝ) * rexp (-((n : ℝ) / 775)) :=
        mul_le_mul_of_nonneg_left hpi hnpos.le
    _ = 775 * ((n : ℝ) / 775 * rexp (-((n : ℝ) / 775))) := by ring
    _ ≤ 775 * (190 / 10 ^ 10) := by linarith
    _ ≤ 17 / 10 ^ 6 := by norm_num

/-- The side conditions of `MA_i_int` and the two tails for `a₁ = 1.1`, `a₃ = 1.08`,
`δ_e = 0.011`, `n ≥ 16200`. -/
theorem tails_num16 {n : ℕ} (hn : 16200 ≤ n) :
    1 / (11 / 10 : ℝ) ≤ √(1 - 2 * rhoBar n csC) ∧ rG n (11 / 1000) ≤ 1 ∧
    1 / (27 / 25 : ℝ) ≤ √(1 - rG n (11 / 1000)) ∧
    (n : ℝ) * piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) ≤ 17 / 10 ^ 6 ∧
    (n : ℝ) * piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) ≤ 17 / 10 ^ 6 := by
  have hn' : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := BstLean.Part188.Base154_R.rhoBar_facts_NumA16 hn
  obtain ⟨hw1, hw⟩ := BstLean.Part188.Base154_R.wn_bounds_NumA16 hn
  -- `ϱ̄`
  have ha : (9998 / 10000 : ℝ) ≤ √(1 - 2 * rhoBar n csC) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((9998 / 10000 : ℝ)) ^ 2 ≤ 1 - 2 * (19670 / 100000000) := by norm_num
    linarith
  have hd1 : (907 / 10000 : ℝ) ≤ √(1 - 2 * rhoBar n csC) - 1 / (11 / 10) := by
    have : (1 : ℝ) / (11 / 10) ≤ 9091 / 10000 := by norm_num
    linarith
  have hsq1 : (822649 / 100000000 : ℝ) ≤ (√(1 - 2 * rhoBar n csC) - 1 / (11 / 10)) ^ 2 := by
    have : (822649 / 100000000 : ℝ) ≤ (907 / 10000) ^ 2 := by norm_num
    exact this.trans (pow_le_pow_left₀ (by norm_num) hd1 2)
  have hE1 : (n : ℝ) / 775 ≤
      (√(1 - 2 * rhoBar n csC) - 1 / (11 / 10)) ^ 2 / (2 * rhoBar n csC) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `r̄_Γ`
  have hrn : rG n (11 / 1000) * n ≤ 20865 / 10000 := by
    have e : rG n (11 / 1000) * n = 2 * wn n / (1 - 11 / 1000) := by
      unfold rG; field_simp
    rw [e, div_le_iff₀ (by norm_num)]
    linarith
  have hr0 : 0 < rG n (11 / 1000) := by
    unfold rG
    have : (0 : ℝ) < wn n := by linarith
    positivity
  have hr : rG n (11 / 1000) ≤ 12880 / 100000000 := by nlinarith
  have hb : (99993 / 100000 : ℝ) ≤ √(1 - rG n (11 / 1000)) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((99993 / 100000 : ℝ)) ^ 2 ≤ 1 - 12880 / 100000000 := by norm_num
    linarith
  have hd3 : (74 / 1000 : ℝ) ≤ √(1 - rG n (11 / 1000)) - 1 / (27 / 25) := by
    have : (1 : ℝ) / (27 / 25) ≤ 92593 / 100000 := by norm_num
    linarith
  have hsq3 : (5476 / 1000000 : ℝ) ≤ (√(1 - rG n (11 / 1000)) - 1 / (27 / 25)) ^ 2 := by
    have : (5476 / 1000000 : ℝ) ≤ (74 / 1000) ^ 2 := by norm_num
    exact this.trans (pow_le_pow_left₀ (by norm_num) hd3 2)
  have hE3 : (n : ℝ) / 775 ≤
      (√(1 - rG n (11 / 1000)) - 1 / (27 / 25)) ^ 2 / (2 * rG n (11 / 1000)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  refine ⟨by linarith, by linarith, by linarith, ?_, n_piG_le hn hE3⟩
  have h := n_piG_le hn (a := 11 / 10) (u := 2 * rhoBar n csC) (v := rhoBar n csC) hE1
  exact h

lemma xiTt_le16 {n : ℕ} (hn : 16200 ≤ n) :
    0 ≤ 8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
      (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) ∧
    8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
      (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) ≤ 3 / 100000 := by
  have hn8 : 8192 ≤ n := le_trans (by norm_num) hn
  have hn' := n_ge_NumA hn8
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hw1, hw⟩ := BstLean.Part188.Base154_R.wn_bounds_NumA16 hn
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨-, -, -, ht1, ht3⟩ := tails_num16 hn
  have hw0 : 0 ≤ wn n := by linarith
  -- the tails
  have hp1_0 := piG_nonneg (11 / 10) (2 * rhoBar n csC) (rhoBar n csC)
  have hp3_0 := piG_nonneg (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000))
  have hTt_0 : 0 ≤ 8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
      (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) := by
    have := hK0.le
    positivity
  have hTt : 8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
      (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) ≤
      3 / 100000 := by
    have ha : 8 * K0 * wn n ≤ 8 * (9085 / 100000) * (1031745 / 1000000) :=
      mul_le_mul (by linarith) hw hw0 (by norm_num)
    have ha0 : 0 ≤ 8 * K0 * wn n := by have := hK0.le; positivity
    have hsum : (n : ℝ) * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) / (11 / 10) +
        piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) ≤
        17 / 10 ^ 6 / (11 / 10) + 17 / 10 ^ 6 / (27 / 25) := by
      have e : (n : ℝ) * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) / (11 / 10) +
          piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) =
          (n : ℝ) * piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) / (11 / 10) +
          (n : ℝ) * piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25) := by ring
      rw [e]
      exact add_le_add (div_le_div_of_nonneg_right ht1 (by norm_num))
        (div_le_div_of_nonneg_right ht3 (by norm_num))
    have hsum0 : 0 ≤ (n : ℝ) * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) / (11 / 10) +
        piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) := by positivity
    calc 8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
          (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25))
        = 8 * K0 * wn n * ((n : ℝ) * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
          (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25))) := by
          ring
      _ ≤ 8 * (9085 / 100000) * (1031745 / 1000000) *
          (17 / 10 ^ 6 / (11 / 10) + 17 / 10 ^ 6 / (27 / 25)) :=
          mul_le_mul ha hsum hsum0 (by norm_num)
      _ ≤ 3 / 100000 := by norm_num
  exact ⟨hTt_0, hTt⟩

lemma xiT2_le16 {n : ℕ} (hn : 16200 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    0 ≤ 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) ∧
    4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) ≤ 255 / 100000 := by
  have hn8 : 8192 ≤ n := le_trans (by norm_num) hn
  have hn' := n_ge_NumA hn8
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := BstLean.Part188.Base154_R.rhoBar_facts_NumA16 hn
  obtain ⟨hw1, hw⟩ := BstLean.Part188.Base154_R.wn_bounds_NumA16 hn
  obtain ⟨hP0, hP⟩ := piBar_le_rho_NumA hn8
  have hnP := piBar_le_NumA hn8
  obtain ⟨hν0, hν⟩ := nuR_bounds_NumA hn8
  obtain ⟨hs2, hs2'⟩ := sqrt2_bounds_NumA
  have hπ := Real.pi_gt_d6
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  -- the linear term (as in `BstLean.Part188.Base154_R.xiCn_leA16`)
  have hr2 : 0 ≤ √2 - 1 := by linarith
  have hr2' : 4 * (√2 - 1) ^ 2 ≤ 68632 / 100000 := by
    have : (√2 - 1) ^ 2 ≤ (41422 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hr2 (by linarith) 2
    have h' : (4 : ℝ) * (41422 / 100000) ^ 2 ≤ 68632 / 100000 := by norm_num
    linarith
  have hr2'' : 0 ≤ 4 * (√2 - 1) ^ 2 := by positivity
  have hρnν0 : 0 ≤ rhoBar n csC * n * nuR (rhoBar n csC) :=
    mul_nonneg (mul_nonneg hρ0.le hnpos.le) hν0
  have hρnν : rhoBar n csC * n * nuR (rhoBar n csC) ≤
      31864 / 10000 * (40004 / 10000 * (19670 / 100000000)) :=
    mul_le_mul hρn (hν.trans (by linarith)) hν0 (by norm_num)
  have hM : 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) ≤
      68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19670 / 100000000))) := by
    have := mul_le_mul hr2' hρnν hρnν0 (by norm_num)
    calc 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)
        = 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := by ring
      _ ≤ _ := this
  have hM0 : 0 ≤ 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) := by
    have := mul_nonneg hr2'' hρnν0
    calc (0 : ℝ) ≤ 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := this
      _ = _ := by ring
  have hθρ0 : 0 ≤ 2 * θ * rhoBar n csC := by positivity
  have hθρ : 2 * θ * rhoBar n csC ≤ 2 * (55 / 100) * (19670 / 100000000) :=
    mul_le_mul (by linarith) hρ hρ0.le (by norm_num)
  have hfrac : (2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π ≤
      (2 * (55 / 100) * (19670 / 100000000) +
        68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19670 / 100000000)))) / 3.141592 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hπ.le
  have hfrac0 : 0 ≤ (2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π :=
    div_nonneg (by linarith) Real.pi_pos.le
  have hPsmall : piBar (rhoBar n csC) ≤ 1 / 10 ^ 11 := by nlinarith
  have hθP0 : 0 ≤ θ * piBar (rhoBar n csC) := mul_nonneg hθ0 hP0.le
  have hθP : θ * piBar (rhoBar n csC) ≤ 1 / 10 ^ 11 := by nlinarith
  have hT2 : 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) ≤
      4 * (1031745 / 1000000) * ((2 * (55 / 100) * (19670 / 100000000) +
        68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19670 / 100000000)))) / 3.141592 +
          1 / 10 ^ 11) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hT2' : (4 : ℝ) * (1031745 / 1000000) * ((2 * (55 / 100) * (19670 / 100000000) +
        68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19670 / 100000000)))) / 3.141592 +
          1 / 10 ^ 11) ≤ 255 / 100000 := by norm_num
  have hT2_0 : 0 ≤ 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) :=
    mul_nonneg (by linarith) (by linarith)
  exact ⟨hT2_0, hT2.trans hT2'⟩

end BstLean.Part188.Base160_R

