import BstLean.Part160MFApp

/-!
# Part 160 (file `MFNum`): the numbers of `ξ_c′` for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55`

Do not use `sorry`, `native_decide` or `axiom`.

Constants: `a₁ = 1.1` (`ϰ_HS = 1.21`), `a₃ = 1.08` (`κ₃ = 1.1664`), `δ_e = 0.011`,
`c_s = csC`, `c_H = cHSK n K₀`, `h_H = hHn n θ` (Part 154).

* `xiCI_le16`: `0 ≤ ξ_c′(θ) ≤ 0.11751` (Part 154: `ξ_c ≤ 0.3235`).
-/

namespace BstLean.Part160

open Real
open BstLean.Part153 (wn phiG)
open BstLean.Part154

/-- `e⁻¹ ≤ 0.368`. -/
lemma exp_neg_one_le : rexp (-1) ≤ 368 / 1000 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.exp_one_gt_d9
  exact le_trans (by norm_num) this.le

/-- `y·e^{−y} ≤ 2.1·10⁻⁸` for `y ≥ 21.12`. -/
lemma exp_tail_I {y : ℝ} (hy : (2112 / 100 : ℝ) ≤ y) : y * rexp (-y) ≤ 21 / 10 ^ 9 := by
  have h1 : y / 10 ≤ rexp (y / 10 - 1) := by
    have := Real.add_one_le_exp (y / 10 - 1)
    linarith
  have h2 : rexp (y / 10 - 1) * rexp (-y) = rexp (-1) * rexp (-(9 / 10 * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h3 : rexp (-(9 / 10 * y)) ≤ rexp (-19) := Real.exp_le_exp.mpr (by linarith)
  have h4 : rexp (-19) = rexp (-1) ^ 19 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h5 : rexp (-1) ^ 20 ≤ (368 / 1000 : ℝ) ^ 20 :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le 20
  have hp := Real.exp_pos (-y)
  calc y * rexp (-y) = 10 * (y / 10 * rexp (-y)) := by ring
    _ ≤ 10 * (rexp (y / 10 - 1) * rexp (-y)) := by
        have := mul_le_mul_of_nonneg_right h1 hp.le
        linarith
    _ = 10 * (rexp (-1) * rexp (-(9 / 10 * y))) := by rw [h2]
    _ ≤ 10 * (rexp (-1) * rexp (-19)) := by
        have := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-1)).le
        linarith
    _ = 10 * rexp (-1) ^ 20 := by rw [h4]; ring
    _ ≤ 10 * (368 / 1000 : ℝ) ^ 20 := by linarith
    _ ≤ 21 / 10 ^ 9 := by norm_num

/-- `n·piG a u v ≤ 1.7·10⁻⁵` if the exponent is at least `n/775`, `n ≥ 16384`. -/
lemma n_piG_le {n : ℕ} (hn : 16384 ≤ n) {a u v : ℝ}
    (hE : (n : ℝ) / 775 ≤ (√(1 - u) - 1 / a) ^ 2 / (2 * v)) :
    (n : ℝ) * piG a u v ≤ 17 / 10 ^ 6 := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hpi : piG a u v ≤ rexp (-((n : ℝ) / 775)) := by
    unfold piG
    exact Real.exp_le_exp.mpr (neg_le_neg hE)
  have hy : (2112 / 100 : ℝ) ≤ (n : ℝ) / 775 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have := exp_tail_I hy
  calc (n : ℝ) * piG a u v ≤ (n : ℝ) * rexp (-((n : ℝ) / 775)) :=
        mul_le_mul_of_nonneg_left hpi hnpos.le
    _ = 775 * ((n : ℝ) / 775 * rexp (-((n : ℝ) / 775))) := by ring
    _ ≤ 775 * (21 / 10 ^ 9) := by linarith
    _ ≤ 17 / 10 ^ 6 := by norm_num

/-- The side conditions of `MA_i_int` and the two tails for `a₁ = 1.1`, `a₃ = 1.08`,
`δ_e = 0.011`, `n ≥ 16384`. -/
theorem tails_num16 {n : ℕ} (hn : 16384 ≤ n) :
    1 / (11 / 10 : ℝ) ≤ √(1 - 2 * rhoBar n csC) ∧ rG n (11 / 1000) ≤ 1 ∧
    1 / (27 / 25 : ℝ) ≤ √(1 - rG n (11 / 1000)) ∧
    (n : ℝ) * piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) ≤ 17 / 10 ^ 6 ∧
    (n : ℝ) * piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) ≤ 17 / 10 ^ 6 := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := rhoBar_facts_NumA16 hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA16 hn
  -- `ϱ̄`
  have ha : (9998 / 10000 : ℝ) ≤ √(1 - 2 * rhoBar n csC) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((9998 / 10000 : ℝ)) ^ 2 ≤ 1 - 2 * (19444 / 100000000) := by norm_num
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
  have hrn : rG n (11 / 1000) * n ≤ 20860 / 10000 := by
    have e : rG n (11 / 1000) * n = 2 * wn n / (1 - 11 / 1000) := by
      unfold rG; field_simp
    rw [e, div_le_iff₀ (by norm_num)]
    linarith
  have hr0 : 0 < rG n (11 / 1000) := by
    unfold rG
    have : (0 : ℝ) < wn n := by linarith
    positivity
  have hr : rG n (11 / 1000) ≤ 12732 / 100000000 := by nlinarith
  have hb : (99993 / 100000 : ℝ) ≤ √(1 - rG n (11 / 1000)) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((99993 / 100000 : ℝ)) ^ 2 ≤ 1 - 12732 / 100000000 := by norm_num
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

lemma xiT1_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    0 ≤ 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) /
      √(2 * csC * (1 - 11 / 1000)) ∧
    4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) /
      √(2 * csC * (1 - 11 / 1000)) ≤ 113750 / 1000000 := by
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨hcH1, hcH⟩ := cHSK_bounds_NumA16 hn
  obtain ⟨hh1, hh⟩ := hHn_bounds_NumA16 hn h0
  have hθ0 : 0 ≤ θ := by linarith
  have hcH0 : 0 ≤ cHSK n K0 := by linarith
  have hhH0 : 0 ≤ hHn n θ := by linarith
  -- first term
  have hsθ : √θ ≤ 74162 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    have : (55 / 100 : ℝ) ≤ (74162 / 100000) ^ 2 := by norm_num
    linarith
  have hsθ0 : 0 ≤ √θ := Real.sqrt_nonneg _
  have hs0 : (16006 / 10000 : ℝ) ≤ √(2 * csC * (1 - 11 / 1000)) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((16006 / 10000 : ℝ)) ^ 2 ≤ 2 * (129521 / 100000) * (1 - 11 / 1000) := by norm_num
    nlinarith
  have hnum : 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) ≤
      4 * (9085 / 100000) * (100517 / 100000) * (102853 / 100000) * (11 / 10 * (27 / 25)) *
        (55 / 100 * (74162 / 100000)) := by
    have hK00 := hK0.le
    gcongr
  have hnum0 : 0 ≤ 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) := by
    have := hK0.le
    positivity
  have hT1 : 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) /
      √(2 * csC * (1 - 11 / 1000)) ≤ 113750 / 1000000 := by
    rw [div_le_iff₀ (by linarith)]
    have : (4 : ℝ) * (9085 / 100000) * (100517 / 100000) * (102853 / 100000) *
        (11 / 10 * (27 / 25)) * (55 / 100 * (74162 / 100000)) ≤
        113750 / 1000000 * (16006 / 10000) := by norm_num
    nlinarith
  have hT1_0 : 0 ≤ 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) /
      √(2 * csC * (1 - 11 / 1000)) := div_nonneg hnum0 (Real.sqrt_nonneg _)
  exact ⟨hT1_0, hT1⟩

lemma xiTt_le16 {n : ℕ} (hn : 16384 ≤ n) :
    0 ≤ 8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
      (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) ∧
    8 * K0 * wn n * n * (piG (11 / 10) (2 * rhoBar n csC) (rhoBar n csC) /
      (11 / 10) + piG (27 / 25) (rG n (11 / 1000)) (rG n (11 / 1000)) / (27 / 25)) ≤ 3 / 100000 := by
  have hn8 : 8192 ≤ n := le_trans (by norm_num) hn
  have hn' := n_ge_NumA hn8
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA16 hn
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
    have ha : 8 * K0 * wn n ≤ 8 * (9085 / 100000) * (1031495 / 1000000) :=
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
      _ ≤ 8 * (9085 / 100000) * (1031495 / 1000000) *
          (17 / 10 ^ 6 / (11 / 10) + 17 / 10 ^ 6 / (27 / 25)) :=
          mul_le_mul ha hsum hsum0 (by norm_num)
      _ ≤ 3 / 100000 := by norm_num
  exact ⟨hTt_0, hTt⟩

lemma xiT2_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    0 ≤ 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) ∧
    4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) ≤ 252 / 100000 := by
  have hn8 : 8192 ≤ n := le_trans (by norm_num) hn
  have hn' := n_ge_NumA hn8
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := rhoBar_facts_NumA16 hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA16 hn
  obtain ⟨hP0, hP⟩ := piBar_le_rho_NumA hn8
  have hnP := piBar_le_NumA hn8
  obtain ⟨hν0, hν⟩ := nuR_bounds_NumA hn8
  obtain ⟨hs2, hs2'⟩ := sqrt2_bounds_NumA
  have hπ := Real.pi_gt_d6
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  -- the linear term (as in `xiCn_leA16`)
  have hr2 : 0 ≤ √2 - 1 := by linarith
  have hr2' : 4 * (√2 - 1) ^ 2 ≤ 68632 / 100000 := by
    have : (√2 - 1) ^ 2 ≤ (41422 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hr2 (by linarith) 2
    have h' : (4 : ℝ) * (41422 / 100000) ^ 2 ≤ 68632 / 100000 := by norm_num
    linarith
  have hr2'' : 0 ≤ 4 * (√2 - 1) ^ 2 := by positivity
  have hρnν0 : 0 ≤ rhoBar n csC * n * nuR (rhoBar n csC) :=
    mul_nonneg (mul_nonneg hρ0.le hnpos.le) hν0
  have hρnν : rhoBar n csC * n * nuR (rhoBar n csC) ≤
      31856 / 10000 * (40004 / 10000 * (19444 / 100000000)) :=
    mul_le_mul hρn (hν.trans (by linarith)) hν0 (by norm_num)
  have hM : 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) ≤
      68632 / 100000 * (31856 / 10000 * (40004 / 10000 * (19444 / 100000000))) := by
    have := mul_le_mul hr2' hρnν hρnν0 (by norm_num)
    calc 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)
        = 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := by ring
      _ ≤ _ := this
  have hM0 : 0 ≤ 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) := by
    have := mul_nonneg hr2'' hρnν0
    calc (0 : ℝ) ≤ 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := this
      _ = _ := by ring
  have hθρ0 : 0 ≤ 2 * θ * rhoBar n csC := by positivity
  have hθρ : 2 * θ * rhoBar n csC ≤ 2 * (55 / 100) * (19444 / 100000000) :=
    mul_le_mul (by linarith) hρ hρ0.le (by norm_num)
  have hfrac : (2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π ≤
      (2 * (55 / 100) * (19444 / 100000000) +
        68632 / 100000 * (31856 / 10000 * (40004 / 10000 * (19444 / 100000000)))) / 3.141592 :=
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
      4 * (1031495 / 1000000) * ((2 * (55 / 100) * (19444 / 100000000) +
        68632 / 100000 * (31856 / 10000 * (40004 / 10000 * (19444 / 100000000)))) / 3.141592 +
          1 / 10 ^ 11) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hT2' : (4 : ℝ) * (1031495 / 1000000) * ((2 * (55 / 100) * (19444 / 100000000) +
        68632 / 100000 * (31856 / 10000 * (40004 / 10000 * (19444 / 100000000)))) / 3.141592 +
          1 / 10 ^ 11) ≤ 252 / 100000 := by norm_num
  have hT2_0 : 0 ≤ 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) :=
    mul_nonneg (by linarith) (by linarith)
  exact ⟨hT2_0, hT2.trans hT2'⟩

/-- **`0 ≤ ξ_c′(θ) ≤ 0.11751`** for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55`. -/
theorem xiCI_le16 {n : ℕ} (hn : 16384 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    0 ≤ xiCI n csC (cHSK n K0) (hHn n θ) (11 / 10) (27 / 25) (11 / 1000) θ ∧
    xiCI n csC (cHSK n K0) (hHn n θ) (11 / 10) (27 / 25) (11 / 1000) θ ≤ 11751 / 100000 := by
  obtain ⟨a0, a1⟩ := xiT1_le16 hn h0 h1
  obtain ⟨b0, b1⟩ := xiTt_le16 hn
  obtain ⟨c0, c1⟩ := xiT2_le16 hn h0 h1
  obtain ⟨hb0, hb⟩ := bN_bounds_NumA16 hn h0 h1
  constructor
  · unfold xiCI; linarith only [a0, b0, c0, hb0]
  · unfold xiCI
    linarith only [a1, b1, c1, hb]

end BstLean.Part160

open BstLean.Part160 in
#print axioms tails_num16
open BstLean.Part160 in
#print axioms xiCI_le16
