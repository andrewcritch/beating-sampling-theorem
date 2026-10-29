import BstLean.Part154NumA

/-!
# Part 154: the numbers of the centre bounds, first half, for `n ≥ 8192`, `0.457 ≤ θ ≤ 0.555`.
-/

namespace BstLean.Part154

open Real
open BstLean.Part153 (wn phiG)

lemma hHn_bounds_NumA8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) :
    1 ≤ hHn n θ ∧ hHn n θ ≤ 10485 / 10000 := by
  have ha := aHn_bounds_NumA hn
  have hθ : (676 / 1000 : ℝ) ≤ √θ := by
    rw [Real.le_sqrt' (by norm_num)]
    exact le_trans (by norm_num) h0
  have hq0 : 0 ≤ aHn n / √θ := div_nonneg ha.1 (Real.sqrt_nonneg _)
  have hq : aHn n / √θ ≤ 805 / 100000 / (676 / 1000) :=
    div_le_div₀ (by norm_num) ha.2 (by norm_num) hθ
  unfold hHn
  constructor
  · exact one_le_pow₀ (by linarith)
  · calc (1 + aHn n / √θ) ^ 4 ≤ (1 + 805 / 100000 / (676 / 1000)) ^ 4 := by gcongr
      _ ≤ 10485 / 10000 := by norm_num

/-- `0 ≤ b_n(θ) ≤ 0.00231`. -/
lemma bN_bounds_NumA8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ)
    (h1 : θ ≤ 555 / 1000) : 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 231 / 100000 := by
  obtain ⟨hρ0, -, -, hρ⟩ := rhoBar_facts_NumA hn
  obtain ⟨hQ0, hQ⟩ := QB_bounds_NumA hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA hn
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  unfold bN
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) hQ0) hρ0.le
  · rw [div_le_iff₀ hρ0]
    have hA : 4 * θ * wn n ≤ 4 * (555 / 1000) * (1044683 / 1000000) :=
      mul_le_mul (by linarith) hw hw0 (by norm_num)
    have hB : 4 * θ * wn n * QB (rhoBar n csC) (piBar (rhoBar n csC)) ≤
        4 * (555 / 1000) * (1044683 / 1000000) * (25146 / 10000 * rhoBar n csC ^ 2) :=
      mul_le_mul hA hQ hQ0 (by norm_num)
    have hC : rhoBar n csC ^ 2 ≤ 394 / 1000000 * rhoBar n csC := by nlinarith
    linarith

private lemma mul5A8 {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (la : a ≤ a') (lb : b ≤ b') (lc : c ≤ c') (ld : d ≤ d') :
    a * b * 8 * c * d ≤ a' * b' * 8 * c' * d' := by
  have ha' : 0 ≤ a' := ha.trans la
  have hb' : 0 ≤ b' := hb.trans lb
  have hc' : 0 ≤ c' := hc.trans lc
  gcongr

/-- `ξ_c(θ) ≤ 0.3285`, `b_n(θ) ≤ 0.00225`. -/
theorem xiCn_leA8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000) :
    0 ≤ xiCn n θ ∧ xiCn n θ ≤ 3370 / 10000 ∧ 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 231 / 100000 := by
  have hn' := n_ge_NumA hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := rhoBar_facts_NumA hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA hn
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨hcH1, hcH⟩ := cHSK_bounds_NumA hn
  obtain ⟨hh1, hh⟩ := hHn_bounds_NumA8 hn h0
  obtain ⟨hP0, hP⟩ := piBar_le_rho_NumA hn
  have hnP := piBar_le_NumA hn
  obtain ⟨hν0, hν⟩ := nuR_bounds_NumA hn
  obtain ⟨hb0, hb⟩ := bN_bounds_NumA8 hn h0 h1
  obtain ⟨hs2, hs2'⟩ := sqrt2_bounds_NumA
  have hπ := Real.pi_gt_d6
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  have hcs0 : 0 < csC := by linarith
  have hcH0 : 0 ≤ cHSK n K0 := by linarith
  have hhH0 : 0 ≤ hHn n θ := by linarith
  -- first term
  have hq0 : 0 ≤ cHSK n K0 / csC := div_nonneg hcH0 hcs0.le
  have hq : cHSK n K0 / csC ≤ 100746 / 100000 / (129521 / 100000) :=
    div_le_div₀ (by norm_num) hcH (by norm_num) hcs1
  have hT1 := mul5A8 hθ0 hq0 hK0.le hhH0 h1 hq hK hh
  have hT1' : (555 / 1000 : ℝ) * (100746 / 100000 / (129521 / 100000)) * 8 * (9085 / 100000) *
      (10485 / 10000) ≤ 3290 / 10000 := by norm_num
  have hT1_0 : 0 ≤ θ * (cHSK n K0 / csC) * 8 * K0 * hHn n θ := by positivity
  -- second term
  have hr2 : 0 ≤ √2 - 1 := by linarith
  have hr2' : 4 * (√2 - 1) ^ 2 ≤ 68632 / 100000 := by
    have : (√2 - 1) ^ 2 ≤ (41422 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hr2 (by linarith) 2
    have h' : (4 : ℝ) * (41422 / 100000) ^ 2 ≤ 68632 / 100000 := by norm_num
    linarith
  have hr2'' : 0 ≤ 4 * (√2 - 1) ^ 2 := by positivity
  have hρnν0 : 0 ≤ rhoBar n csC * n * nuR (rhoBar n csC) :=
    mul_nonneg (mul_nonneg hρ0.le hnpos.le) hν0
  have hρnν : rhoBar n csC * n * nuR (rhoBar n csC) ≤
      32263 / 10000 * (40004 / 10000 * (394 / 1000000)) :=
    mul_le_mul hρn (hν.trans (by linarith)) hν0 (by norm_num)
  have hM : 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) ≤
      68632 / 100000 * (32263 / 10000 * (40004 / 10000 * (394 / 1000000))) := by
    have := mul_le_mul hr2' hρnν hρnν0 (by norm_num)
    calc 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)
        = 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := by ring
      _ ≤ _ := this
  have hM0 : 0 ≤ 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) := by
    have := mul_nonneg hr2'' hρnν0
    calc (0 : ℝ) ≤ 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := this
      _ = _ := by ring
  have hθρ0 : 0 ≤ 2 * θ * rhoBar n csC := by positivity
  have hθρ : 2 * θ * rhoBar n csC ≤ 2 * (555 / 1000) * (394 / 1000000) :=
    mul_le_mul (by linarith) hρ hρ0.le (by norm_num)
  have hfrac : (2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π ≤
      (2 * (555 / 1000) * (394 / 1000000) +
        68632 / 100000 * (32263 / 10000 * (40004 / 10000 * (394 / 1000000)))) / 3.141592 :=
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
      4 * (1044683 / 1000000) * ((2 * (555 / 1000) * (394 / 1000000) +
        68632 / 100000 * (32263 / 10000 * (40004 / 10000 * (394 / 1000000)))) / 3.141592 +
          1 / 10 ^ 11) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hT2' : (4 : ℝ) * (1044683 / 1000000) * ((2 * (555 / 1000) * (394 / 1000000) +
        68632 / 100000 * (32263 / 10000 * (40004 / 10000 * (394 / 1000000)))) / 3.141592 +
          1 / 10 ^ 11) ≤ 523 / 100000 := by norm_num
  have hT2_0 : 0 ≤ 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) :=
    mul_nonneg (by linarith) (by linarith)
  -- fourth term
  have hT4_0 : 0 ≤ 4 * √2 * K0 * wn n * n * piBar (rhoBar n csC) := by
    have := hK0.le; have := hP0.le; positivity
  have hT4 : 4 * √2 * K0 * wn n * n * piBar (rhoBar n csC) ≤ 1 / 10 ^ 11 := by
    have ha : 4 * √2 * K0 * wn n ≤ 4 * (141422 / 100000) * (9085 / 100000) *
        (1044683 / 1000000) :=
      mul_le_mul (mul_le_mul (by linarith) hK hK0.le (by norm_num)) hw hw0 (by norm_num)
    have ha1 : 4 * √2 * K0 * wn n ≤ 1 := ha.trans (by norm_num)
    have hnP0 : 0 ≤ (n : ℝ) * piBar (rhoBar n csC) := mul_nonneg hnpos.le hP0.le
    calc 4 * √2 * K0 * wn n * n * piBar (rhoBar n csC)
        = 4 * √2 * K0 * wn n * ((n : ℝ) * piBar (rhoBar n csC)) := by ring
      _ ≤ 1 * ((n : ℝ) * piBar (rhoBar n csC)) := mul_le_mul_of_nonneg_right ha1 hnP0
      _ ≤ 1 / 10 ^ 11 := by linarith
  refine ⟨?_, ?_, hb0, hb⟩
  · unfold xiCn xiC; linarith
  · unfold xiCn xiC
    have : (3290 / 10000 : ℝ) + 523 / 100000 + 231 / 100000 + 1 / 10 ^ 11 ≤ 3370 / 10000 := by
      norm_num
    linarith

theorem eMP_leA8 {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 457 / 1000 ≤ θ) (h1 : θ ≤ 555 / 1000) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 := by
  have hn' := n_ge_NumA hn
  obtain ⟨hx0, hx, hb0, hb⟩ := xiCn_leA8 hn h0 h1
  have hπ0 := Real.pi_pos
  have hπ := Real.pi_lt_d6
  have hden : (0 : ℝ) < n * (1 - 11 / 1000) := by nlinarith
  have hπb : π * bN n csC θ ≤ 4 * (231 / 100000) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  have hπx : π * xiCn n θ ≤ 4 * (3370 / 10000) :=
    mul_le_mul (by linarith) hx hx0 (by norm_num)
  have hA : √(π * bN n csC θ / (n * (1 - 11 / 1000))) ≤ 1 / 40 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hden]
    nlinarith
  have hB : π * xiCn n θ / (n * (1 - 11 / 1000)) ≤ 1 / 20 := by
    rw [div_le_iff₀ hden]
    nlinarith
  unfold eMP
  linarith

end BstLean.Part154
