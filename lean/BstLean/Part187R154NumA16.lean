import BstLean.Part154NumA16
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final

/-! Part 187 (file `Part187R154NumA16`): copy of `Part154NumA16` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part154.R

open Real
open BstLean.Part153 (wn phiG)

lemma sqrt_n_ge_NumA16 {n : ℕ} (hn : 16250 ≤ n) : (127 : ℝ) ≤ √(n : ℝ) := by
  rw [Real.le_sqrt' (by norm_num)]
  have h : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  exact le_trans (by norm_num) h

lemma wn_bounds_NumA16 {n : ℕ} (hn : 16250 ≤ n) : 1 ≤ wn n ∧ wn n ≤ 1031745 / 1000000 := by
  have hs := sqrt_n_ge_NumA16 hn
  have h2 : 2 / √(n : ℝ) ≤ 2 / 127 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h0 : 0 ≤ 2 / √(n : ℝ) := by positivity
  unfold wn
  constructor
  · nlinarith
  · calc (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / 127) ^ 2 := by gcongr
      _ ≤ 1031745 / 1000000 := by norm_num

lemma cHSK_bounds_NumA16 {n : ℕ} (hn : 16250 ≤ n) :
    1 ≤ cHSK n K0 ∧ cHSK n K0 ≤ 100520 / 100000 := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hK := K0_bounds_NumA
  have hsq0 : 0 ≤ √(12 / ((n : ℝ) - 4)) := Real.sqrt_nonneg _
  have hsq : √(12 / ((n : ℝ) - 4)) ≤ 2718 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hprod : K0 * √(12 / ((n : ℝ) - 4)) ≤ 9085 / 100000 * (2718 / 100000) :=
    mul_le_mul hK.2 hsq hsq0 (by norm_num)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlast : 4 * (1 + 2 / (n : ℝ)) / n ≤ 4 * (1 + 2 / 16250) / 16250 :=
    div_le_div₀ (by norm_num)
      (by have : 2 / (n : ℝ) ≤ 2 / 16250 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
          linarith) (by norm_num) hn'
  refine ⟨(cHSK_bounds_NumA (le_trans (by norm_num) hn)).1, ?_⟩
  unfold cHSK
  have hK0 := hK.1.le
  calc (1 + K0 * √(12 / ((n : ℝ) - 4))) ^ 2 + 4 * (1 + 2 / (n : ℝ)) / n
      ≤ (1 + 9085 / 100000 * (2718 / 100000)) ^ 2 + 4 * (1 + 2 / 16250) / 16250 := by
        gcongr
    _ ≤ 100520 / 100000 := by norm_num

lemma aHn_bounds_NumA16 {n : ℕ} (hn : 16250 ≤ n) : 0 ≤ aHn n ∧ aHn n ≤ 4841 / 1000000 := by
  have hs := sqrt_n_ge_NumA16 hn
  have hc := (cHSK_bounds_NumA16 hn).1
  have hss : (112694 / 10000 : ℝ) ≤ √(√(n : ℝ)) := by
    rw [Real.le_sqrt' (by norm_num)]
    exact le_trans (by norm_num) hs
  have h4 : (14142 / 10000 : ℝ) ≤ √(√(4 * cHSK n K0)) := by
    rw [Real.le_sqrt' (by norm_num), Real.le_sqrt' (by norm_num)]
    have : ((14142 / 10000 : ℝ) ^ 2) ^ 2 ≤ 4 := by norm_num
    linarith
  have h24 : √(24 : ℝ) ≤ 4899 / 1000 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hden : (14142 / 10000 : ℝ) * (127 * (112694 / 10000)) ≤
      √(√(4 * cHSK n K0)) * (√(n : ℝ) * √(√(n : ℝ))) :=
    mul_le_mul h4 (mul_le_mul hs hss (by norm_num) (by positivity)) (by norm_num) (by positivity)
  refine ⟨(aHn_bounds_NumA (le_trans (by norm_num) hn)).1, ?_⟩
  unfold aHn
  calc 2 * √24 / (√(√(4 * cHSK n K0)) * (√(n : ℝ) * √(√(n : ℝ))))
      ≤ 2 * (4899 / 1000) / ((14142 / 10000 : ℝ) * (127 * (112694 / 10000))) :=
        div_le_div₀ (by norm_num) (by linarith) (by norm_num) hden
    _ ≤ 4841 / 1000000 := by norm_num

lemma hHn_bounds_NumA16 {n : ℕ} (hn : 16250 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) :
    1 ≤ hHn n θ ∧ hHn n θ ≤ 102886 / 100000 := by
  have ha := aHn_bounds_NumA16 hn
  have hθ : (6782 / 10000 : ℝ) ≤ √θ := by
    rw [Real.le_sqrt' (by norm_num)]
    exact le_trans (by norm_num) h0
  have hq0 : 0 ≤ aHn n / √θ := div_nonneg ha.1 (Real.sqrt_nonneg _)
  have hq : aHn n / √θ ≤ 4841 / 1000000 / (6782 / 10000) :=
    div_le_div₀ (by norm_num) ha.2 (by norm_num) hθ
  unfold hHn
  constructor
  · exact one_le_pow₀ (by linarith)
  · calc (1 + aHn n / √θ) ^ 4 ≤ (1 + 4841 / 1000000 / (6782 / 10000)) ^ 4 := by gcongr
      _ ≤ 102886 / 100000 := by norm_num

/-- `0 < ϱ̄`, `3 ≤ ϱ̄ n ≤ 3.1864`, `ϱ̄ ≤ 1.9609·10⁻⁴`. -/
lemma rhoBar_facts_NumA16 {n : ℕ} (hn : 16250 ≤ n) :
    0 < rhoBar n csC ∧ 3 ≤ rhoBar n csC * n ∧ rhoBar n csC * n ≤ 31864 / 10000 ∧
      rhoBar n csC ≤ 19609 / 100000000 := by
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨h0, h3, -, -⟩ := rhoBar_facts_NumA (le_trans (by norm_num) hn)
  have hw := wn_bounds_NumA16 hn
  have hc := csC_bounds_NumA
  have hcpos : 0 < csC := by linarith
  have h5 : rhoBar n csC * n ≤ 31864 / 10000 := by
    have : rhoBar n csC * n = 4 * wn n / csC := by
      unfold rhoBar; field_simp
    rw [this, div_le_iff₀ hcpos]
    nlinarith
  refine ⟨h0, h3, h5, ?_⟩
  nlinarith

/-- `0 ≤ b_n(θ) ≤ 0.00112`. -/
lemma bN_bounds_NumA16 {n : ℕ} (hn : 16250 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ)
    (h1 : θ ≤ 55 / 100) : 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 112 / 100000 := by
  obtain ⟨hρ0, -, -, hρ⟩ := rhoBar_facts_NumA16 hn
  obtain ⟨hQ0, hQ⟩ := QB_bounds_NumA (le_trans (by norm_num) hn)
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA16 hn
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  unfold bN
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) hQ0) hρ0.le
  · rw [div_le_iff₀ hρ0]
    have hA : 4 * θ * wn n ≤ 4 * (55 / 100) * (1031745 / 1000000) :=
      mul_le_mul (by linarith) hw hw0 (by norm_num)
    have hB : 4 * θ * wn n * QB (rhoBar n csC) (piBar (rhoBar n csC)) ≤
        4 * (55 / 100) * (1031745 / 1000000) * (25146 / 10000 * rhoBar n csC ^ 2) :=
      mul_le_mul hA hQ hQ0 (by norm_num)
    have hC : rhoBar n csC ^ 2 ≤ 19609 / 100000000 * rhoBar n csC := by nlinarith
    linarith


theorem rhoBar_ltA16 {n : ℕ} (hn : 16250 ≤ n) : rhoBar n csC < 1 / 4 := by
  have := (rhoBar_facts_NumA16 hn).2.2.2
  linarith

private lemma mul5A16 {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (la : a ≤ a') (lb : b ≤ b') (lc : c ≤ c') (ld : d ≤ d') :
    a * b * 8 * c * d ≤ a' * b' * 8 * c' * d' := by
  have ha' : 0 ≤ a' := ha.trans la
  have hb' : 0 ≤ b' := hb.trans lb
  have hc' : 0 ≤ c' := hc.trans lc
  gcongr

/-- `ξ_c(θ) ≤ 0.3285`, `b_n(θ) ≤ 0.00225`. -/
theorem xiCn_leA16 {n : ℕ} (hn : 16250 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    0 ≤ xiCn n θ ∧ xiCn n θ ≤ 3235 / 10000 ∧ 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 112 / 100000 := by
  have hn8 : 8192 ≤ n := le_trans (by norm_num) hn
  have hn' := n_ge_NumA hn8
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := rhoBar_facts_NumA16 hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA16 hn
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨hcH1, hcH⟩ := cHSK_bounds_NumA16 hn
  obtain ⟨hh1, hh⟩ := hHn_bounds_NumA16 hn h0
  obtain ⟨hP0, hP⟩ := piBar_le_rho_NumA hn8
  have hnP := piBar_le_NumA hn8
  obtain ⟨hν0, hν⟩ := nuR_bounds_NumA hn8
  obtain ⟨hb0, hb⟩ := bN_bounds_NumA16 hn h0 h1
  obtain ⟨hs2, hs2'⟩ := sqrt2_bounds_NumA
  have hπ := Real.pi_gt_d6
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  have hcs0 : 0 < csC := by linarith
  have hcH0 : 0 ≤ cHSK n K0 := by linarith
  have hhH0 : 0 ≤ hHn n θ := by linarith
  -- first term
  have hq0 : 0 ≤ cHSK n K0 / csC := div_nonneg hcH0 hcs0.le
  have hq : cHSK n K0 / csC ≤ 100520 / 100000 / (129521 / 100000) :=
    div_le_div₀ (by norm_num) hcH (by norm_num) hcs1
  have hT1 := mul5A16 hθ0 hq0 hK0.le hhH0 h1 hq hK hh
  have hT1' : (55 / 100 : ℝ) * (100520 / 100000 / (129521 / 100000)) * 8 * (9085 / 100000) *
      (102886 / 100000) ≤ 3192 / 10000 := by norm_num
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
      31864 / 10000 * (40004 / 10000 * (19609 / 100000000)) :=
    mul_le_mul hρn (hν.trans (by linarith)) hν0 (by norm_num)
  have hM : 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) ≤
      68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19609 / 100000000))) := by
    have := mul_le_mul hr2' hρnν hρnν0 (by norm_num)
    calc 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)
        = 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := by ring
      _ ≤ _ := this
  have hM0 : 0 ≤ 4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC) := by
    have := mul_nonneg hr2'' hρnν0
    calc (0 : ℝ) ≤ 4 * (√2 - 1) ^ 2 * (rhoBar n csC * n * nuR (rhoBar n csC)) := this
      _ = _ := by ring
  have hθρ0 : 0 ≤ 2 * θ * rhoBar n csC := by positivity
  have hθρ : 2 * θ * rhoBar n csC ≤ 2 * (55 / 100) * (19609 / 100000000) :=
    mul_le_mul (by linarith) hρ hρ0.le (by norm_num)
  have hfrac : (2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π ≤
      (2 * (55 / 100) * (19609 / 100000000) +
        68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19609 / 100000000)))) / 3.141592 :=
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
      4 * (1031745 / 1000000) * ((2 * (55 / 100) * (19609 / 100000000) +
        68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19609 / 100000000)))) / 3.141592 +
          1 / 10 ^ 11) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hT2' : (4 : ℝ) * (1031745 / 1000000) * ((2 * (55 / 100) * (19609 / 100000000) +
        68632 / 100000 * (31864 / 10000 * (40004 / 10000 * (19609 / 100000000)))) / 3.141592 +
          1 / 10 ^ 11) ≤ 254 / 100000 := by norm_num
  have hT2_0 : 0 ≤ 4 * wn n * ((2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π +
        θ * piBar (rhoBar n csC)) :=
    mul_nonneg (by linarith) (by linarith)
  -- fourth term
  have hT4_0 : 0 ≤ 4 * √2 * K0 * wn n * n * piBar (rhoBar n csC) := by
    have := hK0.le; have := hP0.le; positivity
  have hT4 : 4 * √2 * K0 * wn n * n * piBar (rhoBar n csC) ≤ 1 / 10 ^ 11 := by
    have ha : 4 * √2 * K0 * wn n ≤ 4 * (141422 / 100000) * (9085 / 100000) *
        (1031745 / 1000000) :=
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
    have : (3192 / 10000 : ℝ) + 254 / 100000 + 112 / 100000 + 1 / 10 ^ 11 ≤ 3235 / 10000 := by
      norm_num
    linarith

theorem eMP_leA16 {n : ℕ} (hn : 16250 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 := by
  have hn' := n_ge_NumA (le_trans (by norm_num) hn)
  obtain ⟨hx0, hx, hb0, hb⟩ := xiCn_leA16 hn h0 h1
  have hπ0 := Real.pi_pos
  have hπ := Real.pi_lt_d6
  have hden : (0 : ℝ) < n * (1 - 11 / 1000) := by nlinarith
  have hπb : π * bN n csC θ ≤ 4 * (112 / 100000) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  have hπx : π * xiCn n θ ≤ 4 * (3235 / 10000) :=
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

end BstLean.Part154.R
