import BstLean.Part154Event

/-!
# Part 154: the numbers of the centre bounds, first half (`rhoBar`, `xiCn`, `bN`, `eMP`)
for `n ≥ 8192`, `0.46 ≤ θ ≤ 0.541`.
-/

namespace BstLean.Part154

open Real
open BstLean.Part153 (wn phiG)

/-! ## Elementary constants -/

lemma n_ge_NumA {n : ℕ} (hn : 8192 ≤ n) : (8192 : ℝ) ≤ n := by exact_mod_cast hn

lemma sqrt_n_ge_NumA {n : ℕ} (hn : 8192 ≤ n) : (905096 / 10000 : ℝ) ≤ √(n : ℝ) := by
  rw [Real.le_sqrt' (by norm_num)]
  have h : (905096 / 10000 : ℝ) ^ 2 ≤ 8192 := by norm_num
  exact h.trans (n_ge_NumA hn)

lemma sqrt2_bounds_NumA : (141421 / 100000 : ℝ) ≤ √2 ∧ √2 ≤ 141422 / 100000 := by
  constructor
  · rw [Real.le_sqrt' (by norm_num)]; norm_num
  · rw [Real.sqrt_le_iff]; norm_num

lemma wn_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) : 1 ≤ wn n ∧ wn n ≤ 1044683 / 1000000 := by
  have hs := sqrt_n_ge_NumA hn
  have h2 : 2 / √(n : ℝ) ≤ 2 / (905096 / 10000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have h0 : 0 ≤ 2 / √(n : ℝ) := by positivity
  unfold wn
  constructor
  · nlinarith
  · calc (1 + 2 / √(n : ℝ)) ^ 2 ≤ (1 + 2 / (905096 / 10000)) ^ 2 := by gcongr
      _ ≤ 1044683 / 1000000 := by norm_num

lemma wn_le_NumA {n : ℕ} (hn : 8192 ≤ n) : wn n ≤ 10447 / 10000 :=
  (wn_bounds_NumA hn).2.trans (by norm_num)

lemma csC_bounds_NumA : (129521 / 100000 : ℝ) ≤ csC ∧ csC ≤ 129522 / 100000 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hp : (0 : ℝ) < π := Real.pi_pos
  have ha : 1 / π ≤ 1 / 3.141592 := one_div_le_one_div_of_le (by norm_num) h1.le
  have hb : 1 / 3.141593 ≤ 1 / π := one_div_le_one_div_of_le hp h2.le
  unfold csC
  constructor
  · have : (129521 / 100000 : ℝ) ≤ 0.95 * 2 * (1 - 1 / 3.141592) := by norm_num
    linarith
  · have : (0.95 : ℝ) * 2 * (1 - 1 / 3.141593) ≤ 129522 / 100000 := by norm_num
    linarith

lemma K0_bounds_NumA : 0 < K0 ∧ K0 ≤ 9085 / 100000 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hp : (0 : ℝ) < π := Real.pi_pos
  unfold K0
  constructor
  · apply div_pos <;> linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

lemma K0_le_NumA : K0 ≤ 9085 / 100000 := K0_bounds_NumA.2

lemma cHSK_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) :
    1 ≤ cHSK n K0 ∧ cHSK n K0 ≤ 100746 / 100000 := by
  have hn' := n_ge_NumA hn
  have hK := K0_bounds_NumA
  have hsq0 : 0 ≤ √(12 / ((n : ℝ) - 4)) := Real.sqrt_nonneg _
  have hsq : √(12 / ((n : ℝ) - 4)) ≤ 3829 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hprod0 : 0 ≤ K0 * √(12 / ((n : ℝ) - 4)) := mul_nonneg hK.1.le hsq0
  have hprod : K0 * √(12 / ((n : ℝ) - 4)) ≤ 9085 / 100000 * (3829 / 100000) :=
    mul_le_mul hK.2 hsq hsq0 (by norm_num)
  have hnpos : (0 : ℝ) < n := by linarith
  have h2n : 2 / (n : ℝ) ≤ 2 / 8192 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn'
  have h2n0 : 0 ≤ 2 / (n : ℝ) := by positivity
  have hlast0 : 0 ≤ 4 * (1 + 2 / (n : ℝ)) / n := by positivity
  have hlast : 4 * (1 + 2 / (n : ℝ)) / n ≤ 4 * (1 + 2 / 8192) / 8192 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) hn'
  unfold cHSK
  constructor
  · nlinarith
  · calc (1 + K0 * √(12 / ((n : ℝ) - 4))) ^ 2 + 4 * (1 + 2 / (n : ℝ)) / n
        ≤ (1 + 9085 / 100000 * (3829 / 100000)) ^ 2 + 4 * (1 + 2 / 8192) / 8192 := by
          gcongr
      _ ≤ 100746 / 100000 := by norm_num

lemma cHSK_le_NumA {n : ℕ} (hn : 8192 ≤ n) : cHSK n K0 ≤ 100746 / 100000 :=
  (cHSK_bounds_NumA hn).2

lemma aHn_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) : 0 ≤ aHn n ∧ aHn n ≤ 805 / 100000 := by
  have hs := sqrt_n_ge_NumA hn
  have hc := (cHSK_bounds_NumA hn).1
  have hss : (95136 / 10000 : ℝ) ≤ √(√(n : ℝ)) := by
    rw [Real.le_sqrt' (by norm_num)]
    exact le_trans (by norm_num) hs
  have h4 : (14142 / 10000 : ℝ) ≤ √(√(4 * cHSK n K0)) := by
    rw [Real.le_sqrt' (by norm_num), Real.le_sqrt' (by norm_num)]
    have : ((14142 / 10000 : ℝ) ^ 2) ^ 2 ≤ 4 := by norm_num
    linarith
  have h24 : √(24 : ℝ) ≤ 4899 / 1000 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hden : (14142 / 10000 : ℝ) * (905096 / 10000 * (95136 / 10000)) ≤
      √(√(4 * cHSK n K0)) * (√(n : ℝ) * √(√(n : ℝ))) :=
    mul_le_mul h4 (mul_le_mul hs hss (by norm_num) (by positivity)) (by norm_num) (by positivity)
  unfold aHn
  constructor
  · positivity
  · calc 2 * √24 / (√(√(4 * cHSK n K0)) * (√(n : ℝ) * √(√(n : ℝ))))
        ≤ 2 * (4899 / 1000) / ((14142 / 10000 : ℝ) * (905096 / 10000 * (95136 / 10000))) :=
          div_le_div₀ (by norm_num) (by linarith) (by norm_num) hden
      _ ≤ 805 / 100000 := by norm_num

lemma hHn_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) :
    1 ≤ hHn n θ ∧ hHn n θ ≤ 10484 / 10000 := by
  have ha := aHn_bounds_NumA hn
  have hθ : (6782 / 10000 : ℝ) ≤ √θ := by
    rw [Real.le_sqrt' (by norm_num)]
    exact le_trans (by norm_num) h0
  have hq0 : 0 ≤ aHn n / √θ := div_nonneg ha.1 (Real.sqrt_nonneg _)
  have hq : aHn n / √θ ≤ 805 / 100000 / (6782 / 10000) :=
    div_le_div₀ (by norm_num) ha.2 (by norm_num) hθ
  unfold hHn
  constructor
  · exact one_le_pow₀ (by linarith)
  · calc (1 + aHn n / √θ) ^ 4 ≤ (1 + 805 / 100000 / (6782 / 10000)) ^ 4 := by gcongr
      _ ≤ 10484 / 10000 := by norm_num

lemma hHn_le_NumA {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) :
    hHn n θ ≤ 10484 / 10000 := (hHn_bounds_NumA hn h0).2

/-! ## `ϱ̄` and `π̄` -/

lemma rhoBar_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) :
    3 / (n : ℝ) ≤ rhoBar n csC ∧ rhoBar n csC ≤ 32263 / (10000 * (n : ℝ)) := by
  have hn' := n_ge_NumA hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hw := wn_bounds_NumA hn
  have hc := csC_bounds_NumA
  have hcpos : 0 < csC := by linarith
  unfold rhoBar
  constructor
  · rw [div_le_div_iff₀ hnpos (by positivity)]
    have : 3 * csC ≤ 4 * wn n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hnpos.le]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * wn n * 10000 ≤ 32263 * csC := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hnpos.le]

/-- `0 < ϱ̄`, `3 ≤ ϱ̄ n ≤ 3.2263`, `ϱ̄ ≤ 3.94·10⁻⁴`. -/
lemma rhoBar_facts_NumA {n : ℕ} (hn : 8192 ≤ n) :
    0 < rhoBar n csC ∧ 3 ≤ rhoBar n csC * n ∧ rhoBar n csC * n ≤ 32263 / 10000 ∧
      rhoBar n csC ≤ 394 / 1000000 := by
  have hn' := n_ge_NumA hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨h1, h2⟩ := rhoBar_bounds_NumA hn
  have h3 : (0 : ℝ) < 3 / n := by positivity
  have h4 : 3 ≤ rhoBar n csC * n := by
    rw [div_le_iff₀ hnpos] at h1; exact h1
  have h5 : rhoBar n csC * n ≤ 32263 / 10000 := by
    rw [le_div_iff₀ (by positivity)] at h2; linarith
  refine ⟨by linarith, h4, h5, ?_⟩
  have : (32263 : ℝ) / (10000 * n) ≤ 32263 / (10000 * 8192) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  exact h2.trans (this.trans (by norm_num))

private lemma exp_boundA {y : ℝ} (hy : (134 / 10 : ℝ) ≤ y) :
    608 * y * rexp (-(8 * y)) ≤ 1 / 10 ^ 11 := by
  have h0 : 0 ≤ y := by linarith
  have h1 : y ^ 2 / 2 ≤ rexp y := by
    have := Real.quadratic_le_exp_of_nonneg h0; linarith
  have h2 : (y ^ 2 / 2) ^ 8 ≤ rexp (8 * y) := by
    have : rexp (8 * y) = rexp y ^ 8 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]; gcongr
  have h3 : (134 / 10 : ℝ) ^ 15 ≤ y ^ 15 := by gcongr
  have h5 : (608 : ℝ) * 256 * 10 ^ 11 ≤ y ^ 15 := le_trans (by norm_num) h3
  have h6 := mul_le_mul_of_nonneg_left h5 h0
  have h4 : 608 * y * 10 ^ 11 ≤ (y ^ 2 / 2) ^ 8 := by
    have : (y ^ 2 / 2) ^ 8 = y * y ^ 15 / 256 := by ring
    rw [this]; linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- `n·π̄(ϱ̄) ≤ 10⁻¹¹`. -/
lemma piBar_le_NumA {n : ℕ} (hn : 8192 ≤ n) :
    (n : ℝ) * piBar (rhoBar n csC) ≤ 1 / 10 ^ 11 := by
  have hn' := n_ge_NumA hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, -, hρn, hρ⟩ := rhoBar_facts_NumA hn
  have hs2 := sqrt2_bounds_NumA
  have ha : (9992 / 10000 : ℝ) ≤ √(1 - 2 * rhoBar n csC) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((9992 / 10000 : ℝ)) ^ 2 ≤ 1 - 2 * (394 / 1000000) := by norm_num
    linarith
  have hb : 1 / √2 ≤ 1 / (141421 / 100000 : ℝ) := one_div_le_one_div_of_le (by norm_num) hs2.1
  have hd : (29209 / 100000 : ℝ) ≤ √(1 - 2 * rhoBar n csC) - 1 / √2 := by
    have : (1 : ℝ) / (141421 / 100000) ≤ 70711 / 100000 := by norm_num
    linarith
  have hsq : (853 / 10000 : ℝ) ≤ (√(1 - 2 * rhoBar n csC) - 1 / √2) ^ 2 := by
    have : (853 / 10000 : ℝ) ≤ (29209 / 100000) ^ 2 := by norm_num
    exact this.trans (pow_le_pow_left₀ (by norm_num) hd 2)
  have hE : 8 * ((n : ℝ) / 608) ≤
      (√(1 - 2 * rhoBar n csC) - 1 / √2) ^ 2 / (2 * rhoBar n csC) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hpi : piBar (rhoBar n csC) ≤ rexp (-(8 * ((n : ℝ) / 608))) := by
    unfold piBar
    exact Real.exp_le_exp.mpr (neg_le_neg hE)
  have hy : (134 / 10 : ℝ) ≤ (n : ℝ) / 608 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have := exp_boundA hy
  calc (n : ℝ) * piBar (rhoBar n csC) ≤ (n : ℝ) * rexp (-(8 * ((n : ℝ) / 608))) :=
        mul_le_mul_of_nonneg_left hpi hnpos.le
    _ = 608 * ((n : ℝ) / 608) * rexp (-(8 * ((n : ℝ) / 608))) := by ring
    _ ≤ 1 / 10 ^ 11 := this

/-- `0 < π̄(ϱ̄) ≤ ϱ̄/(3·10¹¹)`. -/
lemma piBar_le_rho_NumA {n : ℕ} (hn : 8192 ≤ n) :
    0 < piBar (rhoBar n csC) ∧ 3 * piBar (rhoBar n csC) ≤ rhoBar n csC / 10 ^ 11 := by
  have hn' := n_ge_NumA hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, -, -⟩ := rhoBar_facts_NumA hn
  have hP0 : 0 < piBar (rhoBar n csC) := Real.exp_pos _
  have hP := piBar_le_NumA hn
  refine ⟨hP0, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hρn3 hP0.le
  have h2 := mul_le_mul_of_nonneg_left hP hρ0.le
  have : 3 * piBar (rhoBar n csC) ≤ rhoBar n csC * (1 / 10 ^ 11) := by nlinarith
  linarith

/-! ## `Q_B` and `b_n` -/

lemma phiG_bounds_NumA :
    0 < phiG 0 ∧ phiG 0 ≤ 39895 / 100000 ∧ 0 < phiG 1 ∧ phiG 1 ≤ 24198 / 100000 := by
  have h1 := Real.pi_gt_d6
  have hsq : (25066 / 10000 : ℝ) ≤ √(2 * π) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : (25066 / 10000 : ℝ) ^ 2 ≤ 2 * 3.141592 := by norm_num
    linarith
  have hinv0 : 0 < (√(2 * π))⁻¹ := by positivity
  have hinv : (√(2 * π))⁻¹ ≤ 398947 / 1000000 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    exact le_trans (by norm_num) hsq
  have he : rexp (-(1 ^ 2 / 2 : ℝ)) ≤ 60654 / 100000 := by
    have hh : (16487 / 10000 : ℝ) ≤ rexp (1 / 2) := by
      by_contra hcon
      rw [not_le] at hcon
      have hpos := Real.exp_pos (1 / 2 : ℝ)
      have h2 : rexp (1 / 2) * rexp (1 / 2) = rexp 1 := by
        rw [← Real.exp_add]; norm_num
      have h3 := Real.exp_one_gt_d9
      nlinarith
    have : rexp (-(1 ^ 2 / 2 : ℝ)) = (rexp (1 / 2))⁻¹ := by
      rw [← Real.exp_neg]; norm_num
    rw [this, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    exact le_trans (by norm_num) hh
  refine ⟨BstLean.Part153.phiG_pos 0, ?_, BstLean.Part153.phiG_pos 1, ?_⟩
  · unfold phiG
    have : rexp (-((0 : ℝ) ^ 2 / 2)) = 1 := by norm_num
    rw [this, mul_one]
    exact hinv.trans (by norm_num)
  · unfold phiG
    calc (√(2 * π))⁻¹ * rexp (-(1 ^ 2 / 2 : ℝ))
        ≤ 398947 / 1000000 * (60654 / 100000) :=
          mul_le_mul hinv he (Real.exp_pos _).le (by norm_num)
      _ ≤ 24198 / 100000 := by norm_num

private lemma QB_monoA {c0 c1 c2 s a0 a1 a2 t : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (h2 : 0 ≤ c2)
    (hs : 0 ≤ s) (l0 : c0 ≤ a0) (l1 : c1 ≤ a1) (l2 : c2 ≤ a2) (ls : s ≤ t) :
    c0 ^ 2 + c1 ^ 2 + 3 * c2 ^ 2 + 2 * s * c0 * c1 + 2 * c0 * c2 + 4 * s * c1 * c2 ≤
      a0 ^ 2 + a1 ^ 2 + 3 * a2 ^ 2 + 2 * t * a0 * a1 + 2 * a0 * a2 + 4 * t * a1 * a2 := by
  have ha0 : 0 ≤ a0 := h0.trans l0
  have ha1 : 0 ≤ a1 := h1.trans l1
  have ha2 : 0 ≤ a2 := h2.trans l2
  have ht : 0 ≤ t := hs.trans ls
  gcongr

/-- `0 ≤ ν(ϱ̄) ≤ 4.0004 ϱ̄`. -/
lemma nuR_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ nuR (rhoBar n csC) ∧ nuR (rhoBar n csC) ≤ 40004 / 10000 * rhoBar n csC := by
  obtain ⟨hρ0, -, -, hρ⟩ := rhoBar_facts_NumA hn
  unfold nuR
  constructor
  · positivity
  · nlinarith

/-- `0 ≤ 𝔠_i`, `𝔠₀ ≤ 0.764ϱ̄`, `𝔠₁ ≤ 0.4841ϱ̄`, `𝔠₂ ≤ 0.2822ϱ̄`. -/
lemma cc_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ cc0 (rhoBar n csC) (piBar (rhoBar n csC)) ∧
    cc0 (rhoBar n csC) (piBar (rhoBar n csC)) ≤ 764 / 1000 * rhoBar n csC ∧
    0 ≤ cc1 (rhoBar n csC) (piBar (rhoBar n csC)) ∧
    cc1 (rhoBar n csC) (piBar (rhoBar n csC)) ≤ 4841 / 10000 * rhoBar n csC ∧
    0 ≤ cc2 (rhoBar n csC) ∧ cc2 (rhoBar n csC) ≤ 2822 / 10000 * rhoBar n csC := by
  obtain ⟨hρ0, -, -, hρ⟩ := rhoBar_facts_NumA hn
  obtain ⟨hP0, hP⟩ := piBar_le_rho_NumA hn
  obtain ⟨hν0, hν⟩ := nuR_bounds_NumA hn
  obtain ⟨hp0, hp0', hp1, hp1'⟩ := phiG_bounds_NumA
  obtain ⟨hs2, -⟩ := sqrt2_bounds_NumA
  set ρ := rhoBar n csC with hρdef
  set P := piBar ρ with hPdef
  have hP' : P ≤ ρ / (3 * 10 ^ 11) := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hS1 : √(P * nuR ρ) ≤ ρ / 10 ^ 5 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc P * nuR ρ ≤ ρ / (3 * 10 ^ 11) * (40004 / 10000 * ρ) :=
          mul_le_mul hP' hν hν0 (by positivity)
      _ ≤ (ρ / 10 ^ 5) ^ 2 := by nlinarith [sq_nonneg ρ]
  have hS2 : √(ρ * nuR ρ) ≤ 20001 / 10000 * ρ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc ρ * nuR ρ ≤ ρ * (40004 / 10000 * ρ) := mul_le_mul_of_nonneg_left hν hρ0.le
      _ ≤ (20001 / 10000 * ρ) ^ 2 := by nlinarith [sq_nonneg ρ]
  have hS3 : √(P * ρ) ≤ ρ / 10 ^ 5 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc P * ρ ≤ ρ / (3 * 10 ^ 11) * ρ := mul_le_mul_of_nonneg_right hP' hρ0.le
      _ ≤ (ρ / 10 ^ 5) ^ 2 := by nlinarith [sq_nonneg ρ]
  have hs2pos : (0 : ℝ) < √2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cc0; positivity
  · unfold cc0
    have hA : phiG 0 * ρ ≤ 39895 / 100000 * ρ := mul_le_mul_of_nonneg_right hp0' hρ0.le
    have hB : phiG 0 * nuR ρ / (2 * √2) ≤ 5643 / 10000 * ρ := by
      have h := div_le_div₀ (c := 39895 / 100000 * (40004 / 10000 * ρ))
        (d := 2 * (141421 / 100000)) (by positivity)
        (mul_le_mul hp0' hν hν0 (by norm_num)) (by norm_num)
        (show 2 * (141421 / 100000 : ℝ) ≤ 2 * √2 by linarith)
      have h' : 39895 / 100000 * (40004 / 10000 * ρ) / (2 * (141421 / 100000)) ≤
          5643 / 10000 * ρ := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      exact h.trans h'
    have hC : 3 / 2 * phiG 0 * √(P * nuR ρ) ≤ 1 / 10000 * ρ := by
      have h : 3 / 2 * phiG 0 * √(P * nuR ρ) ≤ 3 / 2 * (39895 / 100000) * (ρ / 10 ^ 5) :=
        mul_le_mul (by linarith) hS1 (Real.sqrt_nonneg _) (by norm_num)
      have h' : 3 / 2 * (39895 / 100000) * (ρ / 10 ^ 5) ≤ 1 / 10000 * ρ := by nlinarith
      exact h.trans h'
    have hsum : phiG 0 * ρ / 2 ≤ 39895 / 100000 * ρ / 2 := by linarith
    linarith
  · unfold cc1; positivity
  · unfold cc1
    have hA : phiG 1 * √(ρ * nuR ρ) ≤ 24198 / 100000 * (20001 / 10000 * ρ) :=
      mul_le_mul hp1' hS2 (Real.sqrt_nonneg _) (by norm_num)
    linarith
  · unfold cc2; positivity
  · unfold cc2
    have hA : phiG 0 * ρ / √2 ≤ 39895 / 100000 * ρ / (141421 / 100000) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hp0' hρ0.le) (by norm_num) hs2
    linarith

/-- `0 ≤ Q_B(ϱ̄, π̄) ≤ 2.5146 ϱ̄²`. -/
lemma QB_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) :
    0 ≤ QB (rhoBar n csC) (piBar (rhoBar n csC)) ∧
    QB (rhoBar n csC) (piBar (rhoBar n csC)) ≤ 25146 / 10000 * rhoBar n csC ^ 2 := by
  obtain ⟨h0, l0, h1, l1, h2, l2⟩ := cc_bounds_NumA hn
  have hs0 : 0 ≤ √(2 / π) := Real.sqrt_nonneg _
  have hs : √(2 / π) ≤ 798 / 1000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ Real.pi_pos]
    have := Real.pi_gt_d6
    nlinarith
  unfold QB
  constructor
  · positivity
  · have := QB_monoA h0 h1 h2 hs0 l0 l1 l2 hs
    have h3 : (0 : ℝ) ≤ rhoBar n csC ^ 2 := sq_nonneg _
    nlinarith

/-- `0 ≤ b_n(θ) ≤ 0.00225`. -/
lemma bN_bounds_NumA {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    0 ≤ bN n csC θ ∧ bN n csC θ ≤ 225 / 100000 := by
  obtain ⟨hρ0, -, -, hρ⟩ := rhoBar_facts_NumA hn
  obtain ⟨hQ0, hQ⟩ := QB_bounds_NumA hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA hn
  have hθ0 : 0 ≤ θ := by linarith
  have hw0 : 0 ≤ wn n := by linarith
  unfold bN
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) hQ0) hρ0.le
  · rw [div_le_iff₀ hρ0]
    have hA : 4 * θ * wn n ≤ 4 * (541 / 1000) * (1044683 / 1000000) :=
      mul_le_mul (by linarith) hw hw0 (by norm_num)
    have hB : 4 * θ * wn n * QB (rhoBar n csC) (piBar (rhoBar n csC)) ≤
        4 * (541 / 1000) * (1044683 / 1000000) * (25146 / 10000 * rhoBar n csC ^ 2) :=
      mul_le_mul hA hQ hQ0 (by norm_num)
    have hC : rhoBar n csC ^ 2 ≤ 394 / 1000000 * rhoBar n csC := by nlinarith
    linarith

/-! ## The three statements -/

theorem rhoBar_ltA {n : ℕ} (hn : 8192 ≤ n) : rhoBar n csC < 1 / 4 := by
  have := (rhoBar_facts_NumA hn).2.2.2
  linarith

private lemma mul5A {a b c d a' b' c' d' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (la : a ≤ a') (lb : b ≤ b') (lc : c ≤ c') (ld : d ≤ d') :
    a * b * 8 * c * d ≤ a' * b' * 8 * c' * d' := by
  have ha' : 0 ≤ a' := ha.trans la
  have hb' : 0 ≤ b' := hb.trans lb
  have hc' : 0 ≤ c' := hc.trans lc
  gcongr

/-- `ξ_c(θ) ≤ 0.3285`, `b_n(θ) ≤ 0.00225`. -/
theorem xiCn_leA {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    0 ≤ xiCn n θ ∧ xiCn n θ ≤ 3285 / 10000 ∧ 0 ≤ bN n csC θ ∧ bN n csC θ ≤ 225 / 100000 := by
  have hn' := n_ge_NumA hn
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hρ0, hρn3, hρn, hρ⟩ := rhoBar_facts_NumA hn
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA hn
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨hcH1, hcH⟩ := cHSK_bounds_NumA hn
  obtain ⟨hh1, hh⟩ := hHn_bounds_NumA hn h0
  obtain ⟨hP0, hP⟩ := piBar_le_rho_NumA hn
  have hnP := piBar_le_NumA hn
  obtain ⟨hν0, hν⟩ := nuR_bounds_NumA hn
  obtain ⟨hb0, hb⟩ := bN_bounds_NumA hn h0 h1
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
  have hT1 := mul5A hθ0 hq0 hK0.le hhH0 h1 hq hK hh
  have hT1' : (541 / 1000 : ℝ) * (100746 / 100000 / (129521 / 100000)) * 8 * (9085 / 100000) *
      (10484 / 10000) ≤ 3207 / 10000 := by norm_num
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
  have hθρ : 2 * θ * rhoBar n csC ≤ 2 * (541 / 1000) * (394 / 1000000) :=
    mul_le_mul (by linarith) hρ hρ0.le (by norm_num)
  have hfrac : (2 * θ * rhoBar n csC +
      4 * (√2 - 1) ^ 2 * rhoBar n csC * n * nuR (rhoBar n csC)) / π ≤
      (2 * (541 / 1000) * (394 / 1000000) +
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
      4 * (1044683 / 1000000) * ((2 * (541 / 1000) * (394 / 1000000) +
        68632 / 100000 * (32263 / 10000 * (40004 / 10000 * (394 / 1000000)))) / 3.141592 +
          1 / 10 ^ 11) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hT2' : (4 : ℝ) * (1044683 / 1000000) * ((2 * (541 / 1000) * (394 / 1000000) +
        68632 / 100000 * (32263 / 10000 * (40004 / 10000 * (394 / 1000000)))) / 3.141592 +
          1 / 10 ^ 11) ≤ 522 / 100000 := by norm_num
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
    have : (3207 / 10000 : ℝ) + 522 / 100000 + 225 / 100000 + 1 / 10 ^ 11 ≤ 3285 / 10000 := by
      norm_num
    linarith

theorem eMP_leA {n : ℕ} (hn : 8192 ≤ n) {θ : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 541 / 1000) :
    eMP n (11 / 1000) (xiCn n θ) (bN n csC θ) ≤ 1 / 10 := by
  have hn' := n_ge_NumA hn
  obtain ⟨hx0, hx, hb0, hb⟩ := xiCn_leA hn h0 h1
  have hπ0 := Real.pi_pos
  have hπ := Real.pi_lt_d6
  have hden : (0 : ℝ) < n * (1 - 11 / 1000) := by nlinarith
  have hπb : π * bN n csC θ ≤ 4 * (225 / 100000) :=
    mul_le_mul (by linarith) hb hb0 (by norm_num)
  have hπx : π * xiCn n θ ≤ 4 * (3285 / 10000) :=
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
