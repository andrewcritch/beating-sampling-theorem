import BstLean.Part187All
import BstLean.Part160MFB3
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154C16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R154Num16
import BstLean.Part188R160Lib
import BstLean.Part188R160Event
import BstLean.Part188R160MFNum





namespace BstLean.Part188.Base160_R
open BstLean.Part160 BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part160.MFB
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 N2 sq2 hid2Mean_cr Pb wn N22bar)

/-- **A lower bound of `J`** on `θ_in ≥ θlo`, `n ≥ n₁`, with `S₀ = n − 2√(12n)`. -/
theorem JB_ge {n : ℕ} (hn : 16200 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {n1 θlo u Jlo : ℝ} (hn1 : 16200 ≤ n1) (hn1n : n1 ≤ n) (hlo0 : 0 < θlo)
    (hlo : θlo ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) (hu0 : 0 < u) (hu1 : 2 * u < 1)
    (hu : 12 ≤ u ^ 2 * n1) (_hJ0 : 0 ≤ Jlo)
    (hJ : Jlo ^ 2 * (1 + 2 * (1 - θlo) / (θlo * (1 - 2 * u))) ≤ 1) :
    0 < (n : ℝ) - 2 * √((n : ℝ) * 12) ∧ 0 < normSq c ∧
      Jlo ≤ JB c τ ((n : ℝ) - 2 * √((n : ℝ) * 12)) := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1' : 1 ≤ n := by omega
  have hθ0 : 0 < thetaC c τ := lt_of_lt_of_le hlo0 hlo
  have hsq : √((n : ℝ) * 12) ≤ n * u := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : 12 ≤ u ^ 2 * n := hu.trans (mul_le_mul_of_nonneg_left hn1n (sq_nonneg u))
    nlinarith
  have hS : (n : ℝ) * (1 - 2 * u) ≤ (n : ℝ) - 2 * √((n : ℝ) * 12) := by nlinarith
  have hS0 : 0 < (n : ℝ) - 2 * √((n : ℝ) * 12) :=
    lt_of_lt_of_le (mul_pos hn0 (by linarith)) hS
  have hc := normSq_c_eq hn1' c hτ
  have hc0 : 0 < normSq c := by
    rw [hc]
    have : 0 < 1 - thetaC c τ := by linarith
    positivity
  refine ⟨hS0, hc0, ?_⟩
  -- `|c|²/(τ²S₀) ≤ (1 − θlo)/(θlo(1 − 2u))`
  have hratio : normSq c / (τ ^ 2 * ((n : ℝ) - 2 * √((n : ℝ) * 12))) ≤
      (1 - θlo) / (θlo * (1 - 2 * u)) := by
    have hd' : 0 < 1 - 2 * u := by linarith
    have h1 : normSq c / (τ ^ 2 * ((n : ℝ) - 2 * √((n : ℝ) * 12))) ≤
        normSq c / (τ ^ 2 * ((n : ℝ) * (1 - 2 * u))) :=
      div_le_div_of_nonneg_left hc0.le (by positivity)
        (mul_le_mul_of_nonneg_left hS (by positivity))
    have h2 : normSq c / (τ ^ 2 * ((n : ℝ) * (1 - 2 * u))) =
        (1 - thetaC c τ) / (thetaC c τ * (1 - 2 * u)) := by
      rw [hc]
      have : (1 - 2 * u) ≠ 0 := by linarith
      field_simp
    have h3 : (1 - thetaC c τ) / (thetaC c τ * (1 - 2 * u)) ≤ (1 - θlo) / (θlo * (1 - 2 * u)) := by
      have hd : 0 < 1 - 2 * u := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hlo hd.le]
    linarith
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 1 + 2 * (normSq c / (τ ^ 2 * ((n : ℝ) - 2 * √((n : ℝ) * 12)))) :=
    ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by
    rw [hX]
    have : 0 ≤ normSq c / (τ ^ 2 * ((n : ℝ) - 2 * √((n : ℝ) * 12))) :=
      div_nonneg hc0.le (by positivity)
    linarith
  have hXle : X ≤ 1 + 2 * (1 - θlo) / (θlo * (1 - 2 * u)) := by
    rw [hX]
    have : 2 * (1 - θlo) / (θlo * (1 - 2 * u)) = 2 * ((1 - θlo) / (θlo * (1 - 2 * u))) := by ring
    linarith
  unfold JB
  rw [← hX]
  have hsX : 0 < √X := Real.sqrt_pos.mpr (by linarith)
  have hprod : Jlo * √X ≤ 1 := by
    have h2 : (Jlo * √X) ^ 2 ≤ 1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith), one_pow]
      exact (mul_le_mul_of_nonneg_left hXle (sq_nonneg Jlo)).trans hJ
    exact abs_le_of_sq_le_sq' h2 zero_le_one |>.2
  rw [inv_eq_one_div, le_div_iff₀ hsX]
  exact hprod

/-- **An upper bound of the constant `cHSB`** from the certificate `Jlo ≤ J`. -/
theorem cHSB_le {n : ℕ} (hn : 16200 ≤ n) (c : Fin n → ℝ) {τ S0 : ℝ} (hτ : 0 < τ) (hS0 : 0 < S0)
    {n1 Jlo sm : ℝ} (hn1 : 16200 ≤ n1) (hn1n : n1 ≤ n) (_hJ0 : 0 ≤ Jlo)
    (hJ : Jlo ≤ JB c τ S0) (hsm0 : 0 ≤ sm)
    (hsm : (1 - Jlo / 2 + 216 / 100000) * (1 - Jlo / 2 * (1 - 1 / n1) + 216 / 100000) +
      1 / (2 * n1) ≤ sm ^ 2) :
    cHSB n K0 (M1B n c τ S0) ≤ (sm + 248 / 100000) ^ 2 + 248 / 1000000 := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn10 : (0 : ℝ) < n1 := by linarith
  obtain ⟨hJB0, hJB1⟩ := JB_bounds c hτ hS0
  have he := epsB_le
  have he0 := epsB_pos
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨J, hJd⟩ : ∃ J : ℝ, J = JB c τ S0 := ⟨_, rfl⟩
  rw [← hJd] at hJ hJB0 hJB1
  -- `M1B ≤ sm²`
  have hinv : 1 / (n : ℝ) ≤ 1 / n1 := one_div_le_one_div_of_le hn10 hn1n
  have hq : 1 / 2 * (1 - 1 / n1) ≤ ((n : ℝ) - 1) / (2 * n) := by
    have e : ((n : ℝ) - 1) / (2 * n) = 1 / 2 * (1 - 1 / n) := by field_simp
    rw [e]; linarith
  have hq0 : 0 ≤ 1 / 2 * (1 - 1 / n1) := by
    have : 1 / n1 ≤ 1 := by rw [div_le_one hn10]; linarith
    linarith
  have hM : M1B n c τ S0 ≤ sm ^ 2 := by
    unfold M1B
    rw [← hJd]
    have f1 : 1 - J / 2 + epsB / 2 ≤ 1 - Jlo / 2 + 216 / 100000 := by linarith
    have f1' : 0 ≤ 1 - J / 2 + epsB / 2 := by linarith
    have hJq : Jlo * (1 / 2 * (1 - 1 / n1)) ≤ J * (((n : ℝ) - 1) / (2 * n)) :=
      mul_le_mul hJ hq hq0 hJB0.le
    have f2 : 1 - J * (((n : ℝ) - 1) / (2 * n)) + epsB / 2 ≤
        1 - Jlo / 2 * (1 - 1 / n1) + 216 / 100000 := by linarith
    have f2' : 0 ≤ 1 - J * (((n : ℝ) - 1) / (2 * n)) + epsB / 2 := by
      have : ((n : ℝ) - 1) / (2 * n) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      have h3 : J * (((n : ℝ) - 1) / (2 * n)) ≤ 1 * (1 / 2) :=
        mul_le_mul hJB1 this (hq0.trans hq) (by norm_num)
      linarith
    have f3 : J / (2 * n) ≤ 1 / (2 * n1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := mul_le_mul f1 f2 f2' (f1'.trans f1)
    linarith
  have hM0 := (Real.sqrt_nonneg (M1B n c τ S0))
  have hsM : √(M1B n c τ S0) ≤ sm := by
    rw [Real.sqrt_le_iff]; exact ⟨hsm0, hM⟩
  -- the other terms
  have hsq0 : 0 ≤ √(12 / ((n : ℝ) - 4)) := Real.sqrt_nonneg _
  have hsq : √(12 / ((n : ℝ) - 4)) ≤ 2723 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hprod : K0 * √(12 / ((n : ℝ) - 4)) ≤ 9085 / 100000 * (2723 / 100000) :=
    mul_le_mul hK hsq hsq0 (by norm_num)
  have hprod0 : 0 ≤ K0 * √(12 / ((n : ℝ) - 4)) := mul_nonneg hK0.le hsq0
  have hlast : 4 * (1 + 2 / (n : ℝ)) / n ≤ 4 * (1 + 2 / 16200) / 16200 :=
    div_le_div₀ (by norm_num)
      (by have : 2 / (n : ℝ) ≤ 2 / 16200 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
          linarith) (by norm_num) hnR
  unfold cHSB
  have h1 : √(M1B n c τ S0) + K0 * √(12 / ((n : ℝ) - 4)) ≤ sm + 248 / 100000 := by
    have : (9085 / 100000 : ℝ) * (2723 / 100000) ≤ 248 / 100000 := by norm_num
    linarith
  have h2 := pow_le_pow_left₀ (add_nonneg hM0 hprod0) h1 2
  have h3 : (4 : ℝ) * (1 + 2 / 16200) / 16200 ≤ 248 / 1000000 := by norm_num
  linarith

/-- **The bound of `‖H‖²_HS` on `E_H` with change (B)**: `‖H‖²_HS ≤ 4·((y + d)⁴/4)·τ⁴/n`. -/
theorem hsH_le_B {n : ℕ} (hn : 16200 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} (hA : A₁ ∉ BadH n c τ 12)
    {n1 θlo u Jlo sm y s k d : ℝ} (hn1 : 16200 ≤ n1) (hn1n : n1 ≤ n) (hlo0 : 0 < θlo)
    (hlo : θlo ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) (hu0 : 0 < u) (hu1 : 2 * u < 1)
    (hu : 12 ≤ u ^ 2 * n1) (hJ0 : 0 ≤ Jlo)
    (hJ : Jlo ^ 2 * (1 + 2 * (1 - θlo) / (θlo * (1 - 2 * u))) ≤ 1) (hsm0 : 0 ≤ sm)
    (hsm : (1 - Jlo / 2 + 216 / 100000) * (1 - Jlo / 2 * (1 - 1 / n1) + 216 / 100000) +
      1 / (2 * n1) ≤ sm ^ 2)
    (hy0 : 0 ≤ y) (hy : 4 * ((sm + 248 / 100000) ^ 2 + 248 / 1000000) ≤ y ^ 4)
    (hs0 : 0 < s) (hs : s ^ 2 ≤ θlo) (hk0 : 0 < k) (hk : k ^ 4 ≤ n1 ^ 3) (hd0 : 0 ≤ d)
    (hd : 98 / 10 ≤ d * s * k) :
    hsH A₁ c τ ≤ 4 * ((y + d) ^ 4 / 4) * τ ^ 4 * 1 / n := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1' : 1 ≤ n := by omega
  obtain ⟨hS0, hc0, hJB⟩ := JB_ge hn c hτ hn1 hn1n hlo0 hlo hθ1 hu0 hu1 hu hJ0 hJ
  have hcb := cHSB_le hn c hτ hS0 hn1 hn1n hJ0 hJB hsm0 hsm
  obtain ⟨hint, hB⟩ := hsH_mean_B (by omega : 8 ≤ n) c hc0 hτ hS0 le_rfl K0_pos.le PRvecAbs_K0
  have hB' : ∫ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ, hsH A₁ c τ ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      y ^ 4 * τ ^ 4 / n := by
    refine hB.trans ?_
    have h1 : 4 * cHSB n K0 (M1B n c τ ((n : ℝ) - 2 * √((n : ℝ) * 12))) ≤ y ^ 4 := by linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hn0.le
  have hb := EH_bound hn1' c τ (by norm_num : (0 : ℝ) ≤ 12) hint hB' hA
  rw [sqrt4_eq hn0 hy0 hτ] at hb
  have hθ0 : 0 < thetaC c τ := lt_of_lt_of_le hlo0 hlo
  have hρ := rhoC_posP hn1' c hτ
  have hρ2 := rhoC_sqP c τ
  have hρθ : rhoC c τ ^ 2 * thetaC c τ = (n : ℝ) * τ ^ 2 := by
    unfold thetaC; field_simp
  have hk' : k ^ 4 ≤ (n : ℝ) ^ 3 := hk.trans (pow_le_pow_left₀ (by linarith) hn1n 3)
  have hT2 := devH_le hn0 hτ hρ hθ0 hρθ hs0 (hs.trans hlo) hk0 hk' hd0 hd
  rw [← hρ2, Real.sqrt_sq hρ.le] at hb
  have hq0 : 0 < √(√(n : ℝ)) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn0)
  have hq4 : √(√(n : ℝ)) ^ 4 = n := by
    have : √(√(n : ℝ)) ^ 4 = (√(√(n : ℝ)) ^ 2) ^ 2 := by ring
    rw [this, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hn0.le]
  have hsum : y * τ / √(√(n : ℝ)) + 2 * √(2 * 12) * rhoC c τ / ((n : ℝ) * √(n : ℝ)) ≤
      (y + d) * τ / √(√(n : ℝ)) := by
    have : (y + d) * τ / √(√(n : ℝ)) = y * τ / √(√(n : ℝ)) + d * τ / √(√(n : ℝ)) := by ring
    linarith
  have h0 : 0 ≤ y * τ / √(√(n : ℝ)) + 2 * √(2 * 12) * rhoC c τ / ((n : ℝ) * √(n : ℝ)) := by
    positivity
  refine hb.trans ((pow_le_pow_left₀ h0 hsum 4).trans (le_of_eq ?_))
  rw [div_pow, mul_pow, hq4]
  ring

/-- `ξ_c′` with the constant of change (B): `≤ 0.26973·C_b·θhi·r + 0.00367`. -/
theorem xiCI_B_gen {n : ℕ} (hn : 16200 ≤ n) {θ θhi r Cb : ℝ} (h0 : 46 / 100 ≤ θ)
    (h1 : θ ≤ 55 / 100) (hθ : θ ≤ θhi) (hr0 : 0 ≤ r) (hr : θhi ≤ r ^ 2) (hCb : 0 ≤ Cb) :
    xiCI n csC Cb 1 (11 / 10) (27 / 25) (11 / 1000) θ ≤
      26973 / 100000 * Cb * (θhi * r) + 371 / 100000 := by
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨b0, b1⟩ := xiTt_le16 hn
  obtain ⟨c0, c1⟩ := xiT2_le16 hn h0 h1
  obtain ⟨hb0, hb⟩ := BstLean.Part188.Base154_R.bN_bounds_NumA16 hn h0 h1
  have hθ0 : 0 ≤ θ := by linarith
  have hsθ : √θ ≤ r := by
    rw [Real.sqrt_le_iff]; exact ⟨hr0, by linarith⟩
  have hsθ0 : 0 ≤ √θ := Real.sqrt_nonneg _
  have hs0 : (16006 / 10000 : ℝ) ≤ √(2 * csC * (1 - 11 / 1000)) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((16006 / 10000 : ℝ)) ^ 2 ≤ 2 * (129521 / 100000) * (1 - 11 / 1000) := by norm_num
    nlinarith
  have hθr : θ * √θ ≤ θhi * r := mul_le_mul hθ hsθ hsθ0 (by linarith)
  have hθr0 : 0 ≤ θhi * r := mul_nonneg (by linarith) hr0
  have hnum : 4 * K0 * Cb * 1 * (11 / 10 * (27 / 25)) * (θ * √θ) ≤
      4 * (9085 / 100000) * Cb * 1 * (11 / 10 * (27 / 25)) * (θhi * r) := by
    have hK00 := hK0.le
    gcongr
  have hT1 : 4 * K0 * Cb * 1 * (11 / 10 * (27 / 25)) * (θ * √θ) /
      √(2 * csC * (1 - 11 / 1000)) ≤ 26973 / 100000 * Cb * (θhi * r) := by
    rw [div_le_iff₀ (by linarith)]
    have hX : 0 ≤ Cb * (θhi * r) := mul_nonneg hCb hθr0
    have h2 : (4 : ℝ) * (9085 / 100000) * Cb * 1 * (11 / 10 * (27 / 25)) * (θhi * r) ≤
        26973 / 100000 * Cb * (θhi * r) * (16006 / 10000) := by nlinarith
    have h3 : 26973 / 100000 * Cb * (θhi * r) * (16006 / 10000) ≤
        26973 / 100000 * Cb * (θhi * r) * √(2 * csC * (1 - 11 / 1000)) :=
      mul_le_mul_of_nonneg_left hs0 (by positivity)
    linarith
  unfold xiCI
  linarith only [hT1, b1, c1, hb]

/-- **The mean bound on `GoodC16` from any bound of `‖H‖²_HS`.** -/
theorem mean_gen {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) {cH hH ξc : ℝ}
    (hHS : hsH A₁ c τ ≤ 4 * cH * τ ^ 4 * hH / n)
    (hξc : xiCI n csC cH hH (11 / 10) (27 / 25) (11 / 1000) (thetaC c τ) ≤ ξc) :
    ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξc := by
  have hn8 : 8192 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm := BstLean.Part130.one_le_mA hn1
  obtain ⟨⟨hop, hop2, -⟩, hΓ, -, hsc0⟩ := BstLean.Part153.AStage_bounds hn8 h.1.1
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hρ2 := rhoC_sqP c τ
  have hρ := rhoC_posP hn1 c hτ
  rw [← hρ2] at hΓ
  have hΓlo : (1 - 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 ≤ gO A₁ c τ := by
    rw [← BstLean.Part153.GamS_eq_gO hm]
    have := (abs_le.mp hΓ).1
    linarith
  obtain ⟨hg1, hrG, hg3, -, -⟩ := tails_num16 hn
  obtain ⟨-, hmean0⟩ := MA_i_int hn1 A₁ c hτ csC_pos_I (BstLean.Part188.Base154_R.rhoBar_lt16 hn) hop2 hsc hHS
    (δe := 11 / 1000) (by norm_num) hΓlo (a1 := 11 / 10) (a3 := 27 / 25) (by norm_num)
    (by norm_num) hg1 hrG hg3
  exact hmean0.trans (mul_le_mul_of_nonneg_left hξc (by positivity))

/-- **The centre error from a bound of `|𝐝|`** on `GoodC16`. -/
theorem centre_from_dC {n : ℕ} (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) {cd : ℝ}
    (c1 : dC A₁ A₂ c τ ≤ rhoC c τ * √(2 / (n : ℝ) / n) * cd) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cd + xiNr n (thetaC c τ) (11911 / 10000) +
        epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12)) := by
  have hn1 : 1 ≤ n := by omega
  have hρ := rhoC_posP hn1 c hτ
  obtain ⟨-, -, hN22, -, -⟩ := BstLean.Part153.GoodA_norms hn1 h.2
  have hXi := BstLean.Part188.Base153_R.AStage16_Xi hn hτ h.2
  have c2 := MA_iv (by omega : 6 ≤ n) A₁ A₂ c hτ (MP := 11911 / 10000) (by norm_num) c1 hN22 hXi
  have c5 := (BstLean.Part188.Base154_R.GoodC16_centre hn hn1 hτ h (BstLean.Part188.Base154_R.rhoBar_lt16 hn) (BstLean.Part188.Base154_R.eMP_le16 hn hθ0 hθ1)
    (θlo := 46 / 100) hθ0).2.2.2.1
  have hst0 : 0 ≤ √(2 / ((mA n : ℕ) : ℝ)) := Real.sqrt_nonneg _
  have e : hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ =
      (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) +
        (rhoC c τ)⁻¹ • (bO A₁ A₂ c τ - bT n n A₁ A₂ c τ) := by
    rw [one_div, smul_sub]; abel
  have hrev : nrm ((rhoC c τ)⁻¹ • (bO A₁ A₂ c τ - bT n n A₁ A₂ c τ)) =
      nrm (bT n n A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos (inv_pos.mpr hρ)]
    have hneg : nrm (bO A₁ A₂ c τ - bT n n A₁ A₂ c τ) =
        nrm (bT n n A₁ A₂ c τ - bO A₁ A₂ c τ) := by
      unfold BstLean.Part153.nrm normSq
      congr 1
      exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
    rw [hneg]; ring
  have htri := BstLean.Part153.nrm_add_le (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)
    ((rhoC c τ)⁻¹ • (bO A₁ A₂ c τ - bT n n A₁ A₂ c τ))
  rw [e]
  have h5 : √(2 / ((mA n : ℕ) : ℝ)) * (nrm (bT n n A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ) ≤
      epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) * √(2 / (n : ℝ) / n) := by
    have : √(2 / ((mA n : ℕ) : ℝ)) * (nrm (bT n n A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ) =
        √(2 / ((mA n : ℕ) : ℝ)) * nrm (bT n n A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ := by ring
    rw [this]; exact c5
  have c2' : √(2 / ((mA n : ℕ) : ℝ)) *
      nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cd + xiNr n (thetaC c τ) (11911 / 10000)) := c2
  calc √(2 / ((mA n : ℕ) : ℝ)) *
        nrm ((hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) +
          (rhoC c τ)⁻¹ • (bO A₁ A₂ c τ - bT n n A₁ A₂ c τ))
      ≤ √(2 / ((mA n : ℕ) : ℝ)) *
        (nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) +
          nrm ((rhoC c τ)⁻¹ • (bO A₁ A₂ c τ - bT n n A₁ A₂ c τ))) :=
        mul_le_mul_of_nonneg_left htri hst0
    _ = √(2 / ((mA n : ℕ) : ℝ)) *
          nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) +
        √(2 / ((mA n : ℕ) : ℝ)) * (nrm (bT n n A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ) := by
        rw [hrev]; ring
    _ ≤ _ := by linarith

end BstLean.Part188.Base160_R

