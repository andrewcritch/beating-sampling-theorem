import BstLean.Part169Asm

/-! Grid and stored-rule errors apply to every measurable kept subset of the bulk. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)
variable {n : ℕ}

theorem grid_f_bulk (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {q : ℝ} (hq : 0 < q) (hLH : nodeL c < nodeH c)
    (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q) {a : Ix n} (ha : a ∈ bulkIx (paperDesignP n) c) :
    |fbR c a - fbarS c (nodeS c (gIdx c (latC (paperDesignP n) c a)))| ≤
      O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q) := by
  have hal : nodeL c ≤ latC (paperDesignP n) c a ∧ latC (paperDesignP n) c a ≤ nodeH c := ha
  obtain ⟨hl1, hl2⟩ := hal
  obtain ⟨hnear, hg⟩ := gIdx_near hn c hLH hl1 hl2
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH hg
  rw [fbR_eq]
  refine (fbar_lip hn c h1 h2 hO₁ hO₂ hq (hbulk _ hl1 hl2) (hbulk _ hs1 hs2)).trans ?_
  have hpos : 0 < √(n : ℝ) * √q :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))) (Real.sqrt_pos.mpr hq)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by positivity)) hpos.le

/-- **The energy grid error** (paper `t7:p08:grid`): on a kept index,
`|ω̄(s) − ω̄(s_g)| ≤ Λ²Δ/(n√q)`. -/
theorem grid_w_bulk (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {q : ℝ} (hq : 0 < q) (hLH : nodeL c < nodeH c)
    (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q) {a : Ix n} (ha : a ∈ bulkIx (paperDesignP n) c) :
    |wbR c a - wbarS c (nodeS c (gIdx c (latC (paperDesignP n) c a)))| ≤
      2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q) := by
  have hal : nodeL c ≤ latC (paperDesignP n) c a ∧ latC (paperDesignP n) c a ≤ nodeH c := ha
  obtain ⟨hl1, hl2⟩ := hal
  obtain ⟨hnear, hg⟩ := gIdx_near hn c hLH hl1 hl2
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH hg
  rw [wbR_eq]
  refine (wbar_lip hn c h1 h2 hO₁ hO₂ hq (hbulk _ hl1 hl2) (hbulk _ hs1 hs2)).trans ?_
  have hpos : 0 < (n : ℝ) * √q :=
    mul_pos (by exact_mod_cast (show 0 < n by omega)) (Real.sqrt_pos.mpr hq)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by positivity)) hpos.le

theorem location_error_of_exact (hn : 2 ≤ n) (c : Ret n) {K : Set (Ix n)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP n) c) {O₁ O₂ q σ0 A : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 < O₁) (hO₂ : 0 < O₂) (hq : 0 < q) (hσ : 0 < σ0)
    (hLH : nodeL c < nodeH c) (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q)
    (hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ σ0 ^ 2) (hA : 0 < A)
    (iX : IntegrableOn (fun a => exF c a ^ 8) K (muI n))
    (hX : ∫ a in K, exF c a ^ 8 ∂muI n ≤ A ^ 8) :
    IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) K (muI n) ∧
      ∫ a in K, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤
        (A + ((n : ℝ) * (O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q)) +
          n * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n)))) ^ 8 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos hn)
  have hD : 0 < nodeD c := div_pos (by linarith) (by exact_mod_cast (show 0 < Js n by
    unfold Js; omega))
  have hc1 : 0 < c1F (rexp (1 / 2) / 12) (Jz n) := by
    unfold c1F; have := Real.pi_pos; positivity
  have mY : Measurable (fun a => (n : ℝ) * (fbR c a - ftR c a)) :=
    ((measurable_fbR c).sub (measurable_ftR c)).const_mul _
  refine int_pow8_add_const hK measureReal_le_one mY iX hA (by positivity) hX ?_
  intro a ha
  have hg := grid_f_bulk hn1 c h1 h2 hO₁.le hO₂.le hq hLH hbulk (hsub ha)
  have hr := rule_f hn c (sgR c a)
  have hrs : √(vsig2 c (sgR c a)) ≤ σ0 := by
    rw [Real.sqrt_le_left hσ.le]; exact hvs a ha
  have hr' : |fPass c (sgR c a) - fGauss c (sgR c a)| ≤
      √(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n) := by
    refine hr.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrs hc1.le) hJ.le
  have e : (n : ℝ) * (fbR c a - ftR c a) = (n : ℝ) * (fbR c a - fbarS c (sgR c a)) + exF c a -
      (n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a)) := by
    unfold exF ftR sgR; ring
  rw [e]
  have t1 : |(n : ℝ) * (fbR c a - fbarS c (sgR c a))| ≤
      (n : ℝ) * (O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hg hnR.le
  have t3 : |(n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a))| ≤
      (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * σ0 / Jz n)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hr' hnR.le
  calc _ ≤ |(n : ℝ) * (fbR c a - fbarS c (sgR c a))| + |exF c a| +
        |(n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a))| := by
        have h3 := abs_sub ((n : ℝ) * (fbR c a - fbarS c (sgR c a)) + exF c a)
          ((n : ℝ) * (fPass c (sgR c a) - fGauss c (sgR c a)))
        have h4 := abs_add_le ((n : ℝ) * (fbR c a - fbarS c (sgR c a))) (exF c a)
        linarith
    _ ≤ _ := by linarith

/-- **`‖n(ω̄ − ω̃)‖_{L⁸(K)} ≤ A + g_ω + r_ω`** from the `L⁸` bound `A` of the exact-rule error. -/
theorem energy_error_of_exact (hn : 2 ≤ n) (c : Ret n) {K : Set (Ix n)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP n) c) {O₁ O₂ q σ0 A : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 < O₁) (hO₂ : 0 < O₂) (hq : 0 < q) (hσ : 0 < σ0)
    (hLH : nodeL c < nodeH c) (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q)
    (hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ σ0 ^ 2) (hA : 0 < A)
    (iX : IntegrableOn (fun a => exW c a ^ 8) K (muI n))
    (hX : ∫ a in K, exW c a ^ 8 ∂muI n ≤ A ^ 8) :
    IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) K (muI n) ∧
      ∫ a in K, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤
        (A + ((n : ℝ) * (2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q)) +
          n * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n)))) ^ 8 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos hn)
  have hD : 0 < nodeD c := div_pos (by linarith) (by exact_mod_cast (show 0 < Js n by
    unfold Js; omega))
  have hc2 : 0 < c2F (rexp (1 / 2) / 12) (Jz n) := by
    unfold c2F; have := Real.pi_pos; positivity
  have mY : Measurable (fun a => (n : ℝ) * (wbR c a - wtR c a)) :=
    ((measurable_wbR c).sub (measurable_wtR c)).const_mul _
  refine int_pow8_add_const hK measureReal_le_one mY iX hA (by positivity) hX ?_
  intro a ha
  have hg := grid_w_bulk hn1 c h1 h2 hO₁.le hO₂.le hq hLH hbulk (hsub ha)
  have hr := rule_w hn c (sgR c a)
  have hr' : |wPass c (sgR c a) - wGauss c (sgR c a)| ≤
      n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n) := by
    refine hr.trans (mul_le_mul_of_nonneg_left ?_ hnR.le)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hvs a ha) hc2.le) hJ.le
  have e : (n : ℝ) * (wbR c a - wtR c a) = (n : ℝ) * (wbR c a - wbarS c (sgR c a)) + exW c a -
      (n : ℝ) * (wPass c (sgR c a) - wGauss c (sgR c a)) := by
    unfold exW wtR sgR; ring
  rw [e]
  have t1 : |(n : ℝ) * (wbR c a - wbarS c (sgR c a))| ≤
      (n : ℝ) * (2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hg hnR.le
  have t3 : |(n : ℝ) * (wPass c (sgR c a) - wGauss c (sgR c a))| ≤
      (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * σ0 ^ 2 / Jz n)) := by
    rw [abs_mul, abs_of_pos hnR]; exact mul_le_mul_of_nonneg_left hr' hnR.le
  have h3 := abs_sub ((n : ℝ) * (wbR c a - wbarS c (sgR c a)) + exW c a)
    ((n : ℝ) * (wPass c (sgR c a) - wGauss c (sgR c a)))
  have h4 := abs_add_le ((n : ℝ) * (wbR c a - wbarS c (sgR c a))) (exW c a)
  linarith

end BstLean.Part252
