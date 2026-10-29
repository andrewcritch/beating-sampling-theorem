import BstLean.Part160MFNum

/-!
# Part 160 (file `MFCentre`): the centre charge with the integrated remainder

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:MA` and Proposition `t7:p05:certificate`
(changes (A) and (C) only; the events are those of Part 154, unchanged).

* `centre_int_core`: on `GoodC16 n n c τ`, `n ≥ 16384`, `0.46 ≤ θ_in ≤ 0.55`:
  `√t_A·|μ − b| ≤ √(γ_A/n)·(𝖼_d(ξ_c′) + √ξ_N + ϵ_J)` with `ξ_c′ ≤ 0.11751`.
* `centre16_int`: `t_A·|μ − b|² ≤ 0.221·γ_A/n` for `n ≥ 16384` (Part 154: `0.485`).
* `centre50k_int`: `t_A·|μ − b|² ≤ 0.1754·γ_A/n` for `n ≥ 50000`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 N2 sq2 hid2Mean_cr Pb wn N22bar)

lemma csC_pos_I : 0 < csC := by
  have := csC_bounds_NumA.1
  linarith

/-- **The centre error on `GoodC16` with the integrated remainder.** -/
theorem centre_int_core {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cD n 12 (11 / 1000) (11751 / 100000) +
        xiNr n (thetaC c τ) (11911 / 10000) +
        epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12)) := by
  have hn8 : 8192 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm := BstLean.Part130.one_le_mA hn1
  have h16 := h.2
  have hC := h.1
  have hAs := hC.1
  have hD := hC.2.2.1
  obtain ⟨⟨hop, hop2, -⟩, hΓ, -, hsc0⟩ := BstLean.Part153.AStage_bounds hn8 hAs
  obtain ⟨-, -, hN22, -, -⟩ := BstLean.Part153.GoodA_norms hn1 h16
  have hXi := BstLean.Part153.AStage16_Xi hn hτ h16
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hcs := csC_pos_I
  have hρ2 := rhoC_sqP c τ
  have hρ := rhoC_posP hn1 c hτ
  rw [← hρ2] at hΓ
  have hΓ' : BstLean.Part153.GamS A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    have := (abs_le.mp hΓ).2
    linarith
  have hΓlo : (1 - 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 ≤ gO A₁ c τ := by
    rw [← BstLean.Part153.GamS_eq_gO hm]
    have := (abs_le.mp hΓ).1
    linarith
  have hHS := GoodC_HS hn8 hτ hC
  obtain ⟨hg1, hrG, hg3, -, -⟩ := tails_num16 hn
  obtain ⟨-, hmean0⟩ := MA_i_int hn1 A₁ c hτ hcs (rhoBar_lt16 hn) hop2 hsc hHS
    (δe := 11 / 1000) (by norm_num) hΓlo (a1 := 11 / 10) (a3 := 27 / 25) (by norm_num)
    (by norm_num) hg1 hrG hg3
  obtain ⟨-, hx⟩ := xiCI_le16 hn hθ0 hθ1
  have hmean : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * (11751 / 100000) :=
    hmean0.trans (mul_le_mul_of_nonneg_left hx (by positivity))
  have c1 := MA_ii hn1 A₁ A₂ c τ (Lc := 12) (δe := 11 / 1000) (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 11751 / 100000) hmean hΓ' hD
  have c2 := MA_iv (by omega : 6 ≤ n) A₁ A₂ c hτ (MP := 11911 / 10000) (by norm_num) c1 hN22 hXi
  have c5 := (GoodC16_centre hn hn1 hτ h (rhoBar_lt16 hn) (eMP_le16 hn hθ0 hθ1)
    (θlo := 46 / 100) hθ0).2.2.2.1
  -- the triangle inequality
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
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
      √(2 / (n : ℝ) / n) * (cD n 12 (11 / 1000) (11751 / 100000) +
        xiNr n (thetaC c τ) (11911 / 10000)) := c2
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

/-- From `√t·|v| ≤ √(γ/n)·x` to `t·|v|² ≤ x²·γ/n`. -/
lemma sq_form {n : ℕ} (hn : 1 ≤ n) (v : Fin (mA n) → ℝ) {x ξ : ℝ} (_hx : 0 ≤ x) (hxξ : x ^ 2 ≤ ξ)
    (h : √(2 / ((mA n : ℕ) : ℝ)) * nrm v ≤ √(2 / (n : ℝ) / n) * x) :
    2 / (mA n : ℝ) * normSq v ≤ ξ * (2 / (n : ℝ)) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have h2 := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (BstLean.Part153.nrm_nonneg v)) h 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    BstLean.Part153.nrm_sq] at h2
  refine h2.trans ?_
  have : 2 / (n : ℝ) / n * x ^ 2 ≤ 2 / (n : ℝ) / n * ξ :=
    mul_le_mul_of_nonneg_left hxξ (by positivity)
  calc 2 / (n : ℝ) / n * x ^ 2 ≤ 2 / (n : ℝ) / n * ξ := this
    _ = ξ * (2 / (n : ℝ)) / n := by ring

lemma sqrt_xi0_ge : (56877 / 100000 : ℝ) ≤ √(3235 / 10000) := by
  rw [Real.le_sqrt' (by norm_num)]; norm_num

lemma sqrt_xi1_le : √(11751 / 100000 : ℝ) ≤ 3428 / 10000 := by
  rw [Real.sqrt_le_iff]; norm_num

/-- **The centre charge with the integrated remainder, `n ≥ 16384`**: on `GoodC16 n n c τ`,
`0.46 ≤ θ_in ≤ 0.55`: `t_A·|μ − b|² ≤ 0.221·γ_A/n`, `b = bT n n A₁ A₂ c τ/ρ`
(Part 154, `centre16`: `0.485`). -/
theorem centre16_int {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      221 / 1000 * (2 / (n : ℝ)) / n := by
  have hcore := centre_int_core hn hτ hθ0 hθ1 h
  have hx1 := x1_leB16 hn (θ := thetaC c τ) (ξ := 3235 / 10000) hθ0 hθ1 (by norm_num) le_rfl
  obtain ⟨hε0, hε⟩ := epsJ_le16 hn
  have hcd : cD n 12 (11 / 1000) (11751 / 100000) =
      cD n 12 (11 / 1000) (3235 / 10000) - √(3235 / 10000) + √(11751 / 100000) := by
    unfold cD; ring
  have hT0 : 0 ≤ cD n 12 (11 / 1000) (11751 / 100000) := by unfold cD; positivity
  have hN0 : 0 ≤ xiNr n (thetaC c τ) (11911 / 10000) := by
    have hθ : 0 ≤ thetaC c τ := by linarith
    have := (Nbar_le16 hn).1
    unfold xiNr; positivity
  have h0 := sqrt_xi0_ge
  have h1 := sqrt_xi1_le
  refine sq_form (by omega) _ (x := cD n 12 (11 / 1000) (11751 / 100000) +
    xiNr n (thetaC c τ) (11911 / 10000) + epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12))
    (by linarith) ?_ hcore
  have hb : cD n 12 (11 / 1000) (11751 / 100000) + xiNr n (thetaC c τ) (11911 / 10000) +
      epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 47003 / 100000 := by
    rw [hcd]; linarith
  exact (pow_le_pow_left₀ (by linarith) hb 2).trans (by norm_num)

/-- **The centre charge with the integrated remainder, `n ≥ 50000`**:
`t_A·|μ − b|² ≤ 0.1754·γ_A/n`. -/
theorem centre50k_int {n : ℕ} (hn : 50000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      1754 / 10000 * (2 / (n : ℝ)) / n := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (50000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hcore := centre_int_core hn16 hτ hθ0 hθ1 h
  obtain ⟨hε0, hε⟩ := epsJ_le16 hn16
  obtain ⟨hNb0, hNb, -, -⟩ := Nbar_le16 hn16
  have h1 := sqrt_xi1_le
  have hθ : 0 ≤ thetaC c τ := by linarith
  -- the deviation term
  have hT : √(16 * 12 * (1 + 11 / 1000) / (n : ℝ)) ≤ 6231 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hn0]
    nlinarith
  -- the radius term
  have hsn : (2236 / 10 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]
    exact le_trans (by norm_num) hnR
  have hNb' : N22bar n 12 ≤ 367 / 1000000 := by
    refine hNb.trans ?_
    rw [div_le_iff₀ hn0]
    nlinarith
  have hsq : √(11911 / 10000 * thetaC c τ) ≤ 80939 / 100000 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    nlinarith
  have hxi : xiNr n (thetaC c τ) (11911 / 10000) ≤ 609 / 100000 := by
    unfold xiNr
    rw [div_le_iff₀ (by linarith)]
    have hp : thetaC c τ * (1 + N22bar n 12) ≤ 55 / 100 * (1 + 367 / 1000000) :=
      mul_le_mul hθ1 (by linarith) (by linarith) (by norm_num)
    nlinarith
  have hT0 : 0 ≤ cD n 12 (11 / 1000) (11751 / 100000) := by unfold cD; positivity
  have hN0 : 0 ≤ xiNr n (thetaC c τ) (11911 / 10000) := by unfold xiNr; positivity
  refine sq_form (by omega) _ (x := cD n 12 (11 / 1000) (11751 / 100000) +
    xiNr n (thetaC c τ) (11911 / 10000) + epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12))
    (by linarith) ?_ hcore
  have hb : cD n 12 (11 / 1000) (11751 / 100000) + xiNr n (thetaC c τ) (11911 / 10000) +
      epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ 4187 / 10000 := by
    unfold cD; linarith
  exact (pow_le_pow_left₀ (by linarith) hb 2).trans (by norm_num)

end BstLean.Part160

open BstLean.Part160 in
#print axioms centre_int_core
open BstLean.Part160 in
#print axioms centre16_int
open BstLean.Part160 in
#print axioms centre50k_int
