import BstLean.Part154MAi
import BstLean.Part154MP
import BstLean.Part154Fin
import BstLean.Part154HS
import BstLean.Part154L1c
import BstLean.Part154PRabs

/-!
# Part 154: the event of `(A₁, A₂)` for the centre, and the centre bounds on it
Do not use `sorry`, `native_decide` or `axiom`.

`GoodC n J c τ` extends `GoodAs n c τ` of Part 153 by the events `E_H` (of `A₁`) and
`E_D`, `E_Π`, `E_Pb`, `E_χ` (of `A₂`, for a fixed `A₁`), all at the level `L_c = 12`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr GoodAs nuA N22bar)

/-- `c_s = 0.95·2(1 − 1/π)`. -/
noncomputable def csC : ℝ := 0.95 * 2 * (1 - 1 / π)

/-- `a_H = 2√(2L_c)/((4c_HS)^{1/4} n^{3/4})` at `L_c = 12`, with the constant `cHSK n K0` of
`hsH_mean` in the place of `c_HS`. -/
noncomputable def aHn (n : ℕ) : ℝ :=
  2 * √24 / (√(√(4 * cHSK n K0)) * (√(n : ℝ) * √(√(n : ℝ))))

/-- `h_n(θ) = (1 + a_H/√θ)⁴`. -/
noncomputable def hHn (n : ℕ) (θ : ℝ) : ℝ := (1 + aHn n / √θ) ^ 4

/-- `ξ_c(θ)` of Lean: `xiC` with `K = K₀`, `c_s`, `cHSK n K0`, `h_n(θ)`. -/
noncomputable def xiCn (n : ℕ) (θ : ℝ) : ℝ := xiC n K0 csC (cHSK n K0) (hHn n θ) θ

/-- `√ξ_N` with `θ` in the place of `θ_max`: `(θ(1 + N̄₂₂) + √(M_P θ))/√n`. -/
noncomputable def xiNr (n : ℕ) (θ MP : ℝ) : ℝ := (θ * (1 + N22bar n 12) + √(MP * θ)) / √(n : ℝ)

/-- **The event of `(A₁, A₂)` for the centre.** -/
def GoodC (n J : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {θ | θ ∈ GoodAs n c τ ∧ θ.1 ∉ BadH n c τ 12 ∧ θ.2 ∉ BadD θ.1 c τ 12 ∧
    θ.2 ∉ BadPi θ.1 c τ 12 ∧ θ.2 ∉ BadPb θ.1 c τ 12 ∧ θ.2 ∉ BadChi n J θ.1 c τ 12}

private lemma sqrt_sqrt_pow4 {x : ℝ} (hx : 0 ≤ x) : √(√x) ^ 4 = x := by
  have h1 : √(√x) ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : √x ^ 2 = x := Real.sq_sqrt hx
  calc √(√x) ^ 4 = (√(√x) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2]

private lemma sqrt_sqrt_of_pow4 {x : ℝ} (hx : 0 ≤ x) : √(√(x ^ 4)) = x := by
  have e : x ^ 4 = (x ^ 2) ^ 2 := by ring
  rw [e, Real.sqrt_sq (sq_nonneg x), Real.sqrt_sq hx]

private lemma QB_nonneg_Event {ϱ πg : ℝ} (h : 0 ≤ ϱ) (_hπ : 0 ≤ πg) : 0 ≤ QB ϱ πg := by
  have p0 := (BstLean.Part153.phiG_pos 0).le
  have p1 := (BstLean.Part153.phiG_pos 1).le
  have hν : 0 ≤ nuR ϱ := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 ϱ πg := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 ϱ πg := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 ϱ := by unfold cc2; positivity
  unfold QB
  positivity

private lemma csC_pos : 0 < csC := by
  have h : 1 / π < 1 := by
    rw [div_lt_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  unfold csC
  exact mul_pos (by norm_num) (by linarith)

/-- The charge of the event: the charge of `GoodAs` (Part 153) plus `6e^{−12}`
(`E_H`: 1, `E_D`: 1, `E_Π`: 2, `E_Pb`: 1, `E_χ`: 1). -/
theorem GoodC_prob {n : ℕ} (hn : 8192 ≤ n) (J : ℕ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodC n J c τ)ᶜ ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hsub : (GoodC n J c τ)ᶜ ⊆
      ((((((GoodAs n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}) ∪ {θ | θ.2 ∈ BadPb θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadChi n J θ.1 c τ 12}) := by
    intro θ hθ
    by_contra h
    apply hθ
    refine ⟨not_not.mp fun h0 => h (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h0))))),
      fun h1 => h (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))),
      fun h2 => h (Or.inl (Or.inl (Or.inl (Or.inr h2)))),
      fun h3 => h (Or.inl (Or.inl (Or.inr h3))),
      fun h4 => h (Or.inl (Or.inr h4)), fun h5 => h (Or.inr h5)⟩
  have g0 := measureReal_mono (μ := nuA n) hsub
  have g1 := measureReal_union_le (μ := nuA n)
    (((((GoodAs n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}) ∪ {θ | θ.2 ∈ BadPb θ.1 c τ 12})
    {θ | θ.2 ∈ BadChi n J θ.1 c τ 12}
  have g2 := measureReal_union_le (μ := nuA n)
    ((((GoodAs n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}) {θ | θ.2 ∈ BadPb θ.1 c τ 12}
  have g3 := measureReal_union_le (μ := nuA n)
    (((GoodAs n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12})
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}
  have g4 := measureReal_union_le (μ := nuA n)
    ((GoodAs n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) {θ | θ.2 ∈ BadD θ.1 c τ 12}
  have g5 := measureReal_union_le (μ := nuA n)
    (GoodAs n c τ)ᶜ {θ | θ.1 ∈ BadH n c τ 12}
  have e0 := BstLean.Part153.AStage_prob hn c hτ
  have eH : (nuA n).real {θ | θ.1 ∈ BadH n c τ 12} =
      (gaussMat (mA n) n (2 / (n : ℝ))).real (BadH n c τ 12) := BstLean.Part153.prod_real_fst _
  have eH' := EH_prob hn1 c τ (Lc := 12) (by norm_num)
  have eD : (nuA n).real {θ | θ.2 ∈ BadD θ.1 c τ 12} ≤ rexp (-12) :=
    BstLean.Part153.prod_real_le_of_fibre (measurableSet_BadD_joint hm c τ 12) (by positivity)
      (fun A₁ => ED_prob hm A₁ c τ (by norm_num))
  have ePi : (nuA n).real {θ | θ.2 ∈ BadPi θ.1 c τ 12} ≤ 2 * rexp (-12) :=
    BstLean.Part153.prod_real_le_of_fibre (measurableSet_BadPi_joint hm c τ 12) (by positivity)
      (fun A₁ => EPi_prob hm A₁ c τ (by norm_num))
  have ePb : (nuA n).real {θ | θ.2 ∈ BadPb θ.1 c τ 12} ≤ rexp (-12) :=
    BstLean.Part153.prod_real_le_of_fibre (measurableSet_BadPb_joint hm c τ 12) (by positivity)
      (fun A₁ => EPb_prob hm A₁ c τ (by norm_num))
  have eChi : (nuA n).real {θ | θ.2 ∈ BadChi n J θ.1 c τ 12} ≤ rexp (-12) :=
    BstLean.Part153.prod_real_le_of_fibre (measurableSet_BadChi_joint hn1 J c τ 12)
      (by positivity) (fun A₁ => EChi_prob hn1 J A₁ c τ (by norm_num))
  linarith

/-- On `GoodC`: the bound of `‖H‖²_HS` (Lemma L1 (c) and Lemma HS). -/
theorem GoodC_HS {n : ℕ} (hn : 8192 ≤ n) {J : ℕ} {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC n J c τ) :
    hsH A₁ c τ ≤ 4 * cHSK n K0 * τ ^ 4 * hHn n (thetaC c τ) / n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hint, hB⟩ := hsH_mean (by omega : 8 ≤ n) c hτ K0_pos.le PRvecAbs_K0
  have hb := EH_bound hn1 c τ (by norm_num : (0 : ℝ) ≤ 12) hint hB h.2.1
  have hcH : 0 < cHSK n K0 := by
    have h1 : 0 < 4 * (1 + 2 / (n : ℝ)) / n :=
      div_pos (mul_pos (by norm_num) (by have := div_pos (two_pos (α := ℝ)) hnR; linarith)) hnR
    unfold cHSK
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) h1
  obtain ⟨q, hq⟩ : ∃ q, q = √(√(n : ℝ)) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hnR)
  have hsn : √(n : ℝ) = q ^ 2 := by rw [hq, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hnq : (n : ℝ) = q ^ 4 := by rw [hq, sqrt_sqrt_pow4 hnR.le]
  obtain ⟨k, hk⟩ : ∃ k, k = √(√(4 * cHSK n K0)) := ⟨_, rfl⟩
  have hk0 : 0 < k := by
    rw [hk]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hk4 : 4 * cHSK n K0 = k ^ 4 := by rw [hk, sqrt_sqrt_pow4 (by positivity)]
  have hρ := rhoC_posP hn1 c hτ
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = rhoC c τ := ⟨_, rfl⟩
  rw [← hρd] at hρ
  have ea : aHn n = 2 * √24 / (k * (q ^ 2 * q)) := by
    unfold aHn
    rw [hk, ← hsn, hq]
  have eθ : √(thetaC c τ) = τ * q ^ 2 / ρ := by
    have e : thetaC c τ = (τ * q ^ 2 / ρ) ^ 2 := by
      unfold thetaC
      rw [← hρd, hnq]
      ring
    rw [e, Real.sqrt_sq (by positivity)]
  have e1 : √(√(4 * cHSK n K0 * τ ^ 4 / n)) = k * τ / q := by
    have e : 4 * cHSK n K0 * τ ^ 4 / n = (k * τ / q) ^ 4 := by
      rw [hk4, hnq]
      ring
    rw [e, sqrt_sqrt_of_pow4 (by positivity)]
  have e24 : (2 : ℝ) * 12 = 24 := by norm_num
  have eρ : √(normSq c + (n : ℝ) * τ ^ 2) = ρ := hρd.symm
  rw [e1, e24, eρ, hsn] at hb
  have eR : 4 * cHSK n K0 * τ ^ 4 * hHn n (thetaC c τ) / n =
      (k * τ / q + 2 * √24 * ρ / ((n : ℝ) * q ^ 2)) ^ 4 := by
    unfold hHn
    rw [ea, eθ, hk4, hnq]
    field_simp
  rw [eR]
  exact hb

/-- **The centre bounds on `GoodC`** (Lemma MA (ii), (iv), Lemma MP (a), (b), Proposition FC
(iii)), with `θ = θ_in = thetaC c τ`. `hϱ`, `he` are numerical conditions. -/
theorem GoodC_centre {n : ℕ} (hn : 8192 ≤ n) {J : ℕ} (hJ : 1 ≤ J) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h : (A₁, A₂) ∈ GoodC n J c τ)
    (hϱ : rhoBar n csC < 1 / 4)
    (he : eMP n (11 / 1000) (xiCn n (thetaC c τ)) (bN n csC (thetaC c τ)) ≤ 1 / 10) :
    dC A₁ A₂ c τ ≤ rhoC c τ * √(2 / (n : ℝ) / n) * cD n 12 (11 / 1000) (xiCn n (thetaC c τ)) ∧
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cD n 12 (11 / 1000) (xiCn n (thetaC c τ)) +
        xiNr n (thetaC c τ) (12578 / 10000)) ∧
    rhoC c τ * √(2 / (n : ℝ)) * plow n (11 / 1000) ≤ Pb A₁ c τ A₂ ∧
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤
      √(2 / (n : ℝ) / n) *
        (LamMP n 12 (11 / 1000) (xiCn n (thetaC c τ)) (bN n csC (thetaC c τ)) +
          xiNr n (thetaC c τ) (12578 / 10000)) ∧
    √(2 / ((mA n : ℕ) : ℝ)) * nrm (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ ≤
      epsJ n J J (wn n) csC (11 / 1000) (deltaChi n 12) * √(2 / (n : ℝ) / n) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm := BstLean.Part130.one_le_mA hn1
  have hAs := h.1
  have hD := h.2.2.1
  have hPi := h.2.2.2.1
  have hPb := h.2.2.2.2.1
  have hChi := h.2.2.2.2.2
  obtain ⟨⟨hop, hop2, -⟩, hΓ, ⟨-, -, hN22, -, -⟩, hsc0⟩ := BstLean.Part153.AStage_bounds hn hAs
  have hXi := (BstLean.Part153.AStage_Xi hn hτ hAs).1
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hcs := csC_pos
  have hρ2 := rhoC_sqP c τ
  have hρ := rhoC_posP hn1 c hτ
  rw [← hρ2] at hΓ
  have hΓ' : GamS A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    have := (abs_le.mp hΓ).2
    linarith
  have hHS := GoodC_HS hn hτ h
  obtain ⟨-, hmean0⟩ := MA_i hn1 A₁ c hτ (K := K0) Ures_le_K0 hcs hϱ hop2 hsc hHS
  have hmean : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * xiCn n (thetaC c τ) := hmean0
  have hcross := MA_cross hn1 A₁ c hτ hcs hϱ hop2 hsc
  have hξ : 0 ≤ xiCn n (thetaC c τ) := by
    have h0 : 0 ≤ ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) :=
      integral_nonneg fun _ => sq_nonneg _
    exact nonneg_of_mul_nonneg_right (h0.trans hmean) (by positivity)
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  have hrb : 0 < rhoBar n csC := by unfold rhoBar; positivity
  have hθ := (thetaC_bounds hn1 c hτ).1
  have hbn : 0 ≤ bN n csC (thetaC c τ) := by
    have hQ := QB_nonneg_Event hrb.le (piBar_nonneg (rhoBar n csC))
    unfold bN
    positivity
  have c1 := MA_ii hn1 A₁ A₂ c τ (Lc := 12) (δe := 11 / 1000) (by norm_num) (by norm_num) hξ
    hmean hΓ' hD
  have c2 := MA_iv (by omega : 6 ≤ n) A₁ A₂ c hτ (MP := 12578 / 10000) (by norm_num) c1 hN22 hXi
  have c3 := MP_a hn A₁ A₂ c hτ hΓ hPb
  have hΛ := MP_b hn A₁ A₂ c hτ hξ hbn he hΓ hmean hcross hD hPi hPb
  have c4 := MP_b_final hn A₁ A₂ c hτ (MP := 12578 / 10000) (by norm_num) hΛ hN22 hXi
  have hEe : gO A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm]
    exact hΓ'
  have c5 := FC_iii hn1 hJ A₁ A₂ c hτ hcs (δe := 11 / 1000) (Lc := 12) (by norm_num)
    (by norm_num) hop hsc hEe hChi
  exact ⟨c1, c2, c3, c4, c5⟩

end BstLean.Part154
