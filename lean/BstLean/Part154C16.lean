import BstLean.Part154Event

/-!
# Part 154: the event `GoodC16` (`n ≥ 16384`, `M_P = 1.1911`) and the centre bounds on it
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part153 (nrm GamS wn Eop Pb XiS Xi4 N2 hid2Mean_cr GoodAs GoodAs16 nuA N22bar N24bar)

/-- The event `GoodC` with the covariance event at `M_P = 1.1911` (`GoodAs16` of Part 153). -/
def GoodC16 (n J : ℕ) (c : Fin n → ℝ) (τ : ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :=
  {θ | θ ∈ GoodC n J c τ ∧ θ ∈ GoodAs16 n c τ}

private lemma QB_nonneg_C16 {ϱ πg : ℝ} (h : 0 ≤ ϱ) (_hπ : 0 ≤ πg) : 0 ≤ QB ϱ πg := by
  have p0 := (BstLean.Part153.phiG_pos 0).le
  have p1 := (BstLean.Part153.phiG_pos 1).le
  have hν : 0 ≤ nuR ϱ := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 ϱ πg := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 ϱ πg := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 ϱ := by unfold cc2; positivity
  unfold QB
  positivity

private lemma csC_pos_C16 : 0 < csC := by
  have h : 1 / π < 1 := by
    rw [div_lt_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  unfold csC
  exact mul_pos (by norm_num) (by linarith)

private lemma GoodAs16_sub_C16 {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    GoodAs16 n c τ ⊆ GoodAs n c τ := by
  intro θ hθ
  obtain ⟨h1, h2, h3⟩ := hθ
  refine ⟨h1, h2, fun hb => h3 ?_⟩
  have hb' : (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n < BstLean.Part153.Xi4 θ.1 θ.2 c τ := hb
  have h0 : (0 : ℝ) ≤ 2 / (n : ℝ) / n := by positivity
  show (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n < BstLean.Part153.Xi4 θ.1 θ.2 c τ
  have e1 : (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n = 11911 / 10000 * (2 / (n : ℝ) / n) := by ring
  have e2 : (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n = 12578 / 10000 * (2 / (n : ℝ) / n) := by ring
  rw [e1]
  rw [e2] at hb'
  nlinarith

theorem GoodC16_prob {n : ℕ} (hn : 16384 ≤ n) (J : ℕ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodC16 n J c τ)ᶜ ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 := by
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hsub : (GoodC16 n J c τ)ᶜ ⊆
      ((((((GoodAs16 n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}) ∪ {θ | θ.2 ∈ BadPb θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadChi n J θ.1 c τ 12}) := by
    intro θ hθ
    by_contra h
    apply hθ
    have h0 : θ ∈ GoodAs16 n c τ :=
      not_not.mp fun h0 => h (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h0)))))
    refine ⟨⟨GoodAs16_sub_C16 c τ h0,
      fun h1 => h (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))),
      fun h2 => h (Or.inl (Or.inl (Or.inl (Or.inr h2)))),
      fun h3 => h (Or.inl (Or.inl (Or.inr h3))),
      fun h4 => h (Or.inl (Or.inr h4)), fun h5 => h (Or.inr h5)⟩, h0⟩
  have g0 := measureReal_mono (μ := nuA n) hsub
  have g1 := measureReal_union_le (μ := nuA n)
    (((((GoodAs16 n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}) ∪ {θ | θ.2 ∈ BadPb θ.1 c τ 12})
    {θ | θ.2 ∈ BadChi n J θ.1 c τ 12}
  have g2 := measureReal_union_le (μ := nuA n)
    ((((GoodAs16 n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12}) ∪
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}) {θ | θ.2 ∈ BadPb θ.1 c τ 12}
  have g3 := measureReal_union_le (μ := nuA n)
    (((GoodAs16 n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) ∪ {θ | θ.2 ∈ BadD θ.1 c τ 12})
        {θ | θ.2 ∈ BadPi θ.1 c τ 12}
  have g4 := measureReal_union_le (μ := nuA n)
    ((GoodAs16 n c τ)ᶜ ∪ {θ | θ.1 ∈ BadH n c τ 12}) {θ | θ.2 ∈ BadD θ.1 c τ 12}
  have g5 := measureReal_union_le (μ := nuA n)
    (GoodAs16 n c τ)ᶜ {θ | θ.1 ∈ BadH n c τ 12}
  have e0 := BstLean.Part153.AStage16_prob hn c hτ
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

/-- The centre bounds of `GoodC_centre` with `M_P = 1.1911`, and the facts of Part 153 that the
transport lemma needs (`Ξ₄`, `N₂₂`, `N₂₄`, the oracle energy ratio). -/
theorem GoodC16_centre {n : ℕ} (hn : 16384 ≤ n) {J : ℕ} (hJ : 1 ≤ J) {c : Fin n → ℝ} {τ : ℝ}
    (hτ : 0 < τ) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h : (A₁, A₂) ∈ GoodC16 n J c τ)
    (hϱ : rhoBar n csC < 1 / 4)
    (he : eMP n (11 / 1000) (xiCn n (thetaC c τ)) (bN n csC (thetaC c τ)) ≤ 1 / 10)
    {θlo : ℝ} (hθ : θlo ≤ thetaC c τ) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (cD n 12 (11 / 1000) (xiCn n (thetaC c τ)) +
        xiNr n (thetaC c τ) (11911 / 10000)) ∧
    rhoC c τ * √(2 / (n : ℝ)) * plow n (11 / 1000) ≤ Pb A₁ c τ A₂ ∧
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm (bO A₁ A₂ c τ))⁻¹ • bO A₁ A₂ c τ)| ≤
      √(2 / (n : ℝ) / n) *
        (LamMP n 12 (11 / 1000) (xiCn n (thetaC c τ)) (bN n csC (thetaC c τ)) +
          xiNr n (thetaC c τ) (11911 / 10000)) ∧
    √(2 / ((mA n : ℕ) : ℝ)) * nrm (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ ≤
      epsJ n J J (wn n) csC (11 / 1000) (deltaChi n 12) * √(2 / (n : ℝ) / n) ∧
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (csC / 2) * θlo ∧
    Xi4 A₁ A₂ c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n ∧
    N2 2 A₁ A₂ c τ ≤ N22bar n 12 ∧ N2 4 A₁ A₂ c τ ≤ N24bar n 12 := by
  have hn8 : 8192 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm := BstLean.Part130.one_le_mA hn1
  have h16 := h.2
  have h := h.1
  have hAs := h.1
  have hD := h.2.2.1
  have hPi := h.2.2.2.1
  have hPb := h.2.2.2.2.1
  have hChi := h.2.2.2.2.2
  obtain ⟨⟨hop, hop2, -⟩, hΓ, -, hsc0⟩ := BstLean.Part153.AStage_bounds hn8 hAs
  obtain ⟨-, -, hN22, hN24, -⟩ := BstLean.Part153.GoodA_norms hn1 h16
  have hXi := BstLean.Part153.AStage16_Xi hn hτ h16
  have hX4 : Xi4 A₁ A₂ c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n :=
    not_lt.mp (BstLean.Part153.GoodA_unpack h16).2.2.2.2.2.2.2.2
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hcs := csC_pos_C16
  have hρ2 := rhoC_sqP c τ
  have hρ := rhoC_posP hn1 c hτ
  have heb0 := BstLean.Part153.AStage_eb hn8 hτ (θlo := θlo)
    (by rw [← hρ2]; exact hθ) hAs
  rw [← hρ2] at heb0
  have heb : 2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (csC / 2) * θlo := heb0
  rw [← hρ2] at hΓ
  have hΓ' : GamS A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    have := (abs_le.mp hΓ).2
    linarith
  have hHS := GoodC_HS hn8 hτ h
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
  have hθ0 := (thetaC_bounds hn1 c hτ).1
  have hbn : 0 ≤ bN n csC (thetaC c τ) := by
    have hQ := QB_nonneg_C16 hrb.le (piBar_nonneg (rhoBar n csC))
    unfold bN
    positivity
  have c1 := MA_ii hn1 A₁ A₂ c τ (Lc := 12) (δe := 11 / 1000) (by norm_num) (by norm_num) hξ
    hmean hΓ' hD
  have c2 := MA_iv (by omega : 6 ≤ n) A₁ A₂ c hτ (MP := 11911 / 10000) (by norm_num) c1 hN22 hXi
  have c3 := MP_a hn8 A₁ A₂ c hτ hΓ hPb
  have hΛ := MP_b hn8 A₁ A₂ c hτ hξ hbn he hΓ hmean hcross hD hPi hPb
  have c4 := MP_b_final hn8 A₁ A₂ c hτ (MP := 11911 / 10000) (by norm_num) hΛ hN22 hXi
  have hEe : gO A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm]
    exact hΓ'
  have c5 := FC_iii hn1 hJ A₁ A₂ c hτ hcs (δe := 11 / 1000) (Lc := 12) (by norm_num)
    (by norm_num) hop hsc hEe hChi
  exact ⟨c2, c3, c4, c5, heb, hX4, hN22, hN24⟩

end BstLean.Part154
