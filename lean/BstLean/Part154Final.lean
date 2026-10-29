import BstLean.Part154Num

/-!
# Part 154: the centre errors of Theorem 5 on one event of `(A₁, A₂)`, with numbers

For `n ≥ 8192`, a fixed `W` stage `(c, τ)` with `τ > 0` and `0.46 ≤ θ_in ≤ 0.541`, `J = n` atoms.
`a = ā₂`, `bo = b° = b′°/ρ` (the oracle centre), `b = b′/ρ` (the centre of the program),
`s = √t_A`, `X = √(γ_A/n)`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part134 (res)
open BstLean.Part153 (nrm GamS wn Eop Pb XiS N2 hid2Mean_cr GoodAs nuA)

/-- **The centre errors on `GoodC`** (Lemma MA (iv), Lemma MP, Proposition FC (iii), Lemma TF
(a) to (d)): `ξ°_hp ≤ 0.7422²`, `ξ°_∥ ≤ 0.2270²`, `ξ_hp ≤ 0.7528² ≤ 0.5668`, `ξ_∥ ≤ 0.238²`,
`0.549·√γ_A ≤ √t_A|b| ≤ 0.906·√γ_A`, and `‖C_r‖_op ≤ (1.2578 + 0.5668)·γ_A/n`. -/
theorem centre154 {n : ℕ} (hn : 8192 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 541 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC n n c τ) :
    √(2 / ((mA n : ℕ) : ℝ)) * nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (7422 / 10000) ∧
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bO A₁ A₂ c τ)) ⬝ᵥ
        ((nrm ((rhoC c τ)⁻¹ • bO A₁ A₂ c τ))⁻¹ • ((rhoC c τ)⁻¹ • bO A₁ A₂ c τ))| ≤
      √(2 / (n : ℝ) / n) * (2270 / 10000) ∧
    √(2 / ((mA n : ℕ) : ℝ)) * nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (7528 / 10000) ∧
    |(√(2 / ((mA n : ℕ) : ℝ)) • (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ)) ⬝ᵥ
        ((nrm ((rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ))⁻¹ • ((rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ))| ≤
      √(2 / (n : ℝ) / n) * (238 / 1000) ∧
    √(2 / (n : ℝ)) * (549 / 1000) ≤
      √(2 / ((mA n : ℕ) : ℝ)) * nrm ((rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ) ∧
    √(2 / ((mA n : ℕ) : ℝ)) * nrm ((rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ) ≤
      √(2 / (n : ℝ)) * (906 / 1000) ∧
    (∀ w : Fin (mA n) → ℝ,
      2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ res ((rhoC c τ)⁻¹ • bT n n A₁ A₂ c τ)
          (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ^ 2 ∂stdGauss (Fin n) ≤
        (12578 / 10000 + 5668 / 10000) * (2 / (n : ℝ)) / n * normSq w) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hρ := rhoC_posP hn1 c hτ
  have hρ2 := rhoC_sqP c τ
  have hρi : 0 < (rhoC c τ)⁻¹ := inv_pos.mpr hρ
  obtain ⟨ρ, hρd⟩ : ∃ ρ, ρ = rhoC c τ := ⟨_, rfl⟩
  rw [← hρd] at hρ hρ2 hρi ⊢
  obtain ⟨s, hsd⟩ : ∃ s, s = √(2 / ((mA n : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X, X = √(2 / (n : ℝ) / n) := ⟨_, rfl⟩
  obtain ⟨rn, hrnd⟩ : ∃ rn, rn = √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y, Y = √(2 / (n : ℝ)) := ⟨_, rfl⟩
  have hmpos : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    exact_mod_cast BstLean.Part130.one_le_mA hn1
  have hs0 : 0 ≤ s := by rw [hsd]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 / ((mA n : ℕ) : ℝ) := by rw [hsd]; exact Real.sq_sqrt (by positivity)
  have hX : 0 < X := by rw [hXd]; exact Real.sqrt_pos.mpr (by positivity)
  have hX2 : X ^ 2 = 2 / (n : ℝ) / n := by rw [hXd]; exact Real.sq_sqrt (by positivity)
  have hY : 0 < Y := by rw [hYd]; exact Real.sqrt_pos.mpr (by positivity)
  have hY2 : Y ^ 2 = 2 / (n : ℝ) := by rw [hYd]; exact Real.sq_sqrt (by positivity)
  have hrn : (905 / 10 : ℝ) ≤ rn := by
    rw [hrnd]
    apply Real.le_sqrt_of_sq_le
    have : (8192 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [this]
  have hrn0 : 0 < rn := by linarith only [hrn]
  have hXrn : X * rn = Y := by
    rw [hXd, hrnd, hYd, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [← hsd, ← hXd, ← hYd]
  obtain ⟨-, g1, g3, g2, g4⟩ :=
    GoodC_centre hn hn1 hτ h (rhoBar_lt hn) (eMP_le hn hθ0 hθ1)
  rw [← hρd, ← hsd, ← hXd] at g1 g2 g4
  rw [← hρd, ← hYd] at g3
  obtain ⟨a, had⟩ : ∃ a, a = hid2Mean_cr A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨BO, hBOd⟩ : ∃ B, B = bO A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨BT, hBTd⟩ : ∃ B, B = bT n n A₁ A₂ c τ := ⟨_, rfl⟩
  have hPb : Pb A₁ c τ A₂ = s * nrm BO := by rw [hsd, hBOd]; rfl
  rw [hPb] at g3
  rw [← had, ← hBOd] at g1 g2
  rw [← hBOd, ← hBTd] at g4
  rw [← had, ← hBOd, ← hBTd]
  -- the four inputs of Lemma TF
  have c1 : s * nrm (a - ρ⁻¹ • BO) ≤ X * (7422 / 10000) :=
    g1.trans (mul_le_mul_of_nonneg_left (x1_le hn hθ0 hθ1) hX.le)
  have hnbo : nrm (ρ⁻¹ • BO) = ρ⁻¹ * nrm BO := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos hρi]
  have hunit : (nrm (ρ⁻¹ • BO))⁻¹ • (ρ⁻¹ • BO) = (nrm BO)⁻¹ • BO := by
    rw [hnbo, smul_smul, mul_inv, inv_inv]
    congr 1
    calc ρ * (nrm BO)⁻¹ * ρ⁻¹ = (nrm BO)⁻¹ * (ρ * ρ⁻¹) := by ring
      _ = (nrm BO)⁻¹ := by rw [mul_inv_cancel₀ hρ.ne', mul_one]
  have c2 : |(s • (a - ρ⁻¹ • BO)) ⬝ᵥ ((nrm (ρ⁻¹ • BO))⁻¹ • (ρ⁻¹ • BO))| ≤
      X * (2270 / 10000) := by
    rw [hunit]
    exact g2.trans (mul_le_mul_of_nonneg_left (x2_le hn hθ0 hθ1) hX.le)
  have h3 : X * rn * (56 / 100) ≤ s * nrm (ρ⁻¹ • BO) := by
    rw [hnbo, hXrn]
    have k1 : Y * (56 / 100) ≤ Y * plow n (11 / 1000) :=
      mul_le_mul_of_nonneg_left (plow_ge hn) hY.le
    have k2 : ρ⁻¹ * (ρ * Y * plow n (11 / 1000)) ≤ ρ⁻¹ * (s * nrm BO) :=
      mul_le_mul_of_nonneg_left g3 hρi.le
    have k3 : ρ⁻¹ * (ρ * Y * plow n (11 / 1000)) = Y * plow n (11 / 1000) := by
      field_simp
    linarith only [k1, k2, k3]
  have hθeq : thetaC c τ = (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) := by
    unfold thetaC; rw [← hρd, hρ2]
  have heb := BstLean.Part153.AStage_eb hn hτ (θlo := 46 / 100) (by rw [← hθeq]; exact hθ0) h.1
  rw [← hBOd, ← hρ2] at heb
  have hebo := ebo_le
  unfold csC at hebo
  have heb2 : 2 / ((mA n : ℕ) : ℝ) * normSq BO ≤ 819 / 1000 * (2 / (n : ℝ) * ρ ^ 2) := by
    have hd : (0 : ℝ) < 2 / (n : ℝ) * ρ ^ 2 := by positivity
    have := (div_le_iff₀ hd).mp (heb.trans hebo)
    exact this
  have hsq819 : √(819 / 1000 : ℝ) ^ 2 = 819 / 1000 := Real.sq_sqrt (by norm_num)
  have h3' : s * nrm (ρ⁻¹ • BO) ≤ X * rn * √(819 / 1000) := by
    rw [hnbo, hXrn]
    have hl : 0 ≤ s * (ρ⁻¹ * nrm BO) :=
      mul_nonneg hs0 (mul_nonneg hρi.le (BstLean.Part153.nrm_nonneg _))
    have hr : 0 ≤ Y * √(819 / 1000) := mul_nonneg hY.le (Real.sqrt_nonneg _)
    refine (pow_le_pow_iff_left₀ hl hr (two_ne_zero)).mp ?_
    have e1 : (s * (ρ⁻¹ * nrm BO)) ^ 2 = (ρ⁻¹) ^ 2 * (2 / ((mA n : ℕ) : ℝ) * normSq BO) := by
      rw [mul_pow, mul_pow, hs2, BstLean.Part153.nrm_sq]; ring
    have e2 : (Y * √(819 / 1000)) ^ 2 = (ρ⁻¹) ^ 2 * (819 / 1000 * (2 / (n : ℝ) * ρ ^ 2)) := by
      rw [mul_pow, hY2, hsq819]; field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left heb2 (by positivity)
  have h4 : s * nrm (ρ⁻¹ • BT - ρ⁻¹ • BO) ≤ X * (106 / 10000) := by
    rw [← smul_sub, BstLean.Part153.nrm_smul, abs_of_pos hρi]
    have k1 : s * (ρ⁻¹ * nrm (BT - BO)) = s * nrm (BT - BO) / ρ := by
      rw [div_eq_mul_inv]; ring
    rw [k1]
    have k2 := mul_le_mul_of_nonneg_right (epsJ_le hn).2 hX.le
    linarith only [g4, k2]
  have hεpl : (106 / 10000 : ℝ) / rn < 56 / 100 := by
    rw [div_lt_iff₀ hrn0]; linarith only [hrn]
  have hεr : (106 / 10000 : ℝ) / rn ≤ 1 / 1000 := by
    rw [div_le_iff₀ hrn0]; linarith only [hrn]
  have hx1r : 2 * (7422 / 10000 : ℝ) / (56 / 100 * rn) ≤ 293 / 10000 := by
    rw [div_le_iff₀ (by positivity)]; linarith only [hrn]
  have hs819 : √(819 / 1000 : ℝ) ≤ 905 / 1000 := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num
  obtain ⟨t1, t2, t3, t4, t5⟩ := TF_vec a (ρ⁻¹ • BO) (ρ⁻¹ • BT) hs0 hX hrn0
    (by norm_num : (0 : ℝ) < 56 / 100) (by norm_num : (0 : ℝ) ≤ 106 / 10000)
    (by norm_num : (0 : ℝ) ≤ 7422 / 10000) c1 c2 h3 h3' h4 hεpl
  rw [hXrn] at t3 t4
  have c3 : s * nrm (a - ρ⁻¹ • BT) ≤ X * (7528 / 10000) := by
    linarith only [t1]
  refine ⟨c1, c2, c3, ?_, ?_, ?_, ?_⟩
  · refine t2.trans (mul_le_mul_of_nonneg_left ?_ hX.le)
    nlinarith only [hx1r]
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ hY.le) t3
    linarith only [hεr]
  · refine t4.trans (mul_le_mul_of_nonneg_left ?_ hY.le)
    linarith only [hεr, hs819]
  · intro w
    have hb : normSq (ρ⁻¹ • BT) ≠ 0 := by
      rw [← BstLean.Part153.nrm_sq]; exact (pow_pos t5 2).ne'
    have hr := BstLean.Part153.resCov_le_cr (by omega : 6 ≤ n) A₁ A₂ c hτ hb w
    rw [← had] at hr
    refine hr.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg w))
    have hXi := (BstLean.Part153.AStage_Xi hn hτ h.1).1
    have e1 : 2 / ((mA n : ℕ) : ℝ) * normSq (a - ρ⁻¹ • BT) = (s * nrm (a - ρ⁻¹ • BT)) ^ 2 := by
      rw [mul_pow, hs2, BstLean.Part153.nrm_sq]
    have hl : 0 ≤ s * nrm (a - ρ⁻¹ • BT) := mul_nonneg hs0 (BstLean.Part153.nrm_nonneg _)
    have e2 : (s * nrm (a - ρ⁻¹ • BT)) ^ 2 ≤ (X * (7528 / 10000)) ^ 2 :=
      pow_le_pow_left₀ hl c3 2
    have e3 : (X * (7528 / 10000)) ^ 2 ≤ 5668 / 10000 * (2 / (n : ℝ)) / n := by
      rw [mul_pow, hX2]
      have h0 : (0 : ℝ) ≤ 2 / (n : ℝ) / n := by positivity
      have e : 5668 / 10000 * (2 / (n : ℝ)) / n = 5668 / 10000 * (2 / (n : ℝ) / n) := by ring
      rw [e]
      linarith only [h0]
    rw [e1]
    have e4 : (12578 / 10000 + 5668 / 10000) * (2 / (n : ℝ)) / n =
        12578 / 10000 * (2 / (n : ℝ)) / n + 5668 / 10000 * (2 / (n : ℝ)) / n := by ring
    rw [e4]
    exact add_le_add hXi (e2.trans e3)

/-- The charge of the event (restated): `Pr(GoodCᶜ) ≤ e^{−n/2} + 13e^{−12} + 3445/n² + 5·10⁻⁵`. -/
theorem centre154_prob {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (GoodC n n c τ)ᶜ ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 :=
  GoodC_prob hn n c hτ

end BstLean.Part154
