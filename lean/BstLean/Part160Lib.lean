import BstLean.Part160Split

/-!
# Part 160 (file `Lib`): what the library gives for the covariance and the centre

Role: `delegations/statements/p160-spec.md`, item 2. Do not use `sorry`, `native_decide` or
`axiom`.

* `centre16`: the centre bounds of Part 154 on the event `GoodC16 n n c τ` (`n ≥ 16 384`,
  `0.46 ≤ θ_in ≤ 0.55`), for the centre `b = bT n n A₁ A₂ c τ/ρ`. It is a copy of the private
  lemma `centreVOK` of `Part154VOK.lean` (same proof).
* `cov16_at`: `COV_at D c 1.1911` (Gaussian Poincaré and Lemma PP of Part 153).
* `centre16_at`: `CENTRE_at D c 0.485` (the mean-field lemma and the centre lemmas of Part 154).
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (lam res sig)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 N2 sq2 hid2Mean_cr Pb)

lemma le_sqrt_L {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y) : x ≤ √y := by
  rw [← Real.sqrt_sq hx]
  exact Real.sqrt_le_sqrt h

/-- **The centre bounds on `GoodC16`** with the numbers of `Part154Num16` (Lemma TF): the centre
error `ξ_hp ≤ 0.485`, the parallel error `ξ_∥ ≤ 0.028`, the centre energy `e_b ≤ 0.82`, `b ≠ 0`,
`Ξ₄ ≤ 1.1911 γ_A/n`, `N₂₂ ≤ 18.334/n`, `N₂₄ ≤ 24.779/n`. -/
theorem centre16 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      485 / 1000 * (2 / (n : ℝ)) / n ∧
    |√(2 / (mA n : ℝ)) * ((∑ j, (hid2Mean_cr A₁ A₂ c τ j -
        ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) j) * ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) j) /
        √(normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ)))| ≤ √(280 / 10000 * (2 / (n : ℝ)) / n) ∧
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤ 2 / (n : ℝ) * (82 / 100) ∧
    0 < normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ∧
    Xi4 A₁ A₂ c τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n ∧
    N2 2 A₁ A₂ c τ ≤ 18334 / 1000 / (n : ℝ) ∧ N2 4 A₁ A₂ c τ ≤ 24779 / 1000 / (n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hρ := rhoC_posP hn1 c hτ
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := GoodC16_centre hn hn1 hτ h (rhoBar_lt16 hn)
    (eMP_le16 hn hθ0 hθ1) (θlo := 46 / 100) hθ0
  obtain ⟨-, hN22, -, hN24⟩ := Nbar_le16 hn
  obtain ⟨hε0, hε⟩ := epsJ_le16 hn
  have hx1 := x1_le16 hn hθ0 hθ1
  have hx2 := x2_le16 hn hθ0 hθ1
  have hpl := plow_ge16 hn
  have hebo := ebo_le16
  have g2' : rhoC c τ * √(2 / (n : ℝ)) * plow n (11 / 1000) ≤
      √(2 / (mA n : ℝ)) * nrm (bO A₁ A₂ c τ) := g2
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have hsX : √(2 / (mA n : ℝ)) = √(2 / (n : ℝ) / n) := by
    rw [hmR]; congr 1; field_simp
  have hs2 : √(2 / (mA n : ℝ)) ^ 2 = 2 / (mA n : ℝ) := Real.sq_sqrt (by positivity)
  rw [hsX] at g1 g2' g3 g4 ⊢
  rw [hsX] at hs2
  set X := √(2 / (n : ℝ) / n) with hX
  have hX2 : X ^ 2 = 2 / (n : ℝ) / n := Real.sq_sqrt (by positivity)
  have hX0 : 0 < X := Real.sqrt_pos.mpr (by positivity)
  have hrn0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  have hrn : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [show (128 : ℝ) = √(128 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    have e : (128 : ℝ) ^ 2 = 16384 := by norm_num
    exact Real.sqrt_le_sqrt (by linarith only [hnR, e])
  have hXn : X * √(n : ℝ) = √(2 / (n : ℝ)) := by
    rw [hX, ← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  have hg0 : 0 < √(2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  set a := hid2Mean_cr A₁ A₂ c τ with ha
  set bo := bO A₁ A₂ c τ with hbo
  set bt := bT n n A₁ A₂ c τ with hbt
  set ρ := rhoC c τ with hρd
  have hρi : 0 < ρ⁻¹ := inv_pos.mpr hρ
  -- the hypotheses of `TF_vec`
  have h1 : X * nrm (a - ρ⁻¹ • bo) ≤ X * (6885 / 10000) :=
    g1.trans (mul_le_mul_of_nonneg_left hx1 hX0.le)
  have hunit : (nrm (ρ⁻¹ • bo))⁻¹ • (ρ⁻¹ • bo) = (nrm bo)⁻¹ • bo := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos hρi, smul_smul]
    congr 1
    rw [mul_inv, inv_inv, mul_comm ρ, mul_assoc, mul_inv_cancel₀ hρ.ne', mul_one]
  have h2 : |(X • (a - ρ⁻¹ • bo)) ⬝ᵥ ((nrm (ρ⁻¹ • bo))⁻¹ • (ρ⁻¹ • bo))| ≤
      X * (1595 / 10000) := by
    rw [hunit]
    exact g3.trans (mul_le_mul_of_nonneg_left hx2 hX0.le)
  have h3 : X * √(n : ℝ) * (56 / 100) ≤ X * nrm (ρ⁻¹ • bo) := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos hρi, hXn]
    calc √(2 / (n : ℝ)) * (56 / 100) ≤ √(2 / (n : ℝ)) * plow n (11 / 1000) :=
          mul_le_mul_of_nonneg_left hpl hg0.le
      _ = ρ⁻¹ * (ρ * √(2 / (n : ℝ)) * plow n (11 / 1000)) := by field_simp
      _ ≤ ρ⁻¹ * (X * nrm bo) := mul_le_mul_of_nonneg_left g2' hρi.le
      _ = X * (ρ⁻¹ * nrm bo) := by ring
  have h3' : X * nrm (ρ⁻¹ • bo) ≤ X * √(n : ℝ) * √(819 / 1000) := by
    rw [BstLean.Part153.nrm_smul, abs_of_pos hρi, hXn, ← Real.sqrt_mul (by positivity)]
    refine le_sqrt_L (mul_nonneg hX0.le (mul_nonneg hρi.le (BstLean.Part153.nrm_nonneg _))) ?_
    have hq : 2 / (mA n : ℝ) * normSq bo ≤ 819 / 1000 * (2 / (n : ℝ) * ρ ^ 2) :=
      (div_le_iff₀ (by positivity)).mp (g5.trans hebo)
    calc (X * (ρ⁻¹ * nrm bo)) ^ 2 = ρ⁻¹ ^ 2 * (2 / (mA n : ℝ) * normSq bo) := by
          rw [mul_pow, mul_pow, hs2, BstLean.Part153.nrm_sq]; ring
      _ ≤ ρ⁻¹ ^ 2 * (819 / 1000 * (2 / (n : ℝ) * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left hq (sq_nonneg _)
      _ = 2 / (n : ℝ) * (819 / 1000) := by field_simp
  have h4 : X * nrm ((1 / ρ) • bt - ρ⁻¹ • bo) ≤ X * (75 / 10000) := by
    have e : (1 / ρ) • bt - ρ⁻¹ • bo = ρ⁻¹ • (bt - bo) := by rw [one_div, smul_sub]
    rw [e, BstLean.Part153.nrm_smul, abs_of_pos hρi]
    calc X * (ρ⁻¹ * nrm (bt - bo)) = X * nrm (bt - bo) / ρ := by ring
      _ ≤ epsJ n n n (BstLean.Part153.wn n) csC (11 / 1000) (deltaChi n 12) * X := g4
      _ ≤ 75 / 10000 * X := mul_le_mul_of_nonneg_right hε hX0.le
      _ = X * (75 / 10000) := by ring
  have hεpl : (75 / 10000 : ℝ) / √(n : ℝ) < 56 / 100 := by
    rw [div_lt_iff₀ hrn0]; linarith only [hrn]
  obtain ⟨t1, t2, -, t4, t5⟩ := TF_vec a (ρ⁻¹ • bo) ((1 / ρ) • bt) (x1 := 6885 / 10000)
    (x2 := 1595 / 10000) (pl := 56 / 100) (eo := √(819 / 1000)) (ε := 75 / 10000)
    (rn := √(n : ℝ)) hX0.le hX0 hrn0 (by norm_num) (by norm_num) (by norm_num)
    h1 h2 h3 h3' h4 hεpl
  set b := (1 / ρ) • bt with hb
  have hXX : (0 : ℝ) ≤ 2 / (n : ℝ) / n := by positivity
  have hsmall : (75 / 10000 : ℝ) / √(n : ℝ) ≤ 1 / 10000 := by
    rw [div_le_iff₀ hrn0]; linarith only [hrn]
  refine ⟨?_, ?_, ?_, Real.sqrt_pos.mp t5, g6, g7.trans hN22, g8.trans hN24⟩
  · have h := pow_le_pow_left₀ (mul_nonneg hX0.le (BstLean.Part153.nrm_nonneg _)) t1 2
    rw [mul_pow, mul_pow, hX2, BstLean.Part153.nrm_sq] at h
    rw [← hs2, hX2]
    refine h.trans ?_
    rw [show (485 : ℝ) / 1000 * (2 / (n : ℝ)) / n = 2 / (n : ℝ) / n * (485 / 1000) by ring]
    exact mul_le_mul_of_nonneg_left (by norm_num) hXX
  · have e : (X • (a - b)) ⬝ᵥ ((nrm b)⁻¹ • b) =
        X * ((∑ j, (a j - b j) * b j) / √(normSq b)) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, div_eq_inv_mul]
      rfl
    rw [e] at t2
    refine t2.trans (le_sqrt_L (mul_nonneg hX0.le (by positivity)) ?_)
    have hq : 2 * (6885 / 10000 : ℝ) / (56 / 100 * √(n : ℝ)) ≤ 2 / 100 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [hrn]
    have hq0 : (0 : ℝ) ≤ 2 * (6885 / 10000 : ℝ) / (56 / 100 * √(n : ℝ)) := by positivity
    have hK : (1595 / 10000 + 75 / 10000 * (1 + 2 * (6885 / 10000 : ℝ) / (56 / 100 * √(n : ℝ)))) ^ 2
        ≤ 280 / 10000 := by
      refine (pow_le_pow_left₀ (by positivity)
        (show (1595 / 10000 + 75 / 10000 * (1 + 2 * (6885 / 10000 : ℝ) / (56 / 100 * √(n : ℝ))))
          ≤ 16715 / 100000 by linarith only [hq]) 2).trans (by norm_num)
    rw [mul_pow, hX2,
      show (280 : ℝ) / 10000 * (2 / (n : ℝ)) / n = 2 / (n : ℝ) / n * (280 / 10000) by ring]
    exact mul_le_mul_of_nonneg_left hK hXX
  · have h := pow_le_pow_left₀ (mul_nonneg hX0.le (BstLean.Part153.nrm_nonneg _)) t4 2
    rw [hXn, mul_pow, mul_pow, hX2, BstLean.Part153.nrm_sq,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ))] at h
    rw [← hs2, hX2]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hsq : √(819 / 1000 : ℝ) ≤ 905 / 1000 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have h0 : (0 : ℝ) ≤ 75 / 10000 / √(n : ℝ) := by positivity
    exact (pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) h0)
      (show √(819 / 1000 : ℝ) + 75 / 10000 / √(n : ℝ) ≤ 9051 / 10000 by
        linarith only [hsq, hsmall]) 2).trans
      (by norm_num)

variable {n : ℕ}

/-- **(COV) from the library**: on `GoodC16`, `t_A·Var_ξ⟨h, w⟩ ≤ 1.1911·(γ_A/n)·|w|²`. It uses
the Gaussian Poincaré inequality (`cov_hid2_le`) and the moment bound PP of the tangent Jacobian
(`lemmaPP_numeric_16384`, inside the event). The noncentrality factor `θ_in` is not used. -/
theorem cov16_at (hn : 16384 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (h : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c)) :
    COV_at D c (11911 / 10000) := by
  intro w
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hX := BstLean.Part153.AStage16_Xi hn hτ h.2
  have h1 := BstLean.Part153.cov_hid2_le hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ w
  have e : ∀ ξ, ∑ j, (hStand D c ξ j - muStand D c j) * w j =
      w ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) -
        ∫ ξ', w ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ')) ∂stdGauss (Fin n) := by
    intro ξ
    rw [BstLean.Part153.integral_dot_hid2_cr hn1]
    unfold dotProduct
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) j -
      hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) j) * w j = _
    ring
  simp_rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right hX (normSq_nonneg w))

/-- **(CENTRE) from the library**: on `GoodC16`, in the window `0.46 ≤ θ_in ≤ 0.55`, for the
centre of Part 154: `t_A·|μ − b|² ≤ 0.485·γ_A/n`. -/
theorem centre16_at (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (h : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c)) :
    CENTRE_at D c (485 / 1000) := by
  unfold CENTRE_at
  rw [hD c, muStand_eq]
  exact (centre16 hn hτ hθ0 hθ1 h).1

end BstLean.Part160

open BstLean.Part160 in
#print axioms centre16
open BstLean.Part160 in
#print axioms cov16_at
open BstLean.Part160 in
#print axioms centre16_at
