import BstLean.Part154C16
import BstLean.Part154Num16
import BstLean.Part154Win
import BstLean.Part154Phi
import BstLean.Part154Fin
import BstLean.Part151AllB

/-!
# Part 154: the hypotheses of `theorem5_frameProgG` (Part 151) on the event `GoodC16`
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part141 (cenA tauWA)
open BstLean.Part151 (VOK hU v1V eBV sigU lamU phiV ellSqV uV rhoV v1V_mean)
open BstLean.Part134 (lam res sig)
open BstLean.Part148 (EuLip)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 N2 sq2 hid2Mean_cr Pb)
open scoped ENNReal


section genVOK

variable {m : ℕ}

private lemma le_sqrt_VOK {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y) : x ≤ √y := by
  rw [← Real.sqrt_sq hx]
  exact Real.sqrt_le_sqrt h

/-- Pythagoras: `|h|² = ⟨h, b⟩²/|b|² + |res b h|²`. -/
private lemma pyth_VOK {b : Fin m → ℝ} (hb : 0 < normSq b) (h : Fin m → ℝ) :
    normSq h = (h ⬝ᵥ b) ^ 2 / normSq b + normSq (res b h) := by
  rw [BstLean.Part136.normSq_res hb.ne']
  unfold dotProduct
  ring

private lemma res_sub_VOK (b x y : Fin m → ℝ) : res b x - res b y = res b (x - y) := by
  have e : ∑ j, (x j - y j) * b j = ∑ j, x j * b j - ∑ j, y j * b j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  ext j
  simp only [res, lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
  ring

private lemma res_smul_VOK (b h : Fin m → ℝ) (s : ℝ) : res b (s • h) = s • res b h := by
  have e : ∑ j, s * h j * b j = s * ∑ j, h j * b j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  ext j
  simp only [res, lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
  ring

private lemma nrm_res_le_VOK {b : Fin m → ℝ} (hb : 0 < normSq b) (h : Fin m → ℝ) :
    nrm (res b h) ≤ nrm h := by
  refine Real.sqrt_le_sqrt ?_
  have h1 := pyth_VOK hb h
  have h2 : 0 ≤ (h ⬝ᵥ b) ^ 2 / normSq b := div_nonneg (sq_nonneg _) hb.le
  linarith

/-- `φ₁(z) = ⟨z, b̂⟩`. -/
private noncomputable def phi1VOK (b z : Fin m → ℝ) : ℝ := (z ⬝ᵥ b) / nrm b

/-- `φ₂(z) = |Π_b z|`. -/
private noncomputable def phi2VOK (b z : Fin m → ℝ) : ℝ := nrm (res b z)

private lemma eulip1_VOK {b : Fin m → ℝ} (hb : 0 < normSq b) : EuLip (phi1VOK b) 1 := by
  intro x y
  have hN : 0 < nrm b := Real.sqrt_pos.mpr hb
  have e : phi1VOK b x - phi1VOK b y = ((x - y) ⬝ᵥ b) / nrm b := by
    unfold phi1VOK
    rw [sub_dotProduct]
    ring
  rw [e, abs_div, abs_of_pos hN, div_le_iff₀ hN, one_mul]
  exact BstLean.Part153.abs_dot_le_nrm (x - y) b

private lemma eulip2_VOK {b : Fin m → ℝ} (hb : 0 < normSq b) : EuLip (phi2VOK b) 1 := by
  intro x y
  rw [one_mul]
  unfold phi2VOK
  refine (BstLean.Part153.abs_nrm_sub_le _ _).trans ?_
  rw [res_sub_VOK]
  exact nrm_res_le_VOK hb (x - y)

private lemma v1_eq_VOK {b : Fin m → ℝ} (hb : 0 < normSq b) (t : ℝ) (h : Fin m → ℝ) :
    √t * √(normSq b) * lam b h = phi1VOK b (√t • h) := by
  have hN : 0 < √(normSq b) := Real.sqrt_pos.mpr hb
  have e : lam b h = (h ⬝ᵥ b) / normSq b := rfl
  have e2 : normSq b = √(normSq b) ^ 2 := (Real.sq_sqrt hb.le).symm
  unfold phi1VOK nrm
  rw [e, smul_dotProduct, smul_eq_mul]
  generalize h ⬝ᵥ b = d
  rw [e2, Real.sqrt_sq hN.le]
  field_simp

private lemma sig_eq_VOK (b : Fin m → ℝ) (t : ℝ) (h : Fin m → ℝ) :
    sig t b h = phi2VOK b (√t • h) := by
  unfold phi2VOK
  rw [res_smul_VOK, BstLean.Part153.nrm_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl

private lemma rho_eq_VOK {b : Fin m → ℝ} (hb : 0 < normSq b) {t : ℝ} (ht : 0 ≤ t)
    (h : Fin m → ℝ) :
    √((√t * √(normSq b) * lam b h) ^ 2 + sig t b h ^ 2) = √t * nrm h := by
  have e : lam b h = (h ⬝ᵥ b) / normSq b := rfl
  have h1 := pyth_VOK hb h
  have e3 : (√t * √(normSq b) * lam b h) ^ 2 + sig t b h ^ 2 = t * normSq h := by
    unfold sig
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hb.le,
      Real.sq_sqrt (normSq_nonneg _), e, h1]
    field_simp
  rw [e3, Real.sqrt_mul ht]
  rfl

variable {n : ℕ}

private lemma var_v1_VOK (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) :
    ∫ ξ, (√(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ζ, √(2 / (m : ℝ)) * √(normSq b) * lam b (hid2 A₁ A₂ (sphPt (c + τ • ζ)))
        ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤ XiS A₁ A₂ c τ := by
  have h := (BstLean.Part153.lemmaS_jac hn A₁ A₂ c hτ zero_le_one (eulip1_VOK hb)).2
  rw [one_pow, one_mul] at h
  simp_rw [v1_eq_VOK hb]
  exact h

private lemma var_sig_VOK (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {b : Fin m → ℝ}
    (hb : 0 < normSq b) :
    ∫ ξ, (sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ζ, sig (2 / (m : ℝ)) b (hid2 A₁ A₂ (sphPt (c + τ • ζ)))
        ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤ XiS A₁ A₂ c τ := by
  have h := (BstLean.Part153.lemmaS_jac hn A₁ A₂ c hτ zero_le_one (eulip2_VOK hb)).2
  rw [one_pow, one_mul] at h
  simp_rw [sig_eq_VOK]
  exact h

end genVOK

/-- The centre bounds on `GoodC16` with the numbers of Part154Num16 (Lemma TF). -/
private lemma centreVOK {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
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
    refine le_sqrt_VOK (mul_nonneg hX0.le (mul_nonneg hρi.le (BstLean.Part153.nrm_nonneg _))) ?_
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
    refine t2.trans (le_sqrt_VOK (mul_nonneg hX0.le (by positivity)) ?_)
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
      (show √(819 / 1000 : ℝ) + 75 / 10000 / √(n : ℝ) ≤ 9051 / 10000 by linarith only [hsq, hsmall]) 2).trans
      (by norm_num)

/-- **The `A`-stage facts of the frame of Theorem 5 on `GoodC16`** (`n ≥ 16384`, `J = n` atoms,
`0.46 ≤ θ_in ≤ 0.55`): the centre is not `0`; the covariance bound with `1.192`; the centre
error `ξ_hp ≤ 0.485`; and (V1) to (V4) with `s_* = 0.18`, `ξ_∥ = 0.028`. -/
theorem A12_of_GoodC16 {n : ℕ} (hn : 16384 ≤ n) (W : MlpParam (2 * n) (mW n) n)
    (hτ : 0 < tauWA W) (hW : (cenA W, tauWA W) ∈ Wd16 n)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n (cenA W) (tauWA W)) :
    bTW n (W, ((A₁, A₂) : HidParam n (mA n))) ≠ 0 ∧
    (∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ 1192 / 1000 * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2) ∧
    2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bTW n (W, (A₁, A₂)) j) ≤
          485 / 1000 * (2 / (n : ℝ)) / n ∧
    VOK (bTW n) W A₁ A₂ (3 / 10) (18 / 100) (1192 / 1000) (280 / 10000)
      (18334 / 1000 / (n : ℝ)) (24779 / 1000 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hθ0, hθ1⟩ := hW
  have hρ := rhoC_posP hn1 (cenA W) hτ
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := centreVOK hn hτ hθ0 hθ1 h
  have hmR : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hm0 : (0 : ℝ) < mA n := by rw [hmR]; positivity
  have ht0 : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  have hK : (11911 : ℝ) / 10000 * (2 / (n : ℝ)) / n ≤ 1192 / 1000 * (2 / (n : ℝ)) / n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (by positivity)) hn0.le
  set c := cenA W with hc
  set τ := tauWA W with hτd
  set b := bTW n (W, ((A₁, A₂) : HidParam n (mA n))) with hb
  have hbe : b = (1 / rhoC c τ) • bT n n A₁ A₂ c τ := rfl
  have c1' : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤
      485 / 1000 * (2 / (n : ℝ)) / n := c1
  have c2' : |√(2 / (mA n : ℝ)) * ((∑ j, (hid2Mean_cr A₁ A₂ c τ j - b j) * b j) /
      √(normSq b))| ≤ √(280 / 10000 * (2 / (n : ℝ)) / n) := c2
  have c3' : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * (82 / 100) := c3
  have c4' : 0 < normSq b := c4
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0] at c4'
    simp [normSq] at c4'
  have hbnn : ∀ j, 0 ≤ b j := by
    intro j
    have h1 : 0 ≤ bT n n A₁ A₂ c τ j := by
      unfold bT binMean
      exact Finset.sum_nonneg fun i _ => mul_nonneg (binW_nonneg _ _) (relu_nonneg _)
    have e : b j = 1 / rhoC c τ * bT n n A₁ A₂ c τ j := rfl
    rw [e]
    exact mul_nonneg (one_div_nonneg.mpr hρ.le) h1
  have hXi := BstLean.Part153.XiS_le_Xi4 hn6 A₁ A₂ c hτ
  have hXi4_0 : 0 ≤ Xi4 A₁ A₂ c τ := by unfold Xi4; positivity
  refine ⟨hb0, ?_, c1', ?_⟩
  · intro w
    have h1 := BstLean.Part153.cov_hid2_le hn6 A₁ A₂ c hτ w
    have e : ∀ ξ, ∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j =
        w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
          ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n) := by
      intro ξ
      rw [BstLean.Part153.integral_dot_hid2_cr hn1]
      unfold dotProduct
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      show (hid2 A₁ A₂ (sphPt (c + τ • ξ)) j - hid2Mean_cr A₁ A₂ c τ j) * w j = _
      ring
    simp_rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_right (hXi.trans (c5.trans hK)) (normSq_nonneg w))
  · have hF := BstLean.Part153.integrable_XiS (by omega : 4 ≤ n) A₁ A₂ c hτ
    have hG := BstLean.Part153.integrable_Xi4 hn6 A₁ A₂ c hτ
    have eX2 : (fun ξ : Fin n → ℝ => (2 / (mA n : ℝ) * τ ^ 2 *
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)) ^ 2) =
        fun ξ => (2 / (mA n : ℝ) * τ ^ 2) ^ 2 *
          (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2) :=
      funext fun ξ => by ring
    have hXint : ∫ ξ, 2 / (mA n : ℝ) * τ ^ 2 *
        (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)
          ∂stdGauss (Fin n) = XiS A₁ A₂ c τ := by
      rw [integral_const_mul]; rfl
    -- the norm identity
    have hsX : √(2 / (mA n : ℝ)) = √(2 / (n : ℝ)) / √(n : ℝ) := by
      rw [hmR, ← Real.sqrt_div (by positivity)]; congr 1; field_simp
    have hg0 : 0 < √(2 / (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    have hrn0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
    have huV : ∀ ξ, uV (2 / (n : ℝ)) (v1V (bTW n) W A₁ A₂) (sigU (bTW n) W A₁ A₂) ξ =
        sq2 A₁ A₂ c τ ξ - 1 := by
      intro ξ
      have hr : rhoV (v1V (bTW n) W A₁ A₂) (sigU (bTW n) W A₁ A₂) ξ =
          √(2 / (mA n : ℝ)) * nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ))) :=
        rho_eq_VOK c4' ht0 _
      unfold uV
      rw [hr, BstLean.Part153.sq2_eq_hid2, hsX]
      field_simp
    have hmeas : AEStronglyMeasurable (fun ξ => sq2 A₁ A₂ c τ ξ - 1) (stdGauss (Fin n)) :=
      ((BstLean.Part153.measurable_sq2 A₁ A₂ c τ).sub_const 1).aestronglyMeasurable
    have e2 : N2 2 A₁ A₂ c τ ^ 2 = ∫ ξ, |sq2 A₁ A₂ c τ ξ - 1| ^ 2 ∂stdGauss (Fin n) :=
      BstLean.Part153.lpNorm_nat_pow (by norm_num) hmeas
    have e4 : N2 4 A₁ A₂ c τ ^ 4 = ∫ ξ, |sq2 A₁ A₂ c τ ξ - 1| ^ 4 ∂stdGauss (Fin n) :=
      BstLean.Part153.lpNorm_nat_pow (by norm_num) hmeas
    refine ⟨?_, fun ξ => 2 / (mA n : ℝ) * τ ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · show 2 / (mA n : ℝ) * normSq b / (2 / (n : ℝ)) ≤ 1 - 18 / 100
      rw [div_le_iff₀ (by positivity)]
      linarith
    · exact ((((BstLean.Part153.measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 2).mul
        (BstLean.Part153.cont_ns c τ).measurable.inv).const_mul _)
    · intro ξ
      exact mul_nonneg (by positivity)
        (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _)))
    · rw [eX2]
      exact hG.const_mul _
    · rw [eX2, integral_const_mul]
      have e : (2 / (mA n : ℝ) * τ ^ 2) ^ 2 *
          ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2
            ∂stdGauss (Fin n) = Xi4 A₁ A₂ c τ ^ 2 := by
        unfold Xi4
        rw [mul_pow _ (Real.sqrt _), Real.sq_sqrt (integral_nonneg fun ξ => by positivity)]
      rw [e]
      exact pow_le_pow_left₀ hXi4_0 (c5.trans hK) 2
    · rw [hXint]
      exact var_v1_VOK hn6 A₁ A₂ c hτ c4'
    · rw [hXint]
      exact var_sig_VOK hn6 A₁ A₂ c hτ c4'
    · exact phi_poincare hn6 A₁ A₂ c hτ c4'.ne' hbnn (γ := 2 / (n : ℝ)) (ϑ := 3 / 10)
        (by positivity) (by norm_num) (by norm_num)
    · rw [v1V_mean (bTW n) W A₁ A₂ hn1 hb0]
      exact c2'
    · have e : (fun ξ => uV (2 / (n : ℝ)) (v1V (bTW n) W A₁ A₂) (sigU (bTW n) W A₁ A₂) ξ ^ 2) =
          fun ξ => |sq2 A₁ A₂ c τ ξ - 1| ^ 2 := funext fun ξ => by rw [huV, sq_abs]
      rw [e, ← e2]
      exact pow_le_pow_left₀ (BstLean.Part153.N2_nonneg _ _ _ _ _) c6 2
    · have e : (fun ξ => uV (2 / (n : ℝ)) (v1V (bTW n) W A₁ A₂) (sigU (bTW n) W A₁ A₂) ξ ^ 4) =
          fun ξ => |sq2 A₁ A₂ c τ ξ - 1| ^ 4 :=
        funext fun ξ => by rw [huV, Even.pow_abs (by decide)]
      rw [e, ← e4]
      exact pow_le_pow_left₀ (BstLean.Part153.N2_nonneg _ _ _ _ _) c7 4

end BstLean.Part154
