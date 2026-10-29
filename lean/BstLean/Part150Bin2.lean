import BstLean.Part150NormB
import BstLean.Part150Bin

/-!
# Part 150, item 5: the binomial part at SECOND order in `α(J)`, on the good event of `A₁`

`Part150Bin` uses `|s̃ − s|² ≤ |s̃² − s²|` (no lower bound of `s`): its constant `xiBin J` is of
first order in `α(J)`. On the good event of `A₁` (Part 149) the oracle scale has a lower bound
(`sO2_lower`), and `(s̃ − s)² ≤ (s̃² − s²)²/s²` gives a constant of second order (`xiBin2`).

* `bin_disp_pt2`: the pointwise bound with `(s̃ − s)²`.
* `sO2_lower`: `s²/ρ² ≥ ((1 − εD)/2 − 2Λ)/n` for a good `A₁`.
* `bin2_A2`: the mean over `A₂` for a good `A₁`; `bin2_mean`: the mean over `A₁`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part137 BstLean.Part141
open BstLean.Part149 (a1 b1 N2 sMF bMF errD1 Qk)

variable {n m : ℕ}

/-- The pointwise bound of the scaled displacement, with `(s̃ − s)²`. -/
theorem bin_disp_pt2 {J : ℕ} (hJ : 1 ≤ J) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)) ≤
      3 / rhoC c τ ^ 2 * ((m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ +
        (m : ℝ) / (2 * π) * (sT J A₁ c τ - sO A₁ c τ) ^ 2 +
        normSq (A₂.mulVec (hT J A₁ c τ - hO A₁ c τ))) := by
  have hpi := Real.pi_pos
  have h := (centre150_second J hJ A₁ A₂ c τ).2
  set X := nrm (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ) with hX
  set N := nrm (A₂.mulVec (hT J A₁ c τ - hO A₁ c τ)) with hN
  have hX0 : 0 ≤ X := nrm_nonneg _
  have hN0 : 0 ≤ N := nrm_nonneg _
  have hα := alphaJ_nonneg J
  have hs2 := sT2_nonneg J A₁ c τ
  have hsT : sT J A₁ c τ ^ 2 = sT2 J A₁ c τ := Real.sq_sqrt hs2
  have hsT0 : 0 ≤ sT J A₁ c τ := Real.sqrt_nonneg _
  set Δ := |sT J A₁ c τ - sO A₁ c τ| with hΔd
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  have hΔ2 : Δ ^ 2 = (sT J A₁ c τ - sO A₁ c τ) ^ 2 := sq_abs _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0
  have hu0 := Real.sqrt_nonneg (m : ℝ)
  have hφ0 : 0 ≤ 1 / √(2 * π) := by positivity
  have hφ : (1 / √(2 * π)) ^ 2 = 1 / (2 * π) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  set φ := 1 / √(2 * π) with hφd
  set p := √(m : ℝ) * (alphaJ J * sT J A₁ c τ) with hp
  set q := √(m : ℝ) * (φ * Δ) with hq
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hXle : X ≤ p + q + N := by rw [hp, hq]; linarith only [h]
  have h1 : X ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + N ^ 2) := by
    have : X ^ 2 ≤ (p + q + N) ^ 2 := pow_le_pow_left₀ hX0 hXle 2
    nlinarith only [this, sq_nonneg (p - q), sq_nonneg (q - N), sq_nonneg (p - N)]
  have ep : p ^ 2 = (m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ := by
    rw [hp, mul_pow, mul_pow, hu, hsT]; ring
  have eq' : q ^ 2 = (m : ℝ) / (2 * π) * (sT J A₁ c τ - sO A₁ c τ) ^ 2 := by
    rw [hq, mul_pow, mul_pow, hu, hφ, hΔ2]; ring
  rw [normSq_smul, ← nrm_sq (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ),
    ← nrm_sq (A₂.mulVec (hT J A₁ c τ - hO A₁ c τ)), ← hX, ← hN]
  have e3 : (1 / rhoC c τ) ^ 2 * X ^ 2 = 1 / rhoC c τ ^ 2 * X ^ 2 := by rw [div_pow, one_pow]
  rw [e3, ← ep, ← eq']
  have hr0 : 0 ≤ 1 / rhoC c τ ^ 2 := by positivity
  calc 1 / rhoC c τ ^ 2 * X ^ 2 ≤ 1 / rhoC c τ ^ 2 * (3 * (p ^ 2 + q ^ 2 + N ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hr0
    _ = 3 / rhoC c τ ^ 2 * (p ^ 2 + q ^ 2 + N ^ 2) := by ring

/-- The loss of the lower bound of the oracle scale. -/
noncomputable def LamN (n : ℕ) (εD εQ : ℝ) : ℝ :=
  εD * √(6 / (n : ℝ)) + 2 * (εQ * √(6 / (n : ℝ)) +
    √((2 * (6 / (n : ℝ)) * εD ^ 2 + (6 / (n : ℝ)) ^ 2 / 2) * (1 + εD))) +
    6 / (n : ℝ) * (εQ + 2 * εD ^ 2 + 6 / (n : ℝ) / 2)

/-- **The lower bound of the oracle scale of the paper, for a good `A₁`**:
`s²/ρ² ≥ ((1 − εD)/2 − 2Λ)/n`. -/
theorem sO2_lower (hn : 1 ≤ n) (hm : 1 ≤ m) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {k εD εQ : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hεD0 : 0 ≤ εD) (hεD1 : εD < 1) (hεQ0 : 0 ≤ εQ)
    (hcond : k * (1 - εD) + εQ ≤ 3 / 4 * (1 - εD))
    (hD1 : errD1 c τ A₁ ≤ ((m : ℝ) / n * εD) ^ 2)
    (hQ : Qk k c τ A₁ ≤ ((m : ℝ) / n * εQ) ^ 2) :
    ((1 - εD) / 2 - 2 * LamN n εD εQ) / n ≤ sO2 A₁ c τ / rhoC c τ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set d : ℝ := (m : ℝ) / n with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  obtain ⟨hN2pos, hY, _⟩ := BstLean.Part149.centre_det hn hm c τ A₁ (π₀ := 1 / 2) (ζ := 1)
    (K := 0) hk0 hk1 hεD0 hεD1 hεQ0 hcond (by norm_num) (by norm_num) (by norm_num) le_rfl hD1 hQ
  have hNabs : |N2 c τ A₁ - d| ≤ d * εD := BstLean.Part149.abs_N2_sub_le (stdGauss (Fin n))
    (BstLean.Part149.bm_a1 hn c τ A₁) (d := d) (δ := d * εD) (by positivity) hD1
  have hNlo : d * (1 - εD) ≤ N2 c τ A₁ := by linarith only [(abs_le.mp hNabs).1]
  have hNhi : N2 c τ A₁ ≤ d * (1 + εD) := by linarith only [(abs_le.mp hNabs).2]
  set s2 : ℝ := 2 / (m : ℝ) * (N2 c τ A₁ - normSq (b1 c τ A₁)) with hs2
  have hs2lo : (1 - εD) / (2 * n) ≤ s2 := by
    have h1 : d * (1 - εD) / 4 ≤ N2 c τ A₁ - normSq (b1 c τ A₁) := by linarith only [hNlo, hY]
    have h2 : 2 / (m : ℝ) * (d * (1 - εD) / 4) ≤ s2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : 2 / (m : ℝ) * (d * (1 - εD) / 4) = (1 - εD) / (2 * n) := by
      rw [hd]; field_simp; ring
    linarith only [h2, e]
  set V := VN c τ with hV
  have hV0 : 0 ≤ V := VN_nonneg c τ
  have hV6 : V ≤ 6 / (n : ℝ) := VN_le hn c hτ
  set v6 : ℝ := 6 / (n : ℝ) with hv6
  have hv60 : 0 ≤ v6 := by rw [hv6]; positivity
  set E := errD1 c τ A₁ with hE
  have hE0 : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  set Q := Qk k c τ A₁ with hQdef
  have hQ0 : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  set I := ∫ γ, wN c τ γ * nrm (a1 c τ A₁ γ) ∂stdGauss (Fin n) with hI
  have hI2 : |I| ^ 2 ≤ 2 * V * E / d + d * V ^ 2 / 2 := by
    rw [sq_abs]; exact wnrm_sq_le hn hm c hτ A₁
  have he := e1N_normSq_le hn c hτ A₁ k
  rw [← hI, ← sq_abs I] at he
  have hp := dotp_b1_e1N_le hn c hτ A₁ hk0
  have hΔ := sMF_sq_sub_sO2 hn hm c hτ A₁
  set e := normSq (e1N c τ A₁) with hedef
  set p := |dotp (b1 c τ A₁) (e1N c τ A₁)| with hpdef
  have hp0 : 0 ≤ p := abs_nonneg _
  obtain ⟨_, _, he4, _⟩ := arith_II_pre (lam := 1) (ce := εQ + 2 * εD ^ 2 + v6 / 2) hd0 hεQ0 hk1
    hV0 hV6 hE0 hD1 hQ0 hQ hN2pos.le hNhi (abs_nonneg I) hI2 he hp0 hp one_pos rfl
  -- the square roots
  have sE : √E ≤ d * εD := by
    rw [show d * εD = √((d * εD) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hD1
  have sQ : √Q ≤ d * εQ := by
    rw [show d * εQ = √((d * εQ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hQ
  have sV : √V ≤ √v6 := Real.sqrt_le_sqrt hV6
  have sV0 : 0 ≤ √V := Real.sqrt_nonneg _
  have sv60 : 0 ≤ √v6 := Real.sqrt_nonneg _
  set u : ℝ := 2 * v6 * εD ^ 2 + v6 ^ 2 / 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hIu : |I| ≤ √(d * u) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine hI2.trans ?_
    have t1 : 2 * V * E / d ≤ d * (2 * v6 * εD ^ 2) := by
      rw [div_le_iff₀ hd0]
      have h1 : V * E ≤ v6 * (d * εD) ^ 2 := mul_le_mul hV6 hD1 hE0 hv60
      calc 2 * V * E = 2 * (V * E) := by ring
        _ ≤ 2 * (v6 * (d * εD) ^ 2) := by linarith only [h1]
        _ = d * (2 * v6 * εD ^ 2) * d := by ring
    have t2 : d * V ^ 2 / 2 ≤ d * (v6 ^ 2 / 2) := by
      have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV0 hV6 2) hd0.le
      linarith only [this]
    rw [hu]; linarith only [t1, t2]
  have sN : √(N2 c τ A₁) ≤ √(d * (1 + εD)) := Real.sqrt_le_sqrt hNhi
  have hIN : k * |I| * √(N2 c τ A₁) ≤ d * √(u * (1 + εD)) := by
    have h1 : |I| * √(N2 c τ A₁) ≤ √(d * u) * √(d * (1 + εD)) :=
      mul_le_mul hIu sN (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have e1 : √(d * u) * √(d * (1 + εD)) = d * √(u * (1 + εD)) := by
      rw [← Real.sqrt_mul (by positivity), show d * u * (d * (1 + εD)) = d ^ 2 * (u * (1 + εD)) by
        ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hd0.le]
    have h0 : 0 ≤ |I| * √(N2 c τ A₁) := by positivity
    calc k * |I| * √(N2 c τ A₁) = k * (|I| * √(N2 c τ A₁)) := by ring
      _ ≤ 1 * (|I| * √(N2 c τ A₁)) := mul_le_mul_of_nonneg_right hk1 h0
      _ ≤ d * √(u * (1 + εD)) := by rw [one_mul, ← e1]; exact h1
  have hX : √E * √V + 2 * p + e ≤ d * LamN n εD εQ := by
    have t1 : √E * √V ≤ d * εD * √v6 := mul_le_mul sE sV sV0 (by positivity)
    have t2 : √V * √Q ≤ √v6 * (d * εQ) := mul_le_mul sV sQ (Real.sqrt_nonneg _) sv60
    have t3 : e ≤ d * v6 * (εQ + 2 * εD ^ 2 + v6 / 2) := by
      refine he4.trans ?_
      have hce0 : 0 ≤ εQ + 2 * εD ^ 2 + v6 / 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV6 hd0.le) hce0
    unfold LamN
    rw [← hv6, ← hu]
    have e2 : d * (εD * √v6 + 2 * (εQ * √v6 + √(u * (1 + εD))) +
        v6 * (εQ + 2 * εD ^ 2 + v6 / 2)) =
        d * εD * √v6 + 2 * (√v6 * (d * εQ) + d * √(u * (1 + εD))) +
          d * v6 * (εQ + 2 * εD ^ 2 + v6 / 2) := by ring
    rw [e2]
    linarith only [t1, t2, t3, hp, hIN]
  have hΔ' : s2 - sO2 A₁ c τ / rhoC c τ ^ 2 ≤ 2 / (n : ℝ) * LamN n εD εQ := by
    have h1 := (abs_le.mp hΔ).2
    have h2 : 2 / (m : ℝ) * (√E * √V + 2 * p + e) ≤ 2 / (m : ℝ) * (d * LamN n εD εQ) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have e3 : 2 / (m : ℝ) * (d * LamN n εD εQ) = 2 / (n : ℝ) * LamN n εD εQ := by
      rw [hd]; field_simp
    linarith only [h1, h2, e3]
  have e4 : ((1 - εD) / 2 - 2 * LamN n εD εQ) / n =
      (1 - εD) / (2 * n) - 2 / (n : ℝ) * LamN n εD εQ := by field_simp
  rw [e4]
  linarith only [hs2lo, hΔ']

/-! ## The binomial part for a good `A₁` -/

/-- The real inequality of the binomial part at second order. `κ = β + 2α + α²`. -/
lemma bin2_real {mR nR σ α β τ F H G S D E Δ2 sO r2 κ : ℝ} (hm : 0 < mR) (hn : 0 < nR)
    (hσ : 0 < σ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hF0 : 0 ≤ F) (hH0 : 0 ≤ H) (hG0 : 0 ≤ G)
    (hr2 : 0 < r2) (hD0 : 0 ≤ D)
    (hS : S ≤ 2 / mR * (τ ^ 2 * F))
    (hD : D ≤ β * (2 / mR) * τ ^ 2 * F + 2 / mR * (2 * (α * τ * √F) * √H + α ^ 2 * τ ^ 2 * F))
    (hE : E ≤ α ^ 2 * τ ^ 2 * F) (hH : H ≤ G + τ ^ 2 * F)
    (hsO : σ / nR * r2 ≤ sO) (hΔ : Δ2 ≤ D ^ 2 / sO) (hκ : κ = β + 2 * α + α ^ 2) :
    mR * α ^ 2 * S + mR / (2 * π) * Δ2 + 2 * E ≤
      4 * α ^ 2 * τ ^ 2 * F +
        4 * nR / (π * σ * mR * r2) * (κ ^ 2 * τ ^ 4 * F ^ 2 + α ^ 2 * G ^ 2) := by
  have hpi := Real.pi_pos
  have hm2 : mR * (2 / mR) = 2 := by field_simp
  have hFs : √F ^ 2 = F := Real.sq_sqrt hF0
  have hHs : √H ^ 2 = H := Real.sq_sqrt hH0
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have t1 : mR * α ^ 2 * S ≤ 2 * α ^ 2 * τ ^ 2 * F := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ mR * α ^ 2)
    calc mR * α ^ 2 * S ≤ mR * α ^ 2 * (2 / mR * (τ ^ 2 * F)) := this
      _ = (mR * (2 / mR)) * (α ^ 2 * τ ^ 2 * F) := by ring
      _ = _ := by rw [hm2]; ring
  have am0 : 2 * (τ * √F) * √H ≤ τ ^ 2 * F + H := by
    have h0 := sq_nonneg (τ * √F - √H)
    have e : (τ * √F - √H) ^ 2 = τ ^ 2 * √F ^ 2 - 2 * (τ * √F) * √H + √H ^ 2 := by ring
    rw [e, hFs, hHs] at h0
    linarith only [h0]
  set Y : ℝ := κ * τ ^ 2 * F + α * G with hY
  have hτF : 0 ≤ τ ^ 2 * F := by positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hDY : D ≤ 2 / mR * Y := by
    have h1 : 2 * (α * τ * √F) * √H ≤ α * (2 * (τ ^ 2 * F) + G) := by
      have h0 : 2 * (τ * √F) * √H ≤ τ ^ 2 * F + (G + τ ^ 2 * F) := by linarith only [am0, hH]
      have := mul_le_mul_of_nonneg_left h0 hα
      calc 2 * (α * τ * √F) * √H = α * (2 * (τ * √F) * √H) := by ring
        _ ≤ α * (τ ^ 2 * F + (G + τ ^ 2 * F)) := this
        _ = α * (2 * (τ ^ 2 * F) + G) := by ring
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 / mR)
    refine hD.trans ?_
    rw [hY, hκ]
    have e : 2 / mR * ((β + 2 * α + α ^ 2) * τ ^ 2 * F + α * G) =
        β * (2 / mR) * τ ^ 2 * F + 2 / mR * (α * (2 * (τ ^ 2 * F) + G) + α ^ 2 * τ ^ 2 * F) := by
      ring
    rw [e]
    linarith only [h2]
  have hD2 : D ^ 2 ≤ (2 / mR * Y) ^ 2 := pow_le_pow_left₀ hD0 hDY 2
  have hY2 : Y ^ 2 ≤ 2 * (κ ^ 2 * τ ^ 4 * F ^ 2 + α ^ 2 * G ^ 2) := by
    rw [hY]
    nlinarith only [sq_nonneg (κ * τ ^ 2 * F - α * G)]
  have hsO0 : 0 < σ / nR * r2 := by positivity
  have hsOpos : 0 < sO := lt_of_lt_of_le hsO0 hsO
  have hΔ' : Δ2 ≤ (2 / mR) ^ 2 * (2 * (κ ^ 2 * τ ^ 4 * F ^ 2 + α ^ 2 * G ^ 2)) / (σ / nR * r2) := by
    refine hΔ.trans ?_
    have h1 : D ^ 2 ≤ (2 / mR) ^ 2 * (2 * (κ ^ 2 * τ ^ 4 * F ^ 2 + α ^ 2 * G ^ 2)) := by
      refine hD2.trans ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hY2 (by positivity)
    exact div_le_div₀ (by positivity) h1 hsO0 hsO
  have t2 : mR / (2 * π) * Δ2 ≤
      4 * nR / (π * σ * mR * r2) * (κ ^ 2 * τ ^ 4 * F ^ 2 + α ^ 2 * G ^ 2) := by
    have := mul_le_mul_of_nonneg_left hΔ' (by positivity : (0 : ℝ) ≤ mR / (2 * π))
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  linarith only [t1, t2, hE]

/-- The bound of the binomial part for a fixed good `A₁`. `F = ‖A₁‖²_F`, `G = |A₁c|²`. -/
noncomputable def PhiB (J : ℕ) (σ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ℝ :=
  3 / rhoC c τ ^ 2 * (4 * alphaJ J ^ 2 * τ ^ 2 * froSq A₁ +
    4 * (n : ℝ) / (π * σ * (m : ℝ) * rhoC c τ ^ 2) *
      ((betaJ J + 2 * alphaJ J + alphaJ J ^ 2) ^ 2 * τ ^ 4 * froSq A₁ ^ 2 +
        alphaJ J ^ 2 * normSq (A₁.mulVec c) ^ 2))

lemma PhiB_nonneg (J : ℕ) {σ : ℝ} (hσ : 0 < σ) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) : 0 ≤ PhiB J σ A₁ c τ := by
  have := Real.pi_pos
  have := froSq_nonneg A₁
  have := alphaJ_nonneg J
  have := betaJ_nonneg J
  unfold PhiB
  positivity

/-- **The binomial part in mean over `A₂`, for an `A₁` with a lower bound of the oracle scale.** -/
theorem bin2_A2 (hn : 1 ≤ n) (hm : 1 ≤ m) {J : ℕ} (hJ : 1 ≤ J) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {σ : ℝ} (hσ : 0 < σ)
    (hlow : σ / n ≤ sO2 A₁ c τ / rhoC c τ ^ 2) :
    ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ)) ≤ ENNReal.ofReal (PhiB J σ A₁ c τ) := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ := rhoC_pos hn c hτ
  have hρ2 : 0 < rhoC c τ ^ 2 := pow_pos hρ 2
  have hs0 := sT2_nonneg J A₁ c τ
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (m : ℝ) * alphaJ J ^ 2 * sT2 J A₁ c τ +
      (m : ℝ) / (2 * π) * (sT J A₁ c τ - sO A₁ c τ) ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨e, he⟩ : ∃ e : Fin m → ℝ, e = hT J A₁ c τ - hO A₁ c τ := ⟨_, rfl⟩
  have hr0 : 0 ≤ 3 / rhoC c τ ^ 2 := by positivity
  obtain ⟨hint, hval⟩ := layer_lin_sq (m := m) (k := m) (v := 2 / (m : ℝ)) (by positivity) e
  have hi2 : Integrable (fun A₂ : Matrix (Fin m) (Fin m) ℝ =>
      3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e))) (gaussMat m m (2 / (m : ℝ))) :=
    ((integrable_const K).add hint).const_mul _
  have hcK : ∫ _A₂ : Matrix (Fin m) (Fin m) ℝ, K ∂gaussMat m m (2 / (m : ℝ)) = K := by simp
  have hm2 : (m : ℝ) * (2 / (m : ℝ) * normSq e) = 2 * normSq e := by field_simp
  have hv2 : ∫ A₂ : Matrix (Fin m) (Fin m) ℝ, 3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e))
      ∂gaussMat m m (2 / (m : ℝ)) = 3 / rhoC c τ ^ 2 * (K + 2 * normSq e) := by
    rw [integral_const_mul, integral_add (integrable_const K) hint, hval, hcK, hm2]
  have hpt : ∀ A₂ : Matrix (Fin m) (Fin m) ℝ,
      normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)) ≤
        3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e)) := by
    intro A₂
    have h := bin_disp_pt2 hJ A₁ A₂ c τ
    rw [← hK, ← he] at h
    exact h
  -- the real inequality
  obtain ⟨hen, _, _, hsle, hsd⟩ := centre150_first hJ A₁ c hτ.le
  have hHle := hO_sq_sum_le A₁ c τ
  have hsO : σ / (n : ℝ) * rhoC c τ ^ 2 ≤ sO2 A₁ c τ := by
    have := mul_le_mul_of_nonneg_right hlow hρ2.le
    rwa [div_mul_cancel₀ _ hρ2.ne'] at this
  have hsOpos : 0 < sO2 A₁ c τ := lt_of_lt_of_le (by positivity) hsO
  have hΔ : (sT J A₁ c τ - sO A₁ c τ) ^ 2 ≤ |sT2 J A₁ c τ - sO2 A₁ c τ| ^ 2 / sO2 A₁ c τ := by
    rw [sq_abs]
    exact sqrt_sub_sq_le_div _ hsOpos
  have hreal := bin2_real (κ := betaJ J + 2 * alphaJ J + alphaJ J ^ 2) hmR hnR hσ
    (alphaJ_nonneg J) (betaJ_nonneg J) (froSq_nonneg A₁)
    (Finset.sum_nonneg fun i _ => sq_nonneg (hO A₁ c τ i)) (normSq_nonneg (A₁.mulVec c)) hρ2
    (abs_nonneg _) hsle hsd hen hHle hsO hΔ rfl
  have hfin : 3 / rhoC c τ ^ 2 * (K + 2 * normSq e) ≤ PhiB J σ A₁ c τ := by
    unfold PhiB
    refine mul_le_mul_of_nonneg_left ?_ hr0
    rw [hK, he]
    have e0 : normSq (hT J A₁ c τ - hO A₁ c τ) = ∑ i, (hT J A₁ c τ i - hO A₁ c τ i) ^ 2 := rfl
    rw [e0]
    linarith only [hreal]
  calc ∫⁻ A₂, ENNReal.ofReal (normSq ((1 / rhoC c τ) • (bT J J A₁ A₂ c τ - bO A₁ A₂ c τ)))
        ∂gaussMat m m (2 / (m : ℝ))
      ≤ ∫⁻ A₂, ENNReal.ofReal (3 / rhoC c τ ^ 2 * (K + normSq (A₂.mulVec e)))
        ∂gaussMat m m (2 / (m : ℝ)) :=
        lintegral_mono fun A₂ => ENNReal.ofReal_le_ofReal (hpt A₂)
    _ = ENNReal.ofReal (3 / rhoC c τ ^ 2 * (K + 2 * normSq e)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi2
          (Filter.Eventually.of_forall fun A₂ => mul_nonneg hr0
            (add_nonneg hK0 (normSq_nonneg _))), hv2]
    _ ≤ ENNReal.ofReal (PhiB J σ A₁ c τ) := ENNReal.ofReal_le_ofReal hfin

/-! ## The mean over `A₁` -/

/-- `E‖A₁‖⁴_F ≤ 4(m² + 2m)` for a Gaussian matrix with entry variance `2/n`. -/
lemma froSq_sq_integral (hn : 1 ≤ n) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => froSq A₁ ^ 2) (gaussMat m n (2 / (n : ℝ))) ∧
    ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, froSq A₁ ^ 2 ∂gaussMat m n (2 / (n : ℝ)) ≤
      4 * ((m : ℝ) ^ 2 + 2 * m) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, froSq A₁ =
      ∑ j : Fin n, normSq (A₁.mulVec (Pi.single j 1)) := by
    intro A₁
    unfold froSq normSq
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_single_one]
    rfl
  have hl := fun j : Fin n => layer_lin_four (m := m) (k := n) (v := 2 / (n : ℝ)) (by positivity)
    (Pi.single j 1)
  have hs : ∀ j : Fin n, normSq (Pi.single j (1 : ℝ) : Fin n → ℝ) = 1 := by
    intro j
    unfold normSq
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  have hle : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, froSq A₁ ^ 2 ≤
      (n : ℝ) * ∑ j : Fin n, normSq (A₁.mulVec (Pi.single j 1)) ^ 2 := by
    intro A₁
    rw [e]
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => normSq (A₁.mulVec (Pi.single j 1)))
    simpa using this
  have hBi : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      (n : ℝ) * ∑ j : Fin n, normSq (A₁.mulVec (Pi.single j 1)) ^ 2)
      (gaussMat m n (2 / (n : ℝ))) :=
    (integrable_finsetSum _ fun j _ => (hl j).1).const_mul _
  have hmeas : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => froSq A₁ ^ 2) := by
    have h0 : Measurable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
        ∑ j : Fin n, normSq (A₁.mulVec (Pi.single j 1))) :=
      Finset.measurable_sum _ fun j _ => BstLean.Part133.measurable_normSq_mulVec _
    have h1 : (fun A₁ : Matrix (Fin m) (Fin n) ℝ => froSq A₁ ^ 2) =
        fun A₁ => (∑ j : Fin n, normSq (A₁.mulVec (Pi.single j 1))) ^ 2 := by
      funext A₁; rw [e]
    rw [h1]
    exact h0.pow_const 2
  have hFi : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => froSq A₁ ^ 2)
      (gaussMat m n (2 / (n : ℝ))) := by
    refine Integrable.mono' hBi hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun A₁ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle A₁
  refine ⟨hFi, ?_⟩
  refine (integral_mono hFi hBi hle).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hl j).1]
  simp_rw [(hl _).2, hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp; ring

/-- The constant of the binomial part at second order. -/
noncomputable def xiBin2 (J : ℕ) (σ : ℝ) (m : ℕ) : ℝ :=
  3 * (8 * alphaJ J ^ 2 + 16 * (1 + 2 / (m : ℝ)) / (π * σ) *
    ((betaJ J + 2 * alphaJ J + alphaJ J ^ 2) ^ 2 + alphaJ J ^ 2))

lemma xiBin2_nonneg (J : ℕ) {σ : ℝ} (hσ : 0 < σ) (m : ℕ) : 0 ≤ xiBin2 J σ m := by
  have := Real.pi_pos
  have := alphaJ_nonneg J
  have := betaJ_nonneg J
  unfold xiBin2; positivity

/-- **The mean over `A₁` of the bound of the binomial part**: at most `(m/n)·xiBin2`. -/
theorem bin2_mean (hn : 1 ≤ n) (hm : 1 ≤ m) (J : ℕ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ A₁ : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (PhiB J σ A₁ c τ)
        ∂gaussMat m n (2 / (n : ℝ)) ≤ ENNReal.ofReal ((m : ℝ) / n * xiBin2 J σ m) := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hα := alphaJ_nonneg J
  have hβ := betaJ_nonneg J
  have hρ := rhoC_pos hn c hτ
  have hρ2 := rhoC_sq c τ
  have hc0 := normSq_nonneg c
  obtain ⟨hFi, hFv⟩ := froSq_integral (m := m) hn
  obtain ⟨hF2i, hF2v⟩ := froSq_sq_integral (m := m) hn
  obtain ⟨hGi, hGv⟩ := layer_lin_four (m := m) (k := n) (v := 2 / (n : ℝ)) (by positivity) c
  set κ : ℝ := betaJ J + 2 * alphaJ J + alphaJ J ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  set a : ℝ := 3 / rhoC c τ ^ 2 * (4 * alphaJ J ^ 2 * τ ^ 2) with ha
  set b : ℝ := 3 / rhoC c τ ^ 2 * (4 * (n : ℝ) / (π * σ * (m : ℝ) * rhoC c τ ^ 2)) with hb
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have eP : ∀ A₁ : Matrix (Fin m) (Fin n) ℝ, PhiB J σ A₁ c τ =
      a * froSq A₁ + b * (κ ^ 2 * τ ^ 4 * froSq A₁ ^ 2 + alphaJ J ^ 2 * normSq (A₁.mulVec c) ^ 2) := by
    intro A₁; unfold PhiB; rw [ha, hb, hκ]; ring
  have hA : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => κ ^ 2 * τ ^ 4 * froSq A₁ ^ 2)
      (gaussMat m n (2 / (n : ℝ))) := hF2i.const_mul _
  have hB : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      alphaJ J ^ 2 * normSq (A₁.mulVec c) ^ 2) (gaussMat m n (2 / (n : ℝ))) := hGi.const_mul _
  have hI1 : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => a * froSq A₁)
      (gaussMat m n (2 / (n : ℝ))) := hFi.const_mul _
  have hIin : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      κ ^ 2 * τ ^ 4 * froSq A₁ ^ 2 + alphaJ J ^ 2 * normSq (A₁.mulVec c) ^ 2)
      (gaussMat m n (2 / (n : ℝ))) := hA.add hB
  have hI2 : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ =>
      b * (κ ^ 2 * τ ^ 4 * froSq A₁ ^ 2 + alphaJ J ^ 2 * normSq (A₁.mulVec c) ^ 2))
      (gaussMat m n (2 / (n : ℝ))) := hIin.const_mul _
  have hi : Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => PhiB J σ A₁ c τ)
      (gaussMat m n (2 / (n : ℝ))) := by
    simp_rw [eP]
    exact hI1.add hI2
  have hv : ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, PhiB J σ A₁ c τ ∂gaussMat m n (2 / (n : ℝ)) ≤
      a * (2 * m) + b * (κ ^ 2 * τ ^ 4 * (4 * ((m : ℝ) ^ 2 + 2 * m)) +
        alphaJ J ^ 2 * (((m : ℝ) ^ 2 + 2 * m) * (2 / (n : ℝ) * normSq c) ^ 2)) := by
    simp_rw [eP]
    rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul, integral_add hA hB,
      integral_const_mul, integral_const_mul, hFv, hGv]
    have h1 : κ ^ 2 * τ ^ 4 * ∫ A₁ : Matrix (Fin m) (Fin n) ℝ, froSq A₁ ^ 2
        ∂gaussMat m n (2 / (n : ℝ)) ≤ κ ^ 2 * τ ^ 4 * (4 * ((m : ℝ) ^ 2 + 2 * m)) :=
      mul_le_mul_of_nonneg_left hF2v (by positivity)
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_right h1
      (alphaJ J ^ 2 * (((m : ℝ) ^ 2 + 2 * m) * (2 / (n : ℝ) * normSq c) ^ 2))) hb0
    linarith only [h2]
  refine (le_of_eq (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun A₁ => PhiB_nonneg J hσ A₁ c τ)).symm).trans
    (ENNReal.ofReal_le_ofReal (hv.trans ?_))
  -- the real inequality
  set T : ℝ := (n : ℝ) * τ ^ 2 with hT
  set C : ℝ := normSq c with hC
  set R : ℝ := rhoC c τ ^ 2 with hR
  have hR0 : 0 < R := pow_pos hρ 2
  have hRe : R = C + T := hρ2
  have hT0 : 0 ≤ T := by positivity
  have hTR : T ≤ R := by linarith only [hRe, hc0]
  have hCR : C ≤ R := by linarith only [hRe, hT0]
  have hτ2 : τ ^ 2 = T / n := by rw [hT]; field_simp
  have e1 : a * (2 * m) = 24 * alphaJ J ^ 2 * ((m : ℝ) / n) * (T / R) := by
    rw [ha, hτ2]; field_simp; ring
  have e2 : b * (κ ^ 2 * τ ^ 4 * (4 * ((m : ℝ) ^ 2 + 2 * m)) +
      alphaJ J ^ 2 * (((m : ℝ) ^ 2 + 2 * m) * (2 / (n : ℝ) * C) ^ 2)) =
      48 * ((m : ℝ) / n) * (1 + 2 / (m : ℝ)) / (π * σ) *
        (κ ^ 2 * (T / R) ^ 2 + alphaJ J ^ 2 * (C / R) ^ 2) := by
    rw [hb, show τ ^ 4 = (τ ^ 2) ^ 2 by ring, hτ2]
    field_simp; ring
  rw [e1, e2]
  have hTr : T / R ≤ 1 := (div_le_one hR0).mpr hTR
  have hTr0 : 0 ≤ T / R := by positivity
  have hCr : C / R ≤ 1 := (div_le_one hR0).mpr hCR
  have hCr0 : 0 ≤ C / R := by positivity
  have hT2 : (T / R) ^ 2 ≤ 1 := pow_le_one₀ hTr0 hTr
  have hC2 : (C / R) ^ 2 ≤ 1 := pow_le_one₀ hCr0 hCr
  have g1 : 24 * alphaJ J ^ 2 * ((m : ℝ) / n) * (T / R) ≤ 24 * alphaJ J ^ 2 * ((m : ℝ) / n) * 1 :=
    mul_le_mul_of_nonneg_left hTr (by positivity)
  have g2 : κ ^ 2 * (T / R) ^ 2 + alphaJ J ^ 2 * (C / R) ^ 2 ≤ κ ^ 2 + alphaJ J ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT2 (sq_nonneg κ)
    have := mul_le_mul_of_nonneg_left hC2 (sq_nonneg (alphaJ J))
    linarith
  have g3 := mul_le_mul_of_nonneg_left g2
    (by positivity : (0 : ℝ) ≤ 48 * ((m : ℝ) / n) * (1 + 2 / (m : ℝ)) / (π * σ))
  unfold xiBin2
  rw [← hκ]
  have e3 : (m : ℝ) / n * (3 * (8 * alphaJ J ^ 2 + 16 * (1 + 2 / (m : ℝ)) / (π * σ) *
      (κ ^ 2 + alphaJ J ^ 2))) = 24 * alphaJ J ^ 2 * ((m : ℝ) / n) * 1 +
      48 * ((m : ℝ) / n) * (1 + 2 / (m : ℝ)) / (π * σ) * (κ ^ 2 + alphaJ J ^ 2) := by
    field_simp; ring
  rw [e3]
  linarith only [g1, g3]

end BstLean.Part150

open BstLean.Part150 in
#print axioms sO2_lower
open BstLean.Part150 in
#print axioms bin2_A2
open BstLean.Part150 in
#print axioms bin2_mean
