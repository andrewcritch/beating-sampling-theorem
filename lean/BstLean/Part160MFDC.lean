import BstLean.Part160MFD

/-!
# Part 160 (file `MFDC`): the centre charge with changes (A), (C) and (D)

Do not use `sorry`, `native_decide` or `axiom`.

* `dC_le_D`: on `E_D′` (the complement of `BadD'`): `|𝐝| ≤ U_ρ·(√ξ_c + d_v)` when
  `48·(1 + δ_e − (c_s − 4w_n/n)θ/2) ≤ d_v²·n` (Part 154: `d = √(16·12·(1 + δ_e)/n)`).
* `centre_D_core`: the centre error on `GoodC16` and `SD'`.
* `centre_D_gen`: the generic numeric form for a piece `θlo ≤ θ_in ≤ θhi` of the window and
  `n ≥ n₁`.
* `centre16_D` (`n ≥ 16384`, `ξ = 0.1654`), `centre26k_D` (`n ≥ 26000`, `ξ = 0.1561`).
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm jacT XiS Xi4 N2 sq2 hid2Mean_cr Pb wn N22bar)

/-- **The bound of `|𝐝|` on `E_D′`.** -/
theorem dC_le_D {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {ξc dv cs δe : ℝ} (hξ : 0 ≤ ξc) (hdv0 : 0 ≤ dv)
    (hmean : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξc)
    (hop : 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hΓ : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2)
    (hdv : 48 * (1 + δe - (cs - 4 * wn n / n) * thetaC c τ / 2) ≤ dv ^ 2 * n)
    (hD : A₂ ∉ BadD' A₁ c τ 12) :
    dC A₁ A₂ c τ ≤ rhoC c τ * √(2 / (n : ℝ) / n) * (√ξc + dv) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := BstLean.Part130.one_le_mA hn
  have hmR : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hρ := rhoC_posP hn c hτ
  obtain ⟨hi1, hi2⟩ := dC_integrable hm A₁ c τ
  have hD' : dC A₁ A₂ c τ ≤ ∫ A₂, dC A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
      √(2 * 12 * (2 / ((mA n : ℕ) : ℝ))) * LD A₁ c τ := not_lt.mp hD
  have hJ := BstLean.Part133.sq_integral_le hi2
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = rhoC c τ * √(2 / (n : ℝ) / n) := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hU2 : U ^ 2 = rhoC c τ ^ 2 * (2 / (n : ℝ) / n) := by
    rw [hU, mul_pow, Real.sq_sqrt (by positivity)]
  rw [← hU]
  have h1 : ∫ A₂, dC A₁ A₂ c τ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ U * √ξc := by
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hU0 (Real.sqrt_nonneg _)) |>.2
    rw [mul_pow, hU2, Real.sq_sqrt hξ]
    exact hJ.trans hmean
  -- `L_D² ≤ γ_Aρ²·(1 + δ_e − (c_s − 4w_n/n)θ/2)`
  have hτθ : τ ^ 2 = thetaC c τ * rhoC c τ ^ 2 / n := by
    unfold thetaC; field_simp
  have hLD2 : LD A₁ c τ ^ 2 ≤
      2 / (n : ℝ) * rhoC c τ ^ 2 * (1 + δe - (cs - 4 * wn n / n) * thetaC c τ / 2) := by
    unfold LD
    rw [Real.sq_sqrt (mul_nonneg (by positivity)
      (add_nonneg (by positivity) (normSq_nonneg _)))]
    have e : 2 / ((mA n : ℕ) : ℝ) * (τ ^ 2 * opN A₁ ^ 2 + normSq (hO A₁ c τ)) =
        τ ^ 2 * (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) + (gO A₁ c τ - sO2 A₁ c τ) := by
      unfold sO2 normSq; ring
    rw [e]
    have h2 := mul_le_mul_of_nonneg_left hop (sq_nonneg τ)
    have e2 : 2 / (n : ℝ) * rhoC c τ ^ 2 * (1 + δe - (cs - 4 * wn n / n) * thetaC c τ / 2) =
        τ ^ 2 * (4 * wn n / n) + ((1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2) := by
      rw [hτθ]; field_simp; ring
    rw [e2]
    linarith
  have h3 : √(2 * 12 * (2 / ((mA n : ℕ) : ℝ))) * LD A₁ c τ ≤ U * dv := by
    refine abs_le_of_sq_le_sq' ?_ (mul_nonneg hU0 hdv0) |>.2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hU2, hmR]
    have h4 : 2 * 12 * (2 / (n : ℝ) ^ 2) * LD A₁ c τ ^ 2 ≤ 2 * 12 * (2 / (n : ℝ) ^ 2) *
        (2 / (n : ℝ) * rhoC c τ ^ 2 * (1 + δe - (cs - 4 * wn n / n) * thetaC c τ / 2)) :=
      mul_le_mul_of_nonneg_left hLD2 (by positivity)
    refine h4.trans ?_
    have e3 : 2 * 12 * (2 / (n : ℝ) ^ 2) *
        (2 / (n : ℝ) * rhoC c τ ^ 2 * (1 + δe - (cs - 4 * wn n / n) * thetaC c τ / 2)) =
        rhoC c τ ^ 2 * (2 / (n : ℝ) / n) *
          (48 * (1 + δe - (cs - 4 * wn n / n) * thetaC c τ / 2) / n) := by
      field_simp; ring
    rw [e3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ hnR]
    exact hdv
  have : U * (√ξc + dv) = U * √ξc + U * dv := by ring
  rw [this]
  linarith

/-- **The centre error on `GoodC16` and `SD'`** (changes (A), (C), (D)). -/
theorem centre_D_core {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n) {ξc dv : ℝ}
    (hξc0 : 0 ≤ ξc)
    (hξc : xiCI n csC (cHSK n K0) (hHn n (thetaC c τ)) (11 / 10) (27 / 25) (11 / 1000)
      (thetaC c τ) ≤ ξc)
    (hdv0 : 0 ≤ dv)
    (hdv : 48 * (1 + 11 / 1000 - (csC - 4 * wn n / n) * thetaC c τ / 2) ≤ dv ^ 2 * n) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      √(2 / (n : ℝ) / n) * (√ξc + dv + xiNr n (thetaC c τ) (11911 / 10000) +
        epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12)) := by
  have hn8 : 8192 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm := BstLean.Part130.one_le_mA hn1
  have h16 := h.2
  have hC := h.1
  have hAs := hC.1
  obtain ⟨⟨hop, hop2, -⟩, hΓ, -, hsc0⟩ := BstLean.Part153.AStage_bounds hn8 hAs
  obtain ⟨-, -, hN22, -, -⟩ := BstLean.Part153.GoodA_norms hn1 h16
  have hXi := BstLean.Part153.AStage16_Xi hn hτ h16
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hcs := csC_pos_I
  have hρ2 := rhoC_sqP c τ
  have hρ := rhoC_posP hn1 c hτ
  rw [← hρ2] at hΓ
  have hΓ' : gO A₁ c τ ≤ (1 + 11 / 1000) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm]
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
  have hmean : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * ξc :=
    hmean0.trans (mul_le_mul_of_nonneg_left hξc (by positivity))
  have hD' : A₂ ∉ BadD' A₁ c τ 12 := fun hb => hD hb
  have c1 := dC_le_D hn1 A₁ A₂ c hτ hξc0 hdv0 hmean hop2 hsc hΓ' hdv hD'
  have c2 := MA_iv (by omega : 6 ≤ n) A₁ A₂ c hτ (MP := 11911 / 10000) (by norm_num) c1 hN22 hXi
  have c5 := (GoodC16_centre hn hn1 hτ h (rhoBar_lt16 hn) (eMP_le16 hn hθ0 hθ1)
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
      √(2 / (n : ℝ) / n) * (√ξc + dv + xiNr n (thetaC c τ) (11911 / 10000)) := c2
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

/-- `ξ_c′(θ) ≤ 0.27886·θhi·r + 0.00367` for `θ ≤ θhi ≤ r²` in the window. -/
theorem xiCI_gen {n : ℕ} (hn : 16384 ≤ n) {θ θhi r : ℝ} (h0 : 46 / 100 ≤ θ) (h1 : θ ≤ 55 / 100)
    (hθ : θ ≤ θhi) (hr0 : 0 ≤ r) (hr : θhi ≤ r ^ 2) :
    xiCI n csC (cHSK n K0) (hHn n θ) (11 / 10) (27 / 25) (11 / 1000) θ ≤
      27886 / 100000 * (θhi * r) + 367 / 100000 := by
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hK0, hK⟩ := K0_bounds_NumA
  obtain ⟨hcH1, hcH⟩ := cHSK_bounds_NumA16 hn
  obtain ⟨hh1, hh⟩ := hHn_bounds_NumA16 hn h0
  obtain ⟨b0, b1⟩ := xiTt_le16 hn
  obtain ⟨c0, c1⟩ := xiT2_le16 hn h0 h1
  obtain ⟨hb0, hb⟩ := bN_bounds_NumA16 hn h0 h1
  have hθ0 : 0 ≤ θ := by linarith
  have hcH0 : 0 ≤ cHSK n K0 := by linarith
  have hhH0 : 0 ≤ hHn n θ := by linarith
  have hsθ : √θ ≤ r := by
    rw [Real.sqrt_le_iff]; exact ⟨hr0, by linarith⟩
  have hsθ0 : 0 ≤ √θ := Real.sqrt_nonneg _
  have hs0 : (16006 / 10000 : ℝ) ≤ √(2 * csC * (1 - 11 / 1000)) := by
    rw [Real.le_sqrt' (by norm_num)]
    have : ((16006 / 10000 : ℝ)) ^ 2 ≤ 2 * (129521 / 100000) * (1 - 11 / 1000) := by norm_num
    nlinarith
  have hθr : θ * √θ ≤ θhi * r := mul_le_mul hθ hsθ hsθ0 (by linarith)
  have hnum : 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) ≤
      4 * (9085 / 100000) * (100517 / 100000) * (102853 / 100000) * (11 / 10 * (27 / 25)) *
        (θhi * r) := by
    have hK00 := hK0.le
    gcongr
  have hθr0 : 0 ≤ θhi * r := mul_nonneg (by linarith) hr0
  have hT1 : 4 * K0 * cHSK n K0 * hHn n θ * (11 / 10 * (27 / 25)) * (θ * √θ) /
      √(2 * csC * (1 - 11 / 1000)) ≤ 27886 / 100000 * (θhi * r) := by
    rw [div_le_iff₀ (by linarith)]
    have h2 : (4 : ℝ) * (9085 / 100000) * (100517 / 100000) * (102853 / 100000) *
        (11 / 10 * (27 / 25)) * (θhi * r) ≤ 27886 / 100000 * (θhi * r) * (16006 / 10000) := by
      nlinarith
    have h3 : 27886 / 100000 * (θhi * r) * (16006 / 10000) ≤
        27886 / 100000 * (θhi * r) * √(2 * csC * (1 - 11 / 1000)) :=
      mul_le_mul_of_nonneg_left hs0 (by positivity)
    linarith
  unfold xiCI
  linarith only [hT1, b1, c1, hb]

/-- **The generic numeric form**: a piece `θlo ≤ θ_in ≤ θhi` of the window, `n ≥ n₁ ≥ 16384`.
The numbers `r ≥ √θhi`, `sx ≥ √ξ_c`, `dv` (the deviation), `xr` (the radius term), `X` (the sum)
are certificates. -/
theorem centre_D_gen {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hD : ((c, τ), (A₁, A₂)) ∈ SD' n)
    {n1 θlo θhi r sx dv sqn q xr X ξ : ℝ} (hn1 : 16384 ≤ n1) (hn1n : n1 ≤ n)
    (hlo0 : 0 ≤ θlo) (hlo : θlo ≤ thetaC c τ) (hhi : thetaC c τ ≤ θhi)
    (hr0 : 0 ≤ r) (hr : θhi ≤ r ^ 2) (hsx0 : 0 ≤ sx)
    (hsx : 27886 / 100000 * (θhi * r) + 367 / 100000 ≤ sx ^ 2)
    (hdv0 : 0 ≤ dv)
    (hdv : 48 * (1011 / 1000 - (129521 / 100000 - 4 * (1031495 / 1000000) / n1) * θlo / 2) ≤
      dv ^ 2 * n1)
    (hsqn0 : 0 < sqn) (hsqn : sqn ^ 2 ≤ n1) (hq0 : 0 ≤ q) (hq : 11911 / 10000 * θhi ≤ q ^ 2)
    (hxr : θhi * (1 + 18334 / 1000 / n1) + q ≤ xr * sqn)
    (hX : sx + dv + xr + 75 / 10000 ≤ X) (hξ : X ^ 2 ≤ ξ) :
    2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - (1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      ξ * (2 / (n : ℝ)) / n := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn10 : (0 : ℝ) < n1 := by linarith
  obtain ⟨hw1, hw⟩ := wn_bounds_NumA16 hn
  obtain ⟨hcs1, hcs2⟩ := csC_bounds_NumA
  obtain ⟨hε0, hε⟩ := epsJ_le16 hn
  obtain ⟨hNb0, hNb, -, -⟩ := Nbar_le16 hn
  have hθp : 0 ≤ thetaC c τ := by linarith
  have hθhi0 : 0 ≤ θhi := by linarith
  -- `ξ_c`
  have hx := xiCI_gen hn hθ0 hθ1 hhi hr0 hr
  have hsxξ : √(sx ^ 2) = sx := Real.sqrt_sq hsx0
  -- the deviation
  have hinv : 1 / (n : ℝ) ≤ 1 / n1 := one_div_le_one_div_of_le hn10 hn1n
  have hg : 129521 / 100000 - 4 * (1031495 / 1000000) / n1 ≤ csC - 4 * wn n / n := by
    have e1 : 4 * wn n / (n : ℝ) = 4 * wn n * (1 / n) := by ring
    have e2 : 4 * (1031495 / 1000000 : ℝ) / n1 = 4 * (1031495 / 1000000) * (1 / n1) := by ring
    rw [e1, e2]
    have : 4 * wn n * (1 / (n : ℝ)) ≤ 4 * (1031495 / 1000000) * (1 / n1) :=
      mul_le_mul (by linarith) hinv (by positivity) (by norm_num)
    linarith
  have hg0 : 0 ≤ 129521 / 100000 - 4 * (1031495 / 1000000 : ℝ) / n1 := by
    have : 4 * (1031495 / 1000000 : ℝ) / n1 ≤ 4 * (1031495 / 1000000) / 16384 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn1
    have h2 : 4 * (1031495 / 1000000 : ℝ) / 16384 ≤ 1 := by norm_num
    linarith
  have hprod : (129521 / 100000 - 4 * (1031495 / 1000000) / n1) * θlo ≤
      (csC - 4 * wn n / n) * thetaC c τ := mul_le_mul hg hlo hlo0 (hg0.trans hg)
  have hdv' : 48 * (1 + 11 / 1000 - (csC - 4 * wn n / n) * thetaC c τ / 2) ≤ dv ^ 2 * n := by
    have h3 : dv ^ 2 * n1 ≤ dv ^ 2 * n := mul_le_mul_of_nonneg_left hn1n (sq_nonneg _)
    linarith
  have hcore := centre_D_core hn hτ hθ0 hθ1 h hD (ξc := sx ^ 2) (dv := dv) (sq_nonneg _)
    (hx.trans hsx) hdv0 hdv'
  rw [hsxξ] at hcore
  -- the radius term
  have hsn : sqn ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' hsqn0]; linarith
  have hsq : √(11911 / 10000 * thetaC c τ) ≤ q := by
    rw [Real.sqrt_le_iff]
    refine ⟨hq0, ?_⟩
    nlinarith
  have hNb' : N22bar n 12 ≤ 18334 / 1000 / n1 := by
    refine hNb.trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) hn10 hn1n
  have hxi : xiNr n (thetaC c τ) (11911 / 10000) ≤ xr := by
    unfold xiNr
    rw [div_le_iff₀ (lt_of_lt_of_le hsqn0 hsn)]
    have hp : thetaC c τ * (1 + N22bar n 12) ≤ θhi * (1 + 18334 / 1000 / n1) :=
      mul_le_mul hhi (by linarith) (by linarith) hθhi0
    have hxr0 : 0 ≤ xr := by
      have : 0 ≤ θhi * (1 + 18334 / 1000 / n1) + q := by positivity
      exact nonneg_of_mul_nonneg_left (this.trans hxr) hsqn0
    have : xr * sqn ≤ xr * √(n : ℝ) := mul_le_mul_of_nonneg_left hsn hxr0
    linarith
  have hN0 : 0 ≤ xiNr n (thetaC c τ) (11911 / 10000) := by unfold xiNr; positivity
  refine sq_form (by omega) _ (x := sx + dv + xiNr n (thetaC c τ) (11911 / 10000) +
    epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12)) (by linarith) ?_ hcore
  have hb : sx + dv + xiNr n (thetaC c τ) (11911 / 10000) +
      epsJ n n n (wn n) csC (11 / 1000) (deltaChi n 12) ≤ X := by linarith
  exact (pow_le_pow_left₀ (by linarith) hb 2).trans hξ

end BstLean.Part160

open BstLean.Part160 in
#print axioms dC_le_D
open BstLean.Part160 in
#print axioms centre_D_core
open BstLean.Part160 in
#print axioms centre_D_gen
