import BstLean.Part154MF
import BstLean.Part154Hyp

/-!
# Part 154: Lemma MA (i): the centre error of the oracle centre in mean
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

/-- `ϱ̄ = 4w_n/(c_s n)`. -/
noncomputable def rhoBar (n : ℕ) (cs : ℝ) : ℝ := 4 * wn n / (cs * n)

/-- `b_n(θ) = 4θw_n·Q_B(ϱ̄, π̄)/ϱ̄`. -/
noncomputable def bN (n : ℕ) (cs θ : ℝ) : ℝ :=
  4 * θ * wn n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs

/-- `ξ_c(θ)` with the constant `K` of Lemma PR (i), the constant `cH` of Lemma L1 (c) and the
factor `hH` of Lemma HS (the document: `K = K₀` in the first term and `1/8` in the last one,
`cH = c_HS`, `hH = h_n(θ)`, and `0.6863` for `4(√2 − 1)²`). -/
noncomputable def xiC (n : ℕ) (K cs cH hH θ : ℝ) : ℝ :=
  θ * (cH / cs) * 8 * K * hH +
    4 * wn n * ((2 * θ * rhoBar n cs +
      4 * (√2 - 1) ^ 2 * rhoBar n cs * n * nuR (rhoBar n cs)) / π +
        θ * piBar (rhoBar n cs)) +
    bN n cs θ + 4 * √2 * K * wn n * n * piBar (rhoBar n cs)

private noncomputable def g0M (a πg : ℝ) : ℝ :=
  phiG 0 * a / 2 + phiG 0 * (a * (4 + a ^ 2)) / (2 * √2) + 3 / 2 * phiG 0 * √(πg * (4 + a ^ 2))

private noncomputable def g1M (a πg : ℝ) : ℝ := phiG 1 * (a * √(4 + a ^ 2)) + 2 * √πg

private noncomputable def g2M (a : ℝ) : ℝ := phiG 0 * a / √2

private lemma cc0_eqM {a : ℝ} (ha : 0 ≤ a) (πg : ℝ) : cc0 (a ^ 2) πg = a * g0M a πg := by
  unfold cc0 g0M nuR
  have e : πg * (4 * a ^ 2 + (a ^ 2) ^ 2) = a ^ 2 * (πg * (4 + a ^ 2)) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  ring

private lemma cc1_eqM {a : ℝ} (ha : 0 ≤ a) (πg : ℝ) : cc1 (a ^ 2) πg = a * g1M a πg := by
  unfold cc1 g1M nuR
  have e : a ^ 2 * (4 * a ^ 2 + (a ^ 2) ^ 2) = (a ^ 2) ^ 2 * (4 + a ^ 2) := by ring
  have e2 : πg * a ^ 2 = a ^ 2 * πg := by ring
  rw [e, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg a),
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  ring

private lemma cc2_eqM (a : ℝ) : cc2 (a ^ 2) = a * g2M a := by
  unfold cc2 g2M
  ring

private lemma g0M_nonneg {a πg : ℝ} (ha : 0 ≤ a) : 0 ≤ g0M a πg := by
  have := (BstLean.Part153.phiG_pos 0).le
  unfold g0M
  positivity

private lemma g1M_nonneg {a πg : ℝ} (ha : 0 ≤ a) : 0 ≤ g1M a πg := by
  have := (BstLean.Part153.phiG_pos 1).le
  unfold g1M
  positivity

private lemma g2M_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ g2M a := by
  have := (BstLean.Part153.phiG_pos 0).le
  unfold g2M
  positivity

private lemma g0M_mono {a b πg : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hπ : 0 ≤ πg) :
    g0M a πg ≤ g0M b πg := by
  have h0 := (BstLean.Part153.phiG_pos 0).le
  have hb : 0 ≤ b := ha.trans hab
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have h3 : a * (4 + a ^ 2) ≤ b * (4 + b ^ 2) :=
    mul_le_mul hab (by linarith) (by positivity) hb
  have h4 : √(πg * (4 + a ^ 2)) ≤ √(πg * (4 + b ^ 2)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hπ)
  unfold g0M
  gcongr

private lemma g1M_mono {a b πg : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    g1M a πg ≤ g1M b πg := by
  have h0 := (BstLean.Part153.phiG_pos 1).le
  have hb : 0 ≤ b := ha.trans hab
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have h4 : √(4 + a ^ 2) ≤ √(4 + b ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h3 : a * √(4 + a ^ 2) ≤ b * √(4 + b ^ 2) :=
    mul_le_mul hab h4 (Real.sqrt_nonneg _) hb
  unfold g1M
  gcongr

private lemma g2M_mono {a b : ℝ} (hab : a ≤ b) : g2M a ≤ g2M b := by
  have h0 := (BstLean.Part153.phiG_pos 0).le
  unfold g2M
  gcongr

private noncomputable def PM (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + 3 * z ^ 2 + 2 * √(2 / π) * x * y + 2 * x * z + 4 * √(2 / π) * y * z

private lemma PM_mono {x y z x' y' z' : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxx : x ≤ x') (hyy : y ≤ y') (hzz : z ≤ z') : PM x y z ≤ PM x' y' z' := by
  have hx' := hx.trans hxx
  have hy' := hy.trans hyy
  have hz' := hz.trans hzz
  have hq : 0 ≤ √(2 / π) := Real.sqrt_nonneg _
  have h1 : x ^ 2 ≤ x' ^ 2 := pow_le_pow_left₀ hx hxx 2
  have h2 : y ^ 2 ≤ y' ^ 2 := pow_le_pow_left₀ hy hyy 2
  have h3 : z ^ 2 ≤ z' ^ 2 := pow_le_pow_left₀ hz hzz 2
  have h4 : x * y ≤ x' * y' := mul_le_mul hxx hyy hy hx'
  have h5 : x * z ≤ x' * z' := mul_le_mul hxx hzz hz hx'
  have h6 : y * z ≤ y' * z' := mul_le_mul hyy hzz hz hy'
  have h7 := mul_le_mul_of_nonneg_left h4 hq
  have h8 := mul_le_mul_of_nonneg_left h6 hq
  unfold PM
  nlinarith

private lemma QB_eqM {a : ℝ} (ha : 0 ≤ a) (πg : ℝ) :
    QB (a ^ 2) πg = a ^ 2 * PM (g0M a πg) (g1M a πg) (g2M a) := by
  unfold QB PM
  rw [cc0_eqM ha, cc1_eqM ha, cc2_eqM]
  ring

/-- `Q_B(ϱ, π)/ϱ` is nondecreasing in `ϱ`. -/
theorem QB_div_mono {ϱ ϱ' πg : ℝ} (h0 : 0 < ϱ) (h : ϱ ≤ ϱ') (hπ : 0 ≤ πg) :
    QB ϱ πg ≤ ϱ / ϱ' * QB ϱ' πg := by
  have hϱ' : 0 < ϱ' := h0.trans_le h
  obtain ⟨a, ha⟩ : ∃ a, a = √ϱ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = √ϱ' := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr h0
  have hb0 : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr hϱ'
  have hab : a ≤ b := by rw [ha, hb]; exact Real.sqrt_le_sqrt h
  have ea : ϱ = a ^ 2 := by rw [ha, Real.sq_sqrt h0.le]
  have eb : ϱ' = b ^ 2 := by rw [hb, Real.sq_sqrt hϱ'.le]
  rw [ea, eb, QB_eqM ha0.le, QB_eqM hb0.le]
  have hP := PM_mono (g0M_nonneg (πg := πg) ha0.le) (g1M_nonneg (πg := πg) ha0.le)
    (g2M_nonneg ha0.le) (g0M_mono ha0.le hab hπ) (g1M_mono (πg := πg) ha0.le hab) (g2M_mono hab)
  have e : a ^ 2 / b ^ 2 * (b ^ 2 * PM (g0M b πg) (g1M b πg) (g2M b)) =
      a ^ 2 * PM (g0M b πg) (g1M b πg) (g2M b) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hP (sq_nonneg a)


private lemma rhoBar_posM {n : ℕ} (hn : 1 ≤ n) {cs : ℝ} (hcs : 0 < cs) : 0 < rhoBar n cs := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  unfold rhoBar
  positivity

private lemma Uθ_M {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * thetaC c τ = 2 * τ ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := rhoC_posP hn c hτ
  unfold thetaC
  field_simp

/-- The common setup of `MA_i` and `MA_cross`. -/
private theorem setupMAi {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {cs : ℝ} (hcs : 0 < cs) (hϱ : rhoBar n cs < 1 / 4)
    (hop : 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ) :
    ∃ ℓ ϱ : ℝ, ℓ ^ 2 = 4 * wn n * τ ^ 2 / n ∧ ϱ = ℓ ^ 2 / sO2 A₁ c τ ∧ 0 < ϱ ∧
      ϱ ≤ rhoBar n cs ∧
      MFHyp (stdGauss (Fin n)) (fA A₁ c τ) ℓ (piBar (rhoBar n cs)) ∧
      2 * (sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs))) ≤
        rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * bN n cs (thetaC c τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  have hm := BstLean.Part153.one_le_mA hn
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have hcτ : 0 < cs * τ ^ 2 := by positivity
  have hs : 0 < sO2 A₁ c τ := hcτ.trans_le hsc
  have hℓ0 : 0 < 4 * wn n * τ ^ 2 / n := by positivity
  have hℓ2 : √(4 * wn n * τ ^ 2 / n) ^ 2 = 4 * wn n * τ ^ 2 / n := Real.sq_sqrt hℓ0.le
  have hϱb := rhoBar_posM hn hcs
  have hle : √(4 * wn n * τ ^ 2 / n) ^ 2 / sO2 A₁ c τ ≤ rhoBar n cs := by
    rw [hℓ2]
    have h1 : 4 * wn n * τ ^ 2 / n / sO2 A₁ c τ ≤ 4 * wn n * τ ^ 2 / n / (cs * τ ^ 2) :=
      div_le_div_of_nonneg_left hℓ0.le hcτ hsc
    have h2 : 4 * wn n * τ ^ 2 / n / (cs * τ ^ 2) = rhoBar n cs := by
      unfold rhoBar
      field_simp
    linarith
  have hpos : 0 < √(4 * wn n * τ ^ 2 / n) ^ 2 / sO2 A₁ c τ := by rw [hℓ2]; positivity
  refine ⟨√(4 * wn n * τ ^ 2 / n), _, hℓ2, rfl, hpos, hle, ?_, ?_⟩
  · refine MFHyp_fA hm A₁ c hτ (Real.sqrt_pos.mpr hℓ0) ?_ hs (hle.trans_lt hϱ)
      (piBar_mono hpos hle hϱ) (piBar_le_one hϱb)
    rw [hℓ2]
    have := mul_le_mul_of_nonneg_left hop (sq_nonneg τ)
    calc 2 / ((mA n : ℕ) : ℝ) * τ ^ 2 * opN A₁ ^ 2
        = τ ^ 2 * (2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2) := by ring
      _ ≤ τ ^ 2 * (4 * wn n / n) := this
      _ = 4 * wn n * τ ^ 2 / n := by ring
  · obtain ⟨ϱ, hϱd⟩ : ∃ ϱ, ϱ = √(4 * wn n * τ ^ 2 / n) ^ 2 / sO2 A₁ c τ := ⟨_, rfl⟩
    rw [← hϱd] at hle hpos ⊢
    have hsϱ : sO2 A₁ c τ * ϱ = 4 * wn n * τ ^ 2 / n := by
      rw [hϱd, hℓ2]
      field_simp
    have hQ := QB_div_mono hpos hle (piBar_nonneg (rhoBar n cs))
    have h1 := mul_le_mul_of_nonneg_left hQ hs.le
    have hU := Uθ_M hn c hτ
    have e1 : sO2 A₁ c τ * (ϱ / rhoBar n cs * QB (rhoBar n cs) (piBar (rhoBar n cs))) =
        sO2 A₁ c τ * ϱ * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs := by ring
    have e2 : rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * bN n cs (thetaC c τ) =
        rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * thetaC c τ *
          (4 * wn n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs) := by
      unfold bN
      ring
    rw [e2, hU]
    rw [e1, hsϱ] at h1
    have e3 : 2 * τ ^ 2 / (n : ℝ) *
        (4 * wn n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs) =
        2 * (4 * wn n * τ ^ 2 / n * QB (rhoBar n cs) (piBar (rhoBar n cs)) / rhoBar n cs) := by
      ring
    rw [e3]
    linarith

private lemma nuR_monoM {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : nuR x ≤ nuR y := by
  unfold nuR
  nlinarith [pow_le_pow_left₀ hx hxy 2]

/-- **Lemma MA (i).** Fix `A₁` with the conclusions of `E_op`, `E_sc`, `E_H`; integrate `A₂`:
`E|𝐝|² ≤ U_r²·ξ_c(θ_in)`, `U_r² = ρ²γ_A/n`. -/
theorem MA_i {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {K cs cH hH : ℝ} (hK : ∀ a, Ures a ≤ K) (hcs : 0 < cs)
    (hϱ : rhoBar n cs < 1 / 4)
    (hop : 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hHS : hsH A₁ c τ ≤ 4 * cH * τ ^ 4 * hH / n) :
    Integrable (fun A₂ => dC A₁ A₂ c τ ^ 2)
      (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) ∧
    ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * xiC n K cs cH hH (thetaC c τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : 0 < wn n := by unfold BstLean.Part153.wn; positivity
  have hm := BstLean.Part153.one_le_mA hn
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have hcτ : 0 < cs * τ ^ 2 := by positivity
  have hs : 0 < sO2 A₁ c τ := hcτ.trans_le hsc
  have hK0 : 0 ≤ K := (Ures_nonneg 0).trans (hK 0)
  have hρ := rhoC_posP hn c hτ
  have hρ2 := rhoC_sqP c τ
  obtain ⟨hθ0, hθ1⟩ := thetaC_bounds hn c hτ
  have hϱb := rhoBar_posM hn hcs
  have hπ0 := piBar_nonneg (rhoBar n cs)
  have hU := Uθ_M hn c hτ
  obtain ⟨ℓ, ϱ, hℓ2, hϱd, hpos, hle, H, hB⟩ := setupMAi hn A₁ c hτ hcs hϱ hop hsc
  obtain ⟨hI, hle2⟩ := H.lemmaMF_K hK
  have hrm := rows_mean hm hI
  have e : (fun A₂ => dC A₁ A₂ c τ ^ 2) = fun A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      2 / ((mA n : ℕ) : ℝ) * ∑ j, DF (stdGauss (Fin n)) (fA A₁ c τ)
        ((√(2 / ((mA n : ℕ) : ℝ)))⁻¹ • fun k => A₂ j k) ^ 2 :=
    funext fun A₂ => dC_sq hm A₁ A₂ c τ
  rw [e]
  refine ⟨hrm.1, ?_⟩
  rw [hrm.2]
  rw [sF2_fA hm, ← hϱd] at hle2
  have hhs : hsF (stdGauss (Fin n)) (fA A₁ c τ) = hsH A₁ c τ := rfl
  rw [hhs] at hle2
  -- the quantities
  obtain ⟨Gb, hGb⟩ : ∃ Gb, Gb = GamBarF (stdGauss (Fin n)) (fA A₁ c τ) := ⟨_, rfl⟩
  rw [← hGb] at hle2
  have hGb0 : 0 ≤ Gb := by rw [hGb]; exact normSq_nonneg _
  have hΓ : gO A₁ c τ ≤ 4 * wn n / n * rhoC c τ ^ 2 := by
    rw [← BstLean.Part153.GamS_eq_gO hm, hρ2]
    exact (BstLean.Part153.GamS_le A₁ c τ).trans (mul_le_mul_of_nonneg_right hop
      (add_nonneg (normSq_nonneg _) (by positivity)))
  have hGbΓ : Gb ≤ gO A₁ c τ := by
    have h1 : sF2 (stdGauss (Fin n)) (fA A₁ c τ) =
        GamF (stdGauss (Fin n)) (fA A₁ c τ) - GamBarF (stdGauss (Fin n)) (fA A₁ c τ) := rfl
    rw [sF2_fA hm, GamF_fA hm, ← hGb] at h1
    linarith
  have hsΓ : sO2 A₁ c τ ≤ gO A₁ c τ := by
    have h1 : 0 ≤ 2 / ((mA n : ℕ) : ℝ) * ∑ i, hO A₁ c τ i ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    unfold sO2
    linarith
  have hhs0 : 0 ≤ hsH A₁ c τ := by
    rw [← hhs]
    unfold hsF
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨R, hR⟩ : ∃ R, R = rhoC c τ ^ 2 := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = thetaC c τ := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2, s2 = sO2 A₁ c τ := ⟨_, rfl⟩
  obtain ⟨hs', hhs'⟩ : ∃ hs', hs' = hsH A₁ c τ := ⟨_, rfl⟩
  obtain ⟨pb, hpb⟩ : ∃ pb, pb = piBar (rhoBar n cs) := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ rb, rb = rhoBar n cs := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = wn n := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) := ⟨_, rfl⟩
  have hrbe : rb = 4 * w / (cs * N) := by rw [hrb, hwd, hN]; rfl
  rw [← hR, ← hθ] at hU hB ⊢
  rw [← hs2] at hle2 hB hsc hs hsΓ
  rw [← hhs'] at hle2 hHS hhs0
  rw [← hpb] at hle2 hB hπ0
  rw [← hrb] at hle hϱb
  rw [← hR] at hΓ
  rw [← hwd] at hℓ2 hΓ hw
  rw [← hN] at hℓ2 hΓ hU hB hnR hHS ⊢
  have hR0 : 0 < R := by rw [hR]; positivity
  have hΓ' := hGbΓ.trans hΓ
  have hsΓ' := hsΓ.trans hΓ
  -- term 1
  have e1 : 2 * (2 * K * hs' / s2) ≤ R * (2 / N / N) * (θ * (cH / cs) * 8 * K * hH) := by
    have h1 : 2 * K * hs' ≤ 2 * K * (4 * cH * τ ^ 4 * hH / N) :=
      mul_le_mul_of_nonneg_left hHS (by positivity)
    have h0 : 0 ≤ 2 * K * hs' := by positivity
    have h2 : 2 * K * hs' / s2 ≤ 2 * K * (4 * cH * τ ^ 4 * hH / N) / (cs * τ ^ 2) :=
      div_le_div₀ (h0.trans h1) h1 hcτ hsc
    have h3 : R * (2 / N / N) * (θ * (cH / cs) * 8 * K * hH) =
        R * (2 / N / N) * θ * ((cH / cs) * 8 * K * hH) := by ring
    rw [h3, hU]
    have h4 : 2 * τ ^ 2 / N * ((cH / cs) * 8 * K * hH) =
        2 * (2 * K * (4 * cH * τ ^ 4 * hH / N) / (cs * τ ^ 2)) := by
      field_simp
      ring
    rw [h4]
    linarith
  -- term 2
  have e2 : 2 * (K * √2 * s2 * pb) ≤ R * (2 / N / N) * (4 * √2 * K * w * N * pb) := by
    have h1 : K * √2 * s2 * pb ≤ K * √2 * (4 * w / N * R) * pb :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsΓ' (by positivity)) hπ0
    have h2 : R * (2 / N / N) * (4 * √2 * K * w * N * pb) =
        2 * (K * √2 * (4 * w / N * R) * pb) := by
      field_simp
    rw [h2]
    linarith
  -- term 3
  have hν := nuR_monoM hpos.le hle
  have hν0 : 0 ≤ nuR ϱ := by unfold nuR; positivity
  have hG0 : 0 ≤ Gb / s2 := div_nonneg hGb0 hs.le
  have hb : ℓ ^ 2 * (Gb / s2) ≤ R * (2 / N / N) * (2 * w * rb * N) := by
    have h1 : Gb / s2 ≤ (4 * w / N * R) / (cs * τ ^ 2) :=
      div_le_div₀ (hGb0.trans hΓ') hΓ' hcτ hsc
    have h2 : ℓ ^ 2 * (Gb / s2) ≤ ℓ ^ 2 * ((4 * w / N * R) / (cs * τ ^ 2)) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg ℓ)
    have h3 : ℓ ^ 2 * ((4 * w / N * R) / (cs * τ ^ 2)) = R * (2 / N / N) * (2 * w * rb * N) := by
      rw [hℓ2, hrbe]
      field_simp
      ring
    linarith
  have hb0 : 0 ≤ R * (2 / N / N) * (2 * w * rb * N) := by positivity
  have hbν : ℓ ^ 2 * (Gb / s2) * nuR ϱ ≤ R * (2 / N / N) * (2 * w * rb * N) * nuR rb :=
    mul_le_mul hb hν hν0 hb0
  have hℓU : 2 * ℓ ^ 2 = R * (2 / N / N) * θ * (4 * w) := by
    rw [hU, hℓ2]
    ring
  have hℓ0 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hc0 : 0 ≤ 4 * (√2 - 1) ^ 2 := by positivity
  have hπp : 0 < π := Real.pi_pos
  have e3 : 2 * (ℓ ^ 2 * (1 / π * (2 * ϱ + 4 * (√2 - 1) ^ 2 * (Gb / s2) * nuR ϱ) + pb)) ≤
      R * (2 / N / N) * (4 * w * ((2 * θ * rb + 4 * (√2 - 1) ^ 2 * rb * N * nuR rb) / π +
        θ * pb)) := by
    have h1 : 2 * ℓ ^ 2 * ϱ ≤ 2 * ℓ ^ 2 * rb := mul_le_mul_of_nonneg_left hle (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hbν hc0
    have h3 : 2 * (ℓ ^ 2 * (1 / π * (2 * ϱ + 4 * (√2 - 1) ^ 2 * (Gb / s2) * nuR ϱ) + pb)) =
        (1 / π) * (2 * (2 * ℓ ^ 2 * ϱ) +
          2 * (4 * (√2 - 1) ^ 2 * (ℓ ^ 2 * (Gb / s2) * nuR ϱ))) + 2 * ℓ ^ 2 * pb := by ring
    have h4 : R * (2 / N / N) * (4 * w * ((2 * θ * rb + 4 * (√2 - 1) ^ 2 * rb * N * nuR rb) / π +
        θ * pb)) =
        (1 / π) * (2 * (R * (2 / N / N) * θ * (4 * w) * rb) +
          2 * (4 * (√2 - 1) ^ 2 * (R * (2 / N / N) * (2 * w * rb * N) * nuR rb))) +
          R * (2 / N / N) * θ * (4 * w) * pb := by ring
    rw [h3, h4, ← hℓU]
    have h5 : 2 * (2 * ℓ ^ 2 * ϱ) + 2 * (4 * (√2 - 1) ^ 2 * (ℓ ^ 2 * (Gb / s2) * nuR ϱ)) ≤
        2 * (2 * ℓ ^ 2 * rb) +
          2 * (4 * (√2 - 1) ^ 2 * (R * (2 / N / N) * (2 * w * rb * N) * nuR rb)) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 1 / π by positivity)
    linarith
  have e5 : R * (2 / N / N) * xiC n K cs cH hH θ =
      R * (2 / N / N) * (θ * (cH / cs) * 8 * K * hH) +
      R * (2 / N / N) * (4 * w * ((2 * θ * rb + 4 * (√2 - 1) ^ 2 * rb * N * nuR rb) / π +
        θ * pb)) + R * (2 / N / N) * bN n cs θ +
      R * (2 / N / N) * (4 * √2 * K * w * N * pb) := by
    unfold xiC
    rw [← hpb, ← hrb, ← hwd, ← hN]
    ring
  rw [e5]
  linarith

/-- **The difference of the two second moments** (the proof of Lemma MP, "the mean of
`Δ_𝖯`"): `|𝗋_h² − 𝗋_b²| ≤ 2·U_r√(b_n)·𝗋_b + E|𝐝|²`. -/
theorem MA_cross {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) {cs : ℝ} (hcs : 0 < cs) (hϱ : rhoBar n cs < 1 / 4)
    (hop : 2 / ((mA n : ℕ) : ℝ) * opN A₁ ^ 2 ≤ 4 * wn n / n)
    (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ) :
    |∫ A₂, Ph A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) -
        ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))| ≤
      2 * (rhoC c τ * √(2 / (n : ℝ) / n) * √(bN n cs (thetaC c τ))) *
          √(∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) +
        ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := BstLean.Part153.one_le_mA hn
  have hρ := rhoC_posP hn c hτ
  obtain ⟨ℓ, ϱ, hℓ2, hϱd, hpos, hle, H, hB⟩ := setupMAi hn A₁ c hτ hcs hϱ hop hsc
  have hD2 := H.DF_sq_int
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, Γ = GamF (stdGauss (Fin n)) (fA A₁ c τ) := ⟨_, rfl⟩
  have hΓ0 : 0 ≤ Γ := by
    have h := (H.XF_bound 0).1.trans (H.XF_bound 0).2
    have hz : normSq (0 : Fin (mA n) → ℝ) = 0 := by simp [normSq]
    rw [hz, ← hΓ] at h
    linarith
  -- integrability of `𝖷²`
  have j4 : Integrable (fun z : Fin (mA n) → ℝ => nrm z ^ (2 * 2)) (stdGauss (Fin (mA n))) :=
    (BstLean.Part153.nrm_moment (mA n) (P := 2) (by norm_num)).1
  have j2 : Integrable (fun z : Fin (mA n) → ℝ => nrm z ^ 2) (stdGauss (Fin (mA n))) :=
    (BstLean.Part153.int_normSq_std (mA n)).1
  have jB : Integrable (fun z : Fin (mA n) → ℝ => nrm z ^ (2 * 2) + 2 * Γ * nrm z ^ 2 + Γ ^ 2)
      (stdGauss (Fin (mA n))) := (j4.add (j2.const_mul _)).add (integrable_const _)
  have hX2 : Integrable (fun z => XF (stdGauss (Fin n)) (fA A₁ c τ) z ^ 2)
      (stdGauss (Fin (mA n))) := by
    refine jB.mono' (H.meas_XF.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_mul, BstLean.Part153.nrm_sq]
    have hX := H.XF_bound z
    rw [← hΓ] at hX
    have hn0 := normSq_nonneg z
    nlinarith
  have hmψ : Measurable (fun z : Fin (mA n) → ℝ =>
      psiS (sF (stdGauss (Fin n)) (fA A₁ c τ)) (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ))) :=
    BstLean.Part137.measurable_psiS.comp
      (measurable_const.prodMk (meas_dotT measurable_id measurable_const))
  have hψ2 : Integrable (fun z : Fin (mA n) → ℝ =>
      psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
        (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2) (stdGauss (Fin (mA n))) := by
    refine ((hX2.const_mul 2).add (hD2.const_mul 2)).mono'
      (hmψ.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    unfold DF
    nlinarith [sq_nonneg (XF (stdGauss (Fin n)) (fA A₁ c τ) z +
      (XF (stdGauss (Fin n)) (fA A₁ c τ) z - psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
        (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ))))]
  have hmh : Measurable (fun x : ℝ => psiS (sF (stdGauss (Fin n)) (fA A₁ c τ)) x) :=
    BstLean.Part137.measurable_psiS.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hDψ, hcr⟩ := H.lemmaMF_cross hmh hψ2
  rw [sF2_fA hm, ← hϱd] at hcr
  -- the three integrals over `A₂`
  have hPh : ∫ A₂, Ph A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) =
      2 * ∫ z, XF (stdGauss (Fin n)) (fA A₁ c τ) z ^ 2 ∂stdGauss (Fin (mA n)) := by
    rw [show (fun A₂ => Ph A₁ A₂ c τ ^ 2) = _ from funext fun A₂ => Ph_sq hm A₁ A₂ c τ]
    exact (rows_mean hm hX2).2
  have hPb : ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) =
      2 * ∫ z : Fin (mA n) → ℝ, psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
        (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 ∂stdGauss (Fin (mA n)) := by
    rw [show (fun A₂ => Pb A₁ c τ A₂ ^ 2) = _ from funext fun A₂ => Pb_sq' hm A₁ A₂ c τ]
    exact (rows_mean hm hψ2).2
  have hdC : ∫ A₂, dC A₁ A₂ c τ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) =
      2 * ∫ z, DF (stdGauss (Fin n)) (fA A₁ c τ) z ^ 2 ∂stdGauss (Fin (mA n)) := by
    rw [show (fun A₂ => dC A₁ A₂ c τ ^ 2) = _ from funext fun A₂ => dC_sq hm A₁ A₂ c τ]
    exact (rows_mean hm hD2).2
  have hXe : ∫ z, XF (stdGauss (Fin n)) (fA A₁ c τ) z ^ 2 ∂stdGauss (Fin (mA n)) =
      (∫ z : Fin (mA n) → ℝ, psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
        (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 ∂stdGauss (Fin (mA n))) +
      2 * (∫ z : Fin (mA n) → ℝ, DF (stdGauss (Fin n)) (fA A₁ c τ) z *
        psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
          (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ∂stdGauss (Fin (mA n))) +
      ∫ z, DF (stdGauss (Fin n)) (fA A₁ c τ) z ^ 2 ∂stdGauss (Fin (mA n)) := by
    have hsum : Integrable (fun z : Fin (mA n) → ℝ =>
        psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
          (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 +
        2 * (DF (stdGauss (Fin n)) (fA A₁ c τ) z * psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
          (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)))) (stdGauss (Fin (mA n))) :=
      hψ2.add (hDψ.const_mul 2)
    rw [← integral_const_mul, ← integral_add hψ2 (hDψ.const_mul 2), ← integral_add hsum hD2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    unfold DF
    ring
  rw [hPh, hPb, hdC, hXe]
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ z : Fin (mA n) → ℝ, psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
        (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ^ 2 ∂stdGauss (Fin (mA n)) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫ z : Fin (mA n) → ℝ, DF (stdGauss (Fin n)) (fA A₁ c τ) z *
        psiS (sF (stdGauss (Fin n)) (fA A₁ c τ))
          (z ⬝ᵥ fbar (stdGauss (Fin n)) (fA A₁ c τ)) ∂stdGauss (Fin (mA n)) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = ∫ z, DF (stdGauss (Fin n)) (fA A₁ c τ) z ^ 2
      ∂stdGauss (Fin (mA n)) := ⟨_, rfl⟩
  rw [← hI, ← hJ] at hcr
  rw [← hI, ← hJ, ← hD]
  have hD0 : 0 ≤ D := by rw [hD]; exact integral_nonneg fun z => sq_nonneg _
  have hE : rhoC c τ * √(2 / (n : ℝ) / n) * √(bN n cs (thetaC c τ)) =
      √(rhoC c τ ^ 2 * (2 / (n : ℝ) / n) * bN n cs (thetaC c τ)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hρ.le]
  have hS : √(2 * (sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs)))) ≤
      rhoC c τ * √(2 / (n : ℝ) / n) * √(bN n cs (thetaC c τ)) := by
    rw [hE]
    exact Real.sqrt_le_sqrt hB
  have h22 : √(2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hcalc : 4 * |J| ≤ 2 * (rhoC c τ * √(2 / (n : ℝ) / n) * √(bN n cs (thetaC c τ))) *
      √(2 * I) := by
    have h1 : 4 * |J| ≤ 4 * (√(sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs))) * √I) := by linarith
    have h2 : 4 * (√(sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs))) * √I) =
        2 * √(2 * (sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs)))) * √(2 * I) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      linear_combination (-(2 * √(sO2 A₁ c τ * QB ϱ (piBar (rhoBar n cs))) * √I)) * h22
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS
      (by norm_num : (0 : ℝ) ≤ 2)) (Real.sqrt_nonneg (2 * I))
    linarith
  have habs : |2 * (I + 2 * J + D) - 2 * I| ≤ 4 * |J| + 2 * D := by
    have e : 2 * (I + 2 * J + D) - 2 * I = 4 * J + 2 * D := by ring
    rw [e]
    have h1 := abs_add_le (4 * J) (2 * D)
    rw [abs_mul, abs_mul, abs_of_nonneg hD0, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    exact h1
  linarith

end BstLean.Part154
