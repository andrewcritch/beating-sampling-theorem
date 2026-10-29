import BstLean.Part169All
import BstLean.Part177En

/-!
# Part 178 (file `Q`): the kept indices at the removal tolerance `η = 1/50`
(namespace `BstLean.Part178.N36`)

No proof is left open; no `native_decide` or `axiom` is used.

Copies of the declarations of Part 169 that depend on the split data `dP` (through the kept
indices `KR` or the floor `dStar`), with `dP` now built with the removal tolerance
`η = 1/50` (Part 169: `η = 10⁻⁴`); the floor `sd = 0.4691` is unchanged. So
`dStar = (1 − 1/50)·0.4691² ≈ 0.215649 ≥ 1/5`. Declarations that do not depend on `η`
(`fbR`, `wbR`, `eR`, `VR`, `exF`, …; note `(dP c).Sb` does not depend on `η`) stay Part 169's.
Also the `KR`-dependent part of Part 177's file `En` (`fb_of_SEn`).
Inside namespace `N36` these names shadow Part 169's when `BstLean.Part169` is opened.
The docstrings of copied declarations can carry older numbers; the Lean statements are
authoritative.
-/

namespace BstLean.Part178.N36

-- ===== from Part169End.lean =====
section SEnd
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part166 (goodD)

variable {n : ℕ}

noncomputable def dP (c : Ret n) : BstLean.Part161.SplitData n :=
  dPaper (paperDesignP n) c (22 * √(2 / (n : ℝ)) ^ 2)
    (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
    (1 / 50) (by norm_num) (by norm_num)
/-- **The bias hypothesis for the paper's program**: `√(E_kept H²(Q̄_a, Q̃_a)) ≤ 0.004295`, with
`Q̃_a` built from the conditional passes `passF`, `passW`. -/
def BIASP (c : Ret n) : Prop := BIAS_hyp (paperDesignP n) c (dP c) (4295 / 10 ^ 6)

end SEnd

-- ===== from Part169Red.lean =====
section SRed
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (hellG2 keptIx latC muI BIAS_hyp lamX sigX xLat measurable_latC Ix
  measurableSet_bulkIx measurableSet_keptSet)
open BstLean.Part162 (lbar measurable_lbar)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- The kept indices of the paper's program. -/
def KR (c : Ret n) : Set (Ix n) := keptIx (paperDesignP n) c (dP c)
lemma measurableSet_KR (c : Ret n) : MeasurableSet (KR c) :=
  measurableSet_keptSet _ (dP c).mgood (measurableSet_bulkIx _ c) _
/-- **`BIASP` from the inputs and the moments of Part 08.** On the kept indices `K`:
`S̄ ≥ γ_A d` (`d ≥ 1/5`), `|c_A|² ≤ γ_A e_b nχ`, `|V| ≤ v_max`, the `L⁸` bounds `a_ω`, `a_f` on
`n(ω̄ − ω̃)`, `n(f̄ − f̃)`, the bounds `H_f` on `‖f̄‖_4`, `‖f̄‖_24`, the bound `C_v` on `‖nV‖_2`
(with the integrability of the functions involved), and the numerical inequality
`P_B ≤ 0.004295²`. -/
theorem biasP_of_inputs (hn : 0 < n) (c : Ret n) (he : 0 < eR c)
    {χ d ε vmax aw af Hf Cv : ℝ} (hd : 1 / 5 ≤ d) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hSbd : ∀ a ∈ KR c, 2 / (n : ℝ) * d ≤ (dP c).Sb a)
    (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax)
    (iW2 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 2) (KR c) (muI n))
    (iW6 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 6) (KR c) (muI n))
    (iW8 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (KR c) (muI n))
    (iF2 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c) (muI n))
    (iF4 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 4) (KR c) (muI n))
    (iF8 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) (KR c) (muI n))
    (if4 : IntegrableOn (fun a => fbR c a ^ 4) (KR c) (muI n))
    (if24 : IntegrableOn (fun a => fbR c a ^ 24) (KR c) (muI n))
    (ifF2 : IntegrableOn (fun a => fbR c a ^ 2 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c)
      (muI n))
    (ifF6 : IntegrableOn (fun a => fbR c a ^ 6 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 6) (KR c)
      (muI n))
    (iV : IntegrableOn (fun a => ((n : ℝ) * VR c a) ^ 2) (KR c) (muI n))
    (hW8 : ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8)
    (hF8 : ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8)
    (hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4)
    (hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24)
    (hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2)
    (hnum : PB n χ d ε vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2) :
    BIASP c := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hse : 0 < √(eR c) := Real.sqrt_pos.mpr he
  -- the integrand of `BIAS_hyp` in the abstract form
  have hS : ∀ a, (dP c).Sb a = 2 / (n : ℝ) * (wbR c a - fbR c a ^ 2 - VR c a) := by
    intro a; rw [show (dP c).Sb a = (BstLean.Part169.dP c).Sb a from rfl]; unfold VR; field_simp; ring
  have hfun : (fun a => hellG2 n (((dP c).lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        ((dP c).Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2) =
      fun a => hellG2 n ((fbR c a / √(eR c) - ftR c a / √(eR c)) ^ 2 * normSq c.2.1.2)
        (2 / (n : ℝ) * (wbR c a - fbR c a ^ 2 - VR c a))
        (2 / (n : ℝ) * max (1 / 5) (wtR c a - ftR c a ^ 2)) := by
    funext a
    rw [← hS a, mixP_eq]
    have e1 : (dP c).lamb a = fbR c a / √(eR c) := by
      unfold fbR; field_simp; rfl
    rw [e1]
    rfl
  have hint := bias_price_paper (muI n) (measurableSet_KR c)
    (by have := measureReal_le_one (μ := muI n) (s := KR c); exact this) n hn hγ he hd
    (normSq_nonneg _) hc hε1 hT haw haf hHf hCv (measurable_fbR c) (measurable_ftR c)
    (measurable_wbR c) (measurable_wtR c) (measurable_VR c)
    (fun a ha => (hS a) ▸ hSbd a ha) hVm iW2 iW6 iW8 iF2 iF4 iF8 if4 if24 ifF2 ifF6 iV
    hW8 hF8 hf4 hf24 hV
  unfold BIASP BIAS_hyp
  have hle : ∫ a in keptIx (paperDesignP n) c (dP c), hellG2 n (((dP c).lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        ((dP c).Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 ∂muI n ≤
      (4295 / 10 ^ 6) ^ 2 := by
    rw [hfun]; exact hint.trans hnum
  calc _ ≤ √((4295 / 10 ^ 6 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 4295 / 10 ^ 6 := Real.sqrt_sq (by norm_num)

end SRed

-- ===== from Part169In.lean =====
section SIn
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (keptIx latC muI xLat Ix sA lamX sigX)
open BstLean.Part162 (sgA latC_sq_le normSq_xLat_le)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

noncomputable def dStar : ℝ := (1 - 1 / 50) * (4691 / 10000) ^ 2
lemma dStar_ge : (1 : ℝ) / 5 ≤ dStar := by unfold dStar; norm_num
/-- **The floor of the kept full means** (paper `t7:p08:inputs`, first inequality):
`S̄(a) ≥ γ_A·dStar` on the kept indices of the paper's program. -/
theorem Sb_lower (hn : 1 ≤ n) (c : Ret n) {a : Ix n} (ha : a ∈ KR c) :
    2 / (n : ℝ) * dStar ≤ (dP c).Sb a := by
  set D := paperDesignP n
  have hk := BstLean.Part162.kept_facts hn D c (by norm_num : (0:ℝ) < 1 / 50)
    (by norm_num : (1:ℝ) / 50 < 1) ha
  obtain ⟨-, hm1, -, -, hsl, -⟩ := hk
  set σl : ℝ := √(2 / (n : ℝ)) * (4691 / 10000) with hσl
  set sl := BstLean.Part161.slice (dP c) a with hsl_def
  have msl : MeasurableSet sl := BstLean.Part161.measurableSet_slice _ a
  have hσ0 : 0 ≤ σl := by positivity
  have hpt : ∀ v, sl.indicator (fun _ => σl ^ 2) v ≤ sA D c a v := by
    intro v
    by_cases hv : v ∈ sl
    · rw [Set.indicator_of_mem hv]
      have h1 := (hsl v hv).2
      show σl ^ 2 ≤ sgA D c a v ^ 2
      exact pow_le_pow_left₀ hσ0 h1 2
    · rw [Set.indicator_of_notMem hv]
      show 0 ≤ sgA D c a v ^ 2
      positivity
  have hint := integral_mono ((integrable_const (σl ^ 2)).indicator msl) (integrable_sA hn D c a)
    hpt
  rw [integral_indicator msl, integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hint
  have hS : (dP c).Sb a = ∫ v, sA D c a v ∂stdGauss (Fin (n - 1)) := rfl
  rw [hS]
  refine le_trans ?_ hint
  have hσ2 : σl ^ 2 = 2 / (n : ℝ) * (4691 / 10000) ^ 2 := by
    rw [hσl, mul_pow, Real.sq_sqrt (by positivity)]
  rw [hσ2]
  unfold dStar
  have h0 : (0 : ℝ) ≤ 2 / (n : ℝ) * (4691 / 10000) ^ 2 := by positivity
  have hm1' : 1 - 1 / 50 ≤ (stdGauss (Fin (n - 1))).real sl := hm1
  have := mul_le_mul_of_nonneg_right hm1' h0
  linarith

end SIn

-- ===== from Part169Lip.lean =====
section SLip
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (xLat hhMat uHat consV latC Ix lamX bulkI bulkIx keptIx hh_normSq
  normSq_consV)
open BstLean.Part162 (lbar)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

lemma lat_mem_of_KR {c : Ret n} {a : Ix n} (ha : a ∈ KR c) :
    nodeL c ≤ latC (paperDesignP n) c a ∧ latC (paperDesignP n) c a ≤ nodeH c := by
  have h : latC (paperDesignP n) c a ∈ bulkI (paperDesignP n) c := ha.1
  rw [bulkI_eq] at h
  exact h
/-- **The location grid error** (paper `t7:p08:grid`): on a kept index,
`|f̄(s) − f̄(s_g)| ≤ ΛΔ/(2√n√q)` when `s² ≤ 1 − q` on `[L, H]`. -/
theorem grid_f (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {q : ℝ} (hq : 0 < q) (hLH : nodeL c < nodeH c)
    (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q) {a : Ix n} (ha : a ∈ KR c) :
    |fbR c a - fbarS c (nodeS c (gIdx c (latC (paperDesignP n) c a)))| ≤
      O₂ * O₁ * (nodeD c / 2) / (√(n : ℝ) * √q) := by
  obtain ⟨hl1, hl2⟩ := lat_mem_of_KR ha
  obtain ⟨hnear, hg⟩ := gIdx_near hn c hLH hl1 hl2
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH hg
  rw [fbR_eq]
  refine (fbar_lip hn c h1 h2 hO₁ hO₂ hq (hbulk _ hl1 hl2) (hbulk _ hs1 hs2)).trans ?_
  have hpos : 0 < √(n : ℝ) * √q :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))) (Real.sqrt_pos.mpr hq)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by positivity)) hpos.le
/-- **The energy grid error** (paper `t7:p08:grid`): on a kept index,
`|ω̄(s) − ω̄(s_g)| ≤ Λ²Δ/(n√q)`. -/
theorem grid_w (hn : 1 ≤ n) (c : Ret n) {O₁ O₂ : ℝ} (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO₁ : 0 ≤ O₁) (hO₂ : 0 ≤ O₂) {q : ℝ} (hq : 0 < q) (hLH : nodeL c < nodeH c)
    (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q) {a : Ix n} (ha : a ∈ KR c) :
    |wbR c a - wbarS c (nodeS c (gIdx c (latC (paperDesignP n) c a)))| ≤
      2 * (O₂ * O₁) ^ 2 * (nodeD c / 2) / (n * √q) := by
  obtain ⟨hl1, hl2⟩ := lat_mem_of_KR ha
  obtain ⟨hnear, hg⟩ := gIdx_near hn c hLH hl1 hl2
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH hg
  rw [wbR_eq]
  refine (wbar_lip hn c h1 h2 hO₁ hO₂ hq (hbulk _ hl1 hl2) (hbulk _ hs1 hs2)).trans ?_
  have hpos : 0 < (n : ℝ) * √q :=
    mul_pos (by exact_mod_cast (show 0 < n by omega)) (Real.sqrt_pos.mpr hq)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnear (by positivity)) hpos.le

end SLip

-- ===== from Part169Mom.lean =====
section SMom
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (muI)
open BstLean.Part166 (goodD)

variable {n : ℕ}

structure MomIn (c : Ret n) (ε vmax aw af Hf Cv : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  iW2 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 2) (KR c) (muI n)
  iW6 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 6) (KR c) (muI n)
  iW8 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (KR c) (muI n)
  iF2 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c) (muI n)
  iF4 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 4) (KR c) (muI n)
  iF8 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) (KR c) (muI n)
  if4 : IntegrableOn (fun a => fbR c a ^ 4) (KR c) (muI n)
  if24 : IntegrableOn (fun a => fbR c a ^ 24) (KR c) (muI n)
  ifF2 : IntegrableOn (fun a => fbR c a ^ 2 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c)
    (muI n)
  ifF6 : IntegrableOn (fun a => fbR c a ^ 6 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 6) (KR c)
    (muI n)
  iV : IntegrableOn (fun a => ((n : ℝ) * VR c a) ^ 2) (KR c) (muI n)
  hW8 : ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8
  hF8 : ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2
/-- **`BIASP` on the good set from the moment inputs.** -/
theorem biasP_goodD (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hM : MomIn c ε vmax aw af Hf Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2) :
    BIASP c := by
  obtain ⟨he, hcA⟩ := cA_input hn hc
  exact biasP_of_inputs (by omega) c he dStar_ge hε1 hT haw haf hHf hCv
    (fun a ha => Sb_lower (by omega) c ha) hcA hM.hVm hM.iW2 hM.iW6 hM.iW8 hM.iF2 hM.iF4 hM.iF8
    hM.if4 hM.if24 hM.ifF2 hM.ifF6 hM.iV hM.hW8 hM.hF8 hM.hf4 hM.hf24 hM.hV hnum

end SMom

-- ===== from Part169Asm.lean =====
section SAsm
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI)
open BstLean.Part150 (c1F c2F)

variable {n : ℕ}

/-- **`‖n(f̄ − f̃)‖_{L⁸(K)} ≤ A + g_f + r_f`** from the `L⁸` bound `A` of the exact-rule error,
on the operator events (`OpB`), the upper `ς` bound at the nodes, and the bulk bound
`s² ≤ 1 − q` on `[L, H]`. -/
theorem hF8_of_exact (hn : 2 ≤ n) (c : Ret n) {O₁ O₂ q σ0 A : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 < O₁) (hO₂ : 0 < O₂) (hq : 0 < q) (hσ : 0 < σ0)
    (hLH : nodeL c < nodeH c) (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q)
    (hvs : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ σ0 ^ 2) (hA : 0 < A)
    (iX : IntegrableOn (fun a => exF c a ^ 8) (KR c) (muI n))
    (hX : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ A ^ 8) :
    IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) (KR c) (muI n) ∧
      ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤
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
  refine int_pow8_add_const (measurableSet_KR c) measureReal_le_one mY iX hA (by positivity) hX ?_
  intro a ha
  have hg := grid_f hn1 c h1 h2 hO₁.le hO₂.le hq hLH hbulk ha
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
theorem hW8_of_exact (hn : 2 ≤ n) (c : Ret n) {O₁ O₂ q σ0 A : ℝ} (h1 : OpB (A1 c) O₁)
    (h2 : OpB (A2 c) O₂) (hO₁ : 0 < O₁) (hO₂ : 0 < O₂) (hq : 0 < q) (hσ : 0 < σ0)
    (hLH : nodeL c < nodeH c) (hbulk : ∀ s, nodeL c ≤ s → s ≤ nodeH c → s ^ 2 ≤ 1 - q)
    (hvs : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ σ0 ^ 2) (hA : 0 < A)
    (iX : IntegrableOn (fun a => exW c a ^ 8) (KR c) (muI n))
    (hX : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ A ^ 8) :
    IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (KR c) (muI n) ∧
      ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤
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
  refine int_pow8_add_const (measurableSet_KR c) measureReal_le_one mY iX hA (by positivity) hX ?_
  intro a ha
  have hg := grid_w hn1 c h1 h2 hO₁.le hO₂.le hq hLH hbulk ha
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

end SAsm

-- ===== from Part169Int.lean =====
section SInt
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- **`MomIn` without the integrability items.** -/
structure MomB (c : Ret n) (ε vmax aw af Hf Cv : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  hW8 : ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8
  hF8 : ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2
/-- **The integrability items of `MomIn` are theorems.** -/
theorem momIn_of_momB (hn : 1 ≤ n) {c : Ret n} {ε vmax aw af Hf Cv : ℝ}
    (h : MomB c ε vmax aw af Hf Cv) : MomIn c ε vmax aw af Hf Cv := by
  obtain ⟨Mf, hf⟩ := bdd_fbR hn c
  obtain ⟨Mw, hw⟩ := bdd_wbR hn c
  obtain ⟨Nf, hf'⟩ := bdd_ftR hn c
  obtain ⟨Nw, hw'⟩ := bdd_wtR hn c
  obtain ⟨MV, hV⟩ := bdd_VR hn c
  have mf := measurable_fbR c
  have mw := measurable_wbR c
  have mf' := measurable_ftR c
  have mw' := measurable_wtR c
  have mV := measurable_VR c
  have mW : Measurable (fun a => (n : ℝ) * (wbR c a - wtR c a)) := (mw.sub mw').const_mul _
  have mF : Measurable (fun a => (n : ℝ) * (fbR c a - ftR c a)) := (mf.sub mf').const_mul _
  have bW := bdd_nsub hw hw'
  have bF := bdd_nsub hf hf'
  exact
  { hVm := h.hVm
    iW2 := intOn_of_bdd (mW.pow_const 2) (bdd_pow bW 2) _
    iW6 := intOn_of_bdd (mW.pow_const 6) (bdd_pow bW 6) _
    iW8 := intOn_of_bdd (mW.pow_const 8) (bdd_pow bW 8) _
    iF2 := intOn_of_bdd (mF.pow_const 2) (bdd_pow bF 2) _
    iF4 := intOn_of_bdd (mF.pow_const 4) (bdd_pow bF 4) _
    iF8 := intOn_of_bdd (mF.pow_const 8) (bdd_pow bF 8) _
    if4 := intOn_of_bdd (mf.pow_const 4) (bdd_pow hf 4) _
    if24 := intOn_of_bdd (mf.pow_const 24) (bdd_pow hf 24) _
    ifF2 := intOn_of_bdd ((mf.pow_const 2).mul (mF.pow_const 2))
      (bdd_mul (bdd_pow hf 2) (bdd_pow bF 2)) _
    ifF6 := intOn_of_bdd ((mf.pow_const 6).mul (mF.pow_const 6))
      (bdd_mul (bdd_pow hf 6) (bdd_pow bF 6)) _
    iV := intOn_of_bdd ((mV.const_mul _).pow_const 2) (bdd_pow (bdd_nmul hV) 2) _
    hW8 := h.hW8
    hF8 := h.hF8
    hf4 := h.hf4
    hf24 := h.hf24
    hV := h.hV }

end SInt

-- ===== from Part169Op.lean =====
section SOp
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI)
open BstLean.Part166 (goodD)
open BstLean.Part150 (c1F c2F rhoC)

variable {n : ℕ}

/-- **The moment inputs with the exact-rule errors**: the upper `ς` bound at the nodes, the
`L⁸` bounds `A_f`, `A_ω` of the exact-rule errors, and the inputs `v_max`, `H_f`, `C_v`. -/
structure MomX (c : Ret n) (vmax Af Aw Hf Cv σ0 : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  hvs : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ σ0 ^ 2
  hXF : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ Af ^ 8
  hXW : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ Aw ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

end SOp

-- ===== from Part169Sig.lean =====
section SSig
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat hhMat uHat consV hh_normSq)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)

variable {n : ℕ}

/-- **The moment inputs not yet proved**, after Part 169: the `L⁸` bounds `A_f`, `A_ω` of the
exact-rule errors, and `v_max`, `H_f`, `C_v`. -/
structure MomY (c : Ret n) (vmax Af Aw Hf Cv : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  hXF : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ Af ^ 8
  hXW : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ Aw ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

end SSig

-- ===== from Part169Var.lean =====
section SVar
open BstLean.Part169

open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (latC Ix muI xLat lamX sigX)
open BstLean.Part162 (lbar psiA)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- **The exact-rule `L⁸` bounds**: the only moment inputs of Part 08 left after Part 169. -/
structure MomZ (c : Ret n) (Af Aw : ℝ) : Prop where
  hXF : ∫ a in KR c, exF c a ^ 8 ∂muI n ≤ Af ^ 8
  hXW : ∫ a in KR c, exW c a ^ 8 ∂muI n ≤ Aw ^ 8

end SVar

-- ===== from Part177En.lean =====
section SEn
open MeasureTheory ProbabilityTheory Real
open BstLean.Part177
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg hid2 mA)
open BstLean.Part157
open BstLean.Part161 (Ix muI xLat latC hhMat consV uHat)
open BstLean.Part160 (AgFam agKey agentEv)
open BstLean.Part153 (nuA)
open BstLean.Part53 (unitF53)
open BstLean.Part169 (fbR eR measurable_fbR paperDesignP)
variable {n : ℕ}
/-- **The location means on the energy event**: `∫_K f̄²⁴ ≤ 1.005²⁴` and `∫_K f̄⁴ ≤ 1.005⁴` on
the kept indices `K = KR c` (the inputs `hf24`, `hf4` of `MomX` with `H_f = 1.005`). -/
theorem fb_of_SEn (hn : 2 ≤ n) {c : Ret n} (hc : c ∈ agentEv (paperDesignP n) (SEn n))
    (hτ : 0 < (paperDesignP n).tau0 c) :
    ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ (1005 / 1000) ^ 24 ∧
      ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ (1005 / 1000) ^ 4 := by
  have hn1 : 1 ≤ n := by omega
  have hρ : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by unfold stdGauss; infer_instance
  set D := paperDesignP n
  set θ := c.2.1.1
  set w : Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => omK θ (xLat c (latC D c a) (unitF53 v))
    with hw
  have mw : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => w p.1 p.2) :=
    measurable_omK_comp (θ := fun _ : Ix n × (Fin (n - 1) → ℝ) => θ) measurable_const
      (measurable_ptK_comp (ch := fun _ => c.1.2) (τ := fun _ => D.tau0 c) measurable_const
        measurable_const measurable_fst measurable_snd)
  set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
  have w0 : ∀ a v, 0 ≤ w a v := fun a v => omK_nonneg _ _
  have wb : ∀ a v, w a v ≤ B := fun a v =>
    omK_le hn1 θ (BstLean.Part162.normSq_xLat_le hn1 c (BstLean.Part162.latC_sq_le D c a) v)
  have hB0 : 0 ≤ B := (w0 0 0).trans (wb 0 0)
  have hY : ∫ a, ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ 11 / 10 := YEn_le hc hτ
  set f : Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => √(eR c) * BstLean.Part161.lA D c a v
    with hfd
  have mf : ∀ a, Measurable (fun v => f a v) := fun a =>
    (BstLean.Part161.measurable_lA_left D c a).const_mul _
  have f2 : ∀ a v, f a v ^ 2 ≤ w a v := fun a v => fv_sq_le hn1 c a v
  have fbd : ∀ a v, |f a v| ≤ √B := fun a v => by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt ((f2 a v).trans (wb a v))
  have iv : ∀ a, Integrable (fun v => f a v) (stdGauss (Fin (n - 1))) := fun a =>
    intOfBdd (mf a) (fbd a)
  have efb : ∀ a, fbR c a = ∫ v, f a v ∂stdGauss (Fin (n - 1)) := fun a => by
    simp only [hfd]
    rw [integral_const_mul]; rfl
  -- `f̄²⁴ ≤ ∫ ω¹²`
  have h24 : ∀ a, fbR c a ^ 24 ≤ ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) := fun a => by
    rw [efb a]
    have hJ := (Even.convexOn_pow (𝕜 := ℝ) (n := 24) (by decide)).map_integral_le
      (μ := stdGauss (Fin (n - 1))) (f := fun v => f a v) (continuous_pow 24).continuousOn
      isClosed_univ (Filter.Eventually.of_forall fun v => Set.mem_univ _) (iv a)
      (intOfBdd (M := √B ^ 24) ((mf a).pow_const 24) fun v => by
        simp only [Function.comp_def]; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbd a v) _)
    refine hJ.trans (integral_mono ?_ ?_ fun v => ?_)
    · exact intOfBdd (M := √B ^ 24) ((mf a).pow_const 24) fun v => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbd a v) _
    · exact intOfBdd (M := B ^ 12) ((mw.comp measurable_prodMk_left).pow_const 12) fun v => by
        rw [abs_of_nonneg (pow_nonneg (w0 a v) _)]; exact pow_le_pow_left₀ (w0 a v) (wb a v) _
    · show f a v ^ 24 ≤ w a v ^ 12
      rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) (f2 a v) 12
  have fbb : ∀ a, |fbR c a| ≤ √B := fun a => by
    rw [efb a]
    refine (abs_integral_le_integral_abs).trans ((integral_mono (iv a).abs
      (integrable_const _) (fbd a)).trans (by simp))
  have mfb := measurable_fbR c
  have i24 : Integrable (fun a => fbR c a ^ 24) (muI n) :=
    intOfBdd (M := √B ^ 24) (mfb.pow_const 24) fun a => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbb a) _
  have i4 : Integrable (fun a => fbR c a ^ 4) (muI n) :=
    intOfBdd (M := √B ^ 4) (mfb.pow_const 4) fun a => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbb a) _
  have iW : Integrable (fun a => ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1))) (muI n) :=
    intOfBdd (M := B ^ 12) ((mw.pow_const 12).stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => by
        rw [abs_of_nonneg (integral_nonneg fun v => pow_nonneg (w0 a v) _)]
        calc ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) ≤ ∫ v, B ^ 12 ∂stdGauss (Fin (n - 1)) :=
              integral_mono (intOfBdd (M := B ^ 12) ((mw.comp measurable_prodMk_left).pow_const 12)
                fun v => by
                  rw [abs_of_nonneg (pow_nonneg (w0 a v) _)]
                  exact pow_le_pow_left₀ (w0 a v) (wb a v) _)
                (integrable_const _) fun v => pow_le_pow_left₀ (w0 a v) (wb a v) _
          _ = B ^ 12 := by simp
  have hall24 : ∫ a, fbR c a ^ 24 ∂muI n ≤ 11 / 10 :=
    (integral_mono i24 iW h24).trans hY
  have hK24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ ∫ a, fbR c a ^ 24 ∂muI n :=
    setIntegral_le_integral i24 (Filter.Eventually.of_forall fun a => by positivity)
  have hK4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ ∫ a, fbR c a ^ 4 ∂muI n :=
    setIntegral_le_integral i4 (Filter.Eventually.of_forall fun a => by positivity)
  refine ⟨hK24.trans (hall24.trans (by norm_num)), hK4.trans ?_⟩
  have i5 : Integrable (fun a => (5 + fbR c a ^ 24) / 6) (muI n) :=
    ((integrable_const 5).add i24).div_const 6
  calc ∫ a, fbR c a ^ 4 ∂muI n ≤ ∫ a, (5 + fbR c a ^ 24) / 6 ∂muI n :=
        integral_mono i4 i5 fun a => pow4_le_24
    _ = (5 + ∫ a, fbR c a ^ 24 ∂muI n) / 6 := by
        rw [integral_div, integral_add (integrable_const 5) i24]; simp
    _ ≤ (1005 / 1000) ^ 4 := by linarith [hall24]

theorem fb24_of_SEn (hn : 2 ≤ n) {c : Ret n} (hc : c ∈ agentEv (paperDesignP n) (SEn n))
    (hτ : 0 < (paperDesignP n).tau0 c) :
    ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ (1005 / 1000) ^ 24 := (fb_of_SEn hn hc hτ).1

theorem fb4_of_SEn (hn : 2 ≤ n) {c : Ret n} (hc : c ∈ agentEv (paperDesignP n) (SEn n))
    (hτ : 0 < (paperDesignP n).tau0 c) :
    ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ (1005 / 1000) ^ 4 := (fb_of_SEn hn hc hτ).2

end SEn

end BstLean.Part178.N36
