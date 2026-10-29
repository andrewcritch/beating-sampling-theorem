import BstLean.Part182T168x21M

/-!
# Part 182 (file `T169x21M`) [TI-lite (λ = 0.72) copy: `roomT21M = 0.0018`, `HQF21M_stmt`, namespace `….N21.M`]: the T169 link of the chain at `n ≥ 21 500` (CONDITIONAL on TI through
`HQF21M_stmt`; namespace `BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21`)

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 181's file `T169` with `22 000 ↦ 21 500` (the floor of Fork L1's top
`BstLean.Part179.N30.N27.N26.N24.N23.N22.N21.M.classifier_paper_JM21H`), the argument
`hHQ : BstLean.Part182.HQF21M_stmt` and the room `roomK + roomX + roomT21M`. Retuned constants (valid
from `21 000`): `128q ≤ 0.0854n`, `X2 ≤ 2.2613`, `Z ≤ 0.1514`, `K² ≈ 4.91 ≤ 5`; `qB ≥ 0.4139`,
`√n ≥ 144.9`, `g_f ≤ 38·10⁻⁵`, `g_ω ≤ 308·10⁻⁵`, `v_max ≤ 159·10⁻⁵`, `C_v ≤ 180·10⁻⁶`, `χ ≤ 1.050`;
`PB_boundE`: `P_B ≤ 0.005154²` if `a_ω + 2.01a_f ≤ 0.4160`; `PB_leE`: `A_ω + 2.01A_f ≤ 0.40412`;
node latitude `1 − s² ≤ 0.5903`; `F_fl ≤ 0.0152`, `W_fl ≤ 0.1238` (polynomial certificates at
`r₀ = 144.9`); `A_f = 0.0628`, `A_ω = 0.2778`; `B_f = 0.01286`, `B_ω = 0.01334`; statistics charge
`≤ 3.6·10⁻⁵`. Ledger `3.6·10⁻⁵ + ((0.0152 + 0.01286)/0.0628)⁸ + ((0.1238 + 0.01334)/0.2778)⁸ + 10⁻⁶
≈ 5.153·10⁻³ ≤ 0.00516 ≤ roomK + roomX + roomT21M`.
The docstrings of copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21.M

-- ===== the bias root `0.0029` (Part 169's `BIASP` has `0.004295`) =====
section SBiasR
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (hellG2 keptIx latC muI BIAS_hyp lamX sigX xLat measurable_latC Ix
  measurableSet_bulkIx measurableSet_keptSet)
open BstLean.Part162 (lbar measurable_lbar)
open BstLean.Part53 (unitF53 measurable_unitF)

open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- `BIAS_hyp` for the paper's program with the bias root `0.0029`. -/
def BIASR (c : Ret n) : Prop := BIAS_hyp (paperDesignP n) c (dP c) (5154 / 10 ^ 6)

/-- **`BIASR` from the inputs** (a copy of Part 169's `biasP_of_inputs` with root `0.0029`). -/
theorem biasR_of_inputs (hn : 0 < n) (c : Ret n) (he : 0 < eR c)
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
    (hnum : PB n χ d ε vmax aw af Hf Cv ≤ (5154 / 10 ^ 6) ^ 2) :
    BIASR c := by
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
  unfold BIASR BIAS_hyp
  have hle : ∫ a in keptIx (paperDesignP n) c (dP c), hellG2 n (((dP c).lamb a -
        ((paperDesignP n).mix c (latC (paperDesignP n) c a)).1) ^ 2 * normSq c.2.1.2)
        ((dP c).Sb a) ((paperDesignP n).mix c (latC (paperDesignP n) c a)).2 ∂muI n ≤
      (5154 / 10 ^ 6) ^ 2 := by
    rw [hfun]; exact hint.trans hnum
  calc _ ≤ √((5154 / 10 ^ 6 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
    _ = 5154 / 10 ^ 6 := Real.sqrt_sq (by norm_num)

/-- **`BIASR` on the good set** (a copy of Part 169's `biasP_goodD` with root `0.0029`). -/
theorem biasR_goodD (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hM : MomIn c ε vmax aw af Hf Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (5154 / 10 ^ 6) ^ 2) :
    BIASR c := by
  obtain ⟨he, hcA⟩ := cA_input hn hc
  exact biasR_of_inputs (by omega) c he dStar_ge hε1 hT haw haf hHf hCv
    (fun a ha => Sb_lower (by omega) c ha) hcA hM.hVm hM.iW2 hM.iW6 hM.iW8 hM.iF2 hM.iF4 hM.iF8
    hM.if4 hM.if24 hM.ifF2 hM.ifF6 hM.iV hM.hW8 hM.hF8 hM.hf4 hM.hf24 hM.hV hnum

end SBiasR

-- ===== from Part169End.lean =====
section SPart169End
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part160
open BstLean.Part161 (BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- **The classifier theorem for the paper's program with its tables** (every `n ≥ 45 000`). -/
theorem classifier_paper_pass22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    (hB : ∀ c ∈ goodD n (paperDesignP n) EA, BIASR c) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_LG22k hHQ hn passF passW measurable_passF measurable_passW t hEA
    hA hroom hB

/-- **The classifier theorem with a separate bias event** (every `n ≥ 45 000`). -/
theorem classifier_paper_bias22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    (hB : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), BIASR c) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  set X := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hsub : X ∩ (EA ∩ Eb)ᶜ ⊆ (X ∩ EAᶜ) ∪ Ebᶜ := by
    intro x hx
    rcases hx with ⟨hX, hn'⟩
    by_cases h : x ∈ EA
    · right; exact fun hb' => hn' ⟨h, hb'⟩
    · left; exact ⟨hX, h⟩
  have hle : (retDist (paperCentres n)).real (X ∩ (EA ∩ Eb)ᶜ) ≤ δA + δb :=
    (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hA hb))
  exact classifier_paper_pass22k hHQ hn t (hEA.inter hEb) hle hroom hB

end SPart169End

-- ===== from Part169Mom.lean =====
section SPart169Mom
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (muI)
open BstLean.Part166 (goodD)
variable {n : ℕ}
/-- **The classifier theorem for the paper's program, with `BIAS_hyp` replaced by the moment
inputs of Part 08** (every `n ≥ 45 000`). Remaining: the moment inputs `MomIn` on
`goodD n D (E_A ∩ E_bias)`, the numerical condition `P_B ≤ 0.004295²`, the charges of `E_A` and
of the bias event, and `δ_A + δ_bias ≤ roomK`. -/
theorem classifier_paper_mom22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (5154 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomIn c ε vmax aw af Hf Cv) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_bias22k hHQ hn t hEA hEb hA hb hroom fun c hc =>
    biasR_goodD (by omega) hc hε1 hT haw haf hHf hCv (hM c hc) hnum

end SPart169Mom

-- ===== from Part169Int.lean =====
section SPart169Int
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53)
variable {n : ℕ}
/-- **The classifier theorem with the moment bounds `MomB`** (no integrability hypothesis;
every `n ≥ 45 000`). -/
theorem classifier_paper_momB22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (5154 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomB c ε vmax aw af Hf Cv) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_mom22k hHQ hn t hEA hEb hA hb hroom hε1 hT haw haf hHf hCv hnum
    fun c hc => momIn_of_momB (by omega) (hM c hc)

end SPart169Int

-- ===== from Part169Op.lean =====
section SPart169Op
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI)
open BstLean.Part166 (goodD)
open BstLean.Part150 (c1F c2F rhoC)
variable {n : ℕ}
lemma qB_pos (hn : 21500 ≤ n) : 4139 / 10000 ≤ qB n := by
  unfold qB
  have hnR : (21500 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : √(54 / 100 : ℝ) ≤ 734847 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : √(55 / 100 / (n : ℝ)) ≤ 5118 / 1000000 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]; nlinarith
  have h3 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) := by positivity
  have h4 : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (n : ℝ)) ≤ 76556 / 100000 := by linarith
  nlinarith

/-- **`MomB` from `MomX` on the good set.** -/
theorem momB_of_momX (hn : 21500 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax Af Aw Hf Cv σ0 : ℝ} (hσ : 0 < σ0)
    (hAf : 0 < Af) (hAw : 0 < Aw) (h : MomX c vmax Af Aw Hf Cv σ0) :
    MomB c ε vmax (aWn n Aw σ0) (aFn n Af σ0) Hf Cv := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.window_goodA (by omega) passF passW measurable_passF
    measurable_passW _ c hc
  obtain ⟨hLH, hbulk, hD⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  obtain ⟨h1, h2⟩ := opB_goodD (by omega) hc
  have hq : 0 < qB n := lt_of_lt_of_le (by norm_num) (qB_pos hn)
  have hO1 := O1n_pos (n := n) hn1
  have hO2 := O2n_pos (n := n) hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos hn2)
  have hpos1 : 0 < √(n : ℝ) * √(qB n) := mul_pos (Real.sqrt_pos.mpr hnR) (Real.sqrt_pos.mpr hq)
  have hpos2 : 0 < (n : ℝ) * √(qB n) := mul_pos hnR (Real.sqrt_pos.mpr hq)
  have hD0 : 0 ≤ nodeD c := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hc1 : 0 ≤ c1F (rexp (1 / 2) / 12) (Jz n) := c1F_nonneg _
  have hc2 : 0 ≤ c2F (rexp (1 / 2) / 12) (Jz n) := c2F_nonneg _
  obtain ⟨MF, bF⟩ := bdd_exF hn1 c
  obtain ⟨MW, bW⟩ := bdd_exW hn1 c
  have iXF := intOn_of_bdd ((measurable_exF c).pow_const 8) (bdd_pow bF 8) (KR c)
  have iXW := intOn_of_bdd ((measurable_exW c).pow_const 8) (bdd_pow bW 8) (KR c)
  obtain ⟨-, hF⟩ := hF8_of_exact hn2 c h1 h2 hO1 hO2 hq hσ hLH hbulk h.hvs hAf iXF h.hXF
  obtain ⟨-, hW⟩ := hW8_of_exact hn2 c h1 h2 hO1 hO2 hq hσ hLH hbulk h.hvs hAw iXW h.hXW
  refine ⟨h.hVm, hW.trans ?_, hF.trans ?_, h.hf4, h.hf24, h.hV⟩
  · unfold aWn
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    have : (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (nodeD c / 2) / (n * √(qB n))) ≤
        (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) := by
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hpos2.le) hnR.le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · unfold aFn
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    have : (n : ℝ) * (O2n n * O1n n * (nodeD c / 2) / (√(n : ℝ) * √(qB n))) ≤
        (n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) := by
      refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hpos1.le) hnR.le
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-- **The classifier theorem with the exact-rule moment inputs `MomX`** (every `n ≥ 45 000`).
Remaining: `MomX` on `goodD n D (E_A ∩ E_bias)` (the upper `ς` bound at the nodes, the `L⁸`
bounds `A_f`, `A_ω` of the exact-rule errors, `v_max`, `H_f`, `C_v`), the numerical condition
`P_B ≤ 0.004295²` at `a_f = aFn n A_f σ₀`, `a_ω = aWn n A_ω σ₀`, and the charges. -/
theorem classifier_paper_momX22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {ε vmax Af Aw Hf Cv σ0 : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmax / dStar) (hσ : 0 < σ0)
    (hAf : 0 < Af) (hAw : 0 < Aw) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax (aWn n Aw σ0) (aFn n Af σ0) Hf Cv ≤
      (5154 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomX c vmax Af Aw Hf Cv σ0) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < qB n := lt_of_lt_of_le (by norm_num) (qB_pos hn)
  have hO1 := O1n_pos (n := n) hn1
  have hO2 := O2n_pos (n := n) hn1
  have hJ : (0 : ℝ) < Jz n := by exact_mod_cast (Jz_pos (by omega : 2 ≤ n))
  have hDP : 0 ≤ DeltaP n := by unfold DeltaP; positivity
  have hc1 := c1F_nonneg (Jz n)
  have hc2 := c2F_nonneg (Jz n)
  have haf : 0 < aFn n Af σ0 := by unfold aFn; positivity
  have haw : 0 < aWn n Aw σ0 := by unfold aWn; positivity
  exact classifier_paper_momB22k hHQ hn t hEA hEb hA hb hroom hε1 hT haw haf hHf hCv hnum
    fun c hc => momB_of_momX hn hc hσ hAf hAw (hM c hc)

end SPart169Op

-- ===== from Part169Sig.lean =====
section SPart169Sig
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (latC Ix muI xLat hhMat uHat consV hh_normSq)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
variable {n : ℕ}
/-- **The upper `ς` bound at the nodes on the good set** (no new event). -/
theorem hvs_goodD (hn : 21500 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) : ∀ a ∈ KR c, vsig2 c (sgR c a) ≤ sig0sq n := by
  intro a ha
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := BstLean.Part164.window_goodA (by omega) passF passW measurable_passF
    measurable_passW _ c hc
  obtain ⟨hLH, hbulk, -⟩ := bulk_of_window (by omega) c hτ hθ0 hθ1
  obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH (gIdx_lt c hn1 (latC (paperDesignP n) c a))
  have hq := qB_pos hn
  have hs : sgR c a ^ 2 ≤ 1 := by have := hbulk _ hs1 hs2; unfold sgR; linarith
  have hop : BstLean.Part152.opN (A1 c) ≤ O1n n :=
    BstLean.Part164.eop_of_goodC16 (BstLean.Part164.goodC16_of_goodA (by omega) passF passW
      measurable_passF measurable_passW hc)
  have h0 := BstLean.Part152.opN_nonneg (A1 c)
  refine (vsig2_le (by omega) c hs).trans ?_
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hm : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  unfold sig0sq
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ h1.le) hm
  have hsq : BstLean.Part152.opN (A1 c) ^ 2 ≤ O1n n ^ 2 := pow_le_pow_left₀ h0 hop 2
  have hs0 : 0 ≤ sgR c a ^ 2 := sq_nonneg _
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (1 - sgR c a ^ 2) * (n * BstLean.Part152.opN (A1 c) ^ 2)
      ≤ 1 * (n * O1n n ^ 2) := by
        apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hsq hnn) (by positivity)
          (by norm_num)
    _ = n * O1n n ^ 2 := one_mul _

/-- **The classifier theorem with the remaining moment inputs `MomY`** (every `n ≥ 45 000`).
Remaining: `MomY` on `goodD n D (E_A ∩ E_bias)`, the numerical condition
`P_B ≤ 0.004295²` at `a_f = aFn n A_f σ₀`, `a_ω = aWn n A_ω σ₀` with `σ₀ = √(sig0sq n)`, and
the charges `δ_A + δ_bias ≤ roomK`. -/
theorem classifier_paper_momY22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {ε vmax Af Aw Hf Cv : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmax / dStar)
    (hAf : 0 < Af) (hAw : 0 < Aw) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) Hf Cv ≤ (5154 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomY c vmax Af Aw Hf Cv) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hσ : 0 < √(sig0sq n) := Real.sqrt_pos.mpr (sig0sq_pos (by omega))
  refine classifier_paper_momX22k hHQ hn t hEA hEb hA hb hroom hε1 hT hσ hAf hAw hHf hCv hnum
    fun c hc => ?_
  have hM' := hM c hc
  refine ⟨hM'.hVm, fun a ha => ?_, hM'.hXF, hM'.hXW, hM'.hf4, hM'.hf24, hM'.hV⟩
  rw [Real.sq_sqrt (sig0sq_pos (by omega)).le]
  exact hvs_goodD hn hc a ha

end SPart169Sig

-- ===== from Part169Var.lean =====
section SPart169Var
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part134
open BstLean.Part161 (latC Ix muI xLat lamX sigX)
open BstLean.Part162 (lbar psiA)
open BstLean.Part166 (goodD)
open BstLean.Part53 (unitF53 measurable_unitF)
variable {n : ℕ}
/-- **The pointwise variance bound on the good set**: `0 ≤ V ≤ v_max`. -/
theorem VR_le (hn : 21500 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) (a : Ix n) : 0 ≤ VR c a ∧ VR c a ≤ vmaxN n := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨he, -⟩ := cA_input (by omega) hc
  have hb : normSq (bR c) ≠ 0 := by
    intro h; unfold eR at he; rw [h] at he; simp at he
  obtain ⟨h1, h2⟩ := opB_goodD (by omega) hc
  have hO1 := (O1n_pos (n := n) hn1).le
  have hO2 := (O2n_pos (n := n) hn1).le
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O2n n * O1n n / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O2n n * O1n n / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O2n n * O1n n / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    unfold vmaxN
    exact div_le_div_of_nonneg_right hpsi h2n.le

/-- **The `L²` bound of `nV` on the good set**: `∫_K (nV)² ≤ C_v²`, `C_v = 5.1·0.7315/(n − 2)`. -/
theorem VR_L2 (hn : 21500 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) :
    ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ CvN n ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨he, -⟩ := cA_input (by omega) hc
  have hb : normSq (bR c) ≠ 0 := by
    intro h; unfold eR at he; rw [h] at he; simp at he
  have heR := eR_le (by omega) hc
  -- `V = e_b·Var_v λ`
  set Vl : Ix n → ℝ := fun a => ∫ v, (lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) -
    ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 ∂stdGauss (Fin (n - 1)) with hVl
  have hVe : ∀ a, VR c a = eR c * Vl a := by
    intro a
    have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
    obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
    have hV := VR_eq hn1 c hb a
    rw [fbR_eq] at hV
    unfold fbarS at hV
    rw [← var_eq i1 i2] at hV
    rw [hV, hVl]
    simp only [fX_eq_lam c]
    have hin : ∫ w, √(eR c) * lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
        (unitF53 w)) ∂stdGauss (Fin (n - 1)) = √(eR c) * ∫ w, lamX (paperDesignP n) c
          (xLat c (latC (paperDesignP n) c a) (unitF53 w)) ∂stdGauss (Fin (n - 1)) :=
      integral_const_mul _ _
    rw [hin]
    have e2 : ∀ v, (√(eR c) * lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
        (unitF53 v)) - √(eR c) * ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a)
          (unitF53 w)) ∂stdGauss (Fin (n - 1))) ^ 2 =
        eR c * (lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) -
          ∫ w, lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 w))
            ∂stdGauss (Fin (n - 1))) ^ 2 := by
      intro v; rw [← mul_sub, mul_pow, Real.sq_sqrt he.le]
    simp only [e2]
    exact integral_const_mul _ _
  -- the latitude certificate
  have h12 := (certsD hn passF passW measurable_passF measurable_passW
    hc).1
  have h2 := BstLean.Part162.psi_low_of_12 (by omega) (paperDesignP n) c (BstLean.Part162.lipLam_nonneg (paperDesignP n) c)
    (BstLean.Part162.lamX_euLip (paperDesignP n) c) (fun t x ht => BstLean.Part162.lamX_hom (paperDesignP n) c t x ht)
    (C := 51 / 10) (by norm_num) h12 (j := 2) (m := 6) (by norm_num) (by norm_num)
  have hint := BstLean.Part162.int_var_psi (by omega) (paperDesignP n) c (BstLean.Part162.lipLam_nonneg (paperDesignP n) c)
    (BstLean.Part162.lamX_euLip (paperDesignP n) c) (fun t x ht => BstLean.Part162.lamX_hom (paperDesignP n) c t x ht)
    (C := 51 / 10) (by norm_num) h2
  -- from `K` to the whole index space
  obtain ⟨MV, bV⟩ := bdd_VR hn1 c
  have mV := measurable_VR c
  have iV : Integrable (fun a => ((n : ℝ) * VR c a) ^ 2) (muI n) := by
    have := intOn_of_bdd ((mV.const_mul (n : ℝ)).pow_const 2) (bdd_pow (bdd_nmul bV) 2)
      Set.univ
    rwa [IntegrableOn, Measure.restrict_univ] at this
  have hK : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ ∫ a, ((n : ℝ) * VR c a) ^ 2 ∂muI n :=
    setIntegral_le_integral iV (Filter.Eventually.of_forall fun a => sq_nonneg _)
  refine hK.trans ?_
  have e : (fun a => ((n : ℝ) * VR c a) ^ 2) = fun a => ((n : ℝ) * eR c) ^ 2 * Vl a ^ 2 := by
    funext a; rw [hVe a]; ring
  rw [e, integral_const_mul]
  calc ((n : ℝ) * eR c) ^ 2 * ∫ a, Vl a ^ 2 ∂muI n
      ≤ ((n : ℝ) * eR c) ^ 2 * (51 / 10 / n / ((n : ℝ) - 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hint (sq_nonneg _)
    _ = (51 / 10 * eR c / ((n : ℝ) - 2)) ^ 2 := by field_simp
    _ ≤ CvN n ^ 2 := by
        unfold CvN
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        exact div_le_div_of_nonneg_right (by nlinarith) h2n.le

/-- **The classifier theorem with `BIAS_hyp` reduced to the exact-rule `L⁸` bounds** (every
`n ≥ 45 000`). Remaining: `MomZ` (the `L⁸` bounds `A_f`, `A_ω` of the exact Gaussian-rule
errors `n(f̄(s_g) − f_G(s_g))`, `n(ω̄(s_g) − ω_G(s_g))` on the kept indices) on
`goodD n D (E_A ∩ E_bias)`, the numerical condition `P_B ≤ 0.004295²` with the explicit
constants `vmaxN`, `HfN`, `CvN`, `aFn`, `aWn`, and the charges `δ_A + δ_bias ≤ roomK`. -/
theorem classifier_paper_exact22k (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {ε Af Aw : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmaxN n / dStar) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε (vmaxN n) (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) (HfN n) (CvN n) ≤ (5154 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomZ c Af Aw) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hHf : 0 < HfN n := by
    have := O1n_pos (n := n) hn1; have := O2n_pos (n := n) hn1
    unfold HfN; positivity
  have hCv : 0 < CvN n := by unfold CvN; positivity
  refine classifier_paper_momY22k hHQ hn t hEA hEb hA hb hroom hε1 hT hAf hAw hHf hCv hnum
    fun c hc => ?_
  have hZ := hM c hc
  have bf := fbR_le (by omega) hc
  refine ⟨fun a _ => ?_, hZ.hXF, hZ.hXW, int_pow_le_of_bdd bf _ (measurable_fbR c) 4,
    int_pow_le_of_bdd bf _ (measurable_fbR c) 24, VR_L2 hn hc⟩
  obtain ⟨h0, h1⟩ := VR_le hn hc a
  rw [abs_of_nonneg h0]; exact h1

end SPart169Var

-- ===== from Part169Num.lean =====
section SPart169Num
open BstLean.Part169
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part150 (c1F c2F)
open BstLean.Part166 (goodD)
variable {n : ℕ}
lemma sqrt_n_ge (hn : 21500 ≤ n) : (1449 / 10 : ℝ) ≤ √(n : ℝ) := by
  rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
  have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma HfN_le (hn : 21500 ≤ n) : HfN n ≤ 406 / 100 := by
  have hr := sqrt_n_ge hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [HfN_eq (by omega), div_le_iff₀ (by positivity)]
  have e : (n : ℝ) = √(n : ℝ) ^ 2 := n_eq_sq n
  set r := √(n : ℝ)
  rw [e]
  nlinarith [sq_nonneg r, mul_pos (by linarith : (0:ℝ) < r) (by linarith : (0:ℝ) < r)]

/-- `sig0sq n ≤ 4.12/n`. -/
lemma sig0sq_le (hn : 21500 ≤ n) : sig0sq n ≤ 412 / 100 / n := by
  have hr := sqrt_n_ge hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set r := √(n : ℝ) with hrdef
  have e : (n : ℝ) = r ^ 2 := n_eq_sq n
  have hr0 : 0 < r := by linarith
  have hO : O1n n ^ 2 = 2 * (r + 2) ^ 2 := by
    unfold O1n
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hrdef, e]
    field_simp
  unfold sig0sq mA
  push_cast
  rw [hO]
  have key : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (2 * (r + 2) ^ 2) / ((n : ℝ) - 1)) =
      4 * (r + 2) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by positivity) hn0, e]
  nlinarith [sq_nonneg r, mul_pos hr0 hr0, pow_pos hr0 3, pow_pos hr0 4]

/-- **The price bound with `H_f = 1.005`** (the energy event; `ε = 1/50`, `d = dStar`). -/
theorem PB_boundE (hn : 21500 ≤ n) {χ vmax aw af Cv : ℝ} (hχ0 : 0 ≤ χ) (hχ : χ ≤ 1050 / 1000)
    (hv : vmax ≤ 159 / 100000) (haw0 : 0 ≤ aw) (haf0 : 0 ≤ af)
    (haf : af ≤ 7 / 100) (hX : aw + 2 * (1005 / 1000) * af ≤ 4160 / 10000)
    (hCv0 : 0 ≤ Cv) (hCv : Cv ≤ 180 / 1000000) :
    PB n χ dStar (1 / 50) vmax aw af (1005 / 1000) Cv ≤ (5154 / 10 ^ 6) ^ 2 := by
  have hN : (21500 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hd : dStar = 49 / 50 * (452 / 1000) ^ 2 := by unfold dStar; norm_num
  unfold PB
  rw [hd]
  set d : ℝ := 49 / 50 * (452 / 1000) ^ 2 with hdd
  have hd0 : 0 < d := by rw [hdd]; norm_num
  have hdl : 2002 / 10000 ≤ d := by rw [hdd]; norm_num
  have hT : 120 / 10000 ≤ 1 / 50 - vmax / d := by
    have : vmax / d ≤ 159 / 100000 / (2002 / 10000) :=
      div_le_div₀ (by norm_num) hv (by norm_num) hdl
    have h2 : (159 / 100000 : ℝ) / (2002 / 10000) ≤ 80 / 10000 := by norm_num
    linarith
  have hT0 : 0 < 1 / 50 - vmax / d := lt_of_lt_of_le (by norm_num) hT
  have haf2 : af ^ 2 ≤ 49 / 10000 := by nlinarith
  have hafn : af ^ 2 / n ≤ 5 / 10000000 := by
    rw [div_le_iff₀ hN0]; nlinarith
  have hafn0 : 0 ≤ af ^ 2 / n := by positivity
  have hB0 : 0 ≤ (aw + 2 * (1005 / 1000) * af + af ^ 2 / n + Cv) / d := by positivity
  have hB : (aw + 2 * (1005 / 1000) * af + af ^ 2 / n + Cv) / d ≤ 416181 / 1000000 / d :=
    div_le_div_of_nonneg_right (by linarith) hd0.le
  have hB2 : ((aw + 2 * (1005 / 1000) * af + af ^ 2 / n + Cv) / d) ^ 2 / (8 * (1 - 1 / 50)) ≤
      (416181 / 1000000 / d) ^ 2 / (8 * (1 - 1 / 50)) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hB0 hB 2) (by norm_num)
  have hK1 : (416181 / 1000000 / d) ^ 2 / (8 * (1 - 1 / 50)) ≤ 5512 / 10000 := by
    rw [hdd]; norm_num
  have hcf : χ / (2 * (2 - 1 / 50) * d) * af ^ 2 ≤ 1050 / 1000 / (2 * (2 - 1 / 50) * d) *
      (49 / 10000) :=
    mul_le_mul (div_le_div_of_nonneg_right hχ (by positivity)) haf2 (sq_nonneg _) (by positivity)
  have hK2 : 1050 / 1000 / (2 * (2 - 1 / 50) * d) * (49 / 10000) ≤ 65 / 10000 := by
    rw [hdd]; norm_num
  have ht1 : (χ / (2 * (2 - 1 / 50) * d) * af ^ 2 + ((aw + 2 * (1005 / 1000) * af + af ^ 2 / n + Cv) / d) ^ 2 /
      (8 * (1 - 1 / 50))) / n ≤ (5512 / 10000 + 65 / 10000) / 21500 := by
    have hnum0 : 0 ≤ χ / (2 * (2 - 1 / 50) * d) * af ^ 2 +
        ((aw + 2 * (1005 / 1000) * af + af ^ 2 / n + Cv) / d) ^ 2 / (8 * (1 - 1 / 50)) := by positivity
    calc _ ≤ (5512 / 10000 + 65 / 10000) / (n : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hN0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  have hm1 : (aw + 2 * (1005 / 1000) * af) / (99 / 100 * d * n * (1 / 50 - vmax / d)) ≤ 9 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 99 / 100 * (2002 / 10000) * 21500 * (120 / 10000) ≤ 99 / 100 * d * n * (1 / 50 - vmax / d) := by
      have h2 : 99 / 100 * (2002 / 10000) ≤ 99 / 100 * d := by linarith
      have h3 : 99 / 100 * (2002 / 10000) * 21500 ≤ 99 / 100 * d * n :=
        mul_le_mul h2 hN (by norm_num) (by positivity)
      exact mul_le_mul h3 hT (by norm_num) (by positivity)
    nlinarith
  have hm2 : af ^ 2 / (1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d)) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / 100 * (2002 / 10000) * 21500 ^ 2 * (120 / 10000) ≤
        1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d) := by
      have h2 : 1 / 100 * (2002 / 10000) ≤ 1 / 100 * d := by linarith
      have h3 : (1 / 100 * (2002 / 10000) : ℝ) * 21500 ^ 2 ≤ 1 / 100 * d * n ^ 2 :=
        mul_le_mul h2 (pow_le_pow_left₀ (by norm_num) hN 2) (by norm_num) (by positivity)
      exact mul_le_mul h3 hT (by norm_num) (by positivity)
    nlinarith
  have hm10 : 0 ≤ (aw + 2 * (1005 / 1000) * af) / (99 / 100 * d * n * (1 / 50 - vmax / d)) := by
    positivity
  have hm20 : 0 ≤ af ^ 2 / (1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d)) := by positivity
  have ht2 : 2 * (((aw + 2 * (1005 / 1000) * af) / (99 / 100 * d * n * (1 / 50 - vmax / d))) ^ 6 +
      (af ^ 2 / (1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d))) ^ 4) ≤
      2 * ((9 / 1000) ^ 6 + (1 / 1000) ^ 4) := by
    have := pow_le_pow_left₀ hm10 hm1 6
    have := pow_le_pow_left₀ hm20 hm2 4
    linarith
  have hfin : (5512 / 10000 + 65 / 10000) / 21500 + 2 * ((9 / 1000) ^ 6 + (1 / 1000) ^ 4) ≤
      ((5154 : ℝ) / 10 ^ 6) ^ 2 := by norm_num
  linarith

lemma Jz_ge (hn : 21500 ≤ n) : 99 / 100 * ((n : ℝ) * √(n : ℝ)) ≤ Jz n ∧ 1000000 ≤ Jz n := by
  have hr := sqrt_n_ge hn
  have hN : (21500 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (n : ℝ) * √(n : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    rw [← rpow_three_halves]; exact Nat.le_ceil _
  have hbig : (3000000 : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by nlinarith
  have hc1 : 1 ≤ ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have : (1 : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have hJ : (Jz n : ℝ) = (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz; rw [Nat.cast_sub hc1]; simp
  constructor
  · rw [hJ]; nlinarith
  · have : (1000000 : ℝ) ≤ Jz n := by rw [hJ]; linarith
    exact_mod_cast this

lemma sqrt_qB_ge (hn : 21500 ≤ n) : 6433 / 10000 ≤ √(qB n) := by
  rw [Real.le_sqrt (by norm_num) (by linarith [qB_pos hn])]
  linarith [qB_pos hn]

lemma sqrt_sig0_le (hn : 21500 ≤ n) : √(sig0sq n) ≤ 203 / 100 / √(n : ℝ) := by
  have hr := sqrt_n_ge hn
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt hN0.le]
  refine (sig0sq_le hn).trans (div_le_div_of_nonneg_right (by norm_num) hN0.le)

lemma nDelta_le (hn : 21500 ≤ n) : (n : ℝ) * DeltaP n ≤ 12 * (7417 / 10000) / (512 * (1449 / 10)) := by
  have hr := sqrt_n_ge hn
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold DeltaP
  rw [Real.sqrt_div' _ hN0.le]
  have hs : √(55 / 100 : ℝ) ≤ 7417 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have e : (n : ℝ) * (12 * (√(55 / 100) / √(n : ℝ)) / (512 * n)) = 12 * √(55 / 100) / (512 * √(n : ℝ)) := by
    field_simp
  rw [e]
  exact div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)

lemma gf_le (hn : 21500 ≤ n) :
    (n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) ≤ 38 / 100000 := by
  have hr := sqrt_n_ge hn
  have hq := sqrt_qB_ge hn
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) (by omega)
  have hD := nDelta_le hn
  have hD0 : 0 ≤ (n : ℝ) * DeltaP n := by unfold DeltaP; positivity
  rw [O2O1_eq (by omega)]
  have e : (n : ℝ) * (HfN n * √(n : ℝ) * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) =
      HfN n * ((n : ℝ) * DeltaP n) / (2 * √(qB n)) := by
    field_simp
  rw [e]
  calc HfN n * ((n : ℝ) * DeltaP n) / (2 * √(qB n))
      ≤ 406 / 100 * (12 * (7417 / 10000) / (512 * (1449 / 10))) / (2 * (6433 / 10000)) :=
        div_le_div₀ (by positivity) (mul_le_mul hH hD hD0 (by norm_num)) (by norm_num)
          (by linarith)
    _ ≤ 38 / 100000 := by norm_num

lemma gw_le (hn : 21500 ≤ n) :
    (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) ≤ 308 / 100000 := by
  have hr := sqrt_n_ge hn
  have hq := sqrt_qB_ge hn
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) (by omega)
  have hD := nDelta_le hn
  have hD0 : 0 ≤ (n : ℝ) * DeltaP n := by unfold DeltaP; positivity
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [O2O1_eq (by omega)]
  have e : (n : ℝ) * (2 * (HfN n * √(n : ℝ)) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) =
      HfN n ^ 2 * ((n : ℝ) * DeltaP n) / √(qB n) := by
    rw [mul_pow, Real.sq_sqrt hN0.le]; field_simp
  rw [e]
  have hH2 : HfN n ^ 2 ≤ (406 / 100) ^ 2 := pow_le_pow_left₀ hH0 hH 2
  calc HfN n ^ 2 * ((n : ℝ) * DeltaP n) / √(qB n)
      ≤ (406 / 100) ^ 2 * (12 * (7417 / 10000) / (512 * (1449 / 10))) / (6433 / 10000) :=
        div_le_div₀ (by positivity) (mul_le_mul hH2 hD hD0 (by norm_num)) (by norm_num) hq
    _ ≤ 308 / 100000 := by norm_num

lemma rf_le (hn : 21500 ≤ n) :
    (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) / Jz n)) ≤ 27 / 10000 := by
  have hr := sqrt_n_ge hn
  obtain ⟨hJ, hJ6⟩ := Jz_ge hn
  have hc := c1F_le hJ6
  have hc0 := c1F_nonneg (Jz n)
  have hs := sqrt_sig0_le hn
  have hs0 := Real.sqrt_nonneg (sig0sq n)
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr0 : 0 < √(n : ℝ) := by linarith
  have hJ0 : (0 : ℝ) < Jz n := lt_of_lt_of_le (by positivity) hJ
  have e : (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) / Jz n)) =
      ((n : ℝ) * √(n : ℝ)) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n)) / Jz n := by ring
  rw [e, div_le_iff₀ hJ0]
  have h1 : c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) ≤ 19 / 100 * (203 / 100 / √(n : ℝ)) :=
    mul_le_mul hc hs hs0 (by norm_num)
  have h2 : ((n : ℝ) * √(n : ℝ)) * (19 / 100 * (203 / 100 / √(n : ℝ))) =
      19 / 100 * (203 / 100) * n := by field_simp
  have h3 : 19 / 100 * (203 / 100) * (n : ℝ) ≤ 27 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := by
    nlinarith
  calc ((n : ℝ) * √(n : ℝ)) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n))
      ≤ ((n : ℝ) * √(n : ℝ)) * (19 / 100 * (203 / 100 / √(n : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 19 / 100 * (203 / 100) * n := h2
    _ ≤ 27 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := h3
    _ ≤ 27 / 10000 * Jz n := mul_le_mul_of_nonneg_left hJ (by norm_num)

lemma rw_le (hn : 21500 ≤ n) :
    (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) ^ 2 / Jz n)) ≤ 26 / 10000 := by
  have hr := sqrt_n_ge hn
  obtain ⟨hJ, hJ6⟩ := Jz_ge hn
  have hc := c2F_le hJ6
  have hc0 := c2F_nonneg (Jz n)
  have hs := sig0sq_le hn
  have hs0 := (sig0sq_pos (n := n) (by omega)).le
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr0 : 0 < √(n : ℝ) := by linarith
  have hJ0 : (0 : ℝ) < Jz n := lt_of_lt_of_le (by positivity) hJ
  rw [Real.sq_sqrt hs0]
  have e : (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n / Jz n)) =
      ((n : ℝ) * n) * (c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n) / Jz n := by ring
  rw [e, div_le_iff₀ hJ0]
  have h1 : c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n ≤ 9 / 100 * (412 / 100 / n) :=
    mul_le_mul hc hs hs0 (by norm_num)
  have h2 : ((n : ℝ) * n) * (9 / 100 * (412 / 100 / n)) = 9 / 100 * (412 / 100) * n := by
    field_simp
  have h3 : 9 / 100 * (412 / 100) * (n : ℝ) ≤ 26 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := by
    nlinarith
  calc ((n : ℝ) * n) * (c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n)
      ≤ ((n : ℝ) * n) * (9 / 100 * (412 / 100 / n)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 9 / 100 * (412 / 100) * n := h2
    _ ≤ 26 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := h3
    _ ≤ 26 / 10000 * Jz n := mul_le_mul_of_nonneg_left hJ (by norm_num)

lemma vmaxN_le (hn : 21500 ≤ n) : vmaxN n ≤ 159 / 100000 := by
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) (by omega)
  have hN : (21500 : ℝ) ≤ n := by exact_mod_cast hn
  unfold vmaxN
  rw [← HfN]
  rw [div_le_iff₀ (by linarith)]
  have : HfN n ^ 2 ≤ (406 / 100) ^ 2 := pow_le_pow_left₀ hH0 hH 2
  nlinarith

lemma CvN_le (hn : 21500 ≤ n) : CvN n ≤ 180 / 1000000 := by
  have hN : (21500 : ℝ) ≤ n := by exact_mod_cast hn
  unfold CvN
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma chi_le (hn : 21500 ≤ n) : BstLean.Part164.chiUp n / n ≤ 1050 / 1000 := by
  have hr := sqrt_n_ge hn
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold BstLean.Part164.chiUp
  rw [div_le_iff₀ hN0, Real.sqrt_mul' _ (by norm_num : (0:ℝ) ≤ 12)]
  have h12 : √(12 : ℝ) ≤ 34642 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have e : (n : ℝ) = √(n : ℝ) ^ 2 := n_eq_sq n
  nlinarith [mul_le_mul_of_nonneg_left h12 (by linarith : (0:ℝ) ≤ √(n : ℝ))]

/-- **The numerical condition with the energy event**: `A_ω + 2.01·A_f ≤ 0.429` gives
`P_B ≤ 0.004295²` at `H_f = 1.005` (`ε = 1/50`), every `n ≥ 40 000`. -/
theorem PB_leE (hn : 21500 ≤ n) {Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw)
    (hA : Aw + 201 / 100 * Af ≤ 40412 / 100000) (hAf' : Af ≤ 66 / 1000) :
    PB n (BstLean.Part164.chiUp n / n) dStar (1 / 50) (vmaxN n) (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) (1005 / 1000) (CvN n) ≤ (5154 / 10 ^ 6) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0 : ℝ) < n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hJ, -⟩ := Jz_ge hn
  have hJ0 : (0 : ℝ) < Jz n := lt_of_lt_of_le (by positivity) hJ
  have hq0 : 0 < √(qB n) := lt_of_lt_of_le (by norm_num) (sqrt_qB_ge hn)
  have hO1 := O1n_pos (n := n) hn1
  have hO2 := O2n_pos (n := n) hn1
  have hDP : 0 ≤ DeltaP n := by unfold DeltaP; positivity
  have hc1 := c1F_nonneg (Jz n)
  have hc2 := c2F_nonneg (Jz n)
  have g1 := gf_le hn
  have g2 := rf_le hn
  have g3 := gw_le hn
  have g4 := rw_le hn
  have g10 : 0 ≤ (n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) := by
    positivity
  have g20 : 0 ≤ (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) / Jz n)) := by
    positivity
  have g30 : 0 ≤ (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) := by
    positivity
  have g40 : 0 ≤ (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) ^ 2 / Jz n)) := by
    positivity
  have haf : aFn n Af √(sig0sq n) ≤ Af + 308 / 100000 := by unfold aFn; linarith
  have haf0 : 0 ≤ aFn n Af √(sig0sq n) := by unfold aFn; linarith
  have haw : aWn n Aw √(sig0sq n) ≤ Aw + 568 / 100000 := by unfold aWn; linarith
  have haw0 : 0 ≤ aWn n Aw √(sig0sq n) := by unfold aWn; linarith
  have hCv0 : 0 ≤ CvN n := by
    have : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    unfold CvN; positivity
  refine PB_boundE hn (by unfold BstLean.Part164.chiUp; positivity) (chi_le hn) (vmaxN_le hn)
    haw0 haf0 (by linarith) ?_ hCv0 (CvN_le hn)
  linarith

lemma goodD_mono (D : Design n) {E E' : Set (Ret n)} (h : E ⊆ E') :
    goodD n D E ⊆ goodD n D E' := by
  intro c hc
  unfold goodD BstLean.Part165.goodC BstLean.Part164.goodA goodSet at hc ⊢
  exact ⟨hc.1, ⟨⟨hc.2.1.1, ⟨⟨⟨⟨h hc.2.1.2.1.1.1.1, hc.2.1.2.1.1.1.2⟩, hc.2.1.2.1.1.2⟩,
    hc.2.1.2.1.2⟩, hc.2.1.2.2⟩⟩, hc.2.2⟩⟩

lemma mem_of_goodD (D : Design n) {E : Set (Ret n)} {c : Ret n} (hc : c ∈ goodD n D E) : c ∈ E :=
  hc.2.1.2.1.1.1.1

/-- **The classifier theorem with `BIAS_hyp` reduced to the exact-rule `L⁸` bounds and an energy
event** (every `n ≥ 40 000`): as `classifier_paper_exact22k`, with `H_f = 1.005` supplied on an
abstract measurable event `Een` of charge at most `10⁻⁶`. -/
theorem classifier_paper_exactE30 (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb Een : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb)
    (hEenm : MeasurableSet Een) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    (hroom : δA + δb + 1 / 10 ^ 6 ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {ε Af Aw : ℝ} (hε1 : ε < 1) (hT : 0 < ε - vmaxN n / dStar) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε (vmaxN n) (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) (1005 / 1000) (CvN n) ≤ (5154 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomZ c Af Aw) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hn1 : 1 ≤ n := by omega
  have hCv : 0 < CvN n := by
    have : (21500 : ℝ) ≤ n := by exact_mod_cast hn
    unfold CvN; have : (0:ℝ) < (n:ℝ) - 2 := by linarith
    positivity
  have hA' : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      (EA ∩ Een)ᶜ) ≤ δA + 1 / 10 ^ 6 := by
    rw [Set.compl_inter, Set.inter_union_distrib_left]
    refine (measureReal_union_le _ _).trans (add_le_add hA ?_)
    exact (measureReal_mono Set.inter_subset_right).trans hEen
  refine classifier_paper_momY22k hHQ hn t (hEA.inter hEenm) hEb hA' hb (by linarith) hε1 hT hAf hAw
    (by norm_num) hCv hnum fun c hc => ?_
  have hc' : c ∈ goodD n (paperDesignP n) (EA ∩ Eb) :=
    goodD_mono _ (fun x (hx : x ∈ (EA ∩ Een) ∩ Eb) => (⟨hx.1.1, hx.2⟩ : x ∈ EA ∩ Eb)) hc
  have hZ := hM c hc'
  have hcE : c ∈ Een := (mem_of_goodD _ hc).1.2
  obtain ⟨hτ, -, -⟩ := BstLean.Part164.window_goodA (by omega) passF passW measurable_passF
    measurable_passW _ c hc
  obtain ⟨f4, f24⟩ := hfE c hcE hτ
  refine ⟨fun a _ => ?_, hZ.hXF, hZ.hXW, f4, f24, VR_L2 hn hc⟩
  obtain ⟨h0, h1⟩ := VR_le hn hc a
  rw [abs_of_nonneg h0]; exact h1

/-- **The classifier theorem with `BIAS_hyp` reduced to two exact-rule `L⁸` allowances under the
weak linear condition `A_ω + 2.01·A_f ≤ 0.429`** (energy event; every `n ≥ 40 000`). -/
theorem classifier_paper_AE30 (hHQ : BstLean.Part182.HQF21M_stmt) (hn : 21500 ≤ n) (t : ℝ)
    {EA Eb Een : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb)
    (hEenm : MeasurableSet Een) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hEen : (retDist (paperCentres n)).real Eenᶜ ≤ 1 / 10 ^ 6)
    (hfE : ∀ c ∈ Een, 0 < (paperDesignP n).tau0 c → (∫ a in KR c, fbR c a ^ 4 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 4) ∧
      (∫ a in KR c, fbR c a ^ 24 ∂BstLean.Part161.muI n ≤ (1005 / 1000) ^ 24))
    (hroom : δA + δb + 1 / 10 ^ 6 ≤ roomK + BstLean.Part181.roomX + BstLean.Part182.roomT21M)
    {Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 201 / 100 * Af ≤ 40412 / 100000) (hAf' : Af ≤ 66 / 1000)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomZ c Af Aw) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hT : 0 < 1 / 50 - vmaxN n / dStar := by
    have hv := vmaxN_le hn
    have hd : (2002 : ℝ) / 10000 ≤ dStar := by unfold dStar; norm_num
    have : vmaxN n / dStar ≤ 159 / 100000 / (2002 / 10000) :=
      div_le_div₀ (by norm_num) hv (by norm_num) hd
    have h2 : (159 / 100000 : ℝ) / (2002 / 10000) < 1 / 50 := by norm_num
    linarith
  exact classifier_paper_exactE30 hHQ hn t hEA hEb hEenm hA hb hEen hfE hroom (by norm_num) hT hAf hAw
    (PB_leE hn hAf hAw hlin hAf') hM
end SPart169Num

end BstLean.Part179.N30.N27.N26.N25.N24.N23.N22.N21.M

