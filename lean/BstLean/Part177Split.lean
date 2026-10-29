import BstLean.Part177Top

/-!
# Part 177 (file `Split`): the Hellinger split as a free parameter

No proof is left open; no `native_decide` or `axiom` is used.

Parts 161–164 fix the split of the replacement root `h_A = 0.006583 + 10⁻²⁰` as
`0.002159` (fluctuation root) `+ 0.004295` (bias root) `+ √(8e^{−20})` (tail). Here the first
two are free reals `hfl`, `hb` with `hfl + hb ≤ 0.006454`:
* `repla_of_hypsG`, `repla_of_hyps_chiG` (Part 161);
* `classifier_paper_free23_fluctG`, `classifier_paper_free23_psi12eG` (Part 163);
* `N43.classifier_paper_free23_cA8EG` (file `Top`'s `classifier_paper_free23_cA8E`).
-/

namespace BstLean.Part177

section SRed
open MeasureTheory ProbabilityTheory Real
open BstLean.Part161
open BstLean.Part157

variable {n : ℕ}

/-- The arithmetic of the assembly with a free split: `hfl + hb + √(8e^{−20}) ≤ h_A`. -/
theorem repla_arithG {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6) :
    hfl + hb + √(2 * (4 * exp (-20))) ≤ BstLean.Part156.hAL := by
  have h := repla_arith
  linarith

/-- **`REPLA_mix_hyp` from the named hypotheses with a free split.** -/
theorem repla_of_hypsG (hn : 16384 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ d : SplitData n, FLUCT_hyp D t c d hfl ∧ BIAS_hyp D c d hb) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  intro c hc
  obtain ⟨d, hF, hB⟩ := hd c hc
  have hwc := hw c hc
  have h := repla_root_of_split (by omega) D t c hwc.1 hwc.2.1 d hF hB
    (tail_of_window hn D c hwc)
  exact h.trans (repla_arithG hsum)

/-- **Part 161's `repla_of_hyps_chi` with a free split.** -/
theorem repla_of_hyps_chiG (hn : 16384 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
      FLUCT_chi_hyp D c d ε₀ δ₀ slow hfl ∧ BIAS_hyp D c d hb) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  refine repla_of_hypsG hn D t hsum hw fun c hc => ?_
  obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hd c hc
  exact ⟨d, fluct_of_chi D t c d hF, hB⟩

end SRed

section SBias
open BstLean.Part163
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (FLUCT_chi_hyp BIAS_hyp SplitData muI lamX sigX)
open BstLean.Part162

variable {n : ℕ}

/-- **The free-event classifier theorem with Part 161's named hypotheses (every `n ≥ 23 000`).** -/
theorem classifier_paper_free23_fluctG (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomA) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hFl : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
        FLUCT_chi_hyp (paperDesign n fT wT hf hw) c d ε₀ δ₀ slow hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c d hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_free23 hn fT wT hf hw t hEA hA hroom ?_
  refine BstLean.Part177.repla_of_hyps_chiG (by omega) _ t hsum (fun c hc => ?_) hFl
  exact BstLean.Part161.window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1.1.1 hc.2.1.1.2

/-- **The free-event classifier theorem with the Agent replacement in the form of Part 162's
`classifier_agent_psi12e` (every `n ≥ 23 000`).** IF `E_A` is a measurable event with
`Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomA`, and for every `c` in
`goodSet (HP n) (E_{θ−} ∩ E_{θ+} ∩ E_A ∩ Eframe D) (HbarW D) hWL` there are constants with the two
order-12 certificates `‖Ψ_λ‖₁₂ ≤ C_λ/n`, `‖Ψ_σ‖₁₂ ≤ C_σ/n`, the eighth moment `∫∫σ⁸ ≤ E⁸`, the mass
below the floor `≤ β_low`, `0 < |c_A|² ≤ C_A`, `ε₀ < 1`, the root sum `≤ 0.002159` and
`BIAS_hyp … 0.004295`, THEN success `≥ 99/100`. -/
theorem classifier_paper_free23_psi12eG (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomA) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hM : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS E βlow : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hE : 0 ≤ E) (hβ : 0 ≤ βlow)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧
        rootFL wl ws η CA (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS hE hβ
          hL12 hS12 hE8 hmass) ≤ hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_free23_fluctG hn fT wT hf hw t hEA hA hroom hsum fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, E, βlow, h0, h1, hCL, hCS, hE, hβ, hL12, hS12, hE8, hmass,
    hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1, eps0 ws σl, 2 * wl, σl ^ 2,
    fluct_of_latMom (by omega) _ c hwl hws hσl h0 h1 hcA hCA hε
      (latMomOfPsi12e (by omega) _ c hCL hCS hE hβ hL12 hS12 hE8 hmass) hroot, hbias⟩

end SBias

end BstLean.Part177

namespace BstLean.Part177.N43

section SCA
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part164 (goodA CAn roomB)

variable {n : ℕ}

/-- **Part 164's `classifier_paper_free23_cA8` with a free bound `E` of the eighth moment of `σ`**
(Part 164 fixes `E = E0 n`, an operator-norm bound `≈ 4.06·√γ_A`; here the caller supplies `E`
and a proof of `∫∫σ⁸ ≤ E⁸` for each retained value of the good set). -/
theorem classifier_paper_free23_cA8EG (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomB) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA),
      ∃ (wl ws σl η CL CS βlow E : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hβ : 0 ≤ βlow) (hE : 0 ≤ E)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ eps0 ws σl < 1 ∧
        rootFL wl ws η (CAn n) (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          hE hβ hL12 hS12 hE8 hmass) ≤ hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hEA' : MeasurableSet (EA ∩ BstLean.Part164.EcA (paperCentres n) ∩ BstLean.Part164.Eop2 n) :=
    (hEA.inter (BstLean.Part164.measurableSet_EcA _)).inter (BstLean.Part164.measurableSet_Eop2 n)
  have hA' : (retDist (paperCentres n)).real (S ∩ (EA ∩ BstLean.Part164.EcA (paperCentres n) ∩
      BstLean.Part164.Eop2 n)ᶜ) ≤ δA + 2 * rexp (-12) + rexp (-(25 / 2)) := by
    have hsub : S ∩ (EA ∩ BstLean.Part164.EcA (paperCentres n) ∩ BstLean.Part164.Eop2 n)ᶜ ⊆
        ((S ∩ EAᶜ) ∪ (BstLean.Part164.EcA (paperCentres n))ᶜ) ∪ (BstLean.Part164.Eop2 n)ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · by_cases h2 : c ∈ BstLean.Part164.EcA (paperCentres n)
        · exact Or.inr fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl ⟨hc.1, h1⟩)
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have u1 := measureReal_union_le (μ := retDist (paperCentres n)) (S ∩ EAᶜ)
      (BstLean.Part164.EcA (paperCentres n))ᶜ
    have c1 := BstLean.Part164.EcA_charge (by omega) (paperCentres n)
    have c2 := BstLean.Part164.Eop2_charge (by omega) (paperCentres n)
    linarith
  have hroom' : δA + 2 * rexp (-12) + rexp (-(25 / 2)) ≤ BstLean.Part163.roomA := by
    unfold roomB at hroom; linarith
  refine BstLean.Part177.classifier_paper_free23_psi12eG hn fT wT hf hw t hEA' hA' hroom' hsum
    fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CL, CS, βlow, E, h0, h1, hCL, hCS, hβ, hE, hL12, hS12, hE8, hmass, hwl, hws,
    hσl, hε, hroot, hbias⟩ := hM c hc
  obtain ⟨hpos, hle⟩ := BstLean.Part164.cA_of_good (by omega) fT wT hf hw hc
  exact ⟨wl, ws, σl, η, CAn n, CL, CS, E, βlow, h0, h1, hCL, hCS, hE, hβ, hL12, hS12,
    hE8, hmass, hwl, hws, hσl, hpos, hle, hε, hroot, hbias⟩

end SCA

end BstLean.Part177.N43
