import BstLean.Part181Def

/-!
# Part 181 (file `Split`): the Agent-replacement plumbing at `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 180's file `Split` with the floor `22 000`. The junction
`BstLean.Part163.classifier_paper_free23` is replaced by the hypothesis `FREE22_stmt`
(file `Def`); the rooms carry `+ roomX`.
* `classifier_paper_free22_fluctH` takes `hF : FREE22_stmt`.
* `classifier_paper_free22_psi12eH`, `classifier_paper_free22_cA8EH` take `hHQ : HQF_stmt`
  (`hHQ.1`: Lemma HQ; `hHQ.2`: the junction).
-/

namespace BstLean.Part181

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (FLUCT_hyp BIAS_hyp SplitData muI lamX sigX)
open BstLean.Part162
open BstLean.Part163 (Eframe)
open BstLean.Part180 (HQ_stmt rootFLH)

variable {n : ℕ}

/-- **The free-event classifier theorem with `FLUCT_hyp` (every `n ≥ 22 000`).** -/
theorem classifier_paper_free22_fluctH (hF : FREE22_stmt) (hn : 22000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part163.roomA + roomX) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hFl : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ d : SplitData n, FLUCT_hyp (paperDesign n fT wT hf hw) t c d hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c d hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine hF hn fT wT hf hw t hEA hA hroom ?_
  refine BstLean.Part177.repla_of_hypsG (by omega) _ t hsum (fun c hc => ?_) hFl
  exact BstLean.Part161.window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1.1.1 hc.2.1.1.2

/-- **The free-event classifier theorem with the Lemma HQ root (every `n ≥ 22 000`).** -/
theorem classifier_paper_free22_psi12eH (hHQ : HQF_stmt) (hn : 22000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part163.roomA + roomX) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hM : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS E βlow lam lam' : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
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
        eps0 ws σl < 1 ∧ 0 < lam ∧ lam < 1 ∧ 0 < lam' ∧ lam' < 1 ∧
        rootFLH wl ws η CA lam lam' (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          hE hβ hL12 hS12 hE8 hmass) ≤ hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_free22_fluctH hHQ.2 hn fT wT hf hw t hEA hA hroom hsum fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, E, βlow, lam, lam', h0, h1, hCL, hCS, hE, hβ, hL12, hS12, hE8,
    hmass, hwl, hws, hσl, hcA, hCA, hε, hl0, hl1, hl0', hl1', hroot, hbias⟩ := hM c hc
  exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1,
    hHQ.1 (by omega) _ c t hwl hws hσl h0 h1 hcA hCA hε
      (latMomOfPsi12e (by omega) _ c hCL hCS hE hβ hL12 hS12 hE8 hmass) hl0 hl1 hl0' hl1' hroot,
    hbias⟩

open BstLean.Part164 (goodA CAn roomB) in
/-- **Part 177's `N43.classifier_paper_free22_cA8EG` with the Lemma HQ root.** -/
theorem classifier_paper_free22_cA8EH (hHQ : HQF_stmt) (hn : 22000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomB + roomX) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA),
      ∃ (wl ws σl η CL CS βlow E lam lam' : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hβ : 0 ≤ βlow) (hE : 0 ≤ E)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ eps0 ws σl < 1 ∧ 0 < lam ∧ lam < 1 ∧ 0 < lam' ∧ lam' < 1 ∧
        rootFLH wl ws η (CAn n) lam lam' (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c
          hCL hCS hE hβ hL12 hS12 hE8 hmass) ≤ hfl ∧
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
  have hroom' : δA + 2 * rexp (-12) + rexp (-(25 / 2)) ≤ BstLean.Part163.roomA + roomX := by
    unfold roomB at hroom; linarith
  refine classifier_paper_free22_psi12eH hHQ hn fT wT hf hw t hEA' hA' hroom' hsum
    fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CL, CS, βlow, E, lam, lam', h0, h1, hCL, hCS, hβ, hE, hL12, hS12, hE8, hmass,
    hwl, hws, hσl, hε, hl0, hl1, hl0', hl1', hroot, hbias⟩ := hM c hc
  obtain ⟨hpos, hle⟩ := BstLean.Part164.cA_of_good (by omega) fT wT hf hw hc
  exact ⟨wl, ws, σl, η, CAn n, CL, CS, E, βlow, lam, lam', h0, h1, hCL, hCS, hE, hβ, hL12, hS12,
    hE8, hmass, hwl, hws, hσl, hpos, hle, hε, hl0, hl1, hl0', hl1', hroot, hbias⟩

end BstLean.Part181
